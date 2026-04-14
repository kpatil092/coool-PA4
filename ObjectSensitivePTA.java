import soot.*;
import soot.jimple.*;

import java.util.*;

public class ObjectSensitivePTA {
    class PTAVar {
        String localName;
        SootMethod method;
        Set<AllocObject> pointsTo = new HashSet<>();

        PTAVar(String localName, SootMethod method) {
            this.localName = localName;
            this.method = method;
        }
    }

    class AllocObject {
        String siteName;
        SootClass allocType;
        SootMethod declaringMethod;
        Map<SootField, Set<AllocObject>> fields = new HashMap<>();

        AllocObject(String siteName, SootClass allocType, SootMethod declaringMethod) {
            this.siteName = siteName;
            this.allocType = allocType;
            this.declaringMethod = declaringMethod;
        }

        Set<AllocObject> getField(SootField f) {
            return fields.computeIfAbsent(f, __ -> new HashSet<>());
        }
    }

    class ContextMethod {
        SootMethod method;
        List<AllocObject> context;

        /**
         * Where callers want the return value propagated.
         * Multiple callers may share the same (method, context) but want
         * results in different variables → we keep a *set* of destinations
         * and merge into all of them during return processing.
         */
        Set<PTAVar> returnDests = new HashSet<>();

        ContextMethod(SootMethod method, List<AllocObject> context) {
            this.method = method;
            this.context = Collections.unmodifiableList(new ArrayList<>(context));
        }

        @Override
        public boolean equals(Object o) {
            if (this == o)
                return true;
            if (!(o instanceof ContextMethod))
                return false;
            ContextMethod that = (ContextMethod) o;
            return method.equals(that.method) && context.equals(that.context);
        }

        @Override
        public int hashCode() {
            return Objects.hash(method, context);
        }
    }

    // ---------------------

    final AllocObject NULL_OBJ = new AllocObject("<<null>>", null, null);
    int k;

    Map<ContextMethod, ContextMethod> reachable = new HashMap<>();
    ArrayDeque<ContextMethod> worklist = new ArrayDeque<>();

    Map<String, PTAVar> varCache = new HashMap<>();
    Map<String, AllocObject> allocCache = new HashMap<>();

    Map<ContextMethod, Map<Stmt, Set<ContextMethod>>> callGraph = new HashMap<>();

    ObjectSensitivePTA(int k) {
        // if (k < 0 || k > 3) throw new IllegalArgumentException("k must be 0-3");
        this.k = k;
    }

    // -----------------------------

    public void run(List<SootMethod> entryPoints) {
        for (SootMethod m : entryPoints) {
            if (m.isConcrete()) {
                ContextMethod cm = getOrCreateCM(m, Collections.emptyList());
                seedEntryPoint(cm);
            }
        }

        while (!worklist.isEmpty()) {
            ContextMethod cm = worklist.poll();
            analyzeMethod(cm);
        }
    }

    // ------------------------------------------------------------------ //
    // Method analysis //
    // ------------------------------------------------------------------ //

    private void analyzeMethod(ContextMethod cm) {
        if (cm.method.getDeclaringClass().isJavaLibraryClass()) {
            return;
        }
        Body body = cm.method.retrieveActiveBody();
        // System.out.println("Analyzing " + cm.method.getSignature() + " in context " +
        // ctxKey(cm.context));

        for (Unit u : body.getUnits()) {
            Stmt stmt = (Stmt) u;
            if (stmt instanceof AssignStmt) {
                if (processAssign((AssignStmt) stmt, cm)) {
                    enqueue(cm);
                }
            } else if (stmt instanceof InvokeStmt) {
                processInvoke(stmt, ((InvokeStmt) stmt).getInvokeExpr(), cm, null);
            } else if (stmt instanceof ReturnStmt) {
                processReturn((ReturnStmt) stmt, cm);
            }
        }
    }

    // ------------------------------------------------------------------ //
    // Statement handlers //
    // ------------------------------------------------------------------ //

    /** Returns true if any points-to set grew (so the caller can re-enqueue). */
    private boolean processAssign(AssignStmt stmt, ContextMethod cm) {
        boolean changed = false;
        boolean heapChanged = false;
        Value lhs = stmt.getLeftOp();
        Value rhs = stmt.getRightOp();

        // ---- LHS is a local variable ---------------------------------- //
        if (lhs instanceof Local) {
            PTAVar lhsVar = varFor((Local) lhs, cm);

            if (rhs instanceof NewExpr) {
                // x = new T()
                SootClass allocClass = ((RefType) ((NewExpr) rhs).getBaseType()).getSootClass();
                AllocObject obj = allocFor(stmt.toString(), allocClass, cm);
                changed |= lhsVar.pointsTo.add(obj);

            } else if (rhs instanceof Local) {
                // x = y
                PTAVar rhsVar = varFor((Local) rhs, cm);
                changed |= lhsVar.pointsTo.addAll(rhsVar.pointsTo);

            } else if (rhs instanceof CastExpr) {
                // x = (T) y
                Value op = ((CastExpr) rhs).getOp();
                if (op instanceof Local) {
                    changed |= lhsVar.pointsTo.addAll(varFor((Local) op, cm).pointsTo);
                }

            } else if (rhs instanceof InstanceFieldRef) {
                // x = b.f
                InstanceFieldRef ifr = (InstanceFieldRef) rhs;
                SootField field = ifr.getField();
                if (ifr.getBase() instanceof Local) {
                    PTAVar baseVar = varFor((Local) ifr.getBase(), cm);
                    for (AllocObject obj : new ArrayList<>(baseVar.pointsTo)) {
                        if (obj == NULL_OBJ)
                            continue;
                        changed |= lhsVar.pointsTo.addAll(obj.getField(field));
                    }
                }

            } else if (rhs instanceof StaticFieldRef) {
                // x = ClassName.f – handled via global static field map
                SootField field = ((StaticFieldRef) rhs).getField();
                changed |= lhsVar.pointsTo.addAll(getStaticField(field));

            } else if (rhs instanceof InvokeExpr) {
                // x = foo(...)
                changed |= processInvoke(stmt, (InvokeExpr) rhs, cm, lhsVar);

            } else if (rhs instanceof NullConstant) {
                changed |= lhsVar.pointsTo.add(NULL_OBJ);

            } else if (rhs instanceof NewArrayExpr || rhs instanceof NewMultiArrayExpr) {
                // Treat array allocation like a regular object.
                AllocObject obj = allocFor(stmt.toString(), null, cm);
                changed |= lhsVar.pointsTo.add(obj);
            }

            // ---- LHS is an instance field --------------------------------- //
        } else if (lhs instanceof InstanceFieldRef) {
            // b.f = rhs
            InstanceFieldRef ifr = (InstanceFieldRef) lhs;
            SootField field = ifr.getField();
            if (ifr.getBase() instanceof Local && rhs instanceof Local) {
                PTAVar baseVar = varFor((Local) ifr.getBase(), cm);
                PTAVar rhsVar = varFor((Local) rhs, cm);
                for (AllocObject obj : new ArrayList<>(baseVar.pointsTo)) {
                    if (obj == NULL_OBJ)
                        continue;
                    boolean fieldChanged = obj.getField(field).addAll(rhsVar.pointsTo);
                    changed |= fieldChanged;
                    heapChanged |= fieldChanged;
                }
            }

            // ---- LHS is a static field ------------------------------------ //
        } else if (lhs instanceof StaticFieldRef) {
            // ClassName.f = rhs
            SootField field = ((StaticFieldRef) lhs).getField();
            if (rhs instanceof Local) {
                PTAVar rhsVar = varFor((Local) rhs, cm);
                boolean fieldChanged = getStaticField(field).addAll(rhsVar.pointsTo);
                changed |= fieldChanged;
                heapChanged |= fieldChanged;
            }
        }

        if (heapChanged)
            requeueAll();

        return changed;
    }

    /** Dispatch an invoke expression; returns true if any set grew. */
    private boolean processInvoke(Stmt stmt, InvokeExpr ie, ContextMethod cm, PTAVar retDst) {
        if (ie instanceof StaticInvokeExpr)
            return processStaticCall(stmt, (StaticInvokeExpr) ie, cm, retDst);
        if (ie instanceof SpecialInvokeExpr)
            return processSpecialCall(stmt, (SpecialInvokeExpr) ie, cm, retDst);
        if (ie instanceof InstanceInvokeExpr)
            return processVirtualCall(stmt, (InstanceInvokeExpr) ie, cm, retDst);
        return false;
    }

    /** Propagate return value to all registered destinations. */
    private void processReturn(ReturnStmt stmt, ContextMethod cm) {
        Value retVal = stmt.getOp();
        if (!(retVal instanceof Local) || cm.returnDests.isEmpty())
            return;
        PTAVar retVar = varFor((Local) retVal, cm);
        for (PTAVar dst : cm.returnDests) {
            if (dst.pointsTo.addAll(retVar.pointsTo)) {
                // The destination variable's owning context-method must be re-run.
                // We conservatively re-enqueue all reachable methods that own dst.
                // (A finer approach: maintain a reverse map variable->CM.)
                requeueAll();
            }
        }
    }

    // ------------------------------------------------------------------ //
    // Call handlers //
    // ------------------------------------------------------------------ //

    private boolean processStaticCall(Stmt stmt, StaticInvokeExpr se, ContextMethod cm, PTAVar retDst) {
        SootMethod callee = resolve(se.getMethodRef());
        if (callee == null)
            return false;

        // Static calls inherit the caller's context unchanged (no new receiver).
        List<AllocObject> newCtx = trimContext(cm.context);
        ContextMethod calleeContext = getOrCreateCM(callee, newCtx);

        recordCall(cm, stmt, calleeContext);
        boolean changed = false;
        if (retDst != null)
            changed |= calleeContext.returnDests.add(retDst);
        changed |= pairArgs(se.getArgs(), cm, callee, calleeContext);
        if (changed)
            enqueue(calleeContext);
        return changed;
    }

    private boolean processSpecialCall(Stmt stmt, SpecialInvokeExpr se, ContextMethod cm, PTAVar retDst) {
        SootMethod callee = resolve(se.getMethodRef());
        if (callee == null || !(se.getBase() instanceof Local))
            return false;

        PTAVar baseVar = varFor((Local) se.getBase(), cm);
        boolean changed = false;

        for (AllocObject receiver : new ArrayList<>(baseVar.pointsTo)) {
            if (receiver == NULL_OBJ)
                continue;

            List<AllocObject> newCtx = pushContext(cm.context, receiver);
            ContextMethod calleeContext = getOrCreateCM(callee, newCtx);
            recordCall(cm, stmt, calleeContext);

            // Bind 'this' in callee
            changed |= varForThis(calleeContext).pointsTo.add(receiver);
            if (retDst != null)
                changed |= calleeContext.returnDests.add(retDst);
            changed |= pairArgs(se.getArgs(), cm, callee, calleeContext);
            if (changed)
                enqueue(calleeContext);
        }
        return changed;
    }

    private boolean processVirtualCall(Stmt stmt, InstanceInvokeExpr ie, ContextMethod cm, PTAVar retDst) {
        if (!(ie.getBase() instanceof Local))
            return false;

        PTAVar baseVar = varFor((Local) ie.getBase(), cm);
        boolean changed = false;

        for (AllocObject receiver : new ArrayList<>(baseVar.pointsTo)) {
            if (receiver == NULL_OBJ || receiver.allocType == null)
                continue;

            SootMethod callee = resolveVirtual(receiver.allocType, ie.getMethodRef());
            if (callee == null)
                continue;

            List<AllocObject> newCtx = pushContext(cm.context, receiver);
            ContextMethod calleeContext = getOrCreateCM(callee, newCtx);
            recordCall(cm, stmt, calleeContext);

            // Bind 'this' in callee
            changed |= varForThis(calleeContext).pointsTo.add(receiver);
            if (retDst != null)
                changed |= calleeContext.returnDests.add(retDst);
            changed |= pairArgs(ie.getArgs(), cm, callee, calleeContext);
            if (changed)
                enqueue(calleeContext);
        }
        return changed;
    }

    // ------------------------------------------------------------------ //
    // Helpers //
    // ------------------------------------------------------------------ //

    /**
     * Pair actual arguments in the caller to formal parameters in the callee.
     * Parameter locals are named by their position: "@parameter0", "@parameter1",
     * ...
     * (Jimple convention). We key on that so analyzeMethod finds them correctly.
     */
    private boolean pairArgs(List<Value> args, ContextMethod callerCM,
            SootMethod callee, ContextMethod calleeCM) {
        boolean changed = false;
        Body calleeBody = null;
        if (callee.isConcrete() && callee.hasActiveBody()) {
            calleeBody = callee.getActiveBody();
        }
        for (int i = 0; i < args.size(); i++) {
            Value arg = args.get(i);
            if (!(arg instanceof Local))
                continue;
            PTAVar argVar = varFor((Local) arg, callerCM);
            // Fetch the callee's formal parameter local from its body if available.
            String paramLocalName = (calleeBody != null && i < callee.getParameterCount())
                    ? calleeBody.getParameterLocal(i).getName()
                    : ("@parameter" + i);
            PTAVar paramVar = getOrCreateVar(paramLocalName, calleeCM);
            changed |= paramVar.pointsTo.addAll(argVar.pointsTo);
        }
        return changed;
    }

    /**
     * Seed an entry-point method with fresh abstract objects for its parameters.
     */
    private void seedEntryPoint(ContextMethod cm) {
        if (!cm.method.isConcrete() || !cm.method.hasActiveBody()) {
            return;
        }
        Body body = cm.method.getActiveBody();
        if (!cm.method.isStatic()) {
            Local thisLocal = body.getThisLocal();
            SootClass cls = cm.method.getDeclaringClass();
            AllocObject thisObj = allocFor("<<entry-this>>", cls, cm);
            varFor(thisLocal, cm).pointsTo.add(thisObj);
        }
        for (int i = 0; i < cm.method.getParameterCount(); i++) {
            Type pType = cm.method.getParameterType(i);
            if (!(pType instanceof RefType))
                continue; // skip primitives
            Local paramLocal = body.getParameterLocal(i);
            SootClass cls = ((RefType) pType).getSootClass();
            AllocObject paramObj = allocFor("<<entry-param" + i + ">>", cls, cm);
            varFor(paramLocal, cm).pointsTo.add(paramObj);
        }
    }

    /** Push receiver onto the front of the context, trimming to length k. */
    private List<AllocObject> pushContext(List<AllocObject> ctx, AllocObject receiver) {
        List<AllocObject> next = new ArrayList<>();
        next.add(receiver);
        next.addAll(ctx);
        return trimContext(next);
    }

    /** Trim a context list to at most k elements (keep the most-recent). */
    private List<AllocObject> trimContext(List<AllocObject> ctx) {
        if (ctx.size() <= k)
            return ctx;
        return new ArrayList<>(ctx.subList(0, k));
    }

    // ------------------------------------------------------------------ //
    // Cache management //
    // ------------------------------------------------------------------ //

    /** Get or create the canonical ContextMethod, and enqueue it if new. */
    private ContextMethod getOrCreateCM(SootMethod method, List<AllocObject> ctx) {
        ContextMethod key = new ContextMethod(method, ctx);
        ContextMethod existing = reachable.get(key);
        if (existing != null)
            return existing;
        reachable.put(key, key);
        worklist.add(key);
        return key;
    }

    private PTAVar varFor(Local local, ContextMethod cm) {
        return getOrCreateVar(local.getName(), cm);
    }

    private PTAVar varForThis(ContextMethod cm) {
        if (!cm.method.isConcrete() || !cm.method.hasActiveBody() || cm.method.isStatic()) {
            return getOrCreateVar("@this", cm);
        }
        return varFor(cm.method.getActiveBody().getThisLocal(), cm);
    }

    private PTAVar getOrCreateVar(String localName, ContextMethod cm) {
        String key = varKey(localName, cm);
        PTAVar v = varCache.get(key);
        if (v == null) {
            v = new PTAVar(localName, cm.method);
            varCache.put(key, v);
        }
        return v;
    }

    private AllocObject allocFor(String site, SootClass type, ContextMethod cm) {
        String key = site + "|" + ctxKey(cm.context) + "|" + cm.method.getSignature();
        AllocObject obj = allocCache.get(key);
        if (obj == null) {
            obj = new AllocObject(site, type, cm.method);
            allocCache.put(key, obj);
        }
        return obj;
    }

    // ------------------------------------------------------------------ //
    // Static field global store //
    // ------------------------------------------------------------------ //

    private Map<SootField, Set<AllocObject>> staticFields = new HashMap<>();

    private Set<AllocObject> getStaticField(SootField f) {
        return staticFields.computeIfAbsent(f, __ -> new HashSet<>());
    }

    // ------------------------------------------------------------------ //
    // Key builders //
    // ------------------------------------------------------------------ //

    private String varKey(String localName, ContextMethod cm) {
        return localName + "|" + ctxKey(cm.context) + "|" + cm.method.getSignature();
    }

    private String ctxKey(List<AllocObject> ctx) {
        if (ctx.isEmpty())
            return "";
        StringBuilder sb = new StringBuilder();
        for (AllocObject o : ctx)
            sb.append(o.siteName).append('#');
        return sb.toString();
    }

    // ------------------------------------------------------------------ //
    // Worklist helpers //
    // ------------------------------------------------------------------ //

    private void enqueue(ContextMethod cm) {
        if (!worklist.contains(cm))
            worklist.add(cm);
    }

    /**
     * Conservative re-enqueue: when a return destination grows we don't know
     * which ContextMethod owns it cheaply, so we re-add all reachable ones.
     * For k<=3 and typical programs this is fine; replace with a reverse map
     * for very large programs.
     */
    private void requeueAll() {
        for (ContextMethod cm : reachable.keySet()) {
            if (!worklist.contains(cm))
                worklist.add(cm);
        }
    }

    // ------------------------------------------------------------------ //
    // Virtual dispatch //
    // ------------------------------------------------------------------ //

    private SootMethod resolve(SootMethodRef ref) {
        try {
            SootMethod m = ref.resolve();
            return (m != null && m.isConcrete()) ? m : null;
        } catch (Exception e) {
            return null;
        }
    }

    private SootMethod resolveVirtual(SootClass cls, SootMethodRef ref) {
        try {
            return Scene.v().getActiveHierarchy()
                    .resolveConcreteDispatch(cls, ref.resolve());
        } catch (Exception e) {
            return null;
        }
    }

    private void recordCall(ContextMethod caller, Stmt site, ContextMethod callee) {
        callGraph
                .computeIfAbsent(caller, k -> new HashMap<>())
                .computeIfAbsent(site, k -> new HashSet<>())
                .add(callee);
    }

    // method for printing the call graph
    public void printCallGraph() {
        for (Map.Entry<ContextMethod, Map<Stmt, Set<ContextMethod>>> e : callGraph.entrySet()) {
            ContextMethod caller = e.getKey();
            System.out.println("Caller: " + caller.method.getSignature() + " in context " + ctxKey(caller.context));
            System.out.println("=============================");
            for (Map.Entry<Stmt, Set<ContextMethod>> callSite : e.getValue().entrySet()) {
                Stmt site = callSite.getKey();
                System.out.println("  Call site: " + site);
                for (ContextMethod callee : callSite.getValue()) {
                    System.out.println(
                            "    Callee: " + callee.method.getSignature() + " in context " + ctxKey(callee.context));
                }
                System.out.println("<><><><><>");
            }
            System.out.println("-----------------------------\n---------------------------");
        }
    }

    public Set<ContextMethod> getTargets(ContextMethod cm, Stmt site) {
        return callGraph
                .getOrDefault(cm, Collections.emptyMap())
                .getOrDefault(site, Collections.emptySet());
    }

    public Set<ContextMethod> getReachableContexts() {
        return new LinkedHashSet<>(reachable.keySet());
    }
}

/*
 * 
 * ✅ 5A. Context-sensitive targets
 * public Set<ContextMethod> getTargets(ContextMethod cm, Stmt site) {
 * return callGraph
 * .getOrDefault(cm, Collections.emptyMap())
 * .getOrDefault(site, Collections.emptySet());
 * }
 * ✅ 5B. Context-insensitive targets
 * public Set<SootMethod> getTargets(SootMethod method, Stmt site) {
 * Set<SootMethod> result = new HashSet<>();
 * 
 * for (Map.Entry<ContextMethod, Map<Stmt, Set<ContextMethod>>> e :
 * callGraph.entrySet()) {
 * if (!e.getKey().method.equals(method))
 * continue;
 * 
 * Set<ContextMethod> cms = e.getValue().get(site);
 * if (cms != null) {
 * for (ContextMethod c : cms)
 * result.add(c.method);
 * }
 * }
 * 
 * return result;
 * }
 * ✅ 5C. Monomorphism check
 * public boolean isMonomorphic(ContextMethod cm, Stmt site) {
 * Set<ContextMethod> targets = getTargets(cm, site);
 * return targets.size() == 1;
 * }
 * 🚀 6. How YOU Use It (Cloning + Inlining)
 * 
 * Now your pipeline becomes:
 * 
 * Step 1: iterate all context methods
 * for (ContextMethod cm : reachable.keySet()) {
 * Body body = cm.method.retrieveActiveBody();
 * Step 2: inspect call sites
 * for (Unit u : body.getUnits()) {
 * Stmt stmt = (Stmt) u;
 * 
 * if (!stmt.containsInvokeExpr()) continue;
 * Step 3: query PTA
 * Set<ContextMethod> targets = getTargets(cm, stmt);
 * Step 4: context-sensitive monomorphisation
 * if (targets.size() == 1) {
 * ContextMethod target = targets.iterator().next();
 * 
 * // 🔥 THIS is your cloning point
 * }
 * 🧬 7. Where Cloning Hooks In
 * 
 * Now you can build:
 * 
 * Map<ContextMethod, SootMethod> cloneMap = new HashMap<>();
 * 
 * Then:
 * 
 * SootMethod cloned = cloneMap.computeIfAbsent(target, t -> cloneMethod(t));
 * 
 * And rewrite:
 * 
 * stmt.getInvokeExpr().setMethodRef(cloned.makeRef());
 * ⚠️ 8. One Important Subtlety (Your Code Specific)
 * 
 * Your ContextMethod:
 * 
 * this.context = Collections.unmodifiableList(...)
 * 
 * ✅ GOOD
 * 
 */
