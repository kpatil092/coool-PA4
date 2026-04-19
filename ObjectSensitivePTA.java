import soot.*;
import soot.jimple.*;
import java.util.*;

public class ObjectSensitivePTA {

    // like, a->obj1, a->onj2
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

    final AllocObject NULL_OBJ = new AllocObject("<null_pointer>", null, null);
    int k;

    Map<ContextMethod, ContextMethod> reachable = new HashMap<>();
    ArrayDeque<ContextMethod> worklist = new ArrayDeque<>();

    Map<String, PTAVar> varCache = new HashMap<>();
    Map<String, AllocObject> allocCache = new HashMap<>();

    Map<ContextMethod, Map<Stmt, Set<ContextMethod>>> callGraph = new HashMap<>();

    Map<SootField, Set<AllocObject>> staticFields = new HashMap<>();

    // Work: TO add onWorkList set, to avoid contains check, t

    ObjectSensitivePTA(int k) {
        this.k = k;
    }

    // -----------------------------

    public void run(List<SootMethod> entryPoints) {
        for (SootMethod m : entryPoints) {
            if (m.isConcrete()) {
                ContextMethod cm = getOrCreateCM(m, Collections.emptyList());
                addEntryParams(cm);
            }
        }

        while (!worklist.isEmpty()) {
            ContextMethod cm = worklist.poll();
            analyzeMethod(cm);
        }
    }

    ////////////

    void analyzeMethod(ContextMethod cm) {
        if (cm.method.getDeclaringClass().isJavaLibraryClass()) {
            return;
        }
        Body body = cm.method.retrieveActiveBody();
        // System.out.println("Analyzing " + cm.method.getSignature() + " in context " +
        // ctxKey(cm.context));

        for (Unit u : body.getUnits()) {
            Stmt stmt = (Stmt) u;
            if (stmt instanceof AssignStmt) {
                if (processAssign((AssignStmt) stmt, cm) && !worklist.contains(cm)) {
                    worklist.add(cm);
                    // enqueue(cm);
                }
            } else if (stmt instanceof InvokeStmt) {
                processInvoke(stmt, ((InvokeStmt) stmt).getInvokeExpr(), cm, null);
            } else if (stmt instanceof ReturnStmt) {
                processReturn((ReturnStmt) stmt, cm);
            }
        }
    }

    // ------------------------------------------------------------------

    boolean processAssign(AssignStmt stmt, ContextMethod cm) {
        boolean changed = false;
        boolean heapChanged = false;
        Value lhs = stmt.getLeftOp();
        Value rhs = stmt.getRightOp();

        if (lhs instanceof Local) {
            PTAVar lhsVar = varFor(((Local) lhs).getName(), cm);

            if (rhs instanceof NewExpr) { // x = new T()
                SootClass allocClass = ((RefType) ((NewExpr) rhs).getBaseType()).getSootClass();
                AllocObject obj = allocFor(stmt.toString(), allocClass, cm);
                changed |= lhsVar.pointsTo.add(obj);
            } else if (rhs instanceof Local) {
                // x = y
                PTAVar rhsVar = varFor(((Local) rhs).getName(), cm);
                changed |= lhsVar.pointsTo.addAll(rhsVar.pointsTo);
            } else if (rhs instanceof InstanceFieldRef) {
                // x = b.f
                InstanceFieldRef ifr = (InstanceFieldRef) rhs;
                SootField field = ifr.getField();
                if (ifr.getBase() instanceof Local) {
                    PTAVar baseVar = varFor(((Local) ifr.getBase()).getName(), cm);
                    for (AllocObject obj : new ArrayList<>(baseVar.pointsTo)) {
                        if (obj == NULL_OBJ)
                            continue;
                        changed |= lhsVar.pointsTo.addAll(obj.getField(field));
                    }
                }
            } else if (rhs instanceof StaticFieldRef) {
                SootField field = ((StaticFieldRef) rhs).getField();
                // changed |= lhsVar.pointsTo.addAll(getStaticField(field));
                changed |= lhsVar.pointsTo.addAll(staticFields.computeIfAbsent(field, __ -> new HashSet<>()));
            } else if (rhs instanceof InvokeExpr) {
                changed |= processInvoke(stmt, (InvokeExpr) rhs, cm, lhsVar);
            } else if (rhs instanceof NullConstant) {
                changed |= lhsVar.pointsTo.add(NULL_OBJ);
            } else if (rhs instanceof NewArrayExpr || rhs instanceof NewMultiArrayExpr) {
                AllocObject obj = allocFor(stmt.toString(), null, cm);
                changed |= lhsVar.pointsTo.add(obj);
            }

            else if (rhs instanceof CastExpr) {
                // x = (T) y
                Value op = ((CastExpr) rhs).getOp();
                if (op instanceof Local) {
                    changed |= lhsVar.pointsTo.addAll(varFor(((Local) op).getName(), cm).pointsTo);
                }
            }
        } else if (lhs instanceof InstanceFieldRef) {
            // b.f = rhs
            InstanceFieldRef ifr = (InstanceFieldRef) lhs;
            SootField field = ifr.getField();
            if (ifr.getBase() instanceof Local && rhs instanceof Local) {
                PTAVar baseVar = varFor(((Local) ifr.getBase()).getName(), cm);
                PTAVar rhsVar = varFor(((Local) rhs).getName(), cm);
                for (AllocObject obj : new ArrayList<>(baseVar.pointsTo)) {
                    if (obj == NULL_OBJ)
                        continue;
                    boolean fieldChanged = obj.getField(field).addAll(rhsVar.pointsTo);
                    changed |= fieldChanged;
                    heapChanged |= fieldChanged;
                }
            }

        } else if (lhs instanceof StaticFieldRef) {
            SootField field = ((StaticFieldRef) lhs).getField();
            if (rhs instanceof Local) {
                PTAVar rhsVar = varFor(((Local) rhs).getName(), cm);
                boolean fieldChanged = staticFields.computeIfAbsent(field, __ -> new HashSet<>())
                        .addAll(rhsVar.pointsTo);
                changed |= fieldChanged;
                heapChanged |= fieldChanged;
            }
        }

        if (heapChanged) {
            for (ContextMethod ctxMtd : reachable.keySet()) {
                if (!worklist.contains(ctxMtd))
                    worklist.add(ctxMtd);
            }
        }

        return changed;
    }

    boolean processInvoke(Stmt stmt, InvokeExpr ie, ContextMethod cm, PTAVar retDst) {
        if (ie instanceof StaticInvokeExpr)
            return processStaticCall(stmt, (StaticInvokeExpr) ie, cm, retDst);
        if (ie instanceof SpecialInvokeExpr)
            return processSpecialCall(stmt, (SpecialInvokeExpr) ie, cm, retDst);
        if (ie instanceof InstanceInvokeExpr)
            return processVirtualCall(stmt, (InstanceInvokeExpr) ie, cm, retDst);
        return false;
    }

    void processReturn(ReturnStmt stmt, ContextMethod cm) {
        Value retVal = stmt.getOp();
        if (!(retVal instanceof Local) || cm.returnDests.isEmpty())
            return;
        PTAVar retVar = varFor(((Local) retVal).getName(), cm);
        for (PTAVar dst : cm.returnDests) {
            if (dst.pointsTo.addAll(retVar.pointsTo)) {
                // requeueAll();
                for (ContextMethod ctxMtd : reachable.keySet()) {
                    if (!worklist.contains(ctxMtd))
                        worklist.add(ctxMtd);
                }
            }
        }
    }

    boolean processStaticCall(Stmt stmt, StaticInvokeExpr se, ContextMethod cm, PTAVar retDst) {
        // SootMethod callee = resolve(se.getMethodRef());
        SootMethod callee = null;
        try {
            callee = se.getMethodRef().resolve();
        } catch (Exception e) {
        }

        if (callee == null)
            return false;

        if (!callee.isConcrete())
            return false;

        // List<AllocObject> newCtx = trimContext(cm.context);
        List<AllocObject> newCtx = new ArrayList<>(cm.context);
        if (newCtx.size() > k)
            newCtx = new ArrayList<>(newCtx.subList(0, k));

        ContextMethod calleeContext = getOrCreateCM(callee, newCtx);

        recordCall(cm, stmt, calleeContext);
        boolean changed = false;
        if (retDst != null)
            changed |= calleeContext.returnDests.add(retDst);
        changed |= pairArgs(se.getArgs(), cm, callee, calleeContext);
        if (changed && !worklist.contains(calleeContext))
            worklist.add(calleeContext);
        return changed;
    }

    boolean processSpecialCall(Stmt stmt, SpecialInvokeExpr se, ContextMethod cm, PTAVar retDst) {
        SootMethod callee = null;

        try {
            callee = se.getMethodRef().resolve();
        } catch (Exception e) {
        }

        if (callee == null || !(se.getBase() instanceof Local))
            return false;

        if (!callee.isConcrete())
            return false;

        PTAVar baseVar = varFor(((Local) se.getBase()).getName(), cm);
        boolean changed = false;

        for (AllocObject receiver : new ArrayList<>(baseVar.pointsTo)) {
            if (receiver == NULL_OBJ)
                continue;

            List<AllocObject> newCtx = new ArrayList<>(cm.context);
            newCtx.add(0, receiver);
            if (newCtx.size() > k)
                newCtx = newCtx.subList(0, k);


            ContextMethod calleeContext = getOrCreateCM(callee, newCtx);
            recordCall(cm, stmt, calleeContext);

            // changed |= varForThis(calleeContext).pointsTo.add(receiver);

            PTAVar thisVar = null;
            if (!calleeContext.method.isConcrete() || !calleeContext.method.hasActiveBody()
                    || calleeContext.method.isStatic())
                thisVar = varFor("@this", calleeContext);
            else
                thisVar = varFor(calleeContext.method.getActiveBody().getThisLocal().getName(), calleeContext);

            changed |= thisVar.pointsTo.add(receiver);

            if (retDst != null)
                changed |= calleeContext.returnDests.add(retDst);
            changed |= pairArgs(se.getArgs(), cm, callee, calleeContext);
            if (changed && !worklist.contains(calleeContext))
                worklist.add(calleeContext);
            // enqueue(calleeContext);
        }
        return changed;
    }

    boolean processVirtualCall(Stmt stmt, InstanceInvokeExpr ie, ContextMethod cm, PTAVar retDst) {
        if (!(ie.getBase() instanceof Local))
            return false;

        PTAVar baseVar = varFor(((Local) ie.getBase()).getName(), cm);
        boolean changed = false;

        for (AllocObject receiver : new ArrayList<>(baseVar.pointsTo)) {
            if (receiver == NULL_OBJ || receiver.allocType == null)
                continue;

            SootMethod callee = null;
            // resolveVirtual(receiver.allocType, ie.getMethodRef());
            try {
                callee = Scene.v().getActiveHierarchy()
                        .resolveConcreteDispatch(receiver.allocType, ie.getMethodRef().resolve());
            } catch (Exception e) {
            }

            if (callee == null)
                continue;

            List<AllocObject> newCtx = new ArrayList<>(cm.context);
            newCtx.add(0, receiver);
            if (newCtx.size() > k)
                newCtx = newCtx.subList(0, k);
            //

            ContextMethod calleeContext = getOrCreateCM(callee, newCtx);
            recordCall(cm, stmt, calleeContext);

            // changed |= varForThis(calleeContext).pointsTo.add(receiver);

            PTAVar thisVar = null;
            if (!calleeContext.method.isConcrete() || !calleeContext.method.hasActiveBody()
                    || calleeContext.method.isStatic())
                thisVar = varFor("@this", calleeContext);
            else
                thisVar = varFor(calleeContext.method.getActiveBody().getThisLocal().getName(), calleeContext);

            changed |= thisVar.pointsTo.add(receiver);

            if (retDst != null)
                changed |= calleeContext.returnDests.add(retDst);
            changed |= pairArgs(ie.getArgs(), cm, callee, calleeContext);
            if (changed && !worklist.contains(calleeContext))
                worklist.add(calleeContext);
            // enqueue(calleeContext);
        }
        return changed;
    }

    boolean pairArgs(List<Value> args, ContextMethod callerCM,
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
            PTAVar argVar = varFor(((Local) arg).getName(), callerCM);
            String paramLocalName = (calleeBody != null && i < callee.getParameterCount())
                    ? calleeBody.getParameterLocal(i).getName()
                    : ("@parameter" + i);
            // PTAVar paramVar = getOrCreateVar(paramLocalName, calleeCM);
            PTAVar paramVar = varFor(paramLocalName, calleeCM);
            changed |= paramVar.pointsTo.addAll(argVar.pointsTo);
        }
        return changed;
    }

    void addEntryParams(ContextMethod cm) {
        if (!cm.method.isConcrete() || !cm.method.hasActiveBody()) {
            return;
        }
        Body body = cm.method.getActiveBody();
        if (!cm.method.isStatic()) {
            Local thisLocal = body.getThisLocal();
            SootClass cls = cm.method.getDeclaringClass();
            AllocObject thisObj = allocFor("<THIS_ENTRY>", cls, cm);
            varFor(thisLocal.getName(), cm).pointsTo.add(thisObj);
        }
        for (int i = 0; i < cm.method.getParameterCount(); i++) {
            Type pType = cm.method.getParameterType(i);
            if (!(pType instanceof RefType))
                continue;
            Local paramLocal = body.getParameterLocal(i);
            SootClass cls = ((RefType) pType).getSootClass();
            AllocObject paramObj = allocFor("<PARAM_ENTRY_" + i + ">", cls, cm);
            varFor(paramLocal.getName(), cm).pointsTo.add(paramObj);
        }
    }

    ContextMethod getOrCreateCM(SootMethod method, List<AllocObject> ctx) {
        ContextMethod key = new ContextMethod(method, ctx);
        ContextMethod existing = reachable.get(key);
        if (existing != null)
            return existing;
        reachable.put(key, key);
        worklist.add(key);
        return key;
    }

    PTAVar varFor(String localName, ContextMethod cm) {
        // return getOrCreateVar(local.getName(), cm);
        // String key = varKey(localName, cm);
        String key = localName + "|" + ctxKey(cm.context) + "|" + cm.method.getSignature();
        PTAVar v = varCache.get(key);
        if (v == null) {
            v = new PTAVar(localName, cm.method);
            varCache.put(key, v);
        }
        return v;
    }

    AllocObject allocFor(String site, SootClass type, ContextMethod cm) {
        String key = site + "|" + ctxKey(cm.context) + "|" + cm.method.getSignature();
        AllocObject obj = allocCache.get(key);
        if (obj == null) {
            obj = new AllocObject(site, type, cm.method);
            allocCache.put(key, obj);
        }
        return obj;
    }

    String ctxKey(List<AllocObject> ctx) {
        if (ctx.isEmpty())
            return "";
        StringBuilder sb = new StringBuilder();
        for (AllocObject o : ctx)
            sb.append(o.siteName).append('#');
        return sb.toString();
    }


    void recordCall(ContextMethod caller, Stmt site, ContextMethod callee) {
        callGraph
                .computeIfAbsent(caller, k -> new HashMap<>())
                .computeIfAbsent(site, k -> new HashSet<>())
                .add(callee);
    }

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
