import soot.*;
import soot.jimple.*;
import soot.util.Chain;

import java.util.*;

/**
 * <h2>Devirtualization oracles — precision contract</h2>
 *
 * The transformer uses two oracles, each applicable in a different context:
 *
 * <dl>
 * <dt>Oracle 1 — PTA ({@link #ptaSingleTarget})</dt>
 * <dd>Used for every <em>original</em> application method reachable by PTA.
 * Merges the set of concrete callees across every calling context and
 * returns the unique one (or {@code null} if polymorphic). Never
 * produces false monomorphism because it is backed by flow-sensitive
 * heap information.</dd>
 *
 * <dt>Oracle 2 — Exact-local static dispatch
 * ({@link #exactLocalSingleTarget})</dt>
 * <dd>Used <em>exclusively</em> inside <em>stub bodies</em>, and only on
 * locals that are provably exact-typed:
 * <ol>
 * <li>The stub's own explicit receiver local ({@code r0_explicit}).
 * The stub was created only because PTA proved a single concrete
 * type reached the original call site, so {@code r0_explicit}'s
 * declared type IS that exact runtime type.</li>
 * <li>Locals whose declared type is a {@code final} class — no
 * subclass can exist, so the declared type IS the runtime type.</li>
 * </ol>
 *
 * <h2>Recursion safety</h2>
 * Stubs are inserted into {@link #staticStubCache} <em>before</em> their
 * bodies are built. A recursive virtual call resolves to the same stub via
 * cache hit; no infinite loop occurs.
 *
 * <h2>Stub-chain depth</h2>
 * {@link #transformStubBody} loops to convergence so chains of arbitrary
 * depth are fully devirtualized.
 */
public class AnalysisTransformer extends SceneTransformer {

    // =========================================================================
    // Configuration
    // =========================================================================

    /** Object-sensitivity depth for PTA (0 = context-insensitive). */
    private final int ptaK;

    public AnalysisTransformer() {
        this(2);
    }

    public AnalysisTransformer(int k) {
        this.ptaK = k;
    }

    // =========================================================================
    // State
    // =========================================================================

    /**
     * Cache: original SootMethod → generated static stub.
     * Populated before the stub body is built to handle recursive methods.
     */
    private final Map<SootMethod, SootMethod> staticStubCache = new HashMap<>();

    /**
     * Reverse map: stub → original.
     * Kept for introspection and downstream passes.
     */
    private final Map<SootMethod, SootMethod> stubToOriginal = new HashMap<>();

    /**
     * Per-stub "exact receiver local": the local whose declared type is the
     * exact concrete type that PTA proved. Oracle 2 fires ONLY when the
     * virtual-call base is this local (or a final-typed local).
     *
     * Key: stub SootMethod. Value: the {@code r0_explicit} Local in that stub.
     */
    private final Map<SootMethod, Local> stubReceiverLocal = new HashMap<>();

    /** PTA instance — valid after {@link #internalTransform}. */
    private ObjectSensitivePTA pta;

    // =========================================================================
    // Entry point
    // =========================================================================

    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {

        // ------------------------------------------------------------------
        // Phase 1 — Run Object-Sensitive PTA
        // ------------------------------------------------------------------
        pta = new ObjectSensitivePTA(ptaK);

        List<SootMethod> entryPoints = new ArrayList<>();

        for (SootMethod m : Scene.v().getEntryPoints()) {
            if (!m.getDeclaringClass().isApplicationClass())
                continue;
            if (!m.isConcrete())
                continue;

            entryPoints.add(m);
        }

        pta.run(entryPoints);
        System.out.println("[Mono/PTA] PTA finished. Reachable context-methods: "
                + pta.reachable.size());

        pta.printCallGraph();
        // ------------------------------------------------------------------
        // Phase 2 — Devirtualize PTA-reachable original methods
        //
        // Stubs are devirtualized eagerly inside getOrCreateStaticStub (via
        // transformStubBody with Oracle 2), so they do NOT go on this
        // worklist. The worklist only drives original application methods.
        // ------------------------------------------------------------------
        Set<SootMethod> onWorklist = new LinkedHashSet<>();
        Deque<SootMethod> worklist = new ArrayDeque<>();

        for (ObjectSensitivePTA.ContextMethod cm : pta.reachable.keySet()) {
            // System.out.println(cm.method.getSignature() + " : " + cm.context.toString()
            // );
            SootMethod base = cm.method;
            if (base.isConcrete() && !base.isNative()
                    && base.hasActiveBody() && onWorklist.add(base)) {
                worklist.add(base);
            }
        }

        while (!worklist.isEmpty()) {
            SootMethod m = worklist.poll();
            onWorklist.remove(m);
            if (!m.hasActiveBody())
                continue;

            // Oracle 1: PTA-backed devirtualization.
            boolean changed = transformBody(m.getActiveBody(),
                    null /* not a stub */);
            if (changed && onWorklist.add(m))
                worklist.add(m);
        }

        System.out.println("[Mono/PTA] Static stubs created: "
                + staticStubCache.size());
    }

    // =========================================================================
    // Per-body transformation
    // =========================================================================

    /**
     * Walks every virtual/interface call site in {@code body} and rewrites
     * monomorphic ones as static-stub calls.
     *
     * @param body          the Jimple body to transform
     * @param exactReceiver {@code null} → use Oracle 1 (PTA, for original
     *                      methods). Non-null → use Oracle 2 (exact-local
     *                      static dispatch, for stub bodies); the value is
     *                      the stub's own {@code r0_explicit} local.
     * @return {@code true} if at least one rewrite occurred
     */
    private boolean transformBody(Body body, Local exactReceiver) {
        SootMethod enclosing = body.getMethod();
        boolean changed = false;

        List<Unit> snapshot = new ArrayList<>(body.getUnits());

        for (Unit unit : snapshot) {
            Stmt stmt = (Stmt) unit;
            if (!stmt.containsInvokeExpr())
                continue;

            InvokeExpr ie = stmt.getInvokeExpr();
            if (!(ie instanceof VirtualInvokeExpr)
                    && !(ie instanceof InterfaceInvokeExpr))
                continue;

            InstanceInvokeExpr iie = (InstanceInvokeExpr) ie;

            // ------------------------------------------------------------------
            // Select oracle.
            // ------------------------------------------------------------------
            SootMethod singleTarget = (exactReceiver == null)
                    ? ptaSingleTarget(enclosing, stmt) // Oracle 1
                    : exactLocalSingleTarget(iie, exactReceiver); // Oracle 2

            if (singleTarget == null)
                continue;

            // Guard against un-stubbable targets.
            if (singleTarget.isNative()
                    || singleTarget.isAbstract()
                    || singleTarget.getDeclaringClass().isPhantom()
                    || singleTarget.isStatic())
                continue;

            if (!singleTarget.hasActiveBody()
                    || singleTarget.getDeclaringClass().isJavaLibraryClass())
                continue;

            // ------------------------------------------------------------------
            // Get or create the static stub (cache-before-build → recursion safe).
            // ------------------------------------------------------------------
            SootMethod stub = getOrCreateStaticStub(singleTarget);

            // ------------------------------------------------------------------
            // Rewrite the call site.
            // Before: virtualinvoke base.<C: R m(T...)>(args)
            // After: staticinvoke <C: R __mono_m(C,T...)>(base, args)
            // ------------------------------------------------------------------
            List<Value> newArgs = new ArrayList<>();
            Value receiver = iie.getBase();
            Type declaredReceiverType = singleTarget.getDeclaringClass().getType();
            newArgs.add(ensureType(receiver, declaredReceiverType, stmt, body));
            newArgs.addAll(ie.getArgs());

            StaticInvokeExpr staticInvoke = Jimple.v().newStaticInvokeExpr(stub.makeRef(), newArgs);

            if (stmt instanceof AssignStmt)
                ((AssignStmt) stmt).setRightOp(staticInvoke);
            else if (stmt instanceof InvokeStmt)
                ((InvokeStmt) stmt).setInvokeExpr(staticInvoke);

            changed = true;
        }

        return changed;
    }

    // =========================================================================
    // Oracle 1 — PTA-based (original application methods only)
    // =========================================================================

    /**
     * Context-insensitive monomorphism check via PTA.
     *
     * Collects the union of concrete callee {@link SootMethod}s seen at
     * {@code site} across every context of {@code method}. Returns the unique
     * callee, or {@code null} if zero or more than one.
     *
     * Implements the "5B / 5C" stubs in {@code ObjectSensitivePTA.java}.
     */
    private SootMethod ptaSingleTarget(SootMethod method, Stmt site) {
        Set<SootMethod> targets = new HashSet<>();

        for (ObjectSensitivePTA.ContextMethod cm : pta.reachable.keySet()) {
            if (!cm.method.equals(method))
                continue;

            Map<Stmt, Set<ObjectSensitivePTA.ContextMethod>> siteMap = pta.callGraph.get(cm);
            if (siteMap == null)
                continue;

            Set<ObjectSensitivePTA.ContextMethod> callees = siteMap.get(site);
            if (callees == null)
                continue;

            for (ObjectSensitivePTA.ContextMethod callee : callees)
                targets.add(callee.method);
        }

        return targets.size() == 1 ? targets.iterator().next() : null;
    }

    // =========================================================================
    // Oracle 2 — Exact-local static dispatch (stub bodies only)
    // =========================================================================

    /**
     * Resolves a virtual call inside a stub body, firing ONLY when the
     * receiver base is provably exact-typed.
     *
     * <h3>Exact-type conditions</h3>
     * <ol>
     * <li><b>{@code exactReceiver} identity check</b> — the base local is
     * the same object as the stub's {@code r0_explicit}. That local's
     * declared type is the exact concrete class the PTA proved, so
     * {@code resolveConcreteDispatch} on it is sound and complete.</li>
     * <li><b>Final declared type</b> — no subclass can exist in any
     * well-typed Java program, so the declared type equals the runtime
     * type regardless of what value flows in.</li>
     * </ol>
     *
     * <h3>What is deliberately NOT dispatched on</h3>
     * Any local whose declared type is a non-final class other than the
     * stub's own {@code r0_explicit} is skipped. In the X.jimple case:
     * 
     * <pre>
     *   __mono_call(X r0_explicit, A r0)
     *       virtualinvoke r0.&lt;A: void foo()&gt;();
     * </pre>
     * 
     * {@code r0} has declared type {@code A} (not final, not {@code r0_explicit}),
     * so this oracle returns {@code null} and the virtual call is preserved —
     * which is correct because at runtime {@code r0} could be an {@code A} or
     * a {@code B}.
     *
     * @param iie           the virtual/interface invoke expression to resolve
     * @param exactReceiver the stub's own {@code r0_explicit} local
     * @return the unique concrete target, or {@code null}
     */
    private SootMethod exactLocalSingleTarget(InstanceInvokeExpr iie,
            Local exactReceiver) {
        Value base = iie.getBase();
        if (!(base instanceof Local))
            return null;
        Local baseLocal = (Local) base;

        // ---- Determine whether this local is provably exact-typed ----------
        boolean isExact = false;

        // Condition 1: base IS the stub's own receiver local.
        if (baseLocal == exactReceiver) {
            isExact = true;
        }

        // Condition 2: declared type is a final class.
        if (!isExact) {
            Type t = baseLocal.getType();
            if (t instanceof RefType) {
                SootClass sc = ((RefType) t).getSootClass();
                if (!sc.isInterface() && !sc.isAbstract()
                        && !sc.isPhantom()
                        && Modifier.isFinal(sc.getModifiers())) {
                    isExact = true;
                }
            }
        }

        if (!isExact)
            return null;

        // ---- Resolve concrete dispatch on the exact declared type ----------
        Type receiverType = baseLocal.getType();
        if (!(receiverType instanceof RefType))
            return null;
        SootClass receiverClass = ((RefType) receiverType).getSootClass();

        if (receiverClass.isInterface()
                || receiverClass.isAbstract()
                || receiverClass.isPhantom())
            return null;

        try {
            SootMethod resolved = Scene.v().getActiveHierarchy()
                    .resolveConcreteDispatch(
                            receiverClass, iie.getMethodRef().resolve());
            if (resolved == null || !resolved.isConcrete())
                return null;
            return resolved;
        } catch (Exception e) {
            return null;
        }
    }

    // =========================================================================
    // Context-sensitive query (bonus — for downstream passes)
    // =========================================================================

    /**
     * Returns the single concrete target seen from context-method {@code cm}
     * at {@code site}, or {@code null} if polymorphic / unreachable.
     * Implements the "5A" stub in {@code ObjectSensitivePTA.java}.
     */
    public SootMethod ptaSingleTargetForContext(
            ObjectSensitivePTA.ContextMethod cm, Stmt site) {
        Map<Stmt, Set<ObjectSensitivePTA.ContextMethod>> siteMap = pta.callGraph.get(cm);
        if (siteMap == null)
            return null;
        Set<ObjectSensitivePTA.ContextMethod> callees = siteMap.get(site);
        if (callees == null || callees.isEmpty())
            return null;
        SootMethod single = null;
        for (ObjectSensitivePTA.ContextMethod callee : callees) {
            if (single == null)
                single = callee.method;
            else if (!single.equals(callee.method))
                return null;
        }
        return single;
    }

    // =========================================================================
    // Static stub creation
    // =========================================================================

    /**
     * Returns a cached static stub for {@code original}, creating and
     * registering one if it does not yet exist.
     *
     * <h3>Registration-before-build (recursion safety)</h3>
     * The stub is placed in {@link #staticStubCache} and
     * {@link #stubReceiverLocal} <em>before</em> {@link #buildStubBody} runs.
     * Any recursive virtual call on {@code r0_explicit} inside the cloned body
     * resolves via Oracle 2 to the same original method, which hits the cache
     * and returns this stub — no infinite loop.
     *
     * <h3>Eager stub-body devirtualization</h3>
     * Immediately after building the body, {@link #transformStubBody} applies
     * Oracle 2 to the new stub, turning any remaining virtual calls on exact
     * locals into further static-stub calls. Those nested stubs are created
     * recursively and also devirtualized immediately.
     */
    private SootMethod getOrCreateStaticStub(SootMethod original) {
        SootMethod cached = staticStubCache.get(original);
        if (cached != null)
            return cached;

        SootClass declaringClass = original.getDeclaringClass();

        // Parameter list: (DeclaringClass receiver, <original params>)
        List<Type> stubParams = new ArrayList<>();
        stubParams.add(declaringClass.getType());
        stubParams.addAll(original.getParameterTypes());

        String stubName = uniqueStubName(declaringClass, original, stubParams);

        SootMethod stub = new SootMethod(
                stubName,
                stubParams,
                original.getReturnType(),
                Modifier.PUBLIC | Modifier.STATIC,
                original.getExceptions());

        declaringClass.addMethod(stub);

        // *** Register BEFORE body build — handles direct/mutual recursion ***
        staticStubCache.put(original, stub);
        stubToOriginal.put(stub, original);
        // stubReceiverLocal will be filled by buildStubBody below.

        buildStubBody(stub, original); // clones + patches
        transformStubBody(stub); // Oracle 2 pass on the new stub

        return stub;
    }

    /**
     * Runs Oracle 2 on a stub body until convergence.
     * The loop is needed for chains (stub A calls B calls C …); each pass may
     * create new stubs that are themselves devirtualized recursively, so
     * normally one pass suffices, but we loop defensively.
     */
    private void transformStubBody(SootMethod stub) {
        if (!stub.hasActiveBody())
            return;
        Local exactReceiver = stubReceiverLocal.get(stub);
        if (exactReceiver == null)
            return; // should not happen

        Body body = stub.getActiveBody();
        boolean changed;
        int guard = 0;
        do {
            changed = transformBody(body, exactReceiver);
        } while (changed && ++guard < 32);
    }

    // =========================================================================
    // Stub body builder
    // =========================================================================

    /**
     * Clones {@code original}'s Jimple body into {@code stub}, performing the
     * following rewrites:
     * <ul>
     * <li>Adds explicit receiver local {@code r0_explicit} of the declaring
     * class type; removes the {@code @this} identity statement.</li>
     * <li>Shifts every {@code @parameter i} to {@code @parameter i+1}.</li>
     * <li>Replaces all uses of the original {@code @this} local with
     * {@code r0_explicit}.</li>
     * <li>Maps all other original locals to fresh cloned counterparts.</li>
     * <li>Clones traps with updated unit references.</li>
     * </ul>
     * Registers {@code r0_explicit} in {@link #stubReceiverLocal} so that
     * {@link #transformStubBody} can pass it to Oracle 2.
     */
    private void buildStubBody(SootMethod stub, SootMethod original) {
        // if (!original.hasActiveBody()
        //         || original.getDeclaringClass().isJavaLibraryClass()) {
        //     buildEmptyStubBody(stub);
        //     return;
        // }
        Body origBody = original.getActiveBody();
        JimpleBody stubBody = Jimple.v().newBody(stub);
        stub.setActiveBody(stubBody);

        Local origThisLocal = origBody.getThisLocal();

        // Clone locals.
        Map<Local, Local> localMap = new HashMap<>();
        for (Local origLocal : origBody.getLocals()) {
            Local cl = Jimple.v().newLocal(origLocal.getName(), origLocal.getType());
            stubBody.getLocals().add(cl);
            localMap.put(origLocal, cl);
        }

        // Add the explicit receiver local.
        Local receiverLocal = Jimple.v().newLocal(
                "r0_explicit", original.getDeclaringClass().getType());
        stubBody.getLocals().add(receiverLocal);

        // Register it NOW so recursion is handled before body patching.
        stubReceiverLocal.put(stub, receiverLocal);

        // Clone units.
        Map<Unit, Unit> unitMap = new HashMap<>();
        for (Unit origUnit : origBody.getUnits()) {
            Unit cloned = (Unit) origUnit.clone();
            stubBody.getUnits().add(cloned);
            unitMap.put(origUnit, cloned);
        }

        // Clone traps.
        for (Trap origTrap : origBody.getTraps()) {
            stubBody.getTraps().add(Jimple.v().newTrap(
                    origTrap.getException(),
                    unitMap.get(origTrap.getBeginUnit()),
                    unitMap.get(origTrap.getEndUnit()),
                    unitMap.get(origTrap.getHandlerUnit())));
        }

        // Patch identity statements and local references.
        Unit clonedThisIdentity = null;
        for (Unit unit : new ArrayList<>(stubBody.getUnits())) {
            Stmt stmt = (Stmt) unit;

            if (stmt instanceof IdentityStmt) {
                IdentityStmt id = (IdentityStmt) stmt;
                Value rhs = id.getRightOp();
                if (rhs instanceof ThisRef) {
                    clonedThisIdentity = unit; // will be removed
                } else if (rhs instanceof ParameterRef) {
                    int newIdx = ((ParameterRef) rhs).getIndex() + 1;
                    id.setRightOp(Jimple.v().newParameterRef(
                            stub.getParameterType(newIdx), newIdx));
                }
            }

            for (ValueBox vb : stmt.getUseAndDefBoxes()) {
                Value v = vb.getValue();
                if (v instanceof Local) {
                    Local orig = (Local) v;
                    if (orig.equals(origThisLocal))
                        vb.setValue(receiverLocal);
                    else if (localMap.containsKey(orig))
                        vb.setValue(localMap.get(orig));
                }
            }
        }

        if (clonedThisIdentity != null)
            stubBody.getUnits().remove(clonedThisIdentity);

        // Prepend: r0_explicit := @parameter 0
        stubBody.getUnits().insertBefore(
                Jimple.v().newIdentityStmt(
                        receiverLocal,
                        Jimple.v().newParameterRef(stub.getParameterType(0), 0)),
                stubBody.getUnits().getFirst());

        try {
            stubBody.validate();
        } catch (Exception e) {
            System.err.println("[Mono/PTA] Warning: stub validation failed for "
                    + stub.getSignature() + ": " + e.getMessage());
        }
    }

    /** Minimal stub body for when the original body cannot be retrieved. */
    private void buildEmptyStubBody(SootMethod stub) {
        JimpleBody body = Jimple.v().newBody(stub);
        stub.setActiveBody(body);
        for (int i = 0; i < stub.getParameterCount(); i++) {
            Local p = Jimple.v().newLocal("p" + i, stub.getParameterType(i));
            body.getLocals().add(p);
            body.getUnits().add(Jimple.v().newIdentityStmt(
                    p, Jimple.v().newParameterRef(stub.getParameterType(i), i)));
        }
        Type ret = stub.getReturnType();
        if (ret instanceof VoidType) {
            body.getUnits().add(Jimple.v().newReturnVoidStmt());
        } else {
            Local r = Jimple.v().newLocal("ret", ret);
            body.getLocals().add(r);
            body.getUnits().add(Jimple.v().newAssignStmt(r, defaultValue(ret)));
            body.getUnits().add(Jimple.v().newReturnStmt(r));
        }
    }

    // =========================================================================
    // Helpers
    // =========================================================================

    private String uniqueStubName(SootClass cls, SootMethod original,
            List<Type> params) {
        String base = "__mono_" + original.getName();
        String candidate = base;
        int suffix = 0;
        while (cls.declaresMethod(candidate, params))
            candidate = base + "_" + (++suffix);
        return candidate;
    }

    private Value ensureType(Value value, Type targetType,
            Stmt insertBefore, Body body) {
        if (value.getType().equals(targetType))
            return value;
        Local cast = Jimple.v().newLocal(
                "$cast_" + System.identityHashCode(value), targetType);
        body.getLocals().add(cast);
        body.getUnits().insertBefore(
                Jimple.v().newAssignStmt(
                        cast, Jimple.v().newCastExpr(value, targetType)),
                insertBefore);
        return cast;
    }

    private Value defaultValue(Type t) {
        if (t instanceof IntType || t instanceof ByteType
                || t instanceof ShortType || t instanceof CharType
                || t instanceof BooleanType)
            return IntConstant.v(0);
        if (t instanceof LongType)
            return LongConstant.v(0L);
        if (t instanceof FloatType)
            return FloatConstant.v(0.0f);
        if (t instanceof DoubleType)
            return DoubleConstant.v(0.0);
        return NullConstant.v();
    }

    /** Returns the PTA instance (valid after {@link #internalTransform}). */
    public ObjectSensitivePTA getPTA() {
        return pta;
    }
}