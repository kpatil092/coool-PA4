import soot.*;
import soot.jimple.*;
import soot.util.Chain;

import java.util.*;

public class AnalysisTransformer extends SceneTransformer {

    private final int ptaK;

    /*
     * PTA keeps full contexts for precision.
     * Specialization deliberately merges contexts that share:
     * 1. the same target method
     * 2. the same receiver allocation object
     *
     * This avoids creating duplicate stubs whose behavior is identical.
     */
    private final Map<StubKey, SootMethod> staticStubCache = new HashMap<>();
    private final Map<SootMethod, StubInfo> stubInfo = new HashMap<>();
    private final Map<StubKey, LinkedHashSet<ObjectSensitivePTA.ContextMethod>> specializationGroups = new HashMap<>();

    private ObjectSensitivePTA pta;

    private static final class StubKey {
        final SootMethod method;
        final ObjectSensitivePTA.AllocObject receiver;

        StubKey(SootMethod method, ObjectSensitivePTA.AllocObject receiver) {
            this.method = method;
            this.receiver = receiver;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o)
                return true;
            if (!(o instanceof StubKey))
                return false;
            StubKey that = (StubKey) o;
            return Objects.equals(method, that.method) && Objects.equals(receiver, that.receiver);
        }

        @Override
        public int hashCode() {
            return Objects.hash(method, receiver);
        }
    }

    private static final class StubInfo {
        final StubKey key;
        final Set<ObjectSensitivePTA.ContextMethod> representedContexts;
        final Map<Stmt, Stmt> originalSiteByStubSite = new IdentityHashMap<>();
        Local receiverLocal;

        StubInfo(StubKey key, Set<ObjectSensitivePTA.ContextMethod> representedContexts) {
            this.key = key;
            this.representedContexts = representedContexts;
        }
    }

    private static final class AccessInfo {
        final Set<Local> receiverRootedLocals = new LinkedHashSet<>();
        final Set<Local> allowedBases = new LinkedHashSet<>();

        static AccessInfo empty() {
            return new AccessInfo();
        }
    }

    public AnalysisTransformer() {
        this(1);
    }

    public AnalysisTransformer(int k) {
        this.ptaK = k;
    }

    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        pta = new ObjectSensitivePTA(ptaK);

        List<SootMethod> entryPoints = new ArrayList<>();
        for (SootMethod m : Scene.v().getEntryPoints()) {
            if (m == null) {
                continue;
            }
            if (!m.getDeclaringClass().isApplicationClass()) {
                continue;
            }
            if (!m.isConcrete()) {
                continue;
            }
            entryPoints.add(m);
        }

        if (entryPoints.isEmpty()) {
            throw new IllegalStateException("No concrete application entry points available for PTA.");
        }

        pta.run(entryPoints);
        buildSpecializationGroups();

        System.out.println("[Mono/PTA] " + ptaK
                + "-obj PTA finished. Reachable context-methods: " + pta.getReachableContexts().size());

        Set<SootMethod> queued = new LinkedHashSet<>();
        Deque<SootMethod> worklist = new ArrayDeque<>();

        for (ObjectSensitivePTA.ContextMethod cm : pta.getReachableContexts()) {
            SootMethod method = cm.method;
            if (!isTransformable(method)) {
                continue;
            }
            if (queued.add(method)) {
                worklist.add(method);
            }
        }

        while (!worklist.isEmpty()) {
            SootMethod method = worklist.poll();
            queued.remove(method);

            if (transformBody(method.getActiveBody(), null) && queued.add(method)) {
                worklist.add(method);
            }
        }

        StubInliner inliner = new StubInliner(new HashSet<>(staticStubCache.values()));
        inliner.run();

        System.out.println("[Mono/PTA] Static stubs created: " + staticStubCache.size()
                + "  |  call sites inlined: " + inliner.getInlinedCount());
    }

    private void buildSpecializationGroups() {
        specializationGroups.clear();

        for (ObjectSensitivePTA.ContextMethod cm : pta.getReachableContexts()) {
            StubKey key = stubKeyFor(cm);
            if (key == null) {
                continue;
            }
            specializationGroups
                    .computeIfAbsent(key, __ -> new LinkedHashSet<>())
                    .add(cm);
        }
    }

    private boolean transformBody(Body body, StubInfo stub) {
        boolean changed = false;
        AccessInfo accessInfo = (stub == null || stub.receiverLocal == null)
                ? AccessInfo.empty()
                : computeAccessInfo(body, stub.receiverLocal);

        for (Unit unit : new ArrayList<>(body.getUnits())) {
            if (!(unit instanceof Stmt)) {
                continue;
            }

            Stmt stmt = (Stmt) unit;
            if (!stmt.containsInvokeExpr()) {
                continue;
            }

            InvokeExpr invokeExpr = stmt.getInvokeExpr();
            if (!(invokeExpr instanceof VirtualInvokeExpr) && !(invokeExpr instanceof InterfaceInvokeExpr)) {
                continue;
            }

            InstanceInvokeExpr iie = (InstanceInvokeExpr) invokeExpr;
            Local baseLocal = iie.getBase() instanceof Local ? (Local) iie.getBase() : null;

            StubKey targetKey = (stub == null)
                    ? singleTargetForOriginalBody(body.getMethod(), stmt)
                    : singleTargetForStubBody(stub, stmt, baseLocal, accessInfo);

            if (targetKey == null) {
                continue;
            }
            if (!isValidStubTarget(targetKey.method)) {
                continue;
            }

            SootMethod stubMethod = getOrCreateStaticStub(targetKey);
            rewriteToStaticCall(stmt, iie, targetKey.method, stubMethod, body);
            changed = true;
        }

        return changed;
    }

    /*
     * For original methods, merge all PTA caller contexts of the same method.
     * If every reachable context agrees on one specialization key, rewrite.
     */
    private StubKey singleTargetForOriginalBody(SootMethod method, Stmt site) {
        LinkedHashSet<StubKey> targetKeys = new LinkedHashSet<>();

        for (ObjectSensitivePTA.ContextMethod cm : pta.getReachableContexts()) {
            if (!cm.method.equals(method)) {
                continue;
            }
            collectTargetKeys(targetKeys, pta.getTargets(cm, site));
        }

        return targetKeys.size() == 1 ? targetKeys.iterator().next() : null;
    }

    /*
     * For stubs, query all original PTA contexts represented by that stub.
     * We only specialize when the merged receiver-based target is still unique.
     */
    private StubKey singleTargetForStubBody(
            StubInfo stub,
            Stmt stubSite,
            Local baseLocal,
            AccessInfo accessInfo) {
        if (baseLocal == null || !accessInfo.allowedBases.contains(baseLocal)) {
            return null;
        }

        Stmt originalSite = stub.originalSiteByStubSite.get(stubSite);
        if (originalSite == null) {
            return null;
        }

        LinkedHashSet<StubKey> targetKeys = new LinkedHashSet<>();
        for (ObjectSensitivePTA.ContextMethod cm : stub.representedContexts) {
            collectTargetKeys(targetKeys, pta.getTargets(cm, originalSite));
        }

        return targetKeys.size() == 1 ? targetKeys.iterator().next() : null;
    }

    private void collectTargetKeys(
            Set<StubKey> out,
            Set<ObjectSensitivePTA.ContextMethod> targetContexts) {
        for (ObjectSensitivePTA.ContextMethod target : targetContexts) {
            StubKey key = stubKeyFor(target);
            if (key != null) {
                out.add(key);
            }
        }
    }

    private StubKey stubKeyFor(ObjectSensitivePTA.ContextMethod cm) {
        if (cm == null || cm.method == null || cm.method.isStatic() || cm.context.isEmpty()) {
            return null;
        }
        ObjectSensitivePTA.AllocObject receiver = cm.context.get(0);
        if (receiver == null) {
            return null;
        }
        return new StubKey(cm.method, receiver);
    }

    private SootMethod getOrCreateStaticStub(StubKey key) {
        SootMethod cached = staticStubCache.get(key);
        if (cached != null) {
            return cached;
        }

        SootMethod original = key.method;
        List<Type> params = new ArrayList<>();
        params.add(original.getDeclaringClass().getType());
        params.addAll(original.getParameterTypes());

        String stubName = uniqueStubName(original.getDeclaringClass(), original, params, key.receiver);
        SootMethod stub = new SootMethod(
                stubName,
                params,
                original.getReturnType(),
                Modifier.PUBLIC | Modifier.STATIC,
                original.getExceptions());

        original.getDeclaringClass().addMethod(stub);

        LinkedHashSet<ObjectSensitivePTA.ContextMethod> represented = specializationGroups.getOrDefault(key,
                new LinkedHashSet<>());
        StubInfo info = new StubInfo(key, Collections.unmodifiableSet(new LinkedHashSet<>(represented)));

        staticStubCache.put(key, stub);
        stubInfo.put(stub, info);

        buildStubBody(stub, original, info);
        transformStubBody(stub);
        return stub;
    }

    private void transformStubBody(SootMethod stub) {
        StubInfo info = stubInfo.get(stub);
        if (info == null || !stub.hasActiveBody()) {
            return;
        }

        boolean changed;
        int guard = 0;
        do {
            changed = transformBody(stub.getActiveBody(), info);
        } while (changed && ++guard < 32);
    }

    private void buildStubBody(SootMethod stub, SootMethod original, StubInfo info) {

        Body originalBody = original.getActiveBody();
        JimpleBody stubBody = Jimple.v().newBody(stub);
        stub.setActiveBody(stubBody);

        Map<Local, Local> localMap = new HashMap<>();
        Map<Unit, Unit> unitMap = new HashMap<>();

        // Clone locals
        for (Local l : originalBody.getLocals()) {
            Local nl = Jimple.v().newLocal(l.getName(), l.getType());
            stubBody.getLocals().add(nl);
            localMap.put(l, nl);
        }

        // Create receiver
        Local receiverLocal = Jimple.v().newLocal("r0_explicit", original.getDeclaringClass().getType());
        stubBody.getLocals().add(receiverLocal);
        info.receiverLocal = receiverLocal;

        Chain<Unit> units = stubBody.getUnits();

        // === STEP 1: CREATE IDENTITY BLOCK (CORRECT ORDER) ===

        // receiver (this)
        units.add(Jimple.v().newIdentityStmt(
                receiverLocal,
                Jimple.v().newParameterRef(stub.getParameterType(0), 0)));

        // parameters
        int paramIndex = 1;
        List<Local> paramLocals = new ArrayList<>();

        for (int i = 0; i < original.getParameterCount(); i++) {
            Type t = original.getParameterType(i);

            Local pLocal = Jimple.v().newLocal("p" + i, t);
            stubBody.getLocals().add(pLocal);
            paramLocals.add(pLocal);

            units.add(Jimple.v().newIdentityStmt(
                    pLocal,
                    Jimple.v().newParameterRef(t, paramIndex)));

            paramIndex++;
        }

        // === STEP 2: CLONE BODY (SKIP identity stmts) ===

        for (Unit u : originalBody.getUnits()) {

            if (u instanceof IdentityStmt)
                continue; // 🔥 CRITICAL FIX

            Unit cloned = (Unit) u.clone();
            units.add(cloned);
            unitMap.put(u, cloned);

            if (u instanceof Stmt && cloned instanceof Stmt) {
                info.originalSiteByStubSite.put((Stmt) cloned, (Stmt) u);
            }
        }

        // === STEP 3: FIX LOCALS ===

        Local originalThis = original.isStatic() ? null : originalBody.getThisLocal();

        for (Unit u : units) {
            for (ValueBox vb : u.getUseAndDefBoxes()) {
                Value v = vb.getValue();

                if (!(v instanceof Local))
                    continue;

                Local l = (Local) v;

                if (originalThis != null && l.equals(originalThis)) {
                    vb.setValue(receiverLocal);
                } else if (localMap.containsKey(l)) {
                    vb.setValue(localMap.get(l));
                }
            }
        }

        // === STEP 4: FIX CFG REFERENCES (CRITICAL) ===

        for (Unit u : units) {
            for (UnitBox ub : u.getUnitBoxes()) {
                Unit target = ub.getUnit();
                if (unitMap.containsKey(target)) {
                    ub.setUnit(unitMap.get(target));
                }
            }
        }

        // === STEP 5: FIX TRAPS ===

        for (Trap t : originalBody.getTraps()) {

            Unit begin = unitMap.get(t.getBeginUnit());
            Unit end = unitMap.get(t.getEndUnit());
            Unit handler = unitMap.get(t.getHandlerUnit());

            // ❗ Skip invalid traps (critical fix)
            if (begin == null || end == null || handler == null)
                continue;

            stubBody.getTraps().add(Jimple.v().newTrap(
                    t.getException(),
                    begin,
                    end,
                    handler));
        }

        // === FINAL VALIDATION ===

        try {
            stubBody.validate();
        } catch (RuntimeException e) {
            throw new IllegalStateException(
                    "Invalid stub body generated for " + stub.getSignature(), e);
        }
    }

    private void remapClonedUnitBoxes(
            Body body,
            Map<Unit, Unit> unitMap,
            Unit specialOldTarget,
            Unit specialReplacement) {
        for (Unit unit : new ArrayList<>(body.getUnits())) {
            for (UnitBox ub : unit.getUnitBoxes()) {
                Unit target = ub.getUnit();
                if (target == specialOldTarget && specialReplacement != null) {
                    ub.setUnit(specialReplacement);
                } else {
                    Unit remapped = unitMap.get(target);
                    if (remapped != null) {
                        ub.setUnit(remapped);
                    }
                }
            }
        }
    }

    private void redirectUnitBoxesToReplacement(Body body, Unit oldTarget, Unit replacement) {
        for (Unit unit : new ArrayList<>(body.getUnits())) {
            for (UnitBox ub : unit.getUnitBoxes()) {
                if (ub.getUnit() == oldTarget) {
                    ub.setUnit(replacement);
                }
            }
        }
    }

    private void rewriteToStaticCall(
            Stmt stmt,
            InstanceInvokeExpr originalInvoke,
            SootMethod targetMethod,
            SootMethod stubMethod,
            Body body) {
        List<Value> newArgs = new ArrayList<>();
        newArgs.add(ensureType(originalInvoke.getBase(), targetMethod.getDeclaringClass().getType(), stmt, body));
        newArgs.addAll(originalInvoke.getArgs());

        StaticInvokeExpr staticInvoke = Jimple.v().newStaticInvokeExpr(stubMethod.makeRef(), newArgs);
        if (stmt instanceof AssignStmt) {
            ((AssignStmt) stmt).setRightOp(staticInvoke);
        } else if (stmt instanceof InvokeStmt) {
            ((InvokeStmt) stmt).setInvokeExpr(staticInvoke);
        }
    }

    private AccessInfo computeAccessInfo(Body body, Local receiverLocal) {
        AccessInfo info = new AccessInfo();
        info.receiverRootedLocals.add(receiverLocal);
        info.allowedBases.add(receiverLocal);

        boolean changed;
        do {
            changed = false;
            for (Unit unit : body.getUnits()) {
                if (!(unit instanceof AssignStmt)) {
                    continue;
                }

                AssignStmt stmt = (AssignStmt) unit;
                if (!(stmt.getLeftOp() instanceof Local)) {
                    continue;
                }

                Local lhs = (Local) stmt.getLeftOp();
                Value rhs = stmt.getRightOp();

                if (rhs instanceof Local && info.receiverRootedLocals.contains(rhs)) {
                    changed |= info.receiverRootedLocals.add(lhs);
                    changed |= info.allowedBases.add(lhs);
                } else if (rhs instanceof CastExpr) {
                    Value op = ((CastExpr) rhs).getOp();
                    if (op instanceof Local && info.receiverRootedLocals.contains(op)) {
                        changed |= info.receiverRootedLocals.add(lhs);
                        changed |= info.allowedBases.add(lhs);
                    }
                } else if (rhs instanceof InstanceFieldRef) {
                    Value base = ((InstanceFieldRef) rhs).getBase();
                    if (base instanceof Local && info.receiverRootedLocals.contains(base)) {
                        changed |= info.receiverRootedLocals.add(lhs);
                        changed |= info.allowedBases.add(lhs);
                    }
                }
            }
        } while (changed);

        return info;
    }

    private boolean isTransformable(SootMethod method) {
        return method != null
                && method.isConcrete()
                && !method.isNative()
                && method.hasActiveBody();
    }

    private boolean isValidStubTarget(SootMethod method) {
        return isTransformable(method)
                && !method.isStatic()
                && !method.isAbstract()
                && !method.getDeclaringClass().isPhantom()
                && !method.getDeclaringClass().isJavaLibraryClass();
    }

    private String uniqueStubName(
            SootClass declaringClass,
            SootMethod original,
            List<Type> params,
            ObjectSensitivePTA.AllocObject receiver) {
        String base = "__mono_" + original.getName() + "__recv_"
                + sanitize(receiver == null ? "ctx" : receiver.siteName);
        String candidate = base;
        int suffix = 0;
        while (declaringClass.declaresMethod(candidate, params)) {
            candidate = base + "_" + (++suffix);
        }
        return candidate;
    }

    private String sanitize(String value) {
        if (value == null || value.isEmpty()) {
            return "ctx";
        }

        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < value.length(); i++) {
            char ch = value.charAt(i);
            sb.append(Character.isLetterOrDigit(ch) || ch == '_' ? ch : '_');
        }
        return sb.toString();
    }

    private Value ensureType(Value value, Type targetType, Stmt insertBefore, Body body) {
        if (value.getType().equals(targetType)) {
            return value;
        }

        Local castLocal = Jimple.v().newLocal("$cast_" + System.identityHashCode(insertBefore), targetType);
        body.getLocals().add(castLocal);
        body.getUnits().insertBefore(
                Jimple.v().newAssignStmt(castLocal, Jimple.v().newCastExpr(value, targetType)),
                insertBefore);
        return castLocal;
    }

    public ObjectSensitivePTA getPTA() {
        return pta;
    }
}