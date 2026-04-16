import soot.*;
import soot.jimple.*;
import soot.util.*;

import java.util.*;

public class AnalysisTransformer extends SceneTransformer {

    final int PIC_LIMIT = 1;

    final int k;

    Map<ObjectSensitivePTA.ContextMethod, SootMethod> ctxToStubMap = new HashMap<>();
    Map<SootMethod, StubInfo> stubInfoMap = new HashMap<>();

    ObjectSensitivePTA pta;

    static class StubInfo {
        ObjectSensitivePTA.ContextMethod contextMethod;
        Map<Stmt, Stmt> originalSiteByStubSite = new HashMap<>();
        Local receiverLocal;

        StubInfo(ObjectSensitivePTA.ContextMethod contextMethod) {
            this.contextMethod = contextMethod;
        }
    }

    static class AccessInfo {
        Set<Local> receiverRootedLocals = new LinkedHashSet<>();
        Set<Local> parameterLocals = new LinkedHashSet<>();
        Set<Local> parameterCopies = new LinkedHashSet<>();
        Set<Local> allowedBases = new LinkedHashSet<>();

        static AccessInfo empty() {
            return new AccessInfo();
        }
    }

    public AnalysisTransformer() {
        this(4);
    }

    public AnalysisTransformer(int k) {
        this.k = k;
    }

    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        pta = new ObjectSensitivePTA(k);

        List<SootMethod> entryPoints = new ArrayList<>();
        for (SootMethod m : Scene.v().getEntryPoints()) {
            if (!m.getDeclaringClass().isApplicationClass())
                continue;
            if (!m.isConcrete())
                continue;
            entryPoints.add(m);
        }

        pta.run(entryPoints);
        System.out.println("[Mono/PTA] " + k
                + "-obj PTA finished. Reachable context-methods: " + pta.getReachableContexts().size());
        // pta.printCallGraph();

        Set<SootMethod> onWorklist = new LinkedHashSet<>();
        Deque<SootMethod> worklist = new ArrayDeque<>();

        for (ObjectSensitivePTA.ContextMethod cm : pta.getReachableContexts()) {
            SootMethod method = cm.method;
            if (!method.isConcrete() || method.isNative() || !method.hasActiveBody())
                continue;
            if (onWorklist.add(method))
                worklist.add(method);
        }

        while (!worklist.isEmpty()) {
            SootMethod method = worklist.poll();
            onWorklist.remove(method);
            if (!method.hasActiveBody())
                continue;

            boolean changed = transformBody(method.getActiveBody(), null);
            if (changed && onWorklist.add(method))
                worklist.add(method);
        }

        System.out.println("[Mono/PTA] Static stubs created: " + ctxToStubMap.size());
    }

    boolean transformBody(Body body, StubInfo stub) {
        SootMethod enclosing = body.getMethod();
        boolean changed = false;

        AccessInfo accessInfo = (stub == null || stub.receiverLocal == null)
                ? AccessInfo.empty()
                : computeAccessInfo(body, stub.receiverLocal);

        List<Unit> snapshot = new ArrayList<>(body.getUnits());

        for (Unit unit : snapshot) {
            if (!(unit instanceof Stmt))
                continue;
            Stmt stmt = (Stmt) unit;
            if (!stmt.containsInvokeExpr())
                continue;

            InvokeExpr ie = stmt.getInvokeExpr();
            if (!(ie instanceof VirtualInvokeExpr) && !(ie instanceof InterfaceInvokeExpr))
                continue;

            InstanceInvokeExpr iie = (InstanceInvokeExpr) ie;
            Local baseLocal = (iie.getBase() instanceof Local) ? (Local) iie.getBase() : null;

            Stmt originalSite = (stub == null)
                    ? stmt
                    : stub.originalSiteByStubSite.get(stmt);

            Set<ObjectSensitivePTA.ContextMethod> targets = collectTargetsForSite(enclosing, stub, stmt, originalSite,
                    iie, accessInfo, baseLocal);

            // CASE 1: monomorphic → existing logic
            if (targets.size() == 1) {

                ObjectSensitivePTA.ContextMethod singleTarget = targets.iterator().next();

                SootMethod targetMethod = singleTarget.method;

                if (targetMethod.isNative()
                        || targetMethod.isAbstract()
                        || targetMethod.getDeclaringClass().isPhantom()
                        || targetMethod.isStatic())
                    continue;
                if (!targetMethod.hasActiveBody() || targetMethod.getDeclaringClass().isJavaLibraryClass())
                    continue;

                SootMethod targetStub = getOrCreateStaticStub(singleTarget);

                List<Value> newArgs = new ArrayList<>();
                Type receiverType = targetMethod.getDeclaringClass().getType();
                newArgs.add(ensureType(iie.getBase(), receiverType, stmt, body));
                newArgs.addAll(ie.getArgs());

                StaticInvokeExpr staticInvoke = Jimple.v().newStaticInvokeExpr(targetStub.makeRef(), newArgs);

                if (stmt instanceof AssignStmt)
                    ((AssignStmt) stmt).setRightOp(staticInvoke);
                else
                    ((InvokeStmt) stmt).setInvokeExpr(staticInvoke);

                changed = true;
                continue;
            }

            // CASE 2: PIC
            if (targets.size() > 1 && targets.size() <= PIC_LIMIT) {

                emitPIC(body, stmt, iie, targets);

                changed = true;
                continue;
            }

            // else virtual
        }

        return changed;
    }

    Set<ObjectSensitivePTA.ContextMethod> collectTargetsForSite(
            SootMethod enclosing,
            StubInfo stub,
            Stmt stmt,
            Stmt originalSite,
            InstanceInvokeExpr iie,
            AccessInfo accessInfo,
            Local baseLocal) {

        LinkedHashSet<ObjectSensitivePTA.ContextMethod> targets = new LinkedHashSet<>();

        if (stub == null) {
            for (ObjectSensitivePTA.ContextMethod cm : pta.getReachableContexts()) {
                if (!cm.method.equals(enclosing))
                    continue;
                targets.addAll(pta.getTargets(cm, stmt));
            }
        } else {
            if (baseLocal == null || !accessInfo.allowedBases.contains(baseLocal))
                return targets;

            Set<ObjectSensitivePTA.ContextMethod> t = pta.getTargets(stub.contextMethod, originalSite);

            if (t != null)
                targets.addAll(t);
        }

        return targets;
    }

    SootMethod getOrCreateStaticStub(ObjectSensitivePTA.ContextMethod targetContext) {
        SootMethod cached = ctxToStubMap.get(targetContext);
        if (cached != null)
            return cached;

        SootMethod original = targetContext.method;
        SootClass declaringClass = original.getDeclaringClass();

        List<Type> params = new ArrayList<>();
        params.add(declaringClass.getType());
        params.addAll(original.getParameterTypes());

        String stubName = uniqueStubName(declaringClass, original, params, targetContext);
        SootMethod stub = new SootMethod(
                stubName,
                params,
                original.getReturnType(),
                Modifier.PUBLIC | Modifier.STATIC,
                original.getExceptions());

        declaringClass.addMethod(stub);
        ctxToStubMap.put(targetContext, stub);

        StubInfo info = new StubInfo(targetContext);
        stubInfoMap.put(stub, info);

        buildStubBody(stub, original, info);
        transformStubBody(stub);
        return stub;
    }

    void emitPIC(
            Body body,
            Stmt stmt,
            InstanceInvokeExpr iie,
            Set<ObjectSensitivePTA.ContextMethod> targets) {

        Chain<Unit> units = body.getUnits();
        Local base = (Local) iie.getBase();

        // === STEP 1: sort by specificity (IMPORTANT) ===
        List<ObjectSensitivePTA.ContextMethod> ordered = new ArrayList<>(targets);

        ordered.sort((a, b) -> {
            SootClass ca = a.method.getDeclaringClass();
            SootClass cb = b.method.getDeclaringClass();

            if (Scene.v().getActiveHierarchy().isClassSubclassOf(ca, cb))
                return -1; // a more specific
            if (Scene.v().getActiveHierarchy().isClassSubclassOf(cb, ca))
                return 1;

            return 0;
        });

        List<Unit> newUnits = new ArrayList<>();
        NopStmt endLabel = Jimple.v().newNopStmt();

        // === STEP 2: find most general type (to skip guard) ===
        SootClass mostGeneral = null;
        for (ObjectSensitivePTA.ContextMethod t : ordered) {
            SootClass cls = t.method.getDeclaringClass();
            if (mostGeneral == null)
                mostGeneral = cls;
            else if (Scene.v().getActiveHierarchy().isClassSubclassOf(cls, mostGeneral))
                continue;
            else if (Scene.v().getActiveHierarchy().isClassSubclassOf(mostGeneral, cls))
                mostGeneral = cls;
        }

        // === STEP 3: generate guarded branches ===
        for (ObjectSensitivePTA.ContextMethod target : ordered) {

            SootMethod method = target.method;

            if (!isValidStubTarget(method))
                continue;

            SootClass targetClass = method.getDeclaringClass();

            // Skip guard for most general type (fallback handles it)
            boolean isMostGeneral = targetClass.equals(mostGeneral);

            SootMethod stub = getOrCreateStaticStub(target);

            NopStmt next = Jimple.v().newNopStmt();

            if (!isMostGeneral) {
                // cond = base instanceof T
                Local cond = Jimple.v().newLocal(
                        "$pic_cond_" + System.nanoTime(),
                        BooleanType.v());
                body.getLocals().add(cond);

                newUnits.add(Jimple.v().newAssignStmt(
                        cond,
                        Jimple.v().newInstanceOfExpr(base, targetClass.getType())));

                newUnits.add(Jimple.v().newIfStmt(
                        Jimple.v().newEqExpr(cond, IntConstant.v(0)),
                        next));
            }

            // === cast INSIDE guarded region ===
            Local typedBase = Jimple.v().newLocal(
                    "$pic_cast_" + System.nanoTime(),
                    targetClass.getType());

            body.getLocals().add(typedBase);

            newUnits.add(Jimple.v().newAssignStmt(
                    typedBase,
                    Jimple.v().newCastExpr(base, targetClass.getType())));

            List<Value> args = new ArrayList<>();
            args.add(typedBase);
            args.addAll(iie.getArgs());

            StaticInvokeExpr call = Jimple.v().newStaticInvokeExpr(stub.makeRef(), args);

            Unit callStmt;
            if (stmt instanceof AssignStmt)
                callStmt = Jimple.v().newAssignStmt(((AssignStmt) stmt).getLeftOp(), call);
            else
                callStmt = Jimple.v().newInvokeStmt(call);

            newUnits.add(callStmt);
            newUnits.add(Jimple.v().newGotoStmt(endLabel));

            if (!isMostGeneral)
                newUnits.add(next);
        }

        // === STEP 4: fallback (ONLY if needed) ===
        // --- SAFE FALLBACK RECONSTRUCTION ---
        InvokeExpr origInvoke = (InvokeExpr) iie.clone();

        Unit fallback;

        if (stmt instanceof AssignStmt) {
            fallback = Jimple.v().newAssignStmt(
                    ((AssignStmt) stmt).getLeftOp(),
                    origInvoke);
        } else {
            fallback = Jimple.v().newInvokeStmt(origInvoke);
        }

        newUnits.add(fallback);
        newUnits.add(endLabel);

        // === STEP 5: insert ===
        for (Unit u : newUnits)
            units.insertBefore(u, stmt);

        units.remove(stmt);
    }

    void buildStubBody(SootMethod stub, SootMethod original, StubInfo info) {
        Body originalBody = original.getActiveBody();
        JimpleBody stubBody = Jimple.v().newBody(stub);
        stub.setActiveBody(stubBody);

        Local originalThis = original.isStatic() ? null : originalBody.getThisLocal();

        Map<Local, Local> localMap = new HashMap<>(); // NOTE: Local - local map (old to new)
        for (Local originalLocal : originalBody.getLocals()) {
            Local clonedLocal = Jimple.v().newLocal(originalLocal.getName(), originalLocal.getType());
            stubBody.getLocals().add(clonedLocal);
            localMap.put(originalLocal, clonedLocal);
        }

        Local receiverLocal = Jimple.v().newLocal("r0_explicit", original.getDeclaringClass().getType());
        stubBody.getLocals().add(receiverLocal);
        info.receiverLocal = receiverLocal;

        Map<Unit, Unit> unitMap = new HashMap<>();
        for (Unit originalUnit : originalBody.getUnits()) {
            Unit cloned = (Unit) originalUnit.clone();
            stubBody.getUnits().add(cloned);
            unitMap.put(originalUnit, cloned);
            if (originalUnit instanceof Stmt && cloned instanceof Stmt)
                info.originalSiteByStubSite.put((Stmt) cloned, (Stmt) originalUnit);
        }

        // === FIX: remap all UnitBoxes (CRITICAL) ===
        for (Unit u : stubBody.getUnits()) {
            for (UnitBox ub : u.getUnitBoxes()) {
                Unit target = ub.getUnit();

                if (unitMap.containsKey(target)) {
                    ub.setUnit(unitMap.get(target));
                }
            }
        }

        for (Trap t : originalBody.getTraps()) {

            Unit begin = unitMap.get(t.getBeginUnit());
            Unit end = unitMap.get(t.getEndUnit());
            Unit handler = unitMap.get(t.getHandlerUnit());
            if (begin == null || end == null || handler == null)
                continue;

            stubBody.getTraps().add(Jimple.v().newTrap(
                    t.getException(),
                    begin,
                    end,
                    handler));
        }

        Unit clonedThisIdentity = null;
        for (Unit unit : new ArrayList<>(stubBody.getUnits())) {
            Stmt stmt = (Stmt) unit;

            if (stmt instanceof IdentityStmt) {
                IdentityStmt id = (IdentityStmt) stmt;
                Value rhs = id.getRightOp();
                if (rhs instanceof ThisRef) {
                    clonedThisIdentity = unit;
                } else if (rhs instanceof ParameterRef) {
                    int newIndex = ((ParameterRef) rhs).getIndex() + 1;
                    id.setRightOp(Jimple.v().newParameterRef(stub.getParameterType(newIndex), newIndex));
                }
            }

            for (ValueBox box : stmt.getUseAndDefBoxes()) {
                Value value = box.getValue();
                if (!(value instanceof Local))
                    continue;
                Local local = (Local) value;
                if (originalThis != null && local.equals(originalThis))
                    box.setValue(receiverLocal);
                else if (localMap.containsKey(local))
                    box.setValue(localMap.get(local));
            }
        }

        if (clonedThisIdentity != null)
            stubBody.getUnits().remove(clonedThisIdentity);

        if (!stubBody.getUnits().isEmpty()) {
            stubBody.getUnits().insertBefore(
                    Jimple.v().newIdentityStmt(
                            receiverLocal,
                            Jimple.v().newParameterRef(stub.getParameterType(0), 0)),
                    stubBody.getUnits().getFirst());
        } else {
            stubBody.getUnits().add(
                    Jimple.v().newIdentityStmt(
                            receiverLocal,
                            Jimple.v().newParameterRef(stub.getParameterType(0), 0)));
            appendDefaultReturn(stubBody, stub.getReturnType());
        }

        // try {
        // stubBody.validate();
        // } catch (RuntimeException e) {
        // System.err.println("[Mono/PTA] Warning: stub validation failed for "
        // + stub.getSignature() + ": " + e.getMessage());
        // }
    }

    void transformStubBody(SootMethod stub) {
        if (!stub.hasActiveBody())
            return;

        StubInfo info = stubInfoMap.get(stub);
        if (info == null)
            return;

        boolean changed;
        int guard = 0;
        do {
            changed = transformBody(stub.getActiveBody(), info);
        } while (changed && ++guard < 32);
    }

    AccessInfo computeAccessInfo(Body body, Local receiverLocal) {
        AccessInfo info = new AccessInfo();
        info.receiverRootedLocals.add(receiverLocal);
        info.allowedBases.add(receiverLocal);

        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof IdentityStmt))
                continue;
            IdentityStmt id = (IdentityStmt) unit;
            if (id.getLeftOp() instanceof Local && id.getRightOp() instanceof ParameterRef) {
                Local paramLocal = (Local) id.getLeftOp();
                info.parameterLocals.add(paramLocal);
                info.parameterCopies.add(paramLocal);
                info.allowedBases.add(paramLocal);
            }
        }

        boolean changed;
        do {
            changed = false;
            for (Unit unit : body.getUnits()) {
                if (!(unit instanceof AssignStmt))
                    continue;

                AssignStmt stmt = (AssignStmt) unit;
                Value lhs = stmt.getLeftOp();
                Value rhs = stmt.getRightOp();
                if (!(lhs instanceof Local))
                    continue;

                Local lhsLocal = (Local) lhs;
                if (rhs instanceof Local) {
                    Local rhsLocal = (Local) rhs;
                    if (info.receiverRootedLocals.contains(rhsLocal)) {
                        changed |= info.receiverRootedLocals.add(lhsLocal);
                        changed |= info.allowedBases.add(lhsLocal);
                    }
                    if (info.parameterCopies.contains(rhsLocal)) {
                        changed |= info.parameterCopies.add(lhsLocal);
                        changed |= info.allowedBases.add(lhsLocal);
                    }
                } else if (rhs instanceof CastExpr) {
                    Value op = ((CastExpr) rhs).getOp();
                    if (op instanceof Local) {
                        Local opLocal = (Local) op;
                        if (info.receiverRootedLocals.contains(opLocal)) {
                            changed |= info.receiverRootedLocals.add(lhsLocal);
                            changed |= info.allowedBases.add(lhsLocal);
                        }
                        if (info.parameterCopies.contains(opLocal)) {
                            changed |= info.parameterCopies.add(lhsLocal);
                            changed |= info.allowedBases.add(lhsLocal);
                        }
                    }
                } else if (rhs instanceof InstanceFieldRef) {
                    Value base = ((InstanceFieldRef) rhs).getBase();
                    if (base instanceof Local && info.receiverRootedLocals.contains(base)) {
                        changed |= info.receiverRootedLocals.add(lhsLocal);
                        changed |= info.allowedBases.add(lhsLocal);
                    }
                }
            }
        } while (changed);

        return info;
    }

    String uniqueStubName(
            SootClass declaringClass,
            SootMethod original,
            List<Type> params,
            ObjectSensitivePTA.ContextMethod targetContext) {
        String base = "staticStub" + original.getName() + contextSuffix(targetContext);
        String candidate = base;
        int suffix = 0;
        while (declaringClass.declaresMethod(candidate, params))
            candidate = base + "_" + (++suffix);
        return candidate;
    }
    
    String contextSuffix(ObjectSensitivePTA.ContextMethod cm) {
        if (cm.context.isEmpty())
            return "__ctx0";
        ObjectSensitivePTA.AllocObject receiver = cm.context.get(0);
        String site = receiver == null ? "unknown" : sanitizeForMethodName(receiver.siteName);
        return "__recv_" + site + "_" + Integer.toHexString(cm.context.hashCode());
    }

    String sanitizeForMethodName(String value) {
        if (value == null || value.isEmpty())
            return "ctx";
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < value.length(); i++) {
            char ch = value.charAt(i);
            if (Character.isLetterOrDigit(ch) || ch == '_')
                sb.append(ch);
            else
                sb.append('_');
        }
        return sb.toString();
    }

    Value ensureType(Value value, Type targetType, Stmt insertBefore, Body body) {
        if (value.getType().equals(targetType))
            return value;
        Local castLocal = Jimple.v().newLocal("$cast_" + System.identityHashCode(insertBefore), targetType);
        body.getLocals().add(castLocal);
        body.getUnits().insertBefore(
                Jimple.v().newAssignStmt(castLocal, Jimple.v().newCastExpr(value, targetType)),
                insertBefore);
        return castLocal;
    }

    void appendDefaultReturn(JimpleBody body, Type returnType) {
        if (returnType instanceof VoidType) {
            body.getUnits().add(Jimple.v().newReturnVoidStmt());
            return;
        }

        Local retLocal = Jimple.v().newLocal("$ret_default", returnType);
        body.getLocals().add(retLocal);
        body.getUnits().add(Jimple.v().newAssignStmt(retLocal, defaultValue(returnType)));
        body.getUnits().add(Jimple.v().newReturnStmt(retLocal));
    }

    Value defaultValue(Type type) {
        if (type instanceof IntType || type instanceof ByteType
                || type instanceof ShortType || type instanceof CharType
                || type instanceof BooleanType)
            return IntConstant.v(0);
        if (type instanceof LongType)
            return LongConstant.v(0L);
        if (type instanceof FloatType)
            return FloatConstant.v(0.0f);
        if (type instanceof DoubleType)
            return DoubleConstant.v(0.0);
        return NullConstant.v();
    }

    boolean isValidStubTarget(SootMethod m) {
        return (
            m != null && m.hasActiveBody() && !m.isNative() && 
            !m.isAbstract() && !m.isStatic() && !m.getDeclaringClass().isPhantom() && 
            !m.getDeclaringClass().isJavaLibraryClass()
        );
    }

}
