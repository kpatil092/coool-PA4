import soot.*;
import soot.jimple.*;
import soot.util.*;

import java.util.*;

public class AnalysisTransformer extends SceneTransformer {

    final int PIC_LIMIT = 2;
    final int k = 3;

    // storing the comtext, meethod
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
        Set<Local> rcvrRootLocals = new LinkedHashSet<>();
        Set<Local> paramLocals = new LinkedHashSet<>();
        Set<Local> paramCopies = new LinkedHashSet<>();
        Set<Local> allowedBases = new LinkedHashSet<>();

        static AccessInfo empty() {
            return new AccessInfo();
        }
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
        // System.out.println(k + "-obj :: Reachable context-methods: " +
        // pta.getReachableContexts().size());
        // pta.printCallGraph();

        Set<SootMethod> contains = new LinkedHashSet<>();
        Deque<SootMethod> worklist = new ArrayDeque<>();

        for (ObjectSensitivePTA.ContextMethod cm : pta.getReachableContexts()) {
            SootMethod method = cm.method;
            if (!method.isConcrete() || method.isNative() || !method.hasActiveBody())
                continue;
            if (contains.add(method))
                worklist.add(method);
        }

        while (!worklist.isEmpty()) {
            SootMethod method = worklist.poll();
            contains.remove(method);
            if (!method.hasActiveBody())
                continue;

            boolean changed = transformBody(method.getActiveBody(), null);
            if (changed && contains.add(method))
                worklist.add(method);
        }

        System.out.println("Static stubs created: " + ctxToStubMap.size());
    }

    // boolean transformBody(Body body) {
    boolean transformBody(Body body, StubInfo stub) {
        SootMethod method = body.getMethod();
        boolean changed = false;

        AccessInfo accessInfo = (stub == null || stub.receiverLocal == null)
                ? AccessInfo.empty()
                : computeAccessInfo(body, stub.receiverLocal);

        // System.out.println(method.getName() );

        List<Unit> units = new ArrayList<>(body.getUnits());

        for (Unit unit : units) {
            if (!(unit instanceof Stmt))
                continue;
            Stmt stmt = (Stmt) unit;
            if (!stmt.containsInvokeExpr())
                continue;

            InvokeExpr ie = stmt.getInvokeExpr();
            if (!(ie instanceof VirtualInvokeExpr)
                    && !(ie instanceof InterfaceInvokeExpr))
                continue;

            // System.out.println("call site" + stmt + " -> method: " +
            // method.getSignature());

            InstanceInvokeExpr iie = (InstanceInvokeExpr) ie;
            Local base = (iie.getBase() instanceof Local) ? (Local) iie.getBase() : null;

            Stmt originalSite = (stub == null)
                    ? stmt
                    : stub.originalSiteByStubSite.get(stmt);

            Set<ObjectSensitivePTA.ContextMethod> targets = collectTargets(method, stub, stmt, originalSite,
                    iie, accessInfo, base);

            // monomorphic
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

                SootMethod targetStub = createNewStub(singleTarget);

                List<Value> newArgs = new ArrayList<>();
                Type receiverType = targetMethod.getDeclaringClass().getType();
                newArgs.add(ensureRcvrType(iie.getBase(), receiverType, stmt, body));
                newArgs.addAll(ie.getArgs());

                StaticInvokeExpr staticInvoke = Jimple.v().newStaticInvokeExpr(targetStub.makeRef(), newArgs);

                if (stmt instanceof AssignStmt)
                    ((AssignStmt) stmt).setRightOp(staticInvoke);
                else
                    ((InvokeStmt) stmt).setInvokeExpr(staticInvoke);

                changed = true;
                continue;
            }

            // PIC
            if (targets.size() > 1 && targets.size() <= PIC_LIMIT) {

                buildPIC(body, stmt, iie, targets);

                changed = true;
                continue;
            }

            // else virtual
        }

        return changed;
    }

    Set<ObjectSensitivePTA.ContextMethod> collectTargets(
            SootMethod enclosing, StubInfo stub, Stmt stmt, Stmt originalSite,
            InstanceInvokeExpr iie, AccessInfo accessInfo, Local baseLocal) {

        LinkedHashSet<ObjectSensitivePTA.ContextMethod> tgts = new LinkedHashSet<>();

        if (stub == null) {
            for (ObjectSensitivePTA.ContextMethod cm : pta.getReachableContexts()) {
                if (!cm.method.equals(enclosing))
                    continue;
                tgts.addAll(pta.getTargets(cm, stmt));
            }
        } else {
            if (baseLocal == null || !accessInfo.allowedBases.contains(baseLocal))
                return tgts;

            Set<ObjectSensitivePTA.ContextMethod> t = pta.getTargets(stub.contextMethod, originalSite);

            if (t != null)
                tgts.addAll(t);
        }

        return tgts;
    }

    SootMethod createNewStub(ObjectSensitivePTA.ContextMethod targetContext) {
        SootMethod cached = ctxToStubMap.get(targetContext);
        if (cached != null)
            return cached;

        SootMethod original = targetContext.method;
        SootClass declaringClass = original.getDeclaringClass();

        List<Type> params = new ArrayList<>();
        params.add(declaringClass.getType());
        params.addAll(original.getParameterTypes());

        String stubName = uniqueStubName(declaringClass, original, params, targetContext);
        SootMethod stub = new SootMethod(stubName, params,
                original.getReturnType(),
                Modifier.PUBLIC | Modifier.STATIC, original.getExceptions());

        declaringClass.addMethod(stub);
        ctxToStubMap.put(targetContext, stub);

        StubInfo info = new StubInfo(targetContext);
        stubInfoMap.put(stub, info);

        buildStubBody(stub, original, info);
        transformStubBody(stub);

        // System.out.println("Done building...? " + stubName);
        return stub;
    }

    void buildPIC(Body body, Stmt stmt, InstanceInvokeExpr iie,
            Set<ObjectSensitivePTA.ContextMethod> targets) {

        Chain<Unit> units = body.getUnits();
        Local base = (Local) iie.getBase();

        List<ObjectSensitivePTA.ContextMethod> ordered = new ArrayList<>(targets);

        ordered.sort((a, b) -> {
            SootClass ca = a.method.getDeclaringClass();
            SootClass cb = b.method.getDeclaringClass();

            if (Scene.v().getActiveHierarchy().isClassSubclassOf(ca, cb))
                return -1;
            if (Scene.v().getActiveHierarchy().isClassSubclassOf(cb, ca))
                return 1;
            return 0;
        });

        List<Unit> newUnits = new ArrayList<>();
        NopStmt endLabel = Jimple.v().newNopStmt();

        for (ObjectSensitivePTA.ContextMethod target : ordered) {

            SootMethod method = target.method;

            if (method == null || method.isNative() || method.isAbstract()
                    || method.getDeclaringClass().isPhantom()
                    || method.isStatic() || !method.hasActiveBody()
                    || method.getDeclaringClass().isJavaLibraryClass())
                continue;

            SootClass targetClass = method.getDeclaringClass();

            SootMethod stub = createNewStub(target);

            // System.out.println("stub created: " + stub.getName());
            NopStmt next = Jimple.v().newNopStmt();

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

            newUnits.add(next);
        }

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

        Unit newThis = null;
        for (Unit unit : new ArrayList<>(stubBody.getUnits())) {
            Stmt stmt = (Stmt) unit;

            if (stmt instanceof IdentityStmt) {
                IdentityStmt id = (IdentityStmt) stmt;
                Value rhs = id.getRightOp();
                if (rhs instanceof ThisRef) {
                    newThis = unit;
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

        if (newThis != null)
            stubBody.getUnits().remove(newThis);

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
            addDfltReturn(stubBody, stub.getReturnType());
        }

    }

    void transformStubBody(SootMethod stub) {
        if (!stub.hasActiveBody())
            return;

        StubInfo info = stubInfoMap.get(stub);
        if (info == null)
            return;

        boolean changed = true;
        int stop = 0;
        while (changed && ++stop < 30) {
            changed = transformBody(stub.getActiveBody(), info);
        }
    }

    AccessInfo computeAccessInfo(Body body, Local receiverLocal) {
        AccessInfo info = new AccessInfo();
        info.rcvrRootLocals.add(receiverLocal);
        info.allowedBases.add(receiverLocal);

        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof IdentityStmt))
                continue;
            IdentityStmt id = (IdentityStmt) unit;
            if (id.getLeftOp() instanceof Local && id.getRightOp() instanceof ParameterRef) {
                Local paramLocal = (Local) id.getLeftOp();
                info.paramLocals.add(paramLocal);
                info.paramCopies.add(paramLocal);
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
                    if (info.rcvrRootLocals.contains(rhsLocal)) {
                        changed |= info.rcvrRootLocals.add(lhsLocal);
                        changed |= info.allowedBases.add(lhsLocal);
                    }
                    if (info.paramCopies.contains(rhsLocal)) {
                        changed |= info.paramCopies.add(lhsLocal);
                        changed |= info.allowedBases.add(lhsLocal);
                    }
                } else if (rhs instanceof CastExpr) {
                    Value op = ((CastExpr) rhs).getOp();
                    if (op instanceof Local) {
                        Local opLocal = (Local) op;
                        if (info.rcvrRootLocals.contains(opLocal)) {
                            changed |= info.rcvrRootLocals.add(lhsLocal);
                            changed |= info.allowedBases.add(lhsLocal);
                        }
                        if (info.paramCopies.contains(opLocal)) {
                            changed |= info.paramCopies.add(lhsLocal);
                            changed |= info.allowedBases.add(lhsLocal);
                        }
                    }
                } else if (rhs instanceof InstanceFieldRef) {
                    Value base = ((InstanceFieldRef) rhs).getBase();
                    if (base instanceof Local && info.rcvrRootLocals.contains(base)) {
                        changed |= info.rcvrRootLocals.add(lhsLocal);
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
            ObjectSensitivePTA.ContextMethod cm) {

        String ctx = "c0";
        if (!cm.context.isEmpty() && cm.context.get(0) != null) {
            String site = cm.context.get(0).siteName;
            if (site != null && !site.isEmpty()) {
                site = site.replaceAll("[^a-zA-Z0-9]", "");
                ctx = "c_" + site;
            }
        }

        String base = "stub_" + original.getName() + "_" + ctx;

        String name = base;
        int i = 1;
        while (declaringClass.declaresMethod(name, params)) {
            name = base + i;
            i++;
        }

        return name;
    }

    Value ensureRcvrType(Value value, Type targetType, Stmt stmt, Body body) {
        if (value.getType().equals(targetType))
            return value;

        Local temp = Jimple.v().newLocal("tempVar" + body.getLocals().size(), targetType);
        body.getLocals().add(temp);

        body.getUnits().insertBefore(
                Jimple.v().newAssignStmt(
                        temp,
                        Jimple.v().newCastExpr(value, targetType)),
                stmt);

        return temp;
    }

    void addDfltReturn(JimpleBody body, Type type) {
        if (type instanceof VoidType) {
            body.getUnits().add(Jimple.v().newReturnVoidStmt());
            return;
        }

        Local tmp = Jimple.v().newLocal("ret", type);
        body.getLocals().add(tmp);

        Value dfltVal;
        if (type instanceof IntType || type instanceof ByteType ||
                type instanceof ShortType || type instanceof CharType ||
                type instanceof BooleanType)
            dfltVal = IntConstant.v(0);
        else if (type instanceof LongType)
            dfltVal = LongConstant.v(0L);
        else if (type instanceof FloatType)
            dfltVal = FloatConstant.v(0.0f);
        else if (type instanceof DoubleType)
            dfltVal = DoubleConstant.v(0.0);
        else
            dfltVal = NullConstant.v();

        body.getUnits().add(Jimple.v().newAssignStmt(tmp, dfltVal));
        body.getUnits().add(Jimple.v().newReturnStmt(tmp));
    }

}

// BUG: Library classes enterd in PTA
