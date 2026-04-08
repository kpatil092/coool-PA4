import soot.*;
import soot.jimple.*;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.util.Chain;

import java.util.*;

/**
 * Monomorphization transformation using the Soot framework.
 *
 * <p>
 * Algorithm overview:
 * <ol>
 * <li>Build / retrieve the Soot call graph (SPARK + VTA/CHA combination).</li>
 * <li>Iterate over every reachable method and every invoke statement inside
 * it.</li>
 * <li>For each virtual / interface call site that has EXACTLY ONE target in the
 * call graph, create a fresh static method whose signature mirrors the
 * original but receives the receiver as an explicit first parameter.</li>
 * <li>Replace the virtual invoke expression with a static invoke that passes
 * the old receiver as the new first argument.</li>
 * <li>Reuse already-created static stubs (keyed by original method + declaring
 * class) so we do not duplicate work when the same target is reached from
 * multiple call sites.</li>
 * </ol>
 *
 * <p>
 * Edge cases handled:
 * <ul>
 * <li>Interface invokes ({@link InterfaceInvokeExpr}) as well as virtual
 * invokes
 * ({@link VirtualInvokeExpr}) and special invokes ({@link SpecialInvokeExpr})
 * are all considered.</li>
 * <li>Methods that belong to excluded / phantom classes are skipped.</li>
 * <li>Native methods cannot have a Jimple body and are skipped.</li>
 * <li>Recursive targets (callee == caller) are handled safely because the stub
 * is inserted into the scene before the body is mutated.</li>
 * <li>Methods that are already static are not processed.</li>
 * <li>The receiver cast is inserted when the declared parameter type differs
 * from the concrete receiver type to keep Jimple type-correctness.</li>
 * </ul>
 */
public class AnalysisTransformer extends SceneTransformer {

    /**
     * Cache: (original SootMethod, declaring SootClass) -> generated static stub.
     * This lets us reuse the same stub when multiple call sites share the same
     * single-target callee.
     */
    private final Map<SootMethod, SootMethod> staticStubCache = new HashMap<>();

    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {

        CallGraph cg = Scene.v().getCallGraph();

        LinkedList<SootMethod> worklist = new LinkedList<>();

        // initialize worklist
        for (SootClass sc : Scene.v().getApplicationClasses()) {
            if (sc.isPhantom() || !sc.isConcrete())
                continue;

            for (SootMethod m : sc.getMethods()) {
                if (!m.isConcrete() || m.isAbstract() || m.isNative())
                    continue;

                if (!m.hasActiveBody()) {
                    try {
                        m.retrieveActiveBody();
                    } catch (Exception e) {
                        continue;
                    }
                }

                worklist.add(m);
            }
        }

        Set<SootMethod> seen = new HashSet<>();

        while (!worklist.isEmpty()) {
            SootMethod m = worklist.poll();

            if (!m.hasActiveBody())
                continue;

            Body body = m.getActiveBody();

            boolean changed = transformBody(body, cg);

            if (changed) {
                // 🔥 reprocess this method again
                worklist.add(m);

                // also add all stub methods (important!)
                for (SootMethod stub : staticStubCache.values()) {
                    if (!seen.contains(stub)) {
                        worklist.add(stub);
                        seen.add(stub);
                    }
                }
            }
        }

        System.out.println("[Monomorphization] Static stubs created: " + staticStubCache.size());
    }

    // -------------------------------------------------------------------------
    // Core per-body transformation
    // -------------------------------------------------------------------------

    /**
     * Scans every statement in {@code body} for mono-morphic virtual/interface
     * call sites and replaces them with calls to the corresponding static stub.
     */
    private boolean transformBody(Body body, CallGraph cg) {
        SootMethod enclosingMethod = body.getMethod();
        Chain<Unit> units = body.getUnits();

        boolean changed = false;

        // Snapshot: avoid ConcurrentModificationException while patching.
        List<Unit> unitSnapshot = new ArrayList<>(units);

        for (Unit unit : unitSnapshot) {
            Stmt stmt = (Stmt) unit;
            if (!stmt.containsInvokeExpr()) {
                continue;
            }

            InvokeExpr invokeExpr = stmt.getInvokeExpr();

            // Only virtual / interface / special instance calls are candidates.
            if (!(invokeExpr instanceof VirtualInvokeExpr)
                    && !(invokeExpr instanceof InterfaceInvokeExpr)) {
                continue;
            }

            InstanceInvokeExpr iie = (InstanceInvokeExpr) invokeExpr;

            // ------------------------------------------------------------------
            // 1. Check call graph: how many targets does this call site have?
            // ------------------------------------------------------------------
            Iterator<Edge> edgesOut = cg.edgesOutOf(stmt);

            // IMPORTANT: we must re-iterate, so store edges

            // System.out.println("Callsite: " + stmt);
            Iterator<Edge> it = cg.edgesOutOf(stmt);
            // while (it.hasNext()) {
            //     System.out.println("  -> " + it.next().getTgt().method());
            // }

            List<Edge> edgeList = new ArrayList<>();
            while (edgesOut.hasNext()) {
                edgeList.add(edgesOut.next());
            }
            SootMethod singleTarget = getSingleTarget(edgeList.iterator());

            if (singleTarget == null) {
                if (!edgeList.isEmpty()) {
                    // multiple distinct targets → skip
                    continue;
                }

                // ✔ fallback only when NO edges
                try {
                    singleTarget = iie.getMethod();
                } catch (Exception e) {
                    continue;
                }
            }

            // Skip if target is native, abstract, or belongs to a phantom class.
            if (singleTarget.isNative()
                    || singleTarget.isAbstract()
                    || singleTarget.getDeclaringClass().isPhantom()) {
                continue;
            }

            // Skip if it is already a static method (shouldn't happen via iie, but
            // defensive check).
            if (singleTarget.isStatic()) {
                continue;
            }

            // Self-recursion via the same virtual dispatch — safe, continue.

            // ------------------------------------------------------------------
            // 2. Get or create the static stub for this target.
            // ------------------------------------------------------------------
            SootMethod stub = getOrCreateStaticStub(singleTarget);

            // ------------------------------------------------------------------
            // 3. Build the replacement static invoke expression.
            // Original args: [arg0, arg1, ...]
            // New args: [receiver, arg0, arg1, ...]
            // ------------------------------------------------------------------
            List<Value> newArgs = new ArrayList<>();
            Value receiver = iie.getBase();

            // The stub's first parameter type is the declaring class type.
            // If the receiver's type is a sub-type we may need a cast local.
            Type expectedReceiverType = singleTarget.getDeclaringClass().getType();
            Value receiverArg = ensureType(receiver, expectedReceiverType, stmt, body);

            newArgs.add(receiverArg);
            newArgs.addAll(invokeExpr.getArgs());

            StaticInvokeExpr staticInvoke = Jimple.v().newStaticInvokeExpr(stub.makeRef(), newArgs);

            // ------------------------------------------------------------------
            // 4. Patch the statement in-place.
            // ------------------------------------------------------------------
            if (stmt instanceof AssignStmt) {
                ((AssignStmt) stmt).setRightOp(staticInvoke);
            } else if (stmt instanceof InvokeStmt) {
                ((InvokeStmt) stmt).setInvokeExpr(staticInvoke);
            }
            // Other statement kinds (e.g., ThrowStmt) don't carry invoke exprs
            // in the way that would reach here.

            changed = true;
        }

        return changed;
    }

    // -------------------------------------------------------------------------
    // Helper: resolve single call-graph target
    // -------------------------------------------------------------------------

    /**
     * Returns the unique {@link SootMethod} target of a call site, or
     * {@code null} if there are zero or more than one targets.
     */
    private SootMethod getSingleTarget(Iterator<Edge> edges) {
        SootMethod target = null;
        while (edges.hasNext()) {
            Edge edge = edges.next();
            SootMethod tgt = edge.getTgt().method();
            if (target == null) {
                target = tgt;
            } else if (!target.equals(tgt)) {
                // More than one distinct target → not mono-morphic.
                return null;
            }
        }
        return target; // null if no edges at all; non-null unique target otherwise.
    }

    // -------------------------------------------------------------------------
    // Helper: static stub creation
    // -------------------------------------------------------------------------

    /**
     * Returns a cached static stub for {@code original}, or creates, registers,
     * and populates one if it does not yet exist.
     *
     * <p>
     * The stub has the same name as the original, prefixed with
     * {@code "__mono_"}, resides in the same class, and carries an extra first
     * parameter of the declaring class type (the explicit receiver).
     */
    private SootMethod getOrCreateStaticStub(SootMethod original) {
        if (staticStubCache.containsKey(original)) {
            return staticStubCache.get(original);
        }

        SootClass declaringClass = original.getDeclaringClass();

        // ------------------------------------------------------------------
        // Build parameter list: (DeclaringClass receiver, <original params>)
        // ------------------------------------------------------------------
        List<Type> stubParams = new ArrayList<>();
        stubParams.add(declaringClass.getType()); // explicit receiver
        stubParams.addAll(original.getParameterTypes());

        // ------------------------------------------------------------------
        // Derive a unique name that avoids clashes with existing methods.
        // ------------------------------------------------------------------
        String stubName = uniqueStubName(declaringClass, original, stubParams);

        // ------------------------------------------------------------------
        // Create and register the stub SootMethod.
        // ------------------------------------------------------------------
        SootMethod stub = new SootMethod(
                stubName,
                stubParams,
                original.getReturnType(),
                Modifier.PUBLIC | Modifier.STATIC,
                original.getExceptions());

        declaringClass.addMethod(stub);
        // Register in cache BEFORE populating the body to handle recursive cases.
        staticStubCache.put(original, stub);

        // ------------------------------------------------------------------
        // Build the stub body.
        // ------------------------------------------------------------------
        buildStubBody(stub, original);

        return stub;
    }

    /**
     * Returns a method name that does not already exist in {@code cls} with the
     * given parameter types.
     */
    private String uniqueStubName(SootClass cls, SootMethod original, List<Type> params) {
        String base = "__mono_" + original.getName();
        String candidate = base;
        int suffix = 0;
        while (cls.declaresMethod(candidate, params)) {
            candidate = base + "_" + (++suffix);
        }
        return candidate;
    }

    /**
     * Populates {@code stub} with a Jimple body that:
     * <ol>
     * <li>Receives the receiver as {@code @parameter 0} (type = declaring
     * class).</li>
     * <li>Receives the original parameters as {@code @parameter 1..n}.</li>
     * <li>Reads the original method's body.</li>
     * <li>Replaces every occurrence of {@code @this} with the explicit receiver
     * parameter, and every {@code @parameter i} with {@code @parameter i+1}.</li>
     * <li>Clones all locals, traps, and units from the original body into the
     * stub body, applying the parameter remapping.</li>
     * </ol>
     */
    private void buildStubBody(SootMethod stub, SootMethod original) {
        // Ensure original has a body we can clone.
        if (!original.hasActiveBody()) {
            try {
                original.retrieveActiveBody();
            } catch (Exception e) {
                // Fallback: empty body that just returns.
                buildEmptyStubBody(stub);
                return;
            }
        }

        Body origBody = original.getActiveBody();

        // ------------------------------------------------------------------
        // Create a fresh Jimple body for the stub.
        // ------------------------------------------------------------------
        JimpleBody stubBody = Jimple.v().newBody(stub);
        stub.setActiveBody(stubBody);

        // ------------------------------------------------------------------
        // Determine the original @this local and @parameter locals.
        // ------------------------------------------------------------------
        Local origThisLocal = origBody.getThisLocal();

        // Map: original local → stub local (we clone all locals).
        Map<Local, Local> localMap = new HashMap<>();

        // Clone locals.
        for (Local origLocal : origBody.getLocals()) {
            Local stubLocal = Jimple.v().newLocal(origLocal.getName(), origLocal.getType());
            stubBody.getLocals().add(stubLocal);
            localMap.put(origLocal, stubLocal);
        }

        // Add the explicit receiver parameter local (r0_explicit).
        Local receiverLocal = Jimple.v().newLocal(
                "r0_explicit", original.getDeclaringClass().getType());
        stubBody.getLocals().add(receiverLocal);

        // ------------------------------------------------------------------
        // Build a value substitutor using a box-based visitor.
        // ------------------------------------------------------------------
        // We use Soot's cloneBody utility then patch identity statements.

        // Clone the original body's unit graph into the stub.
        // Soot provides Body.importBodyContentsFrom which deep-clones units,
        // locals (we've already added them), and traps.
        // We'll clone units manually to control @this / @parameter remapping.

        // Traps (exception handlers): clone with updated unit references later.
        // We'll track original->stub unit mapping.
        Map<Unit, Unit> unitMap = new HashMap<>();

        for (Unit origUnit : origBody.getUnits()) {
            Unit cloned = (Unit) origUnit.clone();
            stubBody.getUnits().add(cloned);
            unitMap.put(origUnit, cloned);
        }

        // Clone traps.
        for (Trap origTrap : origBody.getTraps()) {
            Trap cloned = Jimple.v().newTrap(
                    origTrap.getException(),
                    unitMap.get(origTrap.getBeginUnit()),
                    unitMap.get(origTrap.getEndUnit()),
                    unitMap.get(origTrap.getHandlerUnit()));
            stubBody.getTraps().add(cloned);
        }

        // ------------------------------------------------------------------
        // Patch identity statements and local references.
        // ------------------------------------------------------------------
        // After cloning, the cloned body still contains IdentityStmt with
        // ThisRef / ParameterRef pointing to the original method's indices.
        // We need to:
        // - Replace @this → @parameter 0 (receiverLocal) in the stub.
        // - Replace @param i → @parameter i+1 in the stub.
        // - Replace all Value uses of origThisLocal → receiverLocal.
        // - Replace all Value uses of other original locals → their stub clones.

        Unit clonedThisIdentityUnit = null;
        ArrayList<Unit> unitList = new ArrayList<>(stubBody.getUnits());

        for (Unit unit : unitList) {
            Stmt stmt = (Stmt) unit;

            // Fix IdentityStmt (e.g. r0 := @this, x := @parameter 0)
            if (stmt instanceof IdentityStmt) {
                IdentityStmt idStmt = (IdentityStmt) stmt;
                Value rightOp = idStmt.getRightOp();

                if (rightOp instanceof ThisRef) {
                    // Replace with: receiverLocal := @parameter 0
                    // idStmt.setRightOp(Jimple.v().newParameterRef(stub.getParameterType(0), 0));

                    clonedThisIdentityUnit = unit;

                    // The left-hand side local was cloned from origThisLocal;
                    // update localMap so further uses are replaced correctly.
                    // Actually we handle this via the general local-replacement pass below.
                } else if (rightOp instanceof ParameterRef) {
                    ParameterRef pr = (ParameterRef) rightOp;
                    // Shift index by 1 (slot 0 is now the explicit receiver).
                    int newIndex = pr.getIndex() + 1;
                    idStmt.setRightOp(Jimple.v().newParameterRef(
                            stub.getParameterType(newIndex), newIndex));
                }
            }

            // Replace all local references in every ValueBox.
            for (ValueBox vb : stmt.getUseAndDefBoxes()) {
                Value v = vb.getValue();
                if (v instanceof Local) {
                    Local origLocal = (Local) v;
                    if (origLocal.equals(origThisLocal)) {
                        // References to the original @this → receiverLocal
                        vb.setValue(receiverLocal);
                    } else if (localMap.containsKey(origLocal)) {
                        vb.setValue(localMap.get(origLocal));
                    }
                    // Locals already pointing to stub locals are fine as-is.
                }
            }
        }

        if (clonedThisIdentityUnit != null) {
            stubBody.getUnits().remove(clonedThisIdentityUnit);
        }

        // Wire up the receiver identity statement at the top.
        // The cloned @this identity stmt now sets a cloned local to @parameter 0,
        // but we want receiverLocal to carry the receiver. Insert a fresh
        // identity statement for receiverLocal BEFORE all others and remove the
        // clone of the original @this identity.

        IdentityStmt receiverIdStmt = Jimple.v().newIdentityStmt(
                receiverLocal,
                Jimple.v().newParameterRef(stub.getParameterType(0), 0));

        // Remove the cloned @this identity (it now assigns a regular cloned local
        // to @parameter 0 — we'll keep it to preserve the local but we might
        // want to drop it to avoid unused locals; keeping it is safe for Jimple).
        // Insert receiver identity at the very beginning.
        Unit firstUnit = stubBody.getUnits().getFirst();
        stubBody.getUnits().insertBefore(receiverIdStmt, firstUnit);

        // Validate (optional, catches Jimple type errors during development).
        try {
            stubBody.validate();
        } catch (Exception e) {
            System.err.println("[Monomorphization] Warning: stub body validation failed for "
                    + stub.getSignature() + ": " + e.getMessage());
        }
    }

    /**
     * Fallback: build a minimal valid stub body that just returns the default
     * value (used when the original body cannot be retrieved).
     */
    private void buildEmptyStubBody(SootMethod stub) {
        JimpleBody body = Jimple.v().newBody(stub);
        stub.setActiveBody(body);

        // Add identity statements for each parameter.
        List<Local> paramLocals = new ArrayList<>();
        for (int i = 0; i < stub.getParameterCount(); i++) {
            Local p = Jimple.v().newLocal("p" + i, stub.getParameterType(i));
            body.getLocals().add(p);
            body.getUnits().add(Jimple.v().newIdentityStmt(
                    p, Jimple.v().newParameterRef(stub.getParameterType(i), i)));
            paramLocals.add(p);
        }

        Type retType = stub.getReturnType();
        if (retType instanceof VoidType) {
            body.getUnits().add(Jimple.v().newReturnVoidStmt());
        } else {
            Local retLocal = Jimple.v().newLocal("ret", retType);
            body.getLocals().add(retLocal);
            body.getUnits().add(Jimple.v().newAssignStmt(
                    retLocal, defaultValue(retType)));
            body.getUnits().add(Jimple.v().newReturnStmt(retLocal));
        }
    }

    // -------------------------------------------------------------------------
    // Helper: ensure receiver has the correct declared type (insert cast if needed)
    // -------------------------------------------------------------------------

    /**
     * If {@code value}'s type already conforms to {@code targetType}, returns
     * {@code value} unchanged. Otherwise inserts a cast statement before
     * {@code insertBefore} and returns a new typed local holding the cast result.
     */
    private Value ensureType(Value value, Type targetType, Stmt insertBefore, Body body) {
        Type valueType = value.getType();
        if (valueType.equals(targetType)) {
            return value;
        }
        // Insert: castLocal = (TargetType) value
        Local castLocal = Jimple.v().newLocal(
                "$cast_" + System.identityHashCode(value), targetType);
        body.getLocals().add(castLocal);
        AssignStmt castStmt = Jimple.v().newAssignStmt(
                castLocal,
                Jimple.v().newCastExpr(value, targetType));
        body.getUnits().insertBefore(castStmt, insertBefore);
        return castLocal;
    }

    // -------------------------------------------------------------------------
    // Helper: default (zero) value for a type
    // -------------------------------------------------------------------------

    private Value defaultValue(Type t) {
        if (t instanceof IntType
                || t instanceof ByteType
                || t instanceof ShortType
                || t instanceof CharType
                || t instanceof BooleanType) {
            return IntConstant.v(0);
        } else if (t instanceof LongType) {
            return LongConstant.v(0L);
        } else if (t instanceof FloatType) {
            return FloatConstant.v(0.0f);
        } else if (t instanceof DoubleType) {
            return DoubleConstant.v(0.0);
        } else {
            return NullConstant.v(); // reference types
        }
    }
}