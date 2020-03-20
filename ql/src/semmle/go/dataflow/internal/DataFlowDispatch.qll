private import go
private import DataFlowPrivate

/** Gets the receiver of `call`, which must be an interface value. */
private DataFlow::Node getInterfaceCallReceiver(DataFlow::CallNode call) {
  call.getReceiver() = result and
  result.getType().getUnderlyingType() instanceof InterfaceType
}

/** Holds if `nd` may flow into the receiver value of `call`, which is an interface value. */
private DataFlow::Node getInterfaceCallReceiverSource(DataFlow::CallNode call) {
  result.getASuccessor*() = getInterfaceCallReceiver(call)
}

/** Gets the type of `nd`, which must be a valid type and not an interface type. */
private Type getConcreteType(DataFlow::Node nd) {
  result = nd.getType() and
  not result.getUnderlyingType() instanceof InterfaceType and
  not result instanceof InvalidType
}

/**
 * Holds if all concrete (that is, non-interface) types of `nd` concrete types can be determined by
 * local reasoning.
 *
 * `nd` is restricted to nodes that flow into the receiver value of an interface call, since that is
 * all we are ultimately interested in.
 */
private predicate isConcreteValue(DataFlow::Node nd) {
  nd = getInterfaceCallReceiverSource(_) and
  (
    exists(getConcreteType(nd))
    or
    forex(DataFlow::Node pred | pred = nd.getAPredecessor() | isConcreteValue(pred))
  )
}

/**
 * Gets a function that might be called by `call`, where the receiver of `call` has interface type,
 * but its concrete types can be determined by local reasoning.
 */
private FuncDecl getConcreteTarget(DataFlow::CallNode call) {
  isConcreteValue(getInterfaceCallReceiver(call)) and
  exists(Type concreteReceiverType, DeclaredFunction concreteTarget |
    concreteReceiverType = getConcreteType(getInterfaceCallReceiverSource(call)) and
    concreteTarget = concreteReceiverType.getMethod(call.getCalleeName()) and
    result = concreteTarget.getFuncDecl()
  )
}

/**
 * Gets a function that might be called by `call`.
 */
DataFlowCallable viableCallable(CallExpr ma) {
  exists(DataFlow::CallNode call | call.asExpr() = ma |
    if exists(getConcreteTarget(call))
    then result = getConcreteTarget(call)
    else result = call.getACallee()
  )
}

/**
 * Holds if the call context `ctx` reduces the set of viable dispatch
 * targets of `ma` in `c`.
 */
predicate reducedViableImplInCallContext(DataFlowCall ma, DataFlowCallable c, DataFlowCall ctx) {
  none()
}

/**
 * Gets a viable dispatch target of `ma` in the context `ctx`. This is
 * restricted to those `ma`s for which the context makes a difference.
 */
DataFlowCallable prunedViableImplInCallContext(DataFlowCall ma, DataFlowCall ctx) { none() }

/**
 * Holds if flow returning from `m` to `ma` might return further and if
 * this path restricts the set of call sites that can be returned to.
 */
predicate reducedViableImplInReturn(DataFlowCallable m, DataFlowCall ma) { none() }

/**
 * Gets a viable dispatch target of `ma` in the context `ctx`. This is
 * restricted to those `ma`s and results for which the return flow from the
 * result to `ma` restricts the possible context `ctx`.
 */
DataFlowCallable prunedViableImplInCallContextReverse(DataFlowCall ma, DataFlowCall ctx) { none() }
