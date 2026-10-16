package numberTypes

object natPathDep:

  // ============================================================================
  // Nat: без параметра типа, индекс — сам Nat (type member I)
  // ============================================================================

  sealed trait Nat:
    type I <: Nat

  case object Zero extends Nat:
    type I = Zero.type

  final case class Succ[N <: Nat](prev: N) extends Nat:
    type I = Succ[N]

  // ============================================================================
  // Зависимый индуктор
  // ============================================================================

  type IndexedNatNext[P[_ <: Nat]] =
    [J <: Nat] => (prev: Nat { type I = J }, prevP: P[J]) => P[Succ[prev.type]]

  type NatInductor = [P[_ <: Nat]] =>
    (default: P[Zero.type], next: IndexedNatNext[P]) =>
      [N <: Nat] => (n: N) => P[n.I]

  val ind: NatInductor =
    [P[_ <: Nat]] => (default: P[Zero.type], next: IndexedNatNext[P]) =>
      [N <: Nat] => (n: N) =>
        n match
          case Zero =>
            default.asInstanceOf[P[n.I]]
          case s: Succ[?] =>
            val prev = s.prev
            val prevP = ind[P](default, next)(prev)
            next[prev.I](prev, prevP).asInstanceOf[P[n.I]]

  // ============================================================================
  // Тесты
  // ============================================================================

  object test:
    type TupleFamily[I <: Nat] <: Tuple = I match
      case Zero.type => EmptyTuple
      case Succ[prev] => Int *: TupleFamily[prev]

    val myInductor = ind[TupleFamily](
      default = EmptyTuple,
      next = [J <: Nat] => (prev: Nat { type I = J }, prevP: TupleFamily[J]) =>
        (42 *: prevP).asInstanceOf[TupleFamily[Succ[prev.type]]]
    )

    val n0: Nat = Zero
    val n1: Nat = Succ(n0)
    val n2: Nat = Succ(n1)

    val r0: TupleFamily[n0.I] = myInductor(n0)
    val r1: TupleFamily[n1.I] = myInductor(n1)
    val r2: TupleFamily[n2.I] = myInductor(n2)

    println("==================================================")
    println("NAT САМ СЕБЕ ИНДЕКС, БЕЗ NatIdx")
    println("==================================================")
    println(s"r0 = $r0")
    println(s"r1 = $r1")
    println(s"r2 = $r2")
    println("==================================================")
  end test

end natPathDep