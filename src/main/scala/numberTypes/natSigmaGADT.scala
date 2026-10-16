package numberTypes

import numberTypes.sigmaTypes.*

object natSigmaGADT:

  sealed abstract class NatIdx
  final class ZeroIdx              private extends NatIdx
  final class SuccIdx[I <: NatIdx] private extends NatIdx

  type NatFamily[NextLayer[_ <: NatIdx], I <: NatIdx] = [b <: Bool] =>> b match
    case true => Unit
    case false => NextLayer[I]

  type PredIdx[I <: NatIdx] <: NatIdx = I match
    case ZeroIdx => ZeroIdx
    case SuccIdx[prev] => prev

  type NatFunctor[NextLayer[_ <: NatIdx], I <: NatIdx] =
    ∑[Bool, NatFamily[NextLayer, PredIdx[I]]]

  type Nat = μμ[NatIdx][NatFunctor]

  object Nat:
    def zero: Nat[ZeroIdx] =
      Mu[NatIdx, NatFunctor, ZeroIdx](
        Σin[Bool, NatFamily[Nat, ZeroIdx], true](())
      )

    def succ[I <: NatIdx](n: Nat[I]): Nat[SuccIdx[I]] =
      Mu[NatIdx, NatFunctor, SuccIdx[I]](
        Σin[Bool, NatFamily[Nat, I], false](n)
      )

  // ============================================================================
  // 4. Зависимый Элиминатор (Индуктор)
  // ============================================================================

  type IndexedNatNext[P[_ <: NatIdx]] = [I <: NatIdx] => (prev: Nat[I], prevP: P[I]) => P[SuccIdx[I]]
  type NatInductor = [P[_ <: NatIdx]]
    => (default: P[ZeroIdx], next: IndexedNatNext[P])
    => [I <: NatIdx]
    => Nat[I]
    => P[I]

  val ind: NatInductor =
    [P[_ <: NatIdx]] => (default: P[ZeroIdx], next: IndexedNatNext[P]) => [I <: NatIdx] => (n: Nat[I]) =>
      def loop[K <: NatIdx]: Nat[K] => P[K] =
        case Mu(ΣIn(true , _ )) => default.asInstanceOf[P[K]]
        case Mu(ΣIn(false, fi)) =>
          val prevTerm = fi.asInstanceOf[Nat[NatIdx]]
          next(prevTerm, loop(prevTerm)).asInstanceOf[P[K]]

      loop(n)

  // ============================================================================
  // 5. Тестирование
  // ============================================================================

  object test:
    type TupleFamily[I <: NatIdx] <: Tuple = I match
      case ZeroIdx => EmptyTuple
      case SuccIdx[prev] => Int *: TupleFamily[prev]

    val myInductor = ind[TupleFamily](
      default = EmptyTuple,
      next = [I <: NatIdx] => (prev: Nat[I], prevP: TupleFamily[I]) => 42 *: prevP
    )

    val n0 = Nat.zero
    val n1 = Nat.succ(n0)
    val n2 = Nat.succ(n1)

    val r0: EmptyTuple = myInductor(n0)
    val r1: Int *: EmptyTuple = myInductor(n1)
    val r2: Int *: Int *: EmptyTuple = myInductor(n2)

    println("==================================================")
    println("ЗАПУСК С ИСПОЛЬЗОВАНИЕМ СИГМА-ТИПА ЧЕРЕЗ GADT ENUM")
    println("==================================================")
    println(s"Аргумент n0 (Zero)             -> Результат r0: $r0")
    println(s"Аргумент n1 (Succ(Zero))       -> Результат r1: $r1")
    println(s"Аргумент n2 (Succ(Succ(Zero))) -> Результат r2: $r2")
    println("==================================================")
  end test

end natSigmaGADT
