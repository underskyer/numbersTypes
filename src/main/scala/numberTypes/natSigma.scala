package numberTypes

import numberTypes.sigmaTypes.Σᴏᴏᴘ

object natSigma:

  // ============================================================================
  // 1. Индексы и Зависимый Сигма-тип
  // ============================================================================

  enum NatIdx:
    case ZeroIdx extends NatIdx
    case SuccIdx[I <: NatIdx]() extends NatIdx

  import NatIdx.{ZeroIdx, SuccIdx}
  type ZeroIdx = ZeroIdx.type

  type Bool = Boolean & Singleton

  object NatIndexFix:
    type N[B <: Bool] = [P, Succ[_]] =>> B match
      case false => P
      case true => Succ[P]

    //type Succ = NatIdx.SuccIdx

    type N0 = N[false][ZeroIdx, Option]
    type N1 = N[true][N0, Option]
    type N2 = N[true][N1, Option]
    type N3 = N[true][N2, Option]

    case class MuN[F[_[_ <: Bool], _ <: Bool], B <: Bool](
      unfix: F[[X <: Bool] =>> MuN[F, X], B]
    )

    type μN[F[_[_ <: Bool], _ <: Bool]] = [B <: Bool] =>> MuN[F, B]

    type NF[Self[_ <: Bool], B <: Bool] = B match
      case false => Unit
      case true => Self[Unit]

    type NIdx = μN[NF]

  end NatIndexFix

  // ============================================================================
  // 3. Чистый Натуральный Тип без ООП-надстроек (NatFunctor & NatTerm API)
  // ============================================================================

  type NatFamily[NextLayer[_ <: NatIdx], I <: NatIdx] = [b <: Bool] =>> b match
    case true  => Unit
    case false => NextLayer[I]

  type PredIdx[I <: NatIdx] <: NatIdx = I match
    case ZeroIdx => ZeroIdx
    case SuccIdx[prev] => prev

  // Переименовали NatForm в NatFunctor
  type NatFunctor[NextLayer[_ <: NatIdx], I <: NatIdx] = Σᴏᴏᴘ[Bool,
    NatFamily[NextLayer, PredIdx[I]]
  ]

  type Nat = μμ[NatIdx][NatFunctor]

  type ℕ = Σᴏᴏᴘ[NatIdx, Nat]

  given [I <: NatIdx] => Conversion[Nat[I], ℕ] = (n: Nat[I]) => Σᴏᴏᴘ.OOP[NatIdx, Nat, I](n)

  object Nat:
    def zero: Nat[ZeroIdx] =
      Mu[NatIdx, NatFunctor, ZeroIdx](
        Σᴏᴏᴘ[Bool, NatFamily[Nat, ZeroIdx], true](())
          .asInstanceOf[Σᴏᴏᴘ[Bool, NatFamily[Nat, ZeroIdx]]]
      )

    def succ[I <: NatIdx](n: Nat[I]): Nat[SuccIdx[I]] =
      Mu[NatIdx, NatFunctor, SuccIdx[I]](
        Σᴏᴏᴘ[Bool, NatFamily[Nat, I], false](n)
          .asInstanceOf[Σᴏᴏᴘ[Bool, NatFamily[Nat, I]]]
      )
  end Nat

  // ============================================================================
  // 4. Зависимый Элиминатор (Индуктор) работает напрямую с NatTerm
  // ============================================================================

  def ind[P[_ <: NatIdx]](
    vZero: P[ZeroIdx],
    vSucc: [I <: NatIdx] => (prev: Nat[I], prevP: P[I]) => P[SuccIdx[I]]
  ): [I <: NatIdx] => (n: Nat[I]) => P[I] =
    [I <: NatIdx] => (n: Nat[I]) =>
      def loop[K <: NatIdx](m: Nat[K]): P[K] = m.unfix match
        case Σᴏᴏᴘ.OOP(_: Unit) => vZero.asInstanceOf[P[K]]
        case Σᴏᴏᴘ.OOP(_: Nat[I]) =>
        //case _: Σᴏᴏᴘ[NatIdx, NatFamily[Nat, PredIdx[I]]] { type I = false } =>
          val prevTerm = m.unfix.value.asInstanceOf[Nat[NatIdx]]
          val prevP = loop(prevTerm)
          vSucc(prevTerm, prevP).asInstanceOf[P[K]]
      loop(n)

  // ============================================================================
  // 5. Наглядный тест
  // ============================================================================

  object test:
    type TupleFamily[I <: NatIdx] <: Tuple = I match
      case ZeroIdx => EmptyTuple
      case SuccIdx[prev] => Int *: TupleFamily[prev]

    val myInductor = ind[TupleFamily](
      vZero = EmptyTuple,
      vSucc = [I <: NatIdx] => (prev: Nat[I], prevP: TupleFamily[I]) =>
        (42 *: prevP).asInstanceOf[TupleFamily[SuccIdx[I]]]
    )

    // Конструируем термы напрямую через фабрику NatTerm
    val n0 = Nat.zero
    val n1 = Nat.succ(n0)
    val n2 = Nat.succ(n1)

    val r0: EmptyTuple = myInductor(n0)
    val r1: Int *: EmptyTuple = myInductor(n1)
    val r2: Int *: Int *: EmptyTuple = myInductor(n2)

    println("==================================================")
    println("ЗАПУСК: Чистый NatTerm API без лишних Трейтов")
    println("==================================================")
    println(s"Аргумент n0 (Zero)             -> Результат r0: $r0")
    println(s"Аргумент n1 (Succ(Zero))       -> Результат r1: $r1")
    println(s"Аргумент n2 (Succ(Succ(Zero))) -> Результат r2: $r2")
    println("==================================================")

