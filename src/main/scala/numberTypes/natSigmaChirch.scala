package numberTypes

object natSigmaChirch:

  // ============================================================================
  // 1. Индексы и Сигма-тип в чистой кодировке Черча (как Type Lambda)
  // ============================================================================

  sealed abstract class NatIdx
  final class ZeroIdx extends NatIdx
  final class SuccIdx[I <: NatIdx] extends NatIdx

  type Σᴄʜɪʀᴄʜ[IndexType, F[_ <: IndexType]] = [Y] => ([I <: IndexType] => F[I] => Y) => Y

  // ============================================================================
  // 2. Индексированная Неподвижная Точка
  // ============================================================================

  case class Mu[F[_[_ <: NatIdx] <: Any, _ <: NatIdx] <: Any, I <: NatIdx](
                                                                            unfix: F[[X <: NatIdx] =>> Mu[F, X], I]
                                                                          )

  // ============================================================================
  // 3. Кодировка Натуральных чисел через Черч-Сигму
  // ============================================================================

  type NatFamily[R[_ <: NatIdx], I <: NatIdx] = [b <: Boolean] =>> b match
    case true  => Unit
    case false => R[I]

  type NatForm[R[_ <: NatIdx], O <: NatIdx] = Σᴄʜɪʀᴄʜ[Boolean, [b <: Boolean] =>> NatFamily[R, O match
    case ZeroIdx => ZeroIdx
    case SuccIdx[prev] => prev
  ][b]]

  trait Nat[I <: NatIdx]:
    val term: Mu[NatForm, I]
  end Nat

  object Nat:
    def zero: Nat[ZeroIdx] =
      new Nat[ZeroIdx]:
        val term = Mu[NatForm, ZeroIdx](
          ([Y] => (f: [I <: Boolean] => NatFamily[[X <: NatIdx] =>> Mu[NatForm, X], ZeroIdx][I] => Y) =>
            f[true](())
            ).asInstanceOf[NatForm[[X <: NatIdx] =>> Mu[NatForm, X], ZeroIdx]]
        )

    def succ[I <: NatIdx](n: Nat[I]): Nat[SuccIdx[I]] =
      new Nat[SuccIdx[I]]:
        val term = Mu[NatForm, SuccIdx[I]](
          ([Y] => (f: [B <: Boolean] => NatFamily[[X <: NatIdx] =>> Mu[NatForm, X], I][B] => Y) =>
            f[false](n.term)
            ).asInstanceOf[NatForm[[X <: NatIdx] =>> Mu[NatForm, X], SuccIdx[I]]]
        )
  end Nat

  // ============================================================================
  // 4. Зависимый Элиминатор (Индуктор)
  // ============================================================================

  def ind[P[_ <: NatIdx]](
                           vZero: P[ZeroIdx],
                           vSucc: [I <: NatIdx] => (prev: Mu[NatForm, I], prevP: P[I]) => P[SuccIdx[I]]
                         ): [I <: NatIdx] => (n: Nat[I]) => P[I] =
    [I <: NatIdx] => (n: Nat[I]) =>
      def loop[K <: NatIdx](m: Mu[NatForm, K]): P[K] =
        val churchSigma = m.unfix

        // Ожидаемый тип продолжения (continuation) для churchSigma
        type Cont = ([B <: Boolean] => Any => P[K]) => P[K]

        // Применяем каст к churchSigma, избавляя компилятор от необходимости раскрывать NatFamily внутри loop
        churchSigma.asInstanceOf[Cont](
          [B <: Boolean] => (value: Any) =>
            if value.isInstanceOf[Unit] then
              vZero.asInstanceOf[P[K]]
            else
              val prevTerm = value.asInstanceOf[Mu[NatForm, NatIdx]]
              val prevP = loop(prevTerm)
              vSucc(prevTerm, prevP).asInstanceOf[P[K]]
        )
      end loop
      loop(n.term)

  // ============================================================================
  // 5. Тестирование
  // ============================================================================

  object test:
    type TupleFamily[I <: NatIdx] <: Tuple = I match
      case ZeroIdx => EmptyTuple
      case SuccIdx[prev] => Int *: TupleFamily[prev]

    val myInductorBase = ind[TupleFamily](
      vZero = EmptyTuple,
      vSucc = [I <: NatIdx] => (prev: Mu[NatForm, I], prevP: TupleFamily[I]) =>
        (42 *: prevP).asInstanceOf[TupleFamily[SuccIdx[I]]]
    )

    inline def myInductor[I <: NatIdx](n: Nat[I]): TupleFamily[I] =
      myInductorBase[I](n)

    val n0 = Nat.zero
    val n1 = Nat.succ(n0)
    val n2 = Nat.succ(n1)

    val r0: EmptyTuple = myInductor(n0)
    val r1: Int *: EmptyTuple = myInductor(n1)
    val r2: Int *: Int *: EmptyTuple = myInductor(n2)

    println("==================================================")
    println("ЗАПУСК С ИСПОЛЬЗОВАНИЕМ ЧИСТОЙ ЧЕРЧ-СИГМЫ (CPS)")
    println("==================================================")
    println(s"Аргумент n0 (Zero)             -> Результат r0: $r0")
    println(s"Аргумент n1 (Succ(Zero))       -> Результат r1: $r1")
    println(s"Аргумент n2 (Succ(Succ(Zero))) -> Результат r2: $r2")
    println("==================================================")
  end test

end natSigmaChirch
