package numberTypes

object natSigma:

  // ============================================================================
  // 1. Индексы и Зависимый Сигма-тип
  // ============================================================================

  sealed abstract class NatIdx
  final class ZeroIdx extends NatIdx
  final class SuccIdx[I <: NatIdx] extends NatIdx

  trait Sigma[F[_ <: Boolean]]:
    type Tag <: Boolean
    val tag: Tag
    val value: F[Tag]
  end Sigma

  object Sigma:
    def apply[F[_ <: Boolean], B <: Boolean](t: B, v: F[B]): Sigma[F] { type Tag = B } =
      new Sigma[F]:
        type Tag = B
        val tag: B = t
        val value: F[B] = v
      end new
  end Sigma

  // ============================================================================
  // 2. Индексированная Неподвижная Точка
  // ============================================================================

  case class Mu[F[_[_ <: NatIdx] <: Any, _ <: NatIdx] <: Any, I <: NatIdx](
                                                                            unfix: F[[X <: NatIdx] =>> Mu[F, X], I]
                                                                          )

  // ============================================================================
  // 3. Кодировка Натуральных чисел
  // ============================================================================

  type NatFamily[R[_ <: NatIdx], I <: NatIdx] = [b <: Boolean] =>> b match
    case true  => Unit
    case false => R[I]

  type NatForm[R[_ <: NatIdx], O <: NatIdx] = Sigma[NatFamily[R, O match
    case ZeroIdx => ZeroIdx
    case SuccIdx[prev] => prev
  ]]

  trait Nat[I <: NatIdx]:
    val term: Mu[NatForm, I]
  end Nat

  object Nat:
    def zero: Nat[ZeroIdx] =
      new Nat[ZeroIdx]:
        val term = Mu[NatForm, ZeroIdx](
          Sigma[[b <: Boolean] =>> NatFamily[[X <: NatIdx] =>> Mu[NatForm, X], ZeroIdx][b], true](true, ())
            .asInstanceOf[Sigma[[b <: Boolean] =>> NatFamily[[X <: NatIdx] =>> Mu[NatForm, X], ZeroIdx][b]]]
        )
      end new

    def succ[I <: NatIdx](n: Nat[I]): Nat[SuccIdx[I]] =
      new Nat[SuccIdx[I]]:
        val term = Mu[NatForm, SuccIdx[I]](
          Sigma[[b <: Boolean] =>> NatFamily[[X <: NatIdx] =>> Mu[NatForm, X], I][b], false](false, n.term)
            .asInstanceOf[Sigma[[b <: Boolean] =>> NatFamily[[X <: NatIdx] =>> Mu[NatForm, X], I][b]]]
        )
      end new
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
        val sigma = m.unfix
        sigma.tag match
          case _: true =>
            vZero.asInstanceOf[P[K]]
          case _: false =>
            val prevTerm = sigma.value.asInstanceOf[Mu[NatForm, NatIdx]]
            val prevP = loop(prevTerm)
            vSucc(prevTerm, prevP).asInstanceOf[P[K]]
        end match
      end loop
      loop(n.term)

  // ============================================================================
  // 5. Тестирование с наглядным выводом в консоль
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

//    inline def myInductor[I <: NatIdx](n: Nat[I]): TupleFamily[I] =
//      myInductorBase[I](n)

    val n0 = Nat.zero
    val n1 = Nat.succ(n0)
    val n2 = Nat.succ(n1)

    val r0: EmptyTuple = myInductorBase(n0)
    val r1: Int *: EmptyTuple = myInductorBase(n1)
    val r2: Int *: Int *: EmptyTuple = myInductorBase(n2)

    // Блок логики инициализации объекта test (вызовется автоматически при обращении)
    println("==================================================")
    println("ЗАПУСК ЗАВИСИМОГО ИНДУКТОРА (СИГМА-ТИП + FIX)")
    println("==================================================")
    println(s"Аргумент n0 (Zero)             -> Результат r0: $r0")
    println(s"Аргумент n1 (Succ(Zero))       -> Результат r1: $r1")
    println(s"Аргумент n2 (Succ(Succ(Zero))) -> Результат r2: $r2")
    println("==================================================")
  end test

end natSigma
