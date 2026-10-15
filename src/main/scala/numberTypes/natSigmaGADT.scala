package numberTypes

object natSigmaGADT:

  // ============================================================================
  // 1. Индексы и Зависимый Сигма-тип через ENUM
  // ============================================================================

  sealed abstract class NatIdx
  final class ZeroIdx extends NatIdx
  final class SuccIdx[I <: NatIdx] extends NatIdx

  // Исходная сигнатура enum из вашего запроса
  enum SigmaEnum[IndexType, G[_ <: IndexType]]:
    case In[I, F[_ <: I], T <: I](fi: F[T], index: T) extends SigmaEnum[I, F]
  end SigmaEnum

  // ============================================================================
  // 2. Индексированная Неподвижная Точка
  // ============================================================================

  case class Mu[F[_[_ <: NatIdx] <: Any, _ <: NatIdx] <: Any, I <: NatIdx](
                                                                            unfix: F[[X <: NatIdx] =>> Mu[F, X], I]
                                                                          )

  // ============================================================================
  // 3. Кодировка Натуральных чисел через SigmaEnum
  // ============================================================================

  type NatFamily[R[_ <: NatIdx], I <: NatIdx] = [b <: Boolean] =>> b match
    case true  => Unit
    case false => R[I]

  type NatForm[R[_ <: NatIdx], O <: NatIdx] = SigmaEnum[Boolean, [b <: Boolean] =>> NatFamily[R, O match
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
          SigmaEnum.In[Boolean, [b <: Boolean] =>> NatFamily[[X <: NatIdx] =>> Mu[NatForm, X], ZeroIdx][b], true]((), true)
            .asInstanceOf[SigmaEnum[Boolean, [b <: Boolean] =>> NatFamily[[X <: NatIdx] =>> Mu[NatForm, X], ZeroIdx][b]]]
        )
      end new

    def succ[I <: NatIdx](n: Nat[I]): Nat[SuccIdx[I]] =
      new Nat[SuccIdx[I]]:
        val term = Mu[NatForm, SuccIdx[I]](
          SigmaEnum.In[Boolean, [b <: Boolean] =>> NatFamily[[X <: NatIdx] =>> Mu[NatForm, X], I][b], false](n.term, false)
            .asInstanceOf[SigmaEnum[Boolean, [b <: Boolean] =>> NatFamily[[X <: NatIdx] =>> Mu[NatForm, X], I][b]]]
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
        sigma match
          // Извлекаем тип T (литерал true/false) с помощью паттерн-матчинга GADT
          case SigmaEnum.In(_, index) =>
            // Так как index имеет тип T, мы можем сматчиться по его рантайм-значению,
            // а компилятор свяжет это с типами true/false
            (index: Any) match
              case true =>
                vZero.asInstanceOf[P[K]]
              case false =>
                // Извлекаем значение fi, которое теперь гарантированно является типом Mu
                val fiValue = sigma.asInstanceOf[SigmaEnum.In[Boolean, [b <: Boolean] =>> NatFamily[[X <: NatIdx] =>> Mu[NatForm, X], NatIdx][b], false]].fi
                val prevTerm = fiValue.asInstanceOf[Mu[NatForm, NatIdx]]
                val prevP = loop(prevTerm)
                vSucc(prevTerm, prevP).asInstanceOf[P[K]]
            end match
        end match
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
    println("ЗАПУСК С ИСПОЛЬЗОВАНИЕМ СИГМА-ТИПА ЧЕРЕЗ GADT ENUM")
    println("==================================================")
    println(s"Аргумент n0 (Zero)             -> Результат r0: $r0")
    println(s"Аргумент n1 (Succ(Zero))       -> Результат r1: $r1")
    println(s"Аргумент n2 (Succ(Succ(Zero))) -> Результат r2: $r2")
    println("==================================================")
  end test

end natSigmaGADT
