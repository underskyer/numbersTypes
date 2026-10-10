package numberTypes

object indNatural:

  // Базовые кирпичики
  object Zero
  type Zero = Zero.type
  case class Succ[Prev](prev: Prev)
  
  type Bool = Boolean & Singleton

  type NatFamily[B <: Bool] = [Prev] =>> B match
    case false  => Zero
    case true => Succ[Prev]
//    case Bool => String

  type NatFunctor = [Prev] =>> Sigma[? <: Bool, Prev]

  case class Fix[F[_]](unfix: F[Fix[F]])

  class Sigma[B <: Bool, Prev](val value: NatFamily[B][Prev], val tag: B)

  object Sigma:
    // 2. Основной конструктор: принимает только value, а tag подставляет автоматически через implicit-контекст
    def apply[B <: Bool : ValueOf as b, Prev](value: NatFamily[B][Prev]): Sigma[B, Prev] =
      new Sigma(value, b.value)

  type Nat = Fix[NatFunctor]

  val zero: Nat =
    val sigma = Sigma[false, Nat](Zero)
    Fix[NatFunctor](sigma)

  def succ(prev: Nat): Nat =
    val sigma = Sigma[true, Nat](Succ(prev))
    Fix[NatFunctor](sigma)

  // 3. ПРАВИЛО УНИЧТОЖЕНИЯ (Индуктор)
  def ind[C[_ <: Nat]](
    zeroCase: C[zero.type],
    succCase: (p: Nat) => C[p.type] => C[Nat]
  )(n: Nat): C[n.type] = {

    // 4. ПРАВИЛО ВЫЧИСЛЕНИЯ
    // Распаковываем Fix, чтобы получить Sigma
    val sigma = n.unfix

    sigma.tag match {
      case _: false =>
        zeroCase.asInstanceOf[C[n.type]]

      case _: true =>
        // Если флаг false, NatFamily[false][Nat] гарантирует структуру Succ[Nat]
        val succStruct = sigma.value.asInstanceOf[Succ[Nat]]
        val prevNat = succStruct.prev

        val innerRes = ind[C](zeroCase, succCase)(prevNat)
        succCase(prevNat)(innerRes).asInstanceOf[C[n.type]]
    }
  }

  def rec[T](
    zeroCase: T,
    succCase: Nat => T => T
  )(n: Nat): T = {
    ind[[_ <: Nat] =>> T](
      zeroCase,
      (p: Nat) => (ih: T) => succCase(p)(ih)
    )(n)
  }

  object test:

    val z: NatFamily[false][Nothing] = Zero
    val one:  NatFamily[true ][Zero]   = Succ(Zero)
    //val str:  NatFamily[Bool][Zero]   = "Succ(Zero)"

    summon[true <:< Bool]
    summon[false <:< Bool]
    //summon[Singleton <:< Bool]

    private type FactState = (Long, Long)

    // 2. Оптимизированный рекурсор факториала со сложностью O(n)
    private val factStateRec: Nat => FactState = rec[FactState](
      zeroCase = (0L, 1L), // Для нуля: число = 0L, 0! = 1L
      succCase = _ => {
        case (currentLong, currentFact) =>
          val nextLong = currentLong + 1L
          val nextFact = currentFact * nextLong
          (nextLong, nextFact)
      }
    )

    // 3. Финальная функция вычисления факториала
    val factorial: Nat => Long = n => factStateRec(n)._2

    val five: Nat = succ(succ(succ(succ(succ(zero)))))
    println(s"индуктивный факториал: ${factorial(five)}")
