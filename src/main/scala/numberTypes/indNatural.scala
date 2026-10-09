package numberTypes

object indNatural:

  // Базовые кирпичики
  object Zero
  type Zero = Zero.type
  case class Succ[Prev](prev: Prev)

  // Вся структура NatFamily должна принимать Boolean индекс И тип для рекурсии
  type NatFamily[B <: Boolean & Singleton] = [Prev] =>> B match {
    case true => Zero
    case false => Succ[Prev]
  }

  // Правильное определение Fix, где функтором выступает лямбда,
  // которая прячет булев флаг под экзистенциал, сохраняя рекурсию по Prev.
  // Это позволяет нам связать рекурсию до раскрытия Sigma!
  type NatFunctor = [Prev] =>> Sigma[? <: Boolean & Singleton, Prev]

  case class Fix[F[_]](unfix: F[Fix[F]])

  trait Sigma[B <: Boolean & Singleton, Prev] {
    val tag: B
    val value: NatFamily[B][Prev]
  }

  object Sigma {
    // Удобный конструктор для создания зависимой пары
    def apply[B <: Boolean & Singleton, Prev](t: B, v: NatFamily[B][Prev]): Sigma[B, Prev] =
      new Sigma[B, Prev] {
        val tag: B = t
        val value: NatFamily[B][Prev] = v
      }
  }

  // 1. ПРАВИЛО ФОРМУЛИРОВАНИЯ (Formation)
  type Nat = Fix[NatFunctor]

  // 2. ПРАВИЛА ВВЕДЕНИЯ (Introduction)
  // Теперь типы сходятся идеально, так как рекурсия идет строго через Nat (Fix)

  val zero: Nat =
    val sigma = Sigma[true, Nat](true, Zero: Zero)
    Fix[NatFunctor](sigma)

  def succ(prev: Nat): Nat =
    val sigma = Sigma[false, Nat](false, Succ(prev))
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
      case _: true =>
        zeroCase.asInstanceOf[C[n.type]]

      case _: false =>
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
