package numberTypes

object chirchNatural:

  object Zero
  type Zero = Zero.type // Zero ≅ Unit ≅ 1
  case class Succ[Prev](prev: Prev)

  type NatFunctor[A] = Zero + Succ[A]

  type Nat = Fix[NatFunctor]

  val zero: Nat            = [A] => alg => alg(Left(Zero))
  def succ(prev: Nat): Nat = [A] => alg => alg(Right(Succ(prev(alg))))


  val rec: [C] => (C, Nat => C => C) => Nat => C =
    [C] => (z, next) => n =>
      cata[NatFunctor][C](_.fold[C](
        _ => z,
        s => next(n)(s.prev)
      ))(n)

  object test:
    type FactState = (index: Int, result: Long)

    val factorial = rec[FactState](
      (index = 0, result = 1L),
      _ => (currentLong, currentFact) =>
        val nextLong = currentLong + 1
        (nextLong, currentFact * nextLong)
    ).andThen(_.result)

    summon[Nat =:= ([A] => (Zero Either Succ[A] => A) => A)]

    val five: Nat = succ(succ(succ(succ(succ(zero)))))

    println("факториал Чёрча: " + factorial(five))
