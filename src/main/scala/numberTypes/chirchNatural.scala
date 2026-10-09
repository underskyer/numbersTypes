package numberTypes

object chirchNatural:

  object Zero
  type Zero = Zero.type
  case class Succ[Prev](prev: Prev)

  type NatFunctor[A] = Zero + Succ[A]

  type Nat = Fix[NatFunctor]

  val zero: Nat            = [A] => alg => alg(Left(Zero))
  def succ(prev: Nat): Nat = [A] => (alg: Algebra[NatFunctor][A]) => alg(Right(Succ(prev(alg))))


  val rec: [C] => (C, Nat => C => C) => Nat => C =
    [C] => (z, next) => (n: Nat) =>
      cata[NatFunctor][C](_.fold[C](_ => z, s => next(n)(s.prev)))(n)

  object test:
    type FactState = (index: Int, result: Long)
  
    val factorial = rec[FactState](
      (index = 0, result = 1L),
      _ => (currentLong, currentFact) =>
        val nextLong = currentLong + 1
        (nextLong, currentFact * nextLong)
    ).andThen(_.result)
  
    val five: Nat = succ(succ(succ(succ(succ(zero)))))
  
    println("факториал Чёрча: " + factorial(five))
