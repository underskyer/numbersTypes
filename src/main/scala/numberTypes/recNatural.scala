package numberTypes

object recNatural:

  enum NatFunctor[A]: // formation
    case Zero             extends NatFunctor[Nothing] // introduction (1-й конструктор)
    case Succ[P](prev: P) extends NatFunctor[P]       // introduction (2-й конструктор)
    
  case class Fix[F[_]](unfix: F[Fix[F]])
  
  type Nat = Fix[NatFunctor]
  
  import NatFunctor.*

  val zero = Fix[NatFunctor](Zero.asInstanceOf[NatFunctor[Nat]])
  def succ[P <: Nat](prev: P) = Fix[NatFunctor](Succ(prev).asInstanceOf[NatFunctor[Nat]])
  
  val rec: [C] => (C, Nat => C => C) => Nat => C =
    [C] => (default, next) =>
      case Fix(Zero)       => default
      case Fix(Succ(prev)) => next(prev)(rec(default, next)(prev))
      
  object test:

    type FactState = (index: Int, result: Long)
    
    val factorial = rec[FactState](
      (index = 0, result = 1L),
      _ => (currentLong, currentFact) =>
        val nextLong = currentLong + 1
        (nextLong, currentFact * nextLong)
    ).andThen(_.result)
    
    import NatFunctor.*
    
    val five = succ(succ(succ(succ(succ(zero)))))

    println("рекурсивный факториал: " + factorial(five))

