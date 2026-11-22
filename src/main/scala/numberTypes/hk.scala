package numberTypes

object hk:

  type HK[A] = A match
    case (a => _) =>
      a match
        case (b => _) => [F[_[_]]] =>> F
        case _ => List
    case Any => Unit
  
  type Functor[F[_]] = [A, B] => (A => B) =>F[A] => F[A]

  summon[HK[(Int => Int) => Int][Functor][List] =:= Functor[List]]
  summon[HK[Int => Int][Int] =:= List[Int]]
  summon[HK[Int] =:= Unit]



