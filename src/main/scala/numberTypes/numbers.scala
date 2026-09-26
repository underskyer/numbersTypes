package numberTypes

object numbers:

  object Zero
  type Zero = Zero.type
  case class Succ[A]()

  type Countable[A] = Zero + Succ[A]
  type Nat = Fix[Countable]

  opaque type Sum[A] = A × A
  type SumAlgebra = Algebra[Sum]
//  type PeanoSumRule  = [A, B] => Sum[Succ[A], B] => Sum[A, Succ[B]]
//  type PeanoSumZRule = [A, B] => Sum[Zero, B] => B

  opaque type Mul[A] = A × A
  type MulAlgebra = Algebra[Mul]
//  type PeanoMulRule  = [A, B] => Mul[Succ[A], B] => Sum[B, Mul[A, B]]
//  type PeanoMulZRule = [A, B] => Mul[Zero, B] => Zero

//  type Addable[A] =
//    Fix[[T] =>> A + Sum[T, T]] ×
//      PeanoSumRule

//  type Semiring[A] =
//    Fix[[T] =>> A + Sum[T, T] + Mul[T, T]] ×
//      PeanoSumRule × PeanoSumZRule ×
//      PeanoMulRule × PeanoMulZRule


//  given sumIso: Addable[Nat] ~ Nat = ???
//  given semiringIso: Semiring[Nat] ~ Nat = ???
