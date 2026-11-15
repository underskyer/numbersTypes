package numberTypes

object wholeNumbersDyn:

  enum Nat:
    case S[+P <: Nat](prev: P)
    case Z

  def toInt(n: Nat): Int = n match
    case Nat.Z    => 0
    case Nat.S(p) => 1 + toInt(p)
  def nat(n: Int): Nat = n match
    case 0 => Nat.Z
    case x if x > 0 => Nat.S(nat(x - 1))

  transparent inline def s[P <: Nat](p: P): Nat.S[P] = Nat.S(p)
  transparent inline def z: Z = Nat.Z

  export Nat.S
  type Z = Nat.Z.type

  case class Add[+A](a: A, b: A)
  case class Mul[+A](a: A, b: A)
  case class Sub[+A](a: A, b: A)
  case class Div[+A](a: A, b: A)

  transparent inline def add[A](a: A, b: A): Add[A] = Add(a, b)
  transparent inline def mul[A](a: A, b: A): Mul[A] = Mul(a, b)



  object test:

    ???
