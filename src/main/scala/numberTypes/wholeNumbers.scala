package numberTypes

object wholeNumbers:

  enum Nat:
    case S[+P <: Nat](prev: P)
    case Z

  transparent inline def s[P <: Nat](p: P): Nat.S[P] = Nat.S(p)
  transparent inline def z: Z = Nat.Z

  export Nat.S
  type Z = Nat.Z.type

  case class Val[+A, +B](a: A)
  case class Add[+A, +B](a: A, b: B)
  case class Mul[+A, +B](a: A, b: B)
  case class Sub[+A, +B](a: A, b: B)
  case class Div[+A, +B](a: A, b: B)

  transparent inline def add[A, B](a: A, b: B): Add[A, B] = Add(a, b)
  transparent inline def mul[A, B](a: A, b: B): Mul[A, B] = Mul(a, b)

  type AddNatNorm[A <: Nat, B <: Nat] <: Nat = B match
    case Z => A
    case S[b] => AddNatNorm[S[A], b]

  type MulNatNorm[A <: Nat, B <: Nat] <: Nat = (A, B) match
    case (_, Z) => Z
    case (Z, _) => Z
    case (_, S[b]) => AddNatNorm[MulNatNorm[A, b], A]

  // Основной нормализатор: сначала вычисляет аргументы, затем применяет операцию
  type NatNf[Expr] <: Nat = Expr match
    case Z => Z
    case S[n] => S[NatNf[n]]
    case Add[a, b] => AddNatNorm[NatNf[a], NatNf[b]]
    case Mul[a, b] => MulNatNorm[NatNf[a], NatNf[b]]

  type NNat = Nat | Add[Nat, Nat] | Mul[Nat, Nat]

  type SubNf[Expr] = Expr match
    case Sub[S[a], S[b]] => SubNf[Sub[a, b]]
    case Sub[Z, b] => Sub[Z, b]
    case Sub[a, Z] => Sub[a, Z]
    case _ => Expr

  type Finit[N] = N match
    case S[p] => p | Finit[p]
    case _ => Nothing


  object test:

    summon[Finit[Int] =:= Nothing]
    summon[Finit[Z] =:= Nothing]
    summon[Finit[S[S[Z]]] =:= (Z | S[Z])]

    summon[SubNf[Sub[Z, Z]] =:= Sub[Z, Z]]
    summon[SubNf[Sub[Z, S[Z]]] =:= Sub[Z, S[Z]]]
    summon[SubNf[Sub[S[Z], Z]] =:= Sub[S[Z], Z]]
    summon[SubNf[Sub[S[Z], S[Z]]] =:= Sub[Z, Z]]
    summon[SubNf[Sub[S[Z], S[S[S[Z]]]]] =:= Sub[Z, S[S[Z]]]]
    summon[SubNf[Sub[S[S[Z]], S[S[S[Z]]]]] =:= Sub[Z, S[Z]]]

    val a: Mul[Nat.S[Z], Nat.S[Z]] = mul(s(z), s(z))

    summon[NatNf[a.type] =:= S[Z]]

    val aa: Mul[Add[Nat.S[Nat.S[Z]], Nat.S[Nat.S[Z]]], Add[Nat.S[Z], Nat.S[Z]]] = mul(add(s(s(z)), s(s(z))), add(s(z), s(z)))

    val b = mul(s(z), s(z))
    summon[NatNf[b.type] <:< Nat]

