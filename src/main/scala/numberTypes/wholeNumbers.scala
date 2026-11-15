package numberTypes

object wholeNumbers:

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
  type NatNF[Expr] <: Nat = Expr match
    case Z => Z
    case S[n] => S[NatNF[n]]
    case Add[a, b] => AddNatNorm[NatNF[a], NatNF[b]]
    case Mul[a, b] => MulNatNorm[NatNF[a], NatNF[b]]

  def addNat(a: Nat, b: Nat): Nat = b match
    case Nat.Z     => a
    case Nat.S(p)  => addNat(Nat.S(a), p)

  def mulNat(a: Nat, b: Nat): Nat = b match
    case Nat.Z     => Nat.Z
    case Nat.S(p)  =>
      a match
        case Nat.Z => Nat.Z
        case _     => addNat(mulNat(a, p), a)

  def natNorm(a: Any): Nat = a match
    case _: Z        => Nat.Z
    case s: S[?]     => Nat.S(natNorm(s.prev))
    case Add(na, nb) => addNat(natNorm(na), natNorm(nb))
    case Mul(na, nb) => mulNat(natNorm(na), natNorm(nb))


  type Ring[A] = A | Add[A, A] | Mul[A, A]
  type NNat = Ring[Nat]
  //type NNat = Nat | Add[NNat, NNat] | Mul[NNat, NNat]

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
    summon[NatNF[a.type] =:= S[Z]]

    val aa =
      mul(add(s(s(z)), s(s(z))), add(s(z), s(z)))

    val b = mul(s(z), s(z))
    summon[NatNF[b.type] <:< Nat]

    def expr1[A, B, C](a: A, b: B, c: C) = mul(add(a, b), add(c, a))

    val e1 = expr1(s(s(z)), s(z), z)


    var res = natNorm(e1)
    println("нормализация целого числа: " + toInt(res))

