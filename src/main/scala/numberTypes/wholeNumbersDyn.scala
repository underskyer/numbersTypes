package numberTypes

import numberTypes.wholeNumbersDyn.ToFree.tree

object wholeNumbersDyn:

  // Fix[Pointed[F, A]]
  enum Free[F[+_], +A]:
    case Pure(a: A)
    case Suspend(unfix: F[Free[F, A]])

  trait Morph[F[+_], A, T]:
    def apply(t: T): Free[F, A]

  type ToFree[F[+_], A] = [T] =>> Morph[F, A, T]
  //type ToFree[F[+_], A] = [X] =>> X => Free[F, A]

  type Inject[F[_]] = [G[_]] =>> G ~> F

  object ToFree:
    def apply[F[+_], A] = [E: ToFree[F, A] as tf] => (e: E) => tf(e)
    
    given atom[A, F[+_]]: ToFree[F, A][A] = Free.Pure[F, A](_)

    given tree: [G[+_]: {Functor as G, Inject[F] as toF}, A, X: ToFree[F, A] as toFree, F[+_]] => ToFree[F, A][G[X]] =
      (G(toFree(_)) andThen  toF[Free[F, A]] andThen Free.Suspend[F, A])(_)
  end ToFree

  infix type ++[F[_], G[_]] = [X] =>> F[X] | G[X]

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

  given injectUnion: [F[_], G[x] <: F[x]] => Inject[F][G] = [A] => ga => ga
  given addFunctor: Functor[Add] = [A, B] => f => { case Add(a, b) => Add(f(a), f(b)) }
  given mulFunctor: Functor[Mul] = [A, B] => f => { case Mul(a, b) => Mul(f(a), f(b)) }

  type Algebra[F[_]] = [A] =>> F[A] => A
  type NatAlgebra = Algebra[Free[Add ++ Mul, *]][Nat]

  object test:

    def expr[A](x: A, y: A, z: A) = Mul(Add(x, y), Add(y, z))

    ToFree[Add ++ Mul, Int](expr(1, 2, 3))
