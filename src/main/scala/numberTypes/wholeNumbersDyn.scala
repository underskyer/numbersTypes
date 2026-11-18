package numberTypes

object wholeNumbersDyn:

  // Fix[Pointed[F, A]]
  enum Free[F[+_], +A]:
    case Pure(a: A)
    case Suspend(unfix: F[Free[F, A]])

  type Inject[F[_]] = [G[_]] =>> G ~> F

  object Free:
    def apply[F[+_], A] = [E: ToFree[F, A] as tf] => (e: E) => tf(e)

    type ToFree[F[+_], A] = [X] =>> X => Free[F, A]

    given atom[A, F[+_]]: ToFree[F, A][A] = Free.Pure[F, A]

    given tree: [F[+_], A, G[+_]: {Functor as G, Inject[F] as toF}, X: ToFree[F, A] as toFree] => ToFree[F, A][G[X]] =
      G(toFree) andThen toF[Free[F, A]] andThen Free.Suspend[F, A]

    def fold[F[+_]: Functor as F, A](alg: Algebra[F][A]): Algebra[Free[F, *]][A] =
      case Pure(a) => a
      case Suspend(fa) => alg(F(fold(alg))(fa))

  end Free

  extension [F[+_] : Functor as F, A](fa: Free[F, A])
    inline def fold(alg: Algebra[F][A]): A = Free.fold(alg)(fa)


  case class Add[+A](a: A, b: A)
  case class Mul[+A](a: A, b: A)

  given injectUnion: [F[_], G[x] <: F[x]] => Inject[F][G] = [A] => ga => ga
  given addFunctor: Functor[Add] = [A, B] => f => { case Add(a, b) => Add(f(a), f(b)) }
  given mulFunctor: Functor[Mul] = [A, B] => f => { case Mul(a, b) => Mul(f(a), f(b)) }
//  given compFunctor: [F[+_]: Functor as F, G[+_]: Functor as G] => Functor[F ++ G] = [A, B] => f =>
//    //(fga: (F ++ G)[A]) => fga match
//      case fa: F[A] => F.map(f)(fa): (F ++ G)[B]
//      case ga: G[A] => G.map(f)(ga): (F ++ G)[B]


  object test:

    def expr[A](x: A, y: A, z: A, ы: A) = Mul(Add(x, y), Add(z, ы))

    val ll: Free[Add ++ Mul, Int] = Free[Add ++ Mul, Int](expr(1, 2, 3, 4))

    given addMullFunctor: Functor[Add ++ Mul] = [A, B] => f =>
      case fa: Add[A] => addFunctor(f)(fa)
      case ga: Mul[A] => mulFunctor(f)(ga)

    val res = ll.fold:
      case Add(a, b) => a + b
      case Mul(a, b) => a * b

    println("=============== wholeNumbersDyn ================")
    println(res)
