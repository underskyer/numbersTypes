package numberTypes

import numberTypes.sigmaTypes.{InΣ, ⅀}

type Brn[I, B[_ <: I], +Y] = [i <: I] =>> B[i] => Y // ℿ[F[i], Const[Y]] - компилятор умирает

type ℙ[I, B[_ <: I]] = [Y] =>> ⅀[I,  Brn[I, B, Y]]

given polynomialFunctor: [I, F[_ <: I]] => Functor[ℙ[I, F]] =
  [A, B] => (f: A => B) => (pa: ℙ[I, F][A]) => pa match
    case InΣ(i, branches) =>
      val bs = branches.asInstanceOf[Brn[I, F, A][i.type]]
      InΣ(i, (x: F[i.type]) => f(bs(x)))
