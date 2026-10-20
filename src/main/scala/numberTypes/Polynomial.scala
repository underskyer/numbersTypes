package numberTypes

import numberTypes.sigmaTypes.{InΣ, ⅀}

type Branches[Index, F[_ <: Index], +Y] = [I <: Index] =>>
  (i: I) => F[i.type] => Y

type Polynomial[Index, F[_ <: Index]] =
  [Y] =>> ⅀[Index, Branches[Index, F, Y]]

given polynomialFunctor: [Index, F[_ <: Index]] => Functor[Polynomial[Index, F]] =
  [A, B] => (f: A => B) => (pa: Polynomial[Index, F][A]) => pa match
    case InΣ(i, branches) =>
      val bs = branches.asInstanceOf[Branches[Index, F, A][i.type]]
      InΣ(i, (j: i.type) => (x: F[j.type]) => f(bs(j)(x)))
