package numberTypes

import numberTypes.sigmaTypes.{⅀, InΣ}

object wellFounded:

  type Branches[Index, F[_ <: Index], +Y] = [I <: Index] =>>
    (i: I) => F[i.type] => Y

  type Polynomial[Index, F[_ <: Index]] =
    [Y] =>> ⅀[Index, Branches[Index, F, Y]]

  given polynomialFunctor: [Index, F[_ <: Index]] => Functor[Polynomial[Index, F]] =
    [A, B] => (f: A => B) => (pa: Polynomial[Index, F][A]) => pa match
      case InΣ(i, branches) =>
        val bs = branches.asInstanceOf[Branches[Index, F, A][i.type]]
        InΣ(i, (j: i.type) => (x: F[j.type]) => f(bs(j)(x)))

//  enum μᵢ[+F[+_]]:
//    case In[+G[+_], +V <: G[μᵢ[G]]](unfix: V) extends μᵢ[G]
//
//  object μᵢ:
//    def cata[F[+_], A](step: F[μᵢ[F]] => (μᵢ[F] => A) => A): (w: μᵢ[F]) => A =
//      def go: μᵢ[F] => A = { case In(v) => step(v)(go) }
//      go
//
//    extension [F[+_]] (fix: μᵢ[F])
//      inline def fold[A](step: F[μᵢ[F]] => (μᵢ[F] => A) => A): A =
//        cata[F, A](step)(fix)

  type 𝕎[Index, F[_ <: Index]] = μᵢ[Polynomial[Index, F]]

  object 𝕎:

    def sup[Index, F[_ <: Index], Y <: 𝕎[Index, F], I <: Index](
      i: I,
      branches: Branches[Index, F, Y][I]
    ): μᵢ.In[Polynomial[Index, F], InΣ[Index, Branches[Index, F, Y], I]] =
      μᵢ.In[Polynomial[Index, F], InΣ[Index, Branches[Index, F, Y], I]](
        InΣ[Index, Branches[Index, F, Y], I](i, branches)
      )

    def ind[Index, F[_ <: Index], P[_ <: 𝕎[Index, F]]](
      step: [I <: Index] => (i: I) =>
        (branches: Branches[Index, F, 𝕎[Index, F]][i.type]) =>
        (ih: (x: 𝕎[Index, F]) => P[x.type]) => P[𝕎[Index, F]] // Induction Hypothesis - гипотеза индукции
    )(w: 𝕎[Index, F]): P[w.type] =
      w.fold(v => ih => v match
        case InΣ(index, branches) =>
          step(
            index)(
            branches.asInstanceOf[Branches[Index, F, 𝕎[Index, F]][index.type]])(
            x => ih(x).asInstanceOf[P[x.type]]
          )
      ).asInstanceOf[P[w.type]]

  end 𝕎

