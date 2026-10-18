package numberTypes

import numberTypes.sigmaTypes.Σɢᴀᴅᴛ

object wellFounded:

  type Branches[Index, F[_ <: Index], +Y] = [I <: Index] =>>
    (i: I) => F[i.type] => Y

  type PolynomialFunctor[Index, F[_ <: Index]] =
    [Y] =>> Σɢᴀᴅᴛ[Index, Branches[Index, F, Y]]

  type W[Index, F[_ <: Index]] = μᵢ[PolynomialFunctor[Index, F]]

  object W:

//    def sup1[Index, F[_ <: Index], I <: Index]:
//      (I, Branches[Index, F, W[Index, F]][I]) => W[Index, F]
//    = Function.untupled:
//      Σɢᴀᴅᴛ.In[Index, Branches[Index, F, W[Index, F]], I].apply.tupled andThen
//      μᵢ.In[PolynomialFunctor[Index, F], PolynomialFunctor[Index, F][W[Index, F]]].apply


    def sup[Index, F[_ <: Index], Y <: W[Index, F], I <: Index](
      i: I,
      branches: Branches[Index, F, Y][I]
    ): μᵢ.In[PolynomialFunctor[Index, F], Σɢᴀᴅᴛ.In[Index, Branches[Index, F, Y], I]] =
      μᵢ.In[PolynomialFunctor[Index, F], Σɢᴀᴅᴛ.In[Index, Branches[Index, F, Y], I]](
        Σɢᴀᴅᴛ.In[Index, Branches[Index, F, Y], I](i, branches)
      )

    def ind[Index, F[_ <: Index], P[_ <: W[Index, F]]](
      step: [I <: Index] => (i: I) =>
        (branches: Branches[Index, F, W[Index, F]][I]) =>
        (ih: (x: W[Index, F]) => P[x.type]) =>
        P[W[Index, F]]
    ): (w: W[Index, F]) => P[w.type] = w => w match
      case μᵢ.In(Σɢᴀᴅᴛ.In(index, branches)) =>
        step[index.type](index)(branches)(ind[Index, F, P](step))
          .asInstanceOf[P[w.type]]
  end W

