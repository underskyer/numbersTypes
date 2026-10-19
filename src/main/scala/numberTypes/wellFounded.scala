package numberTypes

import numberTypes.sigmaTypes.Σɢᴀᴅᴛ

object wellFounded:

  type Branches[Index, F[_ <: Index], +Y] = [I <: Index] =>>
    (i: I) => F[i.type] => Y

  type PolynomialFunctor[Index, F[_ <: Index]] =
    [Y] =>> Σɢᴀᴅᴛ[Index, Branches[Index, F, Y]]

  type 𝕎[Index, F[_ <: Index]] = μᵢ[PolynomialFunctor[Index, F]]

  // 𝕄 
  object 𝕎:


    def sup[Index, F[_ <: Index], Y <: 𝕎[Index, F], I <: Index](
      i: I,
      branches: Branches[Index, F, Y][I]
    ): μᵢ.In[PolynomialFunctor[Index, F], Σɢᴀᴅᴛ.In[Index, Branches[Index, F, Y], I]] =
      μᵢ.In[PolynomialFunctor[Index, F], Σɢᴀᴅᴛ.In[Index, Branches[Index, F, Y], I]](
        Σɢᴀᴅᴛ.In[Index, Branches[Index, F, Y], I](i, branches)
      )

    def ind[Index, F[_ <: Index], P[_ <: 𝕎[Index, F]]](
      step: [I <: Index] => (i: I) =>
        (branches: Branches[Index, F, 𝕎[Index, F]][I]) =>
        (ih: (x: 𝕎[Index, F]) => P[x.type]) =>
        P[𝕎[Index, F]]
    ): (w: 𝕎[Index, F]) => P[w.type] = w => w match
      case μᵢ.In(Σɢᴀᴅᴛ.In(index, branches)) =>
        step[index.type](index)(branches)(ind[Index, F, P](step))
          .asInstanceOf[P[w.type]]
  end 𝕎

