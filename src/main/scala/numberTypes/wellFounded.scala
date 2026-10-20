package numberTypes

import numberTypes.sigmaTypes.Σɢᴀᴅᴛ

object wellFounded:

  type Branches[Index, F[_ <: Index], +Y] = [I <: Index] =>>
    (i: I) => F[i.type] => Y

  type Polynomial[Index, F[_ <: Index]] =
    [Y] =>> Σɢᴀᴅᴛ[Index, Branches[Index, F, Y]]

  type 𝕎[Index, F[_ <: Index]] = μᵢ[Polynomial[Index, F]]

  object 𝕎:

    def sup[Index, F[_ <: Index], Y <: 𝕎[Index, F], I <: Index](
      i: I,
      branches: Branches[Index, F, Y][I]
    ): μᵢ.In[Polynomial[Index, F], Σɢᴀᴅᴛ.In[Index, Branches[Index, F, Y], I]] =
      μᵢ.In(Σɢᴀᴅᴛ.In[Index, Branches[Index, F, Y], I](i, branches))

    def ind[Index, F[_ <: Index], P[_ <: 𝕎[Index, F]]](
      step: [I <: Index] => (i: I) =>
        (branches: Branches[Index, F, 𝕎[Index, F]][I]) =>
        (ih: (x: 𝕎[Index, F]) => P[x.type]) => P[𝕎[Index, F]] // Induction Hypothesis - гипотеза индукции
    )(w: 𝕎[Index, F]): P[w.type] =
      w.fold(v => ih => v match
        case Σɢᴀᴅᴛ.In(index, branches) =>
          step[index.type](index)(branches)(x => ih(x).asInstanceOf[P[x.type]])
      ).asInstanceOf[P[w.type]]

  end 𝕎

