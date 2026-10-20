package numberTypes

import numberTypes.sigmaTypes.{⅀, InΣ}

object wellFounded:


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
      w.openFold(v => ih => v match
        case InΣ(index, branches) =>
          step(
            index)(
            branches.asInstanceOf[Branches[Index, F, 𝕎[Index, F]][index.type]])(
            x => ih(x).asInstanceOf[P[x.type]]
          )
      ).asInstanceOf[P[w.type]]

  end 𝕎

