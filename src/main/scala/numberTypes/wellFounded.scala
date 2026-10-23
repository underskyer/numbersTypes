package numberTypes

import numberTypes.piTypes.ℿ
import numberTypes.sigmaTypes.{InΣ, ⅀}

object wellFounded:


  type 𝕎[Index, F[_ <: Index]] = μᵢ[ℙ[Index, F]]

  object 𝕎:

    def sup[I, F[_ <: I], Y <: 𝕎[I, F]](
      i: I,
      branches: Brn[I, F, Y][i.type]
    ): μᵢ.In[ℙ[I, F], InΣ[I, Brn[I, F, Y], i.type]] =
      μᵢ.In[ℙ[I, F], InΣ[I, Brn[I, F, Y], i.type]](InΣ(i, branches))

    def ind[I, F[_ <: I], R[_ <: 𝕎[I, F]]](
      step: (i: I) =>
        Brn[I, F, 𝕎[I, F]][i.type] =>
        ℿ[𝕎[I, F], R] =>
        R[𝕎[I, F]]
    ): ℿ[𝕎[I, F], R] =
      μᵢ.openCata[ℙ[I, F], R[𝕎[I, F]]] {
        case InΣ(index, branches) => ih =>
          step(index)(
            branches.asInstanceOf[Brn[I, F, 𝕎[I, F]][index.type]])(
            w => ih(w).asInstanceOf[R[w.type]]
          )
      }.asInstanceOf[ℿ[𝕎[I, F], R]]

  end 𝕎

