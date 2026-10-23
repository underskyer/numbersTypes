package numberTypes

import numberTypes.piTypes.ℿ
import numberTypes.sigmaTypes.{InΣ, ⅀}

object wellFounded:


  type 𝕎[I, F[_ <: I]] = μᵢ[ℙ[I, F]]

  object 𝕎:

    def sup[I, F[_ <: I], Y <: 𝕎[I, F]](
      i: I,
      branches: Brn[I, F, Y][i.type]
    ): μᵢ.In[ℙ[I, F], InΣ[I, Brn[I, F, Y], i.type]] =
      μᵢ.In[ℙ[I, F], InΣ[I, Brn[I, F, Y], i.type]](InΣ(i, branches))

    def ind[I, F[_ <: I], R[_ <: 𝕎[I, F]]](
      step:
        (i: I) => Brn[I, F, 𝕎[I, F]][i.type] => // payload
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


    def ind1[I, F[_ <: I], R[_ <: 𝕎[I, F]]](
      step:
        (node: 𝕎[I, F]) =>
        (payload: ℙ[I, F][𝕎[I, F]]) =>
        (ih: ℿ[𝕎[I, F], R]) =>
        R[node.type]
    ): (w: 𝕎[I, F]) => R[w.type] =
      def go(w: 𝕎[I, F]): R[w.type] =
        w match
          case μᵢ.In(payload) =>
            step(w)(payload)(go)
      go
  end 𝕎

