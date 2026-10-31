package numberTypes

import numberTypes.piTypes.ℿ

object wellFoundedNew:

  type Subtrees[I, B[_ <: I], +W <: 𝕎[I, B]] = (i: I) => B[i.type] => W // Brn[I, B, 𝕎[I, B]]

  enum 𝕎[I, B[_ <: I]]:
    case sup[J, Brn[_ <: J], j <: J, +Subtree <: 𝕎[J, Brn]](
      index: j,
      subtrees: Subtrees[J, Brn, Subtree]
    ) extends 𝕎[J, Brn]

  object 𝕎:

    extension [I, B[_ <: I], i <: I, W <: 𝕎[I, B]](w: sup[I, B, i, W])
      def branches: B[w.index.type] => W = w.subtrees(w.index)

    def ind[I, B[_ <: I], R[_ <: 𝕎[I, B]]](
      alg:
        (w: 𝕎[I, B]) =>  // (i, st: Subtrees(i))
        ℿ[𝕎[I, B], R] => // компромисс, чуть более широкий тип, чем (b: B[w.index]) => R[w.subtrees(b)]
        R[w.type]
    ): ℿ[𝕎[I, B], R] = alg(_)(ind(alg))

    def rec[I, B[_ <: I], R] = ind[I, B, Const[R]]

  end 𝕎

