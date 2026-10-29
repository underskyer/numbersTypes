package numberTypes

import numberTypes.piTypes.ℿ

object wellFoundedNew:

  type Subtrees[I, B[_ <: I]] = (i: I) => B[i.type] => 𝕎[I, B] // Brn[I, B, 𝕎[I, B]]

  enum 𝕎[I, B[_ <: I]]:
    case sup[J, Brn[_ <: J], j <: J, +W <: 𝕎[J, Brn]](
      index: j,
      subtrees: Subtrees[J, Brn]
    ) extends 𝕎[J, Brn]

  object 𝕎:

    def ind[I, B[_ <: I], R[_ <: 𝕎[I, B]]](
      alg:
        (w: 𝕎[I, B]) =>  // (i, subtrees(i))
        ℿ[𝕎[I, B], R] => // компромисс, чуть более широкий тип, чем (b: B[w.index]) => R[w.subtrees(b)]
        R[w.type]
    ): ℿ[𝕎[I, B], R] = alg(_)(ind(alg))

//    def indT[I, B[_ <: I], R[_ <: 𝕎[I, B]]](
//      alg: [i <: I] =>
//        sup[I, B, i, 𝕎[I, B]] => // (i, subtrees(i))
//        (B[i] => R[sup[I, B, i, 𝕎[I, B]]]) =>
//        R[sup[I, B, i, 𝕎[I, B]]]
//    ): [W <: 𝕎[I, B]] => W => R[W] =
//      [W <: 𝕎[I, B]] => w => w match
//        case sup(index, subtrees) =>
//          val st = subtrees.asInstanceOf[B[index.type] => 𝕎[I, B]]
//          alg[index.type](sup(index, st))(b =>
//            indT[I, B, R](alg)(st(b).asInstanceOf[sup[I, B, index.type, 𝕎[I, B]]])
//          ).asInstanceOf[R[W]]


  end 𝕎

