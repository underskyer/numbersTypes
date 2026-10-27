package numberTypes

import numberTypes.piTypes.ℿ

object wellFoundedNew:

  type Subtrees[I, B[_ <: I]] = [i <: I] =>> B[i] => 𝕎[I, B] // Brn[I, B, 𝕎[I, B]]

  enum 𝕎[I, B[_ <: I]]:
    case sup[J, BB[_ <: J], j <: J, +W <: 𝕎[J, BB]](
      index: j,
      subtrees: Subtrees[J, BB][j]
    ) extends 𝕎[J, BB]

  object 𝕎:

    def ind[I, B[_ <: I], R[_ <: 𝕎[I, B]]](
      alg: [i <: I] =>
        (w: sup[I, B, i, 𝕎[I, B]]) =>
        ℿ[𝕎[I, B], R] => // компромисс, чуть более широкий, чем (b: B[w.index]) => R[w.subtrees(b)]
        R[w.type]
    ): ℿ[𝕎[I, B], R] = w => w match
      case vv @ sup(index, subtrees) =>
        alg(vv)(ind(alg))
          .asInstanceOf[R[w.type]]

    def indT[I, B[_ <: I], R[_ <: 𝕎[I, B]]](
      alg: [i <: I] =>
        sup[I, B, i, 𝕎[I, B]] => // (i, subtrees(i))
        (B[i] => R[sup[I, B, i, 𝕎[I, B]]]) =>
        R[sup[I, B, i, 𝕎[I, B]]]
    ): [W <: 𝕎[I, B]] => W => R[W] =
      [W <: 𝕎[I, B]] => w => w match
        case sup(index, subtrees) =>
          val st = subtrees.asInstanceOf[B[index.type] => 𝕎[I, B]]
          alg[index.type](sup(index, st))(b =>
            indT[I, B, R](alg)(st(b).asInstanceOf[sup[I, B, index.type, 𝕎[I, B]]])
          ).asInstanceOf[R[W]]


  end 𝕎

