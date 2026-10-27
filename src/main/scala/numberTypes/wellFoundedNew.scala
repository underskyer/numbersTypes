package numberTypes

import numberTypes.piTypes.ℿ

object wellFoundedNew:


  //final case class 𝕎[I, B[_ <: I]](index: I, subtrees: B[index.type] => 𝕎[I, B])

  type Subtrees[I, B[_ <: I]] = Brn[I, B, 𝕎[I, B]] // [i <: I] =>> B[i] => 𝕎[I, B]

  enum 𝕎[I, B[_ <: I]]:
    case sup[J, BB[_ <: J], j <: J, +W <: 𝕎[J, BB]](
      index: j,
      subtrees: Subtrees[J, BB][j]
    ) extends 𝕎[J, BB]

  object 𝕎:

    def ind[I, B[_ <: I], R[_ <: 𝕎[I, B]]](
      step: [i <: I] => (w: 𝕎[I, B]) =>
        (i: i) => (s: Subtrees[I, B][i]) =>
        (ih: ℿ[𝕎[I, B], R]) =>
        R[w.type]
    ): ℿ[𝕎[I, B], R] = w => w match
      case sup(index, subtrees) =>
        step(w)(index)(subtrees.asInstanceOf[Subtrees[I, B][index.type]])(ind(step))

    def indT[I, B[_ <: I], R[_ <: 𝕎[I, B]]](
      step: [i <: I] =>
        sup[I, B, i, 𝕎[I, B]] => // (i, subtrees(i))
        (B[i] => R[sup[I, B, i, 𝕎[I, B]]]) =>
        R[sup[I, B, i, 𝕎[I, B]]]
    ): [W <: 𝕎[I, B]] => W => R[W] =
      [W <: 𝕎[I, B]] => w => w match
        case sup(index, subtrees) =>
          val st = subtrees.asInstanceOf[B[index.type] => 𝕎[I, B]]
          step[index.type](sup(index, st))(b =>
            indT[I, B, R](step)(st(b).asInstanceOf[sup[I, B, index.type, 𝕎[I, B]]])
          ).asInstanceOf[R[W]]


  end 𝕎

