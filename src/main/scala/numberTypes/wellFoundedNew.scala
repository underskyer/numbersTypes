package numberTypes

import numberTypes.piTypes.ℿ

object wellFoundedNew:


  //final case class 𝕎[I, B[_ <: I]](index: I, subtrees: B[index.type] => 𝕎[I, B])

  type Subtrees[I, B[_ <: I]] = [J <: I, W <: 𝕎[I, B]] =>> B[J] => W

  enum 𝕎[I, B[_ <: I]]:
    case sup[J, BB[_ <: J], j <: J, W <: 𝕎[J, BB]](index: j, subtrees: Subtrees[J, BB][j, W]) extends 𝕎[J, BB]

  object 𝕎:

    def ind[I, B[_ <: I], R[_ <: 𝕎[I, B]]](
      step: [J <: I] => (w: 𝕎[I, B]) =>
        (i: J) =>
        (s: Subtrees[I, B][J, 𝕎[I, B]]) =>
        (ih: ℿ[𝕎[I, B], R]) =>
        R[w.type]
    ): ℿ[𝕎[I, B], R] = w => w match
      case sup(index, subtrees) => step(w)(index)(subtrees)(ind(step))

    def indT[I, B[_ <: I], R[_ <: 𝕎[I, B]]](
      step: [i <: I] =>
        i =>
        Subtrees[I, B][i, 𝕎[I, B]] =>
        ℿ[sup[I, B, i, 𝕎[I, B]], R] =>
        R[sup[I, B, i, 𝕎[I, B]]]
    ): ℿ[𝕎[I, B], R] =
      w => w match
        case sup(index, subtrees) => step(index)(subtrees)(indT(step)).asInstanceOf[R[w.type]]


  end 𝕎

