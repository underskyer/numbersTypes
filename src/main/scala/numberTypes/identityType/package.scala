package numberTypes.identityType

sealed trait Id[A, X <: A, Y <: A]:
  def subst[P[_ <: A]](px: P[X]): P[Y]

final case class Refl[A, X <: A]() extends Id[A, X, X]:
  def subst[P[_ <: A]](px: P[X]): P[X] = px


