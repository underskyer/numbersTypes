package numberTypes

infix type ×[A, B] = (A, B)
infix type +[A, B] = A Either B

infix type ~>[F[_], G[_]] = [A] => F[A] => G[A]
type Algebra[F[_]] = [A] =>> F[A] => A
type Id[A] = A
type Fix[F[_]] = Algebra[F] ~> Id

infix type ~[A, B] = (
  to:   A => B,
  from: B => A
)

object Iso extends LowPriority:
  given convFromIso1: [A, B] =>(iso: A ~ B) => Conversion[A, B] = new:
    def apply(a: A) = iso.to(a)

trait LowPriority:
  given convFromIso2: [A, B] =>(iso: A ~ B) => Conversion[B, A] = new:
    def apply(b: B) = iso.from(b)

sealed trait DepType[Tag, A]:
  val a: A
  type B

type Dep[Tag] = [A] =>> DepType[Tag, A]#B

val a = new DepType[Nothing, Int]:
  val a = 42
  type B = String

val b: a.B = "sas"



