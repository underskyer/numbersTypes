package numberTypes

type Bool = Boolean & Singleton

infix type ×[A, B] = (A, B)
infix type +[A, B] = A Either B

infix type ~>[F[_], G[_]] = [A] => F[A] => G[A]
type Algebra[F[_]] = [A] =>> F[A] => A
type Id[A] = A
type Const[A] = [X] =>> A

type Pair[A, B] = [R <: Bool] =>> R match
  case false => A
  case true => B


infix type ≅[A, B] = (
  forward : A => B,
  backward: B => A
)

type μ[F[_]] = Algebra[F] ~> Id
def cata[F[_]]: Algebra[F] ~> (μ[F] => *) = [A] => alg => _(alg)

case class Fix[F[_]](unfix: F[Fix[F]])

// ============================================================================
// 2. Индексированная Неподвижная Точка
// ============================================================================

case class Mu[IndType, F[Self[_ <: IndType], _ <: IndType], I <: IndType](
  unfix: F[[X <: IndType] =>> Mu[IndType, F, X], I]
)

type μμ[IndType] = [F[Self[_ <: IndType], _ <: IndType]] =>> [I <: IndType] =>> Mu[IndType, F, I]


// Базовые кирпичики
object Zero
type Zero = Zero.type
case class Succ[Prev](prev: Prev)


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



