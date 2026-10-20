package numberTypes

type 𝔹 = Boolean & Singleton

infix type ×[A, B] = (A, B)
infix type +[A, B] = A Either B

infix type ~>[F[_], G[_]] = [A] => F[A] => G[A]
type Algebra[F[_]] = [A] =>> F[A] => A
type Coalgebra[F[_]] = [A] =>> A => F[A]
type Functor[F[+_]] = [A, B] => (A => B) => (F[A] => F[B])

type Id[A] = A
type Const[A] = [X] =>> A

type Pair[A, B] = [R <: 𝔹] =>> R match
  case false => A
  case true => B


type μ[F[_]] = Algebra[F] ~> Id
def cata[F[_]]: Algebra[F] ~> (μ[F] => *) = [A] => alg => _(alg)

case class Fix[F[_]](unfix: F[Fix[F]])

enum μᵢ[+F[+_]]:
  case In[+G[+_], +V <: G[μᵢ[G]]](unfix: V) extends μᵢ[G]

object μᵢ:
  def openCata[F[+_], A](step: F[μᵢ[F]] => (μᵢ[F] => A) => A): μᵢ[F] => A =
    case In(v) => step(v)(openCata(step))
  
  extension [F[+_]] (fix: μᵢ[F])
    inline def openFold[A](step: F[μᵢ[F]] => (μᵢ[F] => A) => A): A =
      openCata[F, A](step)(fix)


// \mathbf{\nu}
trait 𝛎[+F[+_]]:
  def out: F[𝛎[F]]


// ============================================================================
// 2. Индексированная Неподвижная Точка
// ============================================================================

case class Mu[IndType, F[Self[_ <: IndType], _ <: IndType], I <: IndType](
  unfix: F[[X <: IndType] =>> Mu[IndType, F, X], I]
)

type μμ[IndType] = [F[Self[_ <: IndType], _ <: IndType]] =>> [I <: IndType] =>> Mu[IndType, F, I]

trait Σᴏᴏᴘ[IndexType, F[_ <: IndexType]]:
  type I <: IndexType // первая проекция
  //def index: I
  val value: F[I] // вторая проекция

object Σᴏᴏᴘ:
  case class In[IndexType, F[_ <: IndexType], In <: IndexType](value: F[In]) extends Σᴏᴏᴘ[IndexType, F]:
    type I = In


// Базовые кирпичики
object Zero
type Zero = Zero.type
case class Succ[+Prev](prev: Prev)


infix type ~[A, B] = (
  forward:  A => B,
  backward: B => A
)

object Iso extends LowPriority:
  given convFromIso1: [A, B] =>(iso: A ~ B) => Conversion[A, B] = new:
    def apply(a: A) = iso.forward(a)

trait LowPriority:
  given convFromIso2: [A, B] =>(iso: A ~ B) => Conversion[B, A] = new:
    def apply(b: B) = iso.backward(b)


