package numberTypes.identityType

sealed trait Id[A, X <: A, Y <: A]:
  def subst[P[_ <: A]](px: P[X]): P[Y]

final case class Refl[A, X <: A]() extends Id[A, X, X]:
  def subst[P[_ <: A]](px: P[X]): P[X] = px


object test:
  trait Container {
    type Elem
    def value: Elem
  }

  def extractAsInt(c: Container)(using ev: c.Elem =:= Int): Int =
    ev(c.value) // ev: c.Elem => Int, безопасно

  val c = new Container {
    type Elem = Int
    def value = 42
  }

  println("========= identityType ===========")

  // при поиске given используется тип передаваемого выражения,
  // а не усечённый тип из определения функции
  println(extractAsInt(c)) // 42

  trait Repo {
    type Id;
    def find(id: Id): Option[String]
  }

  trait Show[A]:
    def show(a: A): String

  def render[A](id: A)(using show: Show[A]): String =
    show.show(id)

  val r = new Repo:
    override type Id = Int
    override def find(id: Int): Option[String] = Option.when(id == 42)("ответ")
  given intShow: Show[Int] = i => s"[$i]"

  val id: r.Id = 42
  println(render(id)) // ev "пробрасывается"

