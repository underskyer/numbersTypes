package numberTypes

import numberTypes.inductor.indNatural.*

object vector:

  enum Nat: // formation
    case Zero extends Nat // introduction (1-й конструктор)
    case Succ[P](prev: P) extends Nat // introduction (2-й конструктор)

  import Nat.*

  type RepAux[N <: Nat, F[+_], A] = N match
    case Zero => A
    case Succ[prev] => F[RepAux[prev, F, A]]

  type RepNatLambda[F[+_], A] = [N] =>> RepAux[N & Nat, F, A]

  //  type Fix1[F[+_]] = [A] =>> ∑[[N] =>> N match {
  //    case Nat => RepAux[N & Nat, F, A]
  //    case _ => Any
  //  }, Nat]

  type Mul[A] = [X <: Tuple] =>> A *: X
  //  type Lst[A] = Fix1[[X] =>> A *: X][EmptyTuple]

  type Vec1[N <: Nat, A] <: Tuple = N match
    case Zero => EmptyTuple
    case Succ[prev] => A *: Vec1[prev, A]

  opaque type Vector[N <: Nat, A] <: Vec1[N, A] = Vec1[N, A]

  object Vector:
    given [N <: Nat, A] => Conversion[Vec1[N, A], Vector[N, A]] = identity

  //type Vectors[A] <: Vector[Nat, A] = ∑∑[Nat, [N <: Nat] =>> Vector[N, A]]

  //  def zip[N <: Nat, A, B](va: Vec[N, A], vb: Vec[N, B]): Vec[N, (A, B)] =
  //    (va, vb) match
  //      case (a *: as, b *: bs) => (a, b) *: zip(as, bs)
  //      case _ => EmptyTuple


//  trait Zipper[N <: Nat]:
//    def apply[A, B](va: Vec1[N, A], vb: Vec1[N, B]): Vec1[N, (A, B)]
//
//  object Zipper {
//    // Базовый случай индукции: для Nat.Zero.type возвращаем EmptyTuple
//    given zeroZipper: Zipper[Zero.type] with
//      def apply[A, B](va: EmptyTuple, vb: EmptyTuple): EmptyTuple =
//        EmptyTuple
//
//    // Шаг индукции: если умеем зиповать `prev`, то умеем зиповать и `Succ[prev]`
//    given succZipper[Prev <: Nat](using prevZipper: Zipper[Prev]): Zipper[Succ[Prev]] with
//      def apply[A, B](va: A *: Vec1[Prev, A], vb: B *: Vec1[Prev, B]): (A, B) *: Vec1[Prev, (A, B)] =
//        // Здесь компилятор точно знает структуру va и vb (это Tuple с головой и хвостом)
//        val head = (va.head, vb.head)
//        val tail: Vec1[Prev, (A, B)] = prevZipper(va.tail, vb.tail)
//        head *: tail
//  }

  type ZipFunc[N <: Nat] = [A, B] => (Vec1[N, A], Vec1[N, B]) => Vec1[N, (A, B)]

  // Базовый случай индукции (для Zero)
  inline given zeroZipper: ZipFunc[Zero.type] =
    [A, B] => (va: Vec1[Zero.type, A], vb: Vec1[Zero.type, B]) => EmptyTuple.asInstanceOf[Vec1[Zero.type, (A, B)]]

  // Шаг индукции (для Succ)
  inline given succZipper[Prev <: Nat : ZipFunc as prevZip]: ZipFunc[Succ[Prev]] =
    [A, B] => (va: A *: Vec1[Prev, A], vb: B *: Vec1[Prev, B]) =>
      val head = (va.head, vb.head)
      val tail = prevZip[A, B](va.tail, vb.tail)
      head *: tail

  // 2. Красивый внешний метод без inline
  //def zip[N <: Nat : ZipFunc as zipper] = zipper
  def zip[N <: Nat : ZipFunc as zipper, A, B](va: Vector[N, A], vb: Vector[N, B]): Vector[N, (A, B)] = zipper(va, vb)
  
  object test:

    val i0: Vector[Zero.type, Int] = EmptyTuple.asInstanceOf[Vec1[Zero.type, Int]]
    val i1: Vector[Succ[Zero], Int] = Tuple1(42)
    val i2: Vector[Succ[Succ[Zero]], Int] = (42, 21)
    val s2: Vector[Succ[Succ[Zero]], String] = ("ответ", "полответа")


    //var vi: Vector[Nat, Int] = i0

    //println("vec zip: " + zip(i2, s2))
