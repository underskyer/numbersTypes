package numberTypes

object vec:

  sealed trait Nat
  case object Zero extends Nat
  case class Succ[N <: Nat](n: N) extends Nat

  // Истинный зависимый индуктор (элиминатор)
  // vSucc — полиморфная функция: для любого N конструирует P[Succ[N]] из P[N]
  def natRect[P[_ <: Nat]](
    vZero: P[Zero.type],
    vSucc: [N <: Nat] => (n: N, prev: P[N]) => P[Succ[N]]
  ): (n: Nat) => P[n.type] = {

    def loop(n: Nat): Any = n match
      case Zero => vZero
      case Succ(prev) => vSucc(prev, loop(prev).asInstanceOf[P[prev.type]])

    (n: Nat) => loop(n).asInstanceOf[P[n.type]]
  }

  sealed trait Vec[+A, N <: Nat]
  case object VNil extends Vec[Nothing, Zero.type]
  case class VCons[A, N <: Nat](head: A, tail: Vec[A, N]) extends Vec[A, Succ[N]]

  class VectorReplicator[A](elem: A):
    val replicate: (n: Nat) => Vec[A, n.type] = (n: Nat) => {
      val f = natRect[[X <: Nat] =>> Vec[A, X]](
        vZero = VNil,
        vSucc = [N <: Nat] => (n: N, prev: Vec[A, N]) => VCons(elem, prev)
      )
      // Вызываем элиминатор внутри правильного скоупа 'n'
      f(n)
    }
  end VectorReplicator


  // 1. Мотив индукции: генерирует тип функции n-арности
  type ArityFn[N <: Nat] = N match {
    case Zero.type => Int
    case Succ[prev] => Int => ArityFn[prev]
  }

  // 2. Строим каррированный сумматор через элиминатор
  def sumN(acc: Int): (n: Nat) => ArityFn[n.type] =
    natRect[ArityFn](
      vZero = acc,
      vSucc = [N <: Nat] => (n: N, prev: ArityFn[N]) =>
        (x: Int) => sumN(acc + x)(n).asInstanceOf[ArityFn[N]]
    ).apply


  class Flatteners[A] {

    // Мотив индукции: Функция, которая переводит уникальный тип
    // вложенности глубины N в плоский список List[A]
    type FlattenMotive[N <: Nat] = NestedType[N] => List[A]

    // Преобразует N в уникальный тип данных: для каждого N тип свой!
    type NestedType[N <: Nat] = N match {
      case Zero.type => A
      case Succ[prev] => List[NestedType[prev]]
    }

    // Создаем функцию через элиминатор
    val flattenN: (n: Nat) => NestedType[n.type] => List[A] = (n: Nat) => {
      val f = natRect[FlattenMotive](
        // База (Zero): Нам дали одиночный элемент A. Превращаем его в плоский список из одного элемента.
        vZero = (data: A) => List(data),

        // Шаг индукции (Истинный):
        // prev — это функция, которая УЖЕ умеет разворачивать тип `NestedType[N]` в плоский `List[A]`.
        // matrix — это список `List[NestedType[N]]`.
        // Чтобы получить плоский список, мы просто применяем `prev` к каждому элементу через flatMap!
        vSucc = [N <: Nat] => (n: N, prev: FlattenMotive[N]) => {
          (matrix: List[NestedType[N]]) => {
            matrix.flatMap { element =>
              // Каждый элемент списка имеет тип NestedType[N], скармливаем его в prev
              prev(element)
            }
          }
        }.asInstanceOf[FlattenMotive[Succ[N]]]
      )
      f(n)
    }
  }

  object test:
    val rep = new VectorReplicator("Scala")

    val zero = Zero
    val one = Succ(zero)
    val two = Succ(one)
    val three = Succ(two)

    // Идеально выводит точные типы векторов!
    val v0: Vec[String, zero.type] = rep.replicate(zero)
    val v2: Vec[String, two.type ] = rep.replicate(two)

    println(s"v0: $v0") // VNil
    println(s"v2: $v2") // VCons(Scala,VCons(Scala,VNil))

    val res0: Int = sumN(10)(zero)
    val res1: Int => Int = sumN(0)(one)
    val res3: Int => Int => Int => Int = sumN(0)(three)

    val finalSum = res3(10)(20)(30)
    println(s"Арность 3: $finalSum") // 60


    object flatteners:
      val f = new Flatteners[Int]

      // --- N = 0 ---
      // Уникальный тип входа: Int
      val flat0 = f.flattenN(zero)
      val res0: List[Int] = flat0(42)
      println(s"N=0: $res0") // List(42)

      // --- N = 1 ---
      // Уникальный тип входа: List[Int]
      val flat1 = f.flattenN(one)
      val res1: List[Int] = flat1(List(1, 2, 3))
      println(s"N=1: $res1") // List(1, 2, 3)

      // --- N = 2 ---
      // Уникальный тип входа: List[List[Int]]
      val flat2 = f.flattenN(two)
      val nestedMatrix: List[List[Int]] = List(List(1, 2), List(3, 4, 5))
      val res2: List[Int] = flat2(nestedMatrix)
      println(s"N=2: $res2") // List(1, 2, 3, 4, 5)

      // --- N = 3 ---
      // Уникальный тип входа: List[List[List[Int]]]
      val flat3 = f.flattenN(three)
      val deepCube: List[List[List[Int]]] = List(
        List(List(1), List(2, 3)),
        List(List(4, 5, 6))
      )
      val res3: List[Int] = flat3(deepCube)
      println(s"N=3: $res3") // List(1, 2, 3, 4, 5, 6)

      // Попытка передать не тот уровень вложенности вызовет Type Mismatch!
      // flat3(nestedMatrix) // Не скомпилируется: Found List[List[Int]], Required List[List[List[Int]]]
    end flatteners

