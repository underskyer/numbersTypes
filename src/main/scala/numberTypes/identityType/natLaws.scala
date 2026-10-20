package numberTypes.identityType

object natLaws:

  sealed trait Nat
  trait Zero extends Nat
  trait Suc[N <: Nat] extends Nat

  // Сложение на уровне типов (Type-level Match)
  type +[X <: Nat, Y <: Nat] <: Nat = X match
    case Zero => Y
    case Suc[n] => Suc[n + Y]

  // Вектор, длина которого зафиксирована в его типе
  sealed trait Vect[A, N <: Nat]
  case class Nil[A]() extends Vect[A, Zero]
  case class Cons[A, N <: Nat](head: A, tail: Vect[A, N]) extends Vect[A, Suc[N]]

  object test:

    // Сторонняя функция. Она принимает вектор длины N.
    def requireN[A, N <: Nat](vec: Vect[A, N]): String = "Успех!"

    // Наша функция. У нас на руках вектор длины (N + Zero).
    // Мы ЗНАЕМ, что N + Zero == N. Но компилятор Scala этого НЕ знает.
    def run[A, N <: Nat](myVector: Vect[A, N + Zero]): String =

      // ПОПЫТКА 1: Передать напрямую
      //requireN[A, N](myVector)
      // ОШИБКА КОМПИЛЯЦИИ: Found: Vect[A, N + Zero], Required: Vect[A, N]
      // Здесь Scala непреклонна. Для неё это абсолютно разные типы.

      // ПОПЫТКА 2: Использование типа равенства.
      // Предположим, у нас есть доказательство теоремы о правом нуле:
      // лемма, которая для любого конкретного N возвращает Id.
      // (В рантайме мы просто пробрасываем Refl через каст, так как знаем, что это правда)
      val rightIdProof: Id[Nat, N + Zero, N] =
        Refl[Nat, Nat]().asInstanceOf[Id[Nat, N + Zero, N]]

      // Предикат трансформации
      type Property[T <: Nat] = Vect[A, T]

      // АВТОМАТИЧЕСКИЙ ПЕРЕНОС ТИПА:
      // Мы вручную даем компилятору подсказку (rightIdProof),
      // но саму подмену типа внутри функции `requireN` компилятор делает АВТОМАТИЧЕСКИ.
      val alignedVector: Vect[A, N] = rightIdProof.subst[Property](myVector)

      requireN[A, N](alignedVector) // Теперь компилируется!

