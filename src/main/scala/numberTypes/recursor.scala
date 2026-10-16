package numberTypes

import piTypes.*

import scala.util.chaining.scalaUtilChainingOps

object recursor:
  type Recursor[In[+_], Type] = Π[Any, [C] =>> In[C] => Type => C]
  type Recursor2[In[_, _, +_], Type[_, _]] = [A, B] => () =>
    Recursor[In[A, B, *], Type[A, B]]

  val recProd: Recursor2[[A, B, C] =>> A => B => C, ×] =
    [A, B] => () => [C] => () => Function.uncurried(_).tupled

  val recSum: Recursor2[[A, B, C] =>> (A => C) × (B => C), +] =
    [A, B] => () => [C] => () => p => _.fold(p._1, p._2)

  val recExp: Recursor2[[A, B, C] =>> A × (B => C), Function] =
    [A, B] => () => [C] => () => aCont => aCont._1 pipe _ pipe aCont._2


  object test:
    val elimDoubleProdInt: Double × Int => String =
      recProd[Double, Int]()()(d => i => "res = " + (d + i))

    val elimDoublePlusInt: Double + Int => String =
      recSum[Double, Int]()()(d => s"d: $d", i => s"i: $i")

    val elimDoubleFuncInt: (Double => Int) => String =
      recExp[Double, Int]()()(-32.4312 -> {"строка: " + _})

    val res1 = elimDoubleProdInt((-32.4312, 42))          // res = 9.568800000000003x
    val res2 = elimDoublePlusInt(Left(-32.4312))          // d: -32.4312
    val res3 = elimDoubleFuncInt((_: Double).round.toInt) // строка: -32

    println("==================================================")
    println("                 recursor                         ")
    println("==================================================")
    println(res1)
    println(res2)
    println(res3)

    // Ошибка компиляции (Type Mismatch):
    // val wrong: PiType[Role, Permissions][Admin] = "just a string"
  end test

