package numberTypes

object wellFounded:
  // Базовое определение W-типа с зависимыми путями
  sealed trait W[A, B[_ <: A & Singleton]] {
    type Tag <: A & Singleton
    val tag: Tag
    val children: B[Tag] => W[A, B]
  }

  object W {
    // Конструктор (Правило введения) с явным уточнением типа Tag
    def apply[A, B[_ <: A & Singleton], T <: A & Singleton](t: T, ch: B[T] => W[A, B]): W[A, B] {type Tag = T} =
      new W[A, B] {
        type Tag = T
        val tag: T = t
        val children: B[T] => W[A, B] = ch
      }

    // Вспомогательная структура, фиксирующая дочерний узел
    trait ChildOf[A, B[_ <: A & Singleton], ParentTag <: A & Singleton] {
      val b: B[ParentTag]
      val node: W[A, B]
    }

    // 3. ПРАВИЛО УНИЧТОЖЕНИЯ (Зависимый индуктор для W-типа)
    def ind[A, B[_ <: A & Singleton], C[_ <: W[A, B]]](
                                                        step: (w: W[A, B]) => (ih: (c: ChildOf[A, B, w.Tag]) => C[c.node.type]) => C[w.type]
                                                      )(w: W[A, B]): C[w.type] = {

      // 4. ПРАВИЛО ВЫЧИСЛЕНИЯ
      val ih: (c: ChildOf[A, B, w.Tag]) => C[c.node.type] =
        (c: ChildOf[A, B, w.Tag]) => ind[A, B, C](step)(c.node).asInstanceOf[C[c.node.type]]

      step(w)(ih)
    }
  }

  object NatW {
    // Семейство ветвления
    type Branch[B <: Boolean & Singleton] <: Any = B match {
      case true => Nothing
      case false => Unit
    }

    // 1. ПРАВИЛО ФОРМУЛИРОВАНИЯ
    type Nat = W[Boolean, Branch]

    // 2. ПРАВИЛА ВВЕДЕНИЯ
    case object Zero extends W[Boolean, Branch] {
      type Tag = true
      val tag: true = true
      val children: Nothing => Nat = (n: Nothing) => n
    }

    case class Succ(prev: Nat) extends W[Boolean, Branch] {
      type Tag = false
      val tag: false = false
      val children: Unit => Nat = (_: Unit) => prev

      // Упрощение: класс Succ сам знает своего ребенка в терминах W.ChildOf
      val asChild: W.ChildOf[Boolean, Branch, false] = new W.ChildOf[Boolean, Branch, false] {
        val b: Unit = ()
        val node: Nat = prev
      }
    }

    // 3. ПРАВИЛО УНИЧТОЖЕНИЯ (Лаконичный индуктор поверх W.ind)
    def indNat[C[_ <: Nat]](
      zeroCase: C[Zero.type],
      succCase: (p: Nat) => C[p.type] => (s: Succ) => C[s.type]
    )(n: Nat): C[n.type] = {

      // Шаг индукции стал кристально чистым и декларативным
      val natStep = (w: Nat) => (ih: (c: W.ChildOf[Boolean, Branch, w.Tag]) => C[c.node.type]) =>
        w.tag match {
          case _: true => zeroCase
          case _: false =>
            val s = w.asInstanceOf[Succ]
            // Просто передаем в ih уже готового свидетеля из самого объекта Succ!
            val prevProof = ih(s.asChild.asInstanceOf[W.ChildOf[Boolean, Branch, w.Tag]])

            succCase(s.prev)(prevProof.asInstanceOf[C[s.prev.type]])(s)
        }

      W.ind[Boolean, Branch, C](natStep.asInstanceOf)(n)
    }

    // ПРАВИЛО УНИЧТОЖЕНИЯ: Рекурсор (выражен через индуктор)
    // T — фиксированный тип результата (например, Int или Nat)
    def recNat[T](
      zeroCase: T,
      succCase: Nat => T => T
    )(n: Nat): T =
      indNat[[_ <: Nat] =>> T](
        zeroCase,
        (p: Nat) => (ih: T) => (s: Succ) => succCase(p)(ih)
      )(n)
  }


  object test:

    import NatW.*

    val toLong:    Nat => Long = recNat(0L, _ => acc => acc + 1)

    val factorial = recNat[(Long, Long)](
      (0L, 1L),
      _ => (currentLong, currentFact) =>
        val nextLong = currentLong + 1L
        (nextLong, currentFact * nextLong)
    ) andThen {_._2}

    val factorial2: Nat => Long = recNat(1L, p => acc => acc * (toLong(p) + 1))


    val five: Nat = Succ(Succ(Succ(Succ(Succ(Zero)))))

//    val long = toLong(five)
//    println(s"Число: $long")

    val fact = factorial(five)
    println(s"Фундированный факториал: $fact")



