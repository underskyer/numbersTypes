package numberTypes

import numberTypes.sigmaTypes.{InΣ, ⅀}

object mTrees:

  trait 𝛎[+F[+_]]:
    def out: F[𝛎[F]]

  object 𝛎:
    def unfold[F[+_]: Functor as fmap, S](f: Coalgebra[F][S]): S => 𝛎[F] =
      s => new:
        def out: F[𝛎[F]] = fmap(unfold(f))(f(s))

  type 𝕄[Index, F[_ <: Index]] = 𝛎[ℙ[Index, F]]

  object 𝕄:

    def in[Index, F[_ <: Index], I <: Index](
      i: I,
      br: Brn[Index, F, 𝕄[Index, F]][i.type]
    ): 𝕄[Index, F] =
      new 𝛎[ℙ[Index, F]] { val out = InΣ(i, br) }


    def coind[Index, F[_ <: Index], X[_ <: Index]](
      step: (i: Index) => X[i.type] => F[i.type] => X[i.type]
    ): (i: Index) => X[i.type] => 𝕄[Index, F] =
      val coalgebra: Coalgebra[ℙ[Index, F]][⅀[Index, X]] =
        case InΣ(index, v) =>
          val value = v.asInstanceOf[X[index.type]]
          InΣ[Index, Brn[Index, F, ⅀[Index, X]], index.type](
            index,
            b => InΣ(index, step(index)(value)(b))
          )

      j => x => 𝛎.unfold(coalgebra)(InΣ(j, x))
    end coind

    def corec[Index, F[_ <: Index], C] =
      coind[Index, F, [I <: Index] =>> I × C]
  end 𝕄

  object test:
    // ── 1. Индекс: два канала ──
    enum Ch:
      case Num   // поток чисел
      case Flag  // поток флагов
    export Ch.*

    // ── 2. Форма ЗАВИСИТ от индекса ──
    //    Num:  1 ребёнок (метка не нужна)
    //    Flag: 2 ребёнка (метка = выбор ветки)
    type Form = [T <: Ch] =>> T match
      case Num.type  => Unit
      case Flag.type => Boolean

    // ── 3. Мотива ЗАВИСИТ от индекса (неконстантная!) ──
    type Motive = [T <: Ch] =>> T match
      case Num.type  => LazyList[BigInt]
      case Flag.type => LazyList[Boolean]

    // ── 4. Один шаг — общий для обоих каналов ──
    val step: (i: Ch) => Motive[i.type] => Form[i.type] => Motive[i.type] =
      i => seed => _ =>
          i match
            case Ch.Num  => seed.asInstanceOf[LazyList[BigInt  ]].tail.asInstanceOf[Motive[i.type]]
            case Ch.Flag => seed.asInstanceOf[LazyList[Boolean ]].tail.asInstanceOf[Motive[i.type]]

    // ══════════════════════════════════════════════════════════════
    //  Новый тип — поверх 𝕄
    // ══════════════════════════════════════════════════════════════
    type HeteroStream = 𝕄[Ch, Form]

    object HeteroStream:
      // строитель через 𝕄.coind
      def numsFrom(n: BigInt): HeteroStream =
        𝕄.coind(step)(Ch.Num)(LazyList.iterate(n)(_ + 1))

      def flags: HeteroStream =
        𝕄.coind(step)(Ch.Flag)(LazyList.continually(true))

      // комбинатор через 𝕄.sup
      def fork(n: BigInt): HeteroStream =
        𝕄.in[Ch, Form, Ch.Flag.type](
          Ch.Flag,
          (b: Boolean) =>
            if b then flags else numsFrom(n)
        )

    // наблюдатели — через 𝕄.out
    extension (h: HeteroStream)
      def index: Ch = h.out match { case InΣ(i, _) => i }

      def children: List[(String, HeteroStream)] = h.out match
        case InΣ(i: Ch.Num.type, br: Brn[Ch, Form, HeteroStream][Ch.Num.type]) =>
          List("()" -> br(()))
        case InΣ(i: Ch.Flag.type, br: Brn[Ch, Form, HeteroStream][Ch.Flag.type]) =>
          List("false" -> br(false),
            "true"  -> br(true))

//      def render(depth: Int, indent: String = ""): Unit =
//        println(s"$indent${h.index}")
//        if depth > 0 then
//          h.children.foreach { (lbl, c) =>
//            c.render(depth - 1, indent + s"[$lbl]→")
//          }
    extension (h: HeteroStream)
      def render(maxDepth: Int): Unit =
        def loop(h: HeteroStream, depth: Int, prefix: String, conn: String, isLast: Boolean): Unit =
          println(s"$prefix$conn${h.index}")
          if depth < maxDepth then
            val cs = h.children
            cs.zipWithIndex.foreach { case ((lbl, c), i) =>
              val cIsLast = i == cs.size - 1
              val cConn = if cIsLast then "└─" else "├─"
              val nextP =
                if depth == 0 then prefix
                else prefix + (if isLast then "  " else "│ ")
              loop(c, depth + 1, nextP, s"$cConn[$lbl] ", cIsLast)
            }

        loop(h, 0, "", "", true)

    println ("── numsFrom(0)  (coind Ch.Num) ──")
    HeteroStream.numsFrom (0).render (2)

    println ()
    println ("── flags         (coind Ch.Flag) ──")
    HeteroStream.flags.render (1)

    println ()
    println ("── fork(10)      (sup Ch.Flag) ──")
    HeteroStream.fork (10).render (2)

    println ()
    println ("── Статическая защита: строки ниже не компилируются ──")
    println ("  coind(step)(Ch.Num )(LazyList(true))    ✗ LazyList[Boolean] ≠ X[Num]  = LazyList[BigInt]")
    println ("  coind(step)(Ch.Flag)(LazyList(0, 1))    ✗ LazyList[BigInt]   ≠ X[Flag] = LazyList[Boolean]")

end mTrees

