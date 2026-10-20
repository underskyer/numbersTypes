package numberTypes

import numberTypes.sigmaTypes.Σɢᴀᴅᴛ
import numberTypes.wellFounded.{Branches, Polynomial}

object mTrees:

  enum Σɢᴀᴅᴛ[IndexType, +G[_ <: IndexType]]: //
    case In[I, +F[_ <: I], i <: I](index: i, fi: F[i]) extends Σɢᴀᴅᴛ[I, F]

  type Branches[Index, F[_ <: Index], +Y] = [I <: Index] =>>
    (i: I) => F[i.type] => Y

  type Polynomial[Index, F[_ <: Index]] =
    [Y] =>> Σɢᴀᴅᴛ[Index, Branches[Index, F, Y]]

  given [Index, F[_ <: Index]]: Functor[Polynomial[Index, F]] =
    [A, B] => (f: A => B) => (p: Polynomial[Index, F][A]) =>
      p match
        case Σɢᴀᴅᴛ.In(i, br) =>
          Σɢᴀᴅᴛ.In[Index, Branches[Index, F, B], i.type](
            i,
            (k: i.type) => (b: F[k.type]) => f(br(k)(b))
          )

  trait 𝛎[+F[+_]]:
    def out: F[𝛎[F]]

  object 𝛎:
    def unfold[F[+_]: Functor as fmap, S](f: Coalgebra[F][S]): S => 𝛎[F] =
      s => new:
        def out: F[𝛎[F]] = fmap(unfold(f))(f(s))

  type 𝕄[Index, F[_ <: Index]] = 𝛎[Polynomial[Index, F]]



  object 𝕄:

    // Конструктор (ко-интродукция): из «шапки» (index, branches) строим элемент ν
    def sup[Index, F[_ <: Index], I <: Index](
      i: I,
      br: Branches[Index, F, 𝕄[Index, F]][I]
    ): 𝕄[Index, F] =
      new 𝛎[Polynomial[Index, F]]:
        val out = Σɢᴀᴅᴛ.In[Index, Branches[Index, F, 𝕄[Index, F]], I](i, br)

    def unfold[Index, F[_ <: Index], X](
      step: Coalgebra[Polynomial[Index, F]][X]
    ): X => 𝕄[Index, F] =
      lazy val go: X => 𝕄[Index, F] = step(_) match
        case Σɢᴀᴅᴛ.In(i, br) => sup[Index, F, i.type](i, (k: i.type) => (b: F[k.type]) => go(br(k)(b)))
      go

    type DepCoalgebra[Index, F[_ <: Index], X[_ <: Index]] =
      [I <: Index] => (i: I) => X[i.type] =>
        ((k: i.type) => F[k.type] => X[k.type])

    trait DepPair[Index, X[_ <: Index]]:
      type I <: Index
      val i: I
      val x: X[i.type]

    // Мотив для независимого корекурсора
    type ΣState[Index, X] = [I <: Index] =>> I × X

    def dunfold[Index, F[_ <: Index], X[_ <: Index]](
      step: DepCoalgebra[Index, F, X]
    ): [I <: Index] => (i: I) => X[i.type] => 𝕄[Index, F] =
      val coalg: Coalgebra[Polynomial[Index, F]][DepPair[Index, X]] =
        (s: DepPair[Index, X]) =>
          Σɢᴀᴅᴛ.In[Index, Branches[Index, F, DepPair[Index, X]], s.i.type](
            s.i,
            (k: s.i.type) => (b: F[k.type]) =>
              val x2 = step[s.I](s.i)(s.x)(k)(b)
              new DepPair[Index, X]:
                type I = k.type
                val i = k
                val x = x2
          )
      val go = 𝛎.unfold[Polynomial[Index, F], DepPair[Index, X]](coalg)
      [J <: Index] => j => x => go(new DepPair[Index, X]:
        type I = j.type
        val i = j
        val x = x
      )

//    def coind[Index, F[_ <: Index], X, P[_ <: X]](
//      step: (x: X) => P[x.type] => Σɢᴀᴅᴛ[Index, Branches[Index, F, Σɢᴀᴅᴛ[X, P]]]
//    ): (x: X) => P[x.type] => 𝕄[Index, F] =
//      (x: X) => (p: P[x.type]) =>
//        new 𝛎[Polynomial[Index, F]]:
//          def out = step(x)(p) match
//            case in @ Σɢᴀᴅᴛ.In(_, _) =>
//              in match
//                case Σɢᴀᴅᴛ.In(y, q) =>
//                  // здесь y уже имеет синглтон-тип y.typ e, и q : P[y.type]
//                  Σɢᴀᴅᴛ.In(in.index, (j: in.index.type) => (b: F[j.type]) =>
//                    val pair = next(j)(b)          // : ΣɢᴀᴅT[X, P]
//                    pair match
//                      case Σɢᴀᴅᴛ.In(y2, q2) =>      // y2 : X, q2 : P[y2.type]  ← уже согласовано
//                        coind(step)(y2)(q2)
//                  )
//asInstanceOf