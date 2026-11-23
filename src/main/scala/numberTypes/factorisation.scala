package numberTypes

import scala.compiletime.ops.int.*
import scala.compiletime.ops.boolean.*

object factorisation:

  // Вспомогательный предикат равенства двух произвольных типов (вместо запрещенного case (a, a))
  type IsSame[A, B] <: Boolean = A match
    case B =>
      B match
        case A => true
        case _ => false
    case _ => false

  // =========================================================================
  // 1. ЯЗЫК ТЕРМОВ И УРАВНЕНИЙ
  // =========================================================================
  sealed trait Term
  case class Var[Name <: String]() extends Term
  case object UnitT extends Term
  case class S_T[A <: Term]() extends Term
  // PairT — единственный «контейнер» языка: он моделирует ПАРУ значений
  // (произведение). Никаких отдельных конструкторов для операций здесь нет:
  // любая операция над числами (сложение, вычитание, ...) — это та же пара,
  // различие задаётся только УРАВНЕНИЯМИ, а не формой терма.
  case class PairT[A <: Term, B <: Term]() extends Term

  case class Eq[L <: Term, R <: Term]()
  case class Rule[L <: Term, R <: Term]()

  // =========================================================================
  // 2. МЕРА ТЕРМОВ И ОРИЕНТАЦИЯ
  // =========================================================================
  type Weight[T <: Term] <: Int = T match
    case Var[_]      => 1
    case UnitT.type  => 1
    case S_T[a]      => 1 + Weight[a]
    case PairT[a, b] => 1 + Weight[a] + Weight[b]

  // Ориентация одного уравнения. Неориентируемое уравнение (равные веса)
  // отбрасывается, поэтому результат — всегда кортеж (возможно пустой).
  type OrientRule[L <: Term, R <: Term] <: Tuple =
    (Weight[L] > Weight[R]) match
      case true  => Tuple1[Rule[L, R]]
      case false =>
        (Weight[R] > Weight[L]) match
          case true  => Tuple1[Rule[R, L]]
          case false => EmptyTuple

  type Orient[E] <: Tuple = E match
    case Eq[l, r] => OrientRule[l, r]

  type OrientAll[Eqs <: Tuple] <: Tuple = Eqs match
    case EmptyTuple => EmptyTuple
    case h *: t     => Tuple.Concat[Orient[h], OrientAll[t]]

  // =========================================================================
  // 3. ПОДСТАНОВКИ И УНИФИКАЦИЯ НА УРОВНЕ ТИПОВ
  // =========================================================================
  case class Bind[V <: String, T <: Term]()

  type Lookup[V <: String, Sub <: Tuple] <: Term = Sub match
    case EmptyTuple      => Var[V]
    case Bind[V, t] *: _ => t
    case _ *: tail       => Lookup[V, tail]

  type ApplySubst[T <: Term, Sub <: Tuple] <: Term = T match
    case Var[v]      => Lookup[v, Sub]
    case UnitT.type  => UnitT.type
    case S_T[a]      => S_T[ApplySubst[a, Sub]]
    case PairT[a, b] => PairT[ApplySubst[a, Sub], ApplySubst[b, Sub]]

  // Результат поиска подстановки: успех либо явный маркер неудачи.
  // (В match-типах нельзя ветвиться по Nothing и нельзя связывать результат
  //  "голым" `case x`, поэтому используется обычный ADT.)
  sealed trait MatchResult
  case class Matched[Sub <: Tuple]() extends MatchResult
  case object MatchFail extends MatchResult

  // Сопоставление "образец-терм" и проверка равенства через IsSame.
  // Сопоставление ОДНОСТОРОННЕЕ: переменные шаблона Pat связываются, а
  // переменные в T считаются "жёсткими" (rigid). Симметричная унификация
  // здесь непригодна: при нормализации терма с переменными правило
  // применялось бы и в обратную сторону (Pair(a, b) -> Pair(S a, S b) -> ...),
  // что приводит к незавершающейся редукции match-типа.
  // Тело записано одним match-типом (без промежуточного алиаса), т.к. верхнюю
  // границу (`<: MatchResult`) можно указывать только у "настоящего" match-типа.
  type Match[Pat <: Term, T <: Term, Sub <: Tuple] <: MatchResult =
    (Pat, T) match
      case (Var[v], t)      => Matched[Bind[v, t] *: Sub]
      case (S_T[x], S_T[y]) => Match[x, y, Sub]
      case (PairT[a1, b1], PairT[a2, b2]) =>
        Match[a1, a2, Sub] match
          case Matched[sub1]  => Match[b1, b2, sub1]
          case MatchFail.type => MatchFail.type
      case _ =>
        IsSame[Pat, T] match
          case true  => Matched[Sub]
          case false => MatchFail.type

  // =========================================================================
  // 4. ПЕРЕПИСЫВАНИЕ И ПОИСК КРИТИЧЕСКИХ ПАР
  // =========================================================================
  type RewriteRoot[T <: Term, R] <: Term = R match
    case Rule[lhs, rhs] =>
      Match[lhs, T, EmptyTuple] match
        case Matched[sub]   => ApplySubst[rhs, sub]
        case MatchFail.type => T

  type RewriteStep[T <: Term, R] =
    RewriteStepAux[T, RewriteRoot[T, R], R]

  type RewriteStepAux[Orig <: Term, AfterRoot <: Term, R] <: Term =
    IsSame[Orig, AfterRoot] match
      case false => AfterRoot
      case true  =>
        Orig match
          case S_T[a]      => S_T[RewriteStep[a, R]]
          case PairT[a, b] => PairT[RewriteStep[a, R], RewriteStep[b, R]]
          case _           => Orig

  type NormalizeAll[T <: Term, Rules <: Tuple] <: Term = Rules match
    case EmptyTuple => T
    case r *: tail  =>
      NormalizeStepCheck[T, RewriteStep[T, r], tail, Rules]

  type NormalizeStepCheck[Orig <: Term, Next <: Term, Tail <: Tuple, AllRules <: Tuple] <: Term =
    IsSame[Orig, Next] match
      case true  => NormalizeAll[Orig, Tail]
      case false => NormalizeAll[Next, AllRules]

  type CriticalPair[R1, R2] <: Tuple = (R1, R2) match
    case (Rule[l1, r1], Rule[l2, r2]) =>
      Match[l1, l2, EmptyTuple] match
        case Matched[sub] =>
          Tuple1[Eq[ApplySubst[r1, sub], ApplySubst[r2, sub]]]
        case MatchFail.type =>
          l2 match
            case S_T[inner] =>
              Match[l1, inner, EmptyTuple] match
                case Matched[sub] =>
                  Tuple1[Eq[S_T[ApplySubst[r1, sub]], ApplySubst[r2, sub]]]
                case MatchFail.type => EmptyTuple
            case _ => EmptyTuple

  type AllCritPairsFor[R, Rules <: Tuple] <: Tuple = Rules match
    case EmptyTuple => EmptyTuple
    case h *: tail  => Tuple.Concat[CriticalPair[R, h], AllCritPairsFor[R, tail]]

  type AllCritPairs[Rules <: Tuple, All <: Tuple] <: Tuple = Rules match
    case EmptyTuple => EmptyTuple
    case h *: tail  => Tuple.Concat[AllCritPairsFor[h, All], AllCritPairs[tail, All]]

  type ProcessNewEqs[Eqs <: Tuple, Rules <: Tuple] <: Tuple = Eqs match
    case EmptyTuple => EmptyTuple
    case Eq[l, r] *: tail =>
      ProcessSingleEq[NormalizeAll[l, Rules], NormalizeAll[r, Rules], tail, Rules]

  type ProcessSingleEq[NL <: Term, NR <: Term, Tail <: Tuple, Rules <: Tuple] <: Tuple =
    IsSame[NL, NR] match
      case true  => ProcessNewEqs[Tail, Rules]
      case false => Tuple.Concat[OrientRule[NL, NR], ProcessNewEqs[Tail, Rules]]

  type CompleteLoop[Rules <: Tuple] <: Tuple =
    ProcessNewEqs[AllCritPairs[Rules, Rules], Rules] match
      case EmptyTuple    => Rules
      case nr *: nrs     => CompleteLoop[Tuple.Concat[Rules, nr *: nrs]]

  // Взаимная редукция (interreduction): каждая rule нормализуется остальными.
  // Тривиальные правила (левая и правая части совпали) отбрасываются, а
  // избыточные правила (например, S(S(S(y))) -> S(y) при наличии S(S(x)) -> x)
  // схлопываются в пустой кортеж.
  type InterreduceRule[R, Others <: Tuple] <: Tuple = R match
    case Rule[l, r] =>
      InterreduceCheck[NormalizeAll[l, Others], NormalizeAll[r, Others]]

  type InterreduceCheck[NL <: Term, NR <: Term] <: Tuple =
    IsSame[NL, NR] match
      case true  => EmptyTuple
      case false => OrientRule[NL, NR]

  type RemoveRule[R, Rules <: Tuple] <: Tuple = Rules match
    case EmptyTuple => EmptyTuple
    case h *: t     =>
      IsSame[h, R] match
        case true  => t
        case false => h *: RemoveRule[R, t]

  // Обход ведётся по `Todo`, а нормализация каждого правила выполняется по
  // ПОЛНОМУ набору `All` (за вычетом самого правила). Раньше рекурсивный вызов
  // получал только "хвост", из-за чего правила после первого нормализовались
  // против неполного набора и не отбрасывались как избыточные.
  type Interreduce[Rules <: Tuple] = InterreduceWith[Rules, Rules]

  type InterreduceWith[Todo <: Tuple, All <: Tuple] <: Tuple = Todo match
    case EmptyTuple => EmptyTuple
    case h *: t     =>
      Tuple.Concat[InterreduceRule[h, RemoveRule[h, All]], InterreduceWith[t, All]]

  type KnuthBendix[Eqs <: Tuple] = Interreduce[CompleteLoop[OrientAll[Eqs]]]

  // =========================================================================
  // 5. АЛГЕБРА ПОЛИНОМИАЛЬНЫХ ФУНКТОРОВ И ПОСТРОЕНИЕ ИТОГОВОГО ТИПА
  // =========================================================================
  sealed trait FType
  case object Zero extends FType
  case object One extends FType
  case object Rec extends FType
  // Параметры ковариантны: это делает законными вложенные паттерны вида
  // `case Prod[Sum[a, b], c]` (требование SIP-56 для legal patterns).
  // Параметры объявлены полями: для ковариантных параметров dotc доказывает
  // дизъюнктность аргументов (`provablyDisjointTypeArgs` -> `covariantDisjoint`)
  // только если параметр соответствует полю класса. Без полей редукция
  // `Distribute[Prod[One.type, NatF]]` зависает: селектор не сопоставляется с
  // `Prod[Sum[a, b], c]`, но и не доказывается его дизъюнктность.
  case class Sum[+A <: FType, +B <: FType](a: A, b: B) extends FType
  case class Prod[+A <: FType, +B <: FType](a: A, b: B) extends FType

  type SubstRec[T <: FType, Body <: FType] <: FType = T match
    case Rec.type   => Body
    case Sum[a, b]  => Sum[SubstRec[a, Body], SubstRec[b, Body]]
    case Prod[a, b] => Prod[SubstRec[a, Body], SubstRec[b, Body]]
    case _          => T

  type Unroll[T <: FType, Body <: FType, Depth <: Int] <: FType = Depth match
    case 0 => T
    case 1 => T
    case _ => Unroll[SubstRec[T, Body], Body, Depth - 1]

  type TermDepth[T <: Term] <: Int = T match
    case S_T[a]      => 1 + TermDepth[a]
    case PairT[a, b] => Max[TermDepth[a], TermDepth[b]]
    case _           => 0

  type MaxRulesDepth[Rules <: Tuple] <: Int = Rules match
    case EmptyTuple        => 1
    case Rule[lhs, _] *: t => Max[TermDepth[lhs], MaxRulesDepth[t]]

  type TermToPattern[T <: Term] <: FType = T match
    case Var[_]      => Rec.type
    case UnitT.type  => One.type
    case S_T[a]      => TermToPattern[a]
    case PairT[a, b] => Prod[TermToPattern[a], TermToPattern[b]]

  type Distribute[T <: FType] <: FType = T match
    case Prod[Sum[a, b], c] => Sum[Distribute[Prod[a, c]], Distribute[Prod[b, c]]]
    case Prod[a, Sum[b, c]] => Sum[Distribute[Prod[a, b]], Distribute[Prod[a, c]]]
    case Sum[a, b]          => Sum[Distribute[a], Distribute[b]]
    case Prod[a, b]         => DistributeProd[Distribute[a], Distribute[b]]
    case _                  => T

  type DistributeProd[L <: FType, R <: FType] <: FType = (L, R) match
    case (Sum[x, y], r) => Distribute[Prod[Sum[x, y], r]]
    case (l, Sum[x, y]) => Distribute[Prod[l, Sum[x, y]]]
    case (l, r)         => Prod[l, r]

  type SubtractOne[T <: FType, Pat <: FType] <: FType = T match
    case Sum[a, b] => Sum[SubtractOne[a, Pat], SubtractOne[b, Pat]]
    case _         =>
      IsSame[T, Pat] match
        case true  => Zero.type
        case false => T

  type SubtractRules[T <: FType, Rules <: Tuple] <: FType = Rules match
    case EmptyTuple        => T
    case Rule[lhs, _] *: t => SubtractRules[SubtractOne[T, TermToPattern[lhs]], t]

  type SimplifyStep[T <: FType] <: FType = T match
    case Sum[Zero.type, a]  => SimplifyStep[a]
    case Sum[a, Zero.type]  => SimplifyStep[a]
    case Prod[Zero.type, _] => Zero.type
    case Prod[_, Zero.type] => Zero.type
    case Prod[One.type, a]  => SimplifyStep[a]
    case Prod[a, One.type]  => SimplifyStep[a]
    case Sum[a, b]          => Sum[SimplifyStep[a], SimplifyStep[b]]
    case Prod[a, b]         => Prod[SimplifyStep[a], SimplifyStep[b]]
    case _                  => T

  // Повторяем SimplifyStep до неподвижной точки.
  type Simplify[T <: FType] <: FType =
    (T, SimplifyStep[T]) match
      case (orig, next) =>
        IsSame[orig, next] match
          case true  => orig
          case false => Simplify[next]

  // =========================================================================
  // 6. ИТОГОВЫЙ УНИВЕРСАЛЬНЫЙ ОПЕРАТОР ФАКТОРИЗАЦИИ ТИПА
  // =========================================================================
  // Уравнение Eq[l, r] действует на тип одним из двух способов. Выбор
  // определяется ТОЛЬКО весами частей, то есть свойством самого уравнения, —
  // оператор ничего не знает о том, какая житейская операция за ним стоит:
  //
  //   1) Weight[l] > Weight[r] (или наоборот) — уравнение ОРИЕНТИРУЕМО.
  //      Тогда это правило переписывания, и страта (моном), накрытая его
  //      левой частью, «вычитается» (SubtractRules). Так работает замыкание,
  //      которое ПОРОЖДАЕТ новые элементы: (S a, S b) ~ (a, b) даёт Z.
  //
  //   2) Weight[l] = Weight[r] — ориентировать нельзя (части «одного
  //      размера»), это СИММЕТРИЯ. Она ничего не вычитает, а ОТОЖДЕСТВЛЯЕТ:
  //      страты, накрытые частями уравнения, описывают одни и те же классы и
  //      сливаются в одну страту Rec (классов, пронумерованных рекурсией,
  //      столько же) — MergeIdentified. Так работает замыкание, которое новых
  //      элементов НЕ даёт: (S a, b) ~ (a, S b) оставляет Nat = Nat.
  //
  //   3) Если множество классов описывается ровно телом рекурсии
  //      (T =:= RecBody), фактор-тип — это сам рекурсивный тип (FixCheck).
  //      Это не «спец-случай под Nat»: факторизация Nat по пустому набору
  //      уравнений тоже обязана дать Nat, а не Option[Nat].
  type QuotientType[InitType <: FType, RecBody <: FType, Eqs <: Tuple] =
    QuotientWith[InitType, RecBody, KnuthBendix[Eqs], SymmetricEqs[Eqs]]

  type QuotientWith[
      InitType <: FType,
      RecBody <: FType,
      Rules <: Tuple,
      Syms <: Tuple
  ] =
    FixCheck[
      Simplify[
        MergeIdentified[
          SubtractRules[
            Distribute[Unroll[InitType, RecBody, MaxRulesDepth[Rules]]],
            Rules
          ],
          Syms,
          RecBody
        ]
      ],
      RecBody
    ]

  // ----- 6.1. Разделение уравнений по ориентируемости -----------------------

  // Ориентируемо ли уравнение: части разного веса.
  type IsOrientable[L <: Term, R <: Term] =
    (Weight[L] > Weight[R]) || (Weight[R] > Weight[L])

  // Уравнения с равными весами — симметрии (их KnuthBendix отбрасывает,
  // потому что переписывать в одну сторону нельзя).
  type SymmetricEqs[Eqs <: Tuple] <: Tuple = Eqs match
    case EmptyTuple => EmptyTuple
    case Eq[l, r] *: t =>
      IsOrientable[l, r] match
        case true  => SymmetricEqs[t]
        case false => Eq[l, r] *: SymmetricEqs[t]

  // ----- 6.2. Страты терма уравнения ---------------------------------------

  // Множество стран (мономов), которые накрывает терм уравнения.
  // Отличие от TermToPattern: переменная пробегает ВСЕ страты рекурсивного
  // типа (RecBody), а S_T срезает нулевую страту. Поэтому у (S a, b) и
  // (a, S b) наборы стран РАЗНЫЕ, а у (S a, S b) и (a, b) — вложенные друг в
  // друга: именно это различает симметрию и ориентируемое правило.
  type PatternStrata[T <: Term, RecBody <: FType] <: FType = T match
    case Var[_]      => RecBody
    case UnitT.type  => One.type
    case S_T[a]      => StripFirst[PatternStrata[a, RecBody]]
    case PairT[a, b] => Prod[PatternStrata[a, RecBody], PatternStrata[b, RecBody]]

  // Срезание нулевой страты: положительные значения — это тип без нуля.
  type StripFirst[T <: FType] <: FType = T match
    case Sum[One.type, b] => StripFirst[b]
    case Sum[a, One.type] => StripFirst[a]
    case _                => T

  // ----- 6.3. Слияние стран, отождествлённых симметрией --------------------

  type InStrata[Tup <: Tuple, X] <: Boolean = Tup match
    case EmptyTuple => false
    case h *: t     => IsSame[h, X] || InStrata[t, X]

  type StratumList[T <: FType] <: Tuple = T match
    case Sum[a, b] => Tuple.Concat[StratumList[a], StratumList[b]]
    case _         => Tuple1[T]

  // Страты, накрытые уравнением, «выбиваются» в Zero.
  type DropStrata[T <: FType, Affected <: Tuple] <: FType = T match
    case Sum[a, b] => Sum[DropStrata[a, Affected], DropStrata[b, Affected]]
    case _ =>
      InStrata[Affected, T] match
        case true  => Zero.type
        case false => T

  // Слипшиеся страты — это ОДНА страта классов, пронумерованных рекурсией,
  // то есть Rec. Если уравнение не задело ни одной страты, ничего не меняется.
  type MergeAffected[T <: FType, Affected <: Tuple] <: FType =
    IsSame[DropStrata[T, Affected], T] match
      case true  => T
      case false => Sum[Simplify[DropStrata[T, Affected]], Rec.type]

  type MergeEq[T <: FType, E, RecBody <: FType] <: FType = E match
    case Eq[l, r] =>
      MergeAffected[
        T,
        Tuple.Concat[
          StratumList[Distribute[PatternStrata[l, RecBody]]],
          StratumList[Distribute[PatternStrata[r, RecBody]]]
        ]
      ]

  type MergeIdentified[T <: FType, Eqs <: Tuple, RecBody <: FType] <: FType = Eqs match
    case EmptyTuple => T
    case h *: t     => MergeIdentified[MergeEq[T, h, RecBody], t, RecBody]

  // ----- 6.4. Проверка «получился тот же рекурсивный тип» -------------------

  type FixCheck[T <: FType, RecBody <: FType] <: FType =
    IsSame[T, RecBody] match
      case true  => Rec.type
      case false => T

  // =========================================================================
  // 6.5. УНИВЕРСАЛЬНАЯ ТРАНСЛЯЦИЯ FType <-> РЕАЛЬНЫЙ ТИП
  // =========================================================================

  // Универсальный оператор неподвижной точки. Рекурсивные типы
  // (Nat, списки, деревья, ...) выражаются через него:
  //     type NatBody[X] = Either[Unit, X]
  //     type Nat     = Fix[NatBody]
  // Конкретных Nat здесь нет: есть только Fix и операторы-конструкторы ниже.
  case class Fix[F[_]](unfix: F[Fix[F]])

  // Перевод реального типа в фантомный FType.
  // Параметр Self — «якорь» для распознавания себя внутри рекурсивного тела:
  // встреча с Self -> Rec.type, остальное — структурно.
  // Для Fix[F] разворачиваем один слой: F[Fix[F]] при Self = Fix[F].
  // Никаких конкретных Nat и никаких типов-конструкторов операций: только
  // универсальные типы. Пара (a, b) — это ПРОИЗВЕДЕНИЕ, и этим всё сказано.
  type ToFType[T] = ToFTypeSelf[T, Nothing]

  type ToFTypeSelf[T, Self] <: FType = IsSame[T, Self] match
    case true => Rec.type
    case false => T match
      case Unit => One.type
      case Boolean => Sum[One.type, One.type]
      case Option[a] => Sum[One.type, ToFTypeSelf[a, Self]]
      case Either[a, b] => Sum[ToFTypeSelf[a, Self], ToFTypeSelf[b, Self]]
      case (a, b) => Prod[ToFTypeSelf[a, Self], ToFTypeSelf[b, Self]]
      case Fix[g] => ToFTypeSelf[g[Fix[g]], Fix[g]]
      case _ => Zero.type

  // Правая ассоциативность сумм: нужно, чтобы FromFType видел
  // Sum[One, Sum[Rec, Rec]] вместо лево-ассоциативной Sum[Sum[One, Rec], Rec].
  type ReassocSum[T <: FType] <: FType = T match
    case Sum[Sum[a, b], c] => ReassocSum[Sum[a, Sum[b, c]]]
    case Sum[a, b] => Sum[ReassocSum[a], ReassocSum[b]]
    case _ => T

  // Перевод FType обратно в реальный тип. RecType — тот же Fix-тип, которым
  // был Rec на этапе ToFType. Правила для One/Rec/Sum/Prod — универсальны.
  type FromFType[T <: FType, RecType] <: Any = T match
    case Zero.type => Nothing
    case One.type => Unit
    case Rec.type => RecType
    case Sum[One.type, One.type] => Boolean
    case Sum[Rec.type, Rec.type] => (Boolean, RecType) // Either[X, X] ~ (Boolean, X)
    case Sum[One.type, x] => Option[FromFType[x, RecType]]
    case Sum[x, One.type] => Option[FromFType[x, RecType]]
    case Sum[a, b] => Either[FromFType[a, RecType], FromFType[b, RecType]]
    case Prod[a, b] => (FromFType[a, RecType], FromFType[b, RecType])

  // Итоговый оператор: реальный тип -> FType -> факторизация -> реальный тип.
  // RecBody автоматически получается как ToFType[RecType]; никакого выбора
  // «алгебры по операции» нет — алгебра выводится из самих уравнений.
  type RealQuotient[Init, RecType, Eqs <: Tuple] =
    FromFType[ReassocSum[QuotientType[ToFType[Init], ToFType[RecType], Eqs]], RecType]

  object test:
    // =========================================================================
    // 7. ПРОВЕРКА РАБОТОСПОСОБНОСТИ
    // =========================================================================
    type NatF = Sum[One.type, Rec.type]

    // ТЕСТ 1: Замыкание по вычитанию (S(a), S(b)) ~ (a, b)
    type SubEqs = Tuple1[
      Eq[
        PairT[S_T[Var["a"]], S_T[Var["b"]]],
        PairT[Var["a"], Var["b"]]
      ]
    ]

    type ZType = QuotientType[Prod[NatF, NatF], NatF, SubEqs]
    summon[ZType =:= Sum[Sum[One.type, Rec.type], Rec.type]]

    // ТЕСТ 2: Факторизация по модулю 2: S(S(x)) ~ x (плюс избыточное правило)
    type Mod2Eqs = (
      Eq[S_T[S_T[Var["x"]]], Var["x"]],
      Eq[S_T[S_T[S_T[Var["y"]]]], S_T[Var["y"]]]
    )

    type BoolType = QuotientType[NatF, NatF, Mod2Eqs]
    summon[BoolType =:= Sum[One.type, One.type]]

    // =========================================================================
    // ТЕСТ 3 и ТЕСТ 4: реальные типы операций.
    //
    // Sub и Add — ОБЫЧНЫЕ ПАРЫ значений. На уровне типов между ними вообще нет
    // разницы (оба — (A, B), то есть произведение): различие задают только
    // УРАВНЕНИЯ. Поэтому универсальный оператор выше физически не может
    // «узнать» Add — для него это ровно то же, что Sub.
    // =========================================================================
    type NatBody[X] = Either[Unit, X]
    type Nat        = Fix[NatBody]

    opaque type Sub[A, B] <: (A, B) = (A, B)
    opaque type Add[A, B] <: (A, B) = (A, B)

    // ТЕСТ 3: замыкание по ВЫЧИТАНИЮ  (S a, S b) ~ (a, b).
    // Уравнение ориентируемо (вес 4 > 2), поэтому работает вычитание стран:
    //   (1 + R)·(1 + R) = 1 + R + R + R·R --[вычесть R·R]--> 1 + 2·R.
    // Классы: [(0,0)], [(m,0)], [(0,n)]  =>  Z = Option[(Boolean, Nat)].
    type RealSubResult = RealQuotient[Sub[Nat, Nat], Nat, SubEqs]
    summon[RealSubResult =:= Option[(Boolean, Nat)]]

    // ТЕСТ 4: замыкание Nat по СЛОЖЕНИЮ:  (S a, b) ~ (a, S b),
    //         то есть (m + 1) + n = m + (n + 1).
    // Веса частей равны (4 = 4), уравнение НЕ ориентируемо => это симметрия:
    // страты не вычитаются, а отождествляются:
    //   страты левой части : {Rec·1, Rec·Rec}
    //   страты правой части: {1·Rec, Rec·Rec}
    //   => Rec·1, 1·Rec и Rec·Rec слипаются в одну страту Rec,
    //      страта 1 («ноль + ноль») не задета.
    //   (1 + R)·(1 + R)  -->  1 + Rec  =  RecBody  -->  Nat.
    // Новых чисел сложение не порождает: замыкание Nat по сложению — это Nat.
    type AddEqs = Tuple1[
      Eq[
        PairT[S_T[Var["a"]], Var["b"]],
        PairT[Var["a"], S_T[Var["b"]]]
      ]
    ]

    type RealAddResult = RealQuotient[Add[Nat, Nat], Nat, AddEqs]
    summon[RealAddResult =:= Nat]

    // Промежуточные проверки на уровне FType:
    // слияние дало ровно тело рекурсии => это сама рекурсия (Rec);
    summon[QuotientType[Prod[NatF, NatF], NatF, AddEqs] =:= Rec.type]
    // факторизация Nat по пустому набору уравнений — тоже Nat (а не Option[Nat]).
    summon[QuotientType[NatF, NatF, EmptyTuple] =:= Rec.type]


//    infix type /~[T, Eqs <: Tuple] = ???
//    
//    type NN = Fix[[X] =>> Either[Nat, Add[X, X]]] /~ AddEqs
//    summon[Nat =:= NN]
//    
//    type Z = Fix[[X] =>> Either[Nat, Sub[X, X]]] /~ SubEqs
//    summon[Z =:= Option[(Boolean, Nat)]]
    
