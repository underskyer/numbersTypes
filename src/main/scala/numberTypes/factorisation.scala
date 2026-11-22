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
  type QuotientType[InitType <: FType, RecBody <: FType, Eqs <: Tuple] =
    QuotientWithRules[InitType, RecBody, KnuthBendix[Eqs]]

  type QuotientWithRules[InitType <: FType, RecBody <: FType, Rules <: Tuple] =
    Simplify[
      SubtractRules[
        Distribute[Unroll[InitType, RecBody, MaxRulesDepth[Rules]]],
        Rules
      ]
    ]

  // =========================================================================
  // 5.5. РЕАЛЬНЫЕ ТИПЫ И ТРАНСЛЯЦИЯ FType <-> РЕАЛЬНЫЙ ТИП
  // =========================================================================

  // Реальный (не фантомный) Nat.
  sealed trait Nat
  case object Z extends Nat
  case class S(prev: Nat) extends Nat

  // Реальная пара для задачи Sub[Nat, Nat] ~ (Nat, Nat).
  case class Sub[A, B](a: A, b: B)

  // Перевод реального типа в фантомный FType.
  type ToFType[T] <: FType = T match
    case Unit          => One.type
    case Nat           => Sum[One.type, Rec.type]
    case Boolean       => Sum[One.type, One.type]
    case (a, b)        => Prod[ToFType[a], ToFType[b]]
    case Sub[a, b]     => Prod[ToFType[a], ToFType[b]]
    case Either[a, b]  => Sum[ToFType[a], ToFType[b]]
    case Option[a]     => Sum[One.type, ToFType[a]]

  // Правая ассоциативность сумм: (a + b) + c -> a + (b + c).
  // Без этого FromFType не "увидит" в Sum[Sum[One, Rec], Rec] шаблон
  // Sum[One, Sum[Rec, Rec]] = Option[(Boolean, Nat)].
  type ReassocSum[T <: FType] <: FType = T match
    case Sum[Sum[a, b], c] => ReassocSum[Sum[a, Sum[b, c]]]
    case Sum[a, b]         => Sum[ReassocSum[a], ReassocSum[b]]
    case _                 => T

  // Перевод FType обратно в реальный тип.
  type FromFType[T <: FType] <: Any = T match
    case Zero.type                => Nothing
    case One.type                 => Unit
    case Rec.type                 => Nat
    case Sum[One.type, One.type]  => Boolean
    case Sum[Rec.type, Rec.type]  => (Boolean, Nat)
    case Sum[One.type, x]         => Option[FromFType[x]]
    case Sum[x, One.type]         => Option[FromFType[x]]
    case Sum[a, b]                => Either[FromFType[a], FromFType[b]]
    case Prod[a, b]               => (FromFType[a], FromFType[b])

  // Итоговый оператор: реальный тип -> FType -> факторизация -> реальный тип.
  type RealQuotient[Init, RecBody, Eqs <: Tuple] =
    FromFType[ReassocSum[QuotientType[ToFType[Init], ToFType[RecBody], Eqs]]]

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
    // ТЕСТ 3: Факторизация РЕАЛЬНОГО типа Sub[Nat, Nat] ~ (Nat, Nat)
    // =========================================================================
    // Вход  : реальный тип Sub[Nat, Nat].
    // Отношение: (S a, S b) ~ (a, b)  (то есть (a, b) ~ (a - k, b - k)).
    // Классы: [(0,0)], [(m,0)]_{m>0}, [(0,n)]_{n>0}  =>  1 + 2·Nat.
    // Выход : Option[(Boolean, Nat)].
    type RealSubEqs = Tuple1[Eq[
      PairT[S_T[Var["a"]], S_T[Var["b"]]],
      PairT[Var["a"], Var["b"]]
    ]]

    type RealResult = RealQuotient[Sub[Nat, Nat], Nat, RealSubEqs]

    // Проверка: результат действительно Option[(Boolean, Nat)].
    summon[RealResult =:= Option[(Boolean, Nat)]]
