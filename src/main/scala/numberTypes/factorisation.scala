package numberTypes

object factorisation:


  import scala.compiletime.ops.int.*

  object FullKnuthBendixTypeLevel:

    // =========================================================================
    // 1. ЯЗЫК ТЕРМОВ И УРАВНЕНИЙ (для описания произвольной эквивалентности)
    // =========================================================================
    sealed trait Term

    case class Var[Name <: String]() extends Term // Переменная (a, b, x...)

    case object UnitT extends Term // Константа 1 (Z / Unit)

    case class S_T[A <: Term]() extends Term // Конструктор S(x) (шаг рекурсии)

    case class PairT[A <: Term, B <: Term]() extends Term // Конструктор пары (A, B)

    // Ненаправленное уравнение L ~ R и направленное правило переписывания L -> R
    case class Eq[L <: Term, R <: Term]()

    case class Rule[L <: Term, R <: Term]()

    // =========================================================================
    // 2. МЕРА ТЕРМОВ И ОРИЕНТАЦИЯ (LPO-упрощение: вес и глубина терма)
    // =========================================================================
    type Weight[T <: Term] <: Int = T match
      case Var[_] => 1
      case UnitT.type => 1
      case S_T[a] => 1 + Weight[a]
      case PairT[a, b] => 1 + Weight[a] + Weight[b]

    // Ориентация уравнения: тяжелый терм идет в LHS, легкий — в RHS
    type Orient[E] = E match
      case Eq[l, r] =>
        (Weight[l] > Weight[r]) match
          case true => Rule[l, r]
          case false =>
            (Weight[r] > Weight[l]) match
              case true => Rule[r, l]
              case false => Nothing // Неориентируемое уравнение (например, коммутативность)

    type OrientAll[Eqs <: Tuple] <: Tuple = Eqs match
      case EmptyTuple => EmptyTuple
      case h *: t => Orient[h] *: OrientAll[t]

    // =========================================================================
    // 3. ПОДСТАНОВКИ И УНИФИКАЦИЯ НА УРОВНЕ ТИПОВ
    // =========================================================================
    case class Bind[V <: String, T <: Term]() // V -> T

    type Lookup[V <: String, Sub <: Tuple] <: Term = Sub match
      case EmptyTuple => Var[V]
      case Bind[V, t] *: _ => t
      case _ *: tail => Lookup[V, tail]

    type ApplySubst[T <: Term, Sub <: Tuple] <: Term = T match
      case Var[v] => Lookup[v, Sub]
      case UnitT.type => UnitT.type
      case S_T[a] => S_T[ApplySubst[a, Sub]]
      case PairT[a, b] => PairT[ApplySubst[a, Sub], ApplySubst[b, Sub]]

    // Унификация двух термов: возвращает Option[Subst] (или EmptyTuple / Nothing при неудаче)
    type Unify[T1 <: Term, T2 <: Term, Sub <: Tuple] <: Tuple | Nothing =
      (ApplySubst[T1, Sub], ApplySubst[T2, Sub]) match
        case (a, a) => Sub
        case (Var[v], t) => Bind[v, t] *: Sub
        case (t, Var[v]) => Bind[v, t] *: Sub
        case (S_T[a], S_T[b]) => Unify[a, b, Sub]
        case (PairT[a1, b1], PairT[a2, b2]) =>
          Unify[a1, a2, Sub] match
            case Nothing => Nothing
            case sub1 <:< Tuple => Unify[b1, b2, sub1]
        case _ => Nothing

    // =========================================================================
    // 4. ПЕРЕПИСЫВАНИЕ (НОРМАЛИЗАЦИЯ ТЕРМОВ) И ПОИСК КРИТИЧЕСКИХ ПАР
    // =========================================================================
    // Применение одного правила R к корню терма T
    type RewriteRoot[T <: Term, R] <: Term = R match
      case Rule[lhs, rhs] =>
        Unify[lhs, T, EmptyTuple] match
          case Nothing => T
          case sub <:< Tuple => ApplySubst[rhs, sub]

    // Один шаг редукции по всему дереву терма T правилом R
    type RewriteStep[T <: Term, R] <: Term = RewriteRoot[T, R] match
      case T =>
        T match
          case S_T[a] => S_T[RewriteStep[a, R]]
          case PairT[a, b] => PairT[RewriteStep[a, R], RewriteStep[b, R]]
          case _ => T
      case rewritten => rewritten

    // Нормализация терма T всем набором правил до неподвижной точки
    type NormalizeAll[T <: Term, Rules <: Tuple] <: Term = Rules match
      case EmptyTuple => T
      case r *: tail =>
        RewriteStep[T, r] match
          case T => NormalizeAll[T, tail]
          case rewritten => NormalizeAll[rewritten, Rules]

    // Поиск перекрытия (критической пары) между двумя правилами R1 и R2
    // Проверяем перекрытие R1 с корнем R2 и его прямыми подтермами
    type CriticalPair[R1, R2] <: Tuple = (R1, R2) match
      case (Rule[l1, r1], Rule[l2, r2]) =>
        Unify[l1, l2, EmptyTuple] match
          case sub <:< Tuple => Tuple1[Eq[ApplySubst[r1, sub], ApplySubst[r2, sub]]]
          case Nothing =>
            l2 match
              case S_T[inner] =>
                Unify[l1, inner, EmptyTuple] match
                  case sub <:< Tuple => Tuple1[Eq[S_T[ApplySubst[r1, sub]], ApplySubst[r2, sub]]]
                  case Nothing => EmptyTuple
                  case _ => EmptyTuple

    // Сбор всех критических пар для правила R со списком правил
    type AllCritPairsFor[R, Rules <: Tuple] <: Tuple = Rules match
      case EmptyTuple => EmptyTuple
      case h *: tail => Tuple.Concat[CriticalPair[R, h], AllCritPairsFor[R, tail]]

    type AllCritPairs[Rules <: Tuple, All <: Tuple] <: Tuple = Rules match
      case EmptyTuple => EmptyTuple
      case h *: tail => Tuple.Concat[AllCritPairsFor[h, All], AllCritPairs[tail, All]]

    // Фильтрация и нормализация новых уравнений: оставляем только нетривиальные (L != R)
    type ProcessNewEqs[Eqs <: Tuple, Rules <: Tuple] <: Tuple = Eqs match
      case EmptyTuple => EmptyTuple
      case Eq[l, r] *: tail =>
      (NormalizeAll[l, Rules], NormalizeAll[r, Rules]) match
        case (same, same) => ProcessNewEqs[tail, Rules]
        case (nl, nr) => Orient[Eq[nl, nr]] *: ProcessNewEqs[tail, Rules]

    // Основной цикл пополнения Кнута — Бендикса до стабилизации набора правил
    type CompleteLoop[Rules <: Tuple] <: Tuple =
      ProcessNewEqs[AllCritPairs[Rules, Rules], Rules] match
        case EmptyTuple => Rules
        case newRules => CompleteLoop[Tuple.Concat[Rules, newRules]]

    type KnuthBendix[Eqs <: Tuple] = CompleteLoop[OrientAll[Eqs]]

    // =========================================================================
    // 5. АЛГЕБРА ПОЛИНОМИАЛЬНЫХ ФУНКТОРОВ И ПОСТРОЕНИЕ ИТОГОВОГО ТИПА
    // =========================================================================
    sealed trait FType

    case object Zero extends FType // 0 (Nothing)

    case object One extends FType // 1 (Unit)

    case object Rec extends FType // Рекурсивная переменная X

    case class Sum[A <: FType, B <: FType]() extends FType // A + B

    case class Prod[A <: FType, B <: FType]() extends FType // A * B

    // Подстановка функтора Body вместо Rec (один шаг разворачивания рекурсии)
    type SubstRec[T <: FType, Body <: FType] <: FType = T match
      case Rec.type => Body
      case Sum[a, b] => Sum[SubstRec[a, Body], SubstRec[b, Body]]
      case Prod[a, b] => Prod[SubstRec[a, Body], SubstRec[b, Body]]
      case _ => T

    // Разворачивание рекурсивного типа на заданную глубину K
    type Unroll[T <: FType, Body <: FType, Depth <: Int] <: FType = Depth match
      case 0 => T
      case 1 => T
      case _ => Unroll[SubstRec[T, Body], Body, Depth - 1]

    // Максимальная глубина конструктора S_T в левых частях правил
    type TermDepth[T <: Term] <: Int = T match
      case S_T[a] => 1 + TermDepth[a]
      case PairT[a, b] => Max[TermDepth[a], TermDepth[b]]
      case _ => 0

    type MaxRulesDepth[Rules <: Tuple] <: Int = Rules match
      case EmptyTuple => 1
      case Rule[lhs, _] *: t => Max[TermDepth[lhs], MaxRulesDepth[t]]

    // Трансляция левой части правила (Term) в паттерн функтора (FType)
    type TermToPattern[T <: Term] <: FType = T match
      case Var[_] => Rec.type // Переменная матчатся с любым поддеревом (Rec)
      case UnitT.type => One.type
      case S_T[a] => TermToPattern[a] // В типе Nat = 1 + Rec, ветка S(a) — это Rec!
      case PairT[a, b] => Prod[TermToPattern[a], TermToPattern[b]]

    // Раскрытие скобок (дистрибутивность: (A + B) * C => A*C + B*C)
    type Distribute[T <: FType] <: FType = T match
      case Prod[Sum[a, b], c] => Sum[Distribute[Prod[a, c]], Distribute[Prod[b, c]]]
      case Prod[a, Sum[b, c]] => Sum[Distribute[Prod[a, b]], Distribute[Prod[a, c]]]
      case Sum[a, b] => Sum[Distribute[a], Distribute[b]]
      case Prod[a, b] =>
        (Distribute[a], Distribute[b]) match
          case (Sum[x, y], r) => Distribute[Prod[Sum[x, y], r]]
          case (l, Sum[x, y]) => Distribute[Prod[l, Sum[x, y]]]
          case (l, r) => Prod[l, r]
      case _ => T

    // Вычитание одного запрещенного паттерна из ДНФ типа
    type SubtractOne[T <: FType, Pat <: FType] <: FType = T match
      case Sum[a, b] => Sum[SubtractOne[a, Pat], SubtractOne[b, Pat]]
      case Pat => Zero.type
      case _ => T

    // Вычитание всех левых частей пополненной системы правил
    type SubtractRules[T <: FType, Rules <: Tuple] <: FType = Rules match
      case EmptyTuple => T
      case Rule[lhs, _] *: t => SubtractRules[SubtractOne[T, TermToPattern[lhs]], t]

    // Алгебраическое упрощение (0 + X = X, 1 * X = X, 0 * X = 0)
    type SimplifyStep[T <: FType] <: FType = T match
      case Sum[Zero.type, a] => SimplifyStep[a]
      case Sum[a, Zero.type] => SimplifyStep[a]
      case Prod[Zero.type, _] => Zero.type
      case Prod[_, Zero.type] => Zero.type
      case Prod[One.type, a] => SimplifyStep[a]
      case Prod[a, One.type] => SimplifyStep[a]
      case Sum[a, b] => Sum[SimplifyStep[a], SimplifyStep[b]]
      case Prod[a, b] => Prod[SimplifyStep[a], SimplifyStep[b]]
      case _ => T

    type Simplify[T <: FType] <: FType = SimplifyStep[T] match
      case T => T
      case next => Simplify[next]

// =========================================================================
// 6. ИТОГОВЫЙ УНИВЕРСАЛЬНЫЙ ОПЕРАТОР ФАКТОРИЗАЦИИ ТИПА
// =========================================================================
    type QuotientType[InitType <: FType, RecBody <: FType, Eqs <: Tuple] =
      KnuthBendix[Eqs] match
        case rules => Simplify[
          SubtractRules[
            Distribute[Unroll[InitType, RecBody, MaxRulesDepth[rules]]],
            rules
          ]
        ]
    // =========================================================================
    // 7. ПРОВЕРКА РАБОТОСПОСОБНОСТИ НА ДВУХ РАЗНЫХ ЭКВИВАЛЕНТНОСТЯХ
    // =========================================================================
    // Определение функтора натуральных чисел: Nat = 1 + Rec
    type NatF = Sum[One.type, Rec.type]
    // --- ТЕСТ 1: Замыкание по вычитанию: (S(a), S(b)) ~ (a, b) ---
    // Исходный тип: Nat * Nat
    type SubEqs = Tuple1[
      Eq[
        PairT[S_T[Var["a"]], S_T[Var["b"]]],
        PairT[Var["a"], Var["b"]]
      ]
    ]
    type ZType = QuotientType[Prod[NatF, NatF], NatF, SubEqs]
    // Компилятор сам выводит, что (1 + Rec) * (1 + Rec) / ((S(a), S(b)) ~ (a, b))
    // превращается в (1 + Rec) + Rec === Nat + Nat === 2 * Nat!
    summon[ZType =:= Sum[Sum[One.type, Rec.type], Rec.type]]
    // --- ТЕСТ 2: Факторизация по модулю 2: S(S(x)) ~ x ---
    // Исходный тип: бесконечный Nat
    // Проверяем также пополнение критических пар: добавим избыточное правило S(S(S(x))) ~ S(x)
    type Mod2Eqs = (
      Eq[S_T[S_T[Var["x"]]], Var["x"]],
        Eq[S_T[S_T[S_T[Var["y"]]]], S_T[Var["y"]]]
      )
    // Глубина 2: Unroll разворачивает 1 + Rec в 1 + (1 + Rec).
    // Внутренний Rec соответствует S(S(x)) и полностью вырезается правилом!
    type BoolType = QuotientType[NatF, NatF, Mod2Eqs]
    // Компилятор доказывает, что бесконечный тип Nat схлопнулся в конечный 1 + 1 (Boolean)!
    summon[BoolType =:= Sum[One.type, One.type]]
