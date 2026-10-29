package numberTypes

import numberTypes.*
import numberTypes.piTypes.ℿ
import numberTypes.wellFoundedNew.*

import scala.annotation.unchecked.uncheckedVariance

object bTree:

  type TreeArity[A] = [I <: Option[A]] =>> I match
    case Option[Nothing] => Nothing
    case Some[A]         => Boolean
  
  type Tree[A] = 𝕎[Option[A], TreeArity[A]]

  type TreeLeaf[A] = 𝕎.sup[Option[A], TreeArity[A], Option[Nothing], Nothing]
  type TreeNode[A] = [TL <: Tree[A], TR <: Tree[A]] =>> 𝕎.sup[Option[A], TreeArity[A], Some[A], TL | TR] // да, теряется порядок
  
  object Tree:
    def leaf[A]: TreeLeaf[A] = 𝕎.sup[Option[A], TreeArity[A], Option[Nothing], Nothing](None, _ => _.asInstanceOf[Nothing])
    def node[A](a: A, left: Tree[A], right: Tree[A]): TreeNode[A][left.type, right.type] =
      𝕎.sup(Some(a), _ => if _ then right else left)

    def ind[A, R[_ <: Tree[A]]](
      leafCase: R[TreeLeaf[A]],
      nodeCase: [TL <: Tree[A], TR <: Tree[A]] => A => R[TL] => R[TR] => R[TreeNode[A][TL, TR]]
    ): ℿ[Tree[A], R] =
      𝕎.ind[Option[A], TreeArity[A], R]:
        tree => tree match
            case 𝕎.sup(None, _) =>
              _ => leafCase.asInstanceOf[R[tree.type]]
            case 𝕎.sup(optA@Some(a), subtrees) =>
              ih =>
                val left = subtrees(optA)(false.asInstanceOf[TreeArity[A][optA.type]])
                val right = subtrees(optA)(true.asInstanceOf[TreeArity[A][optA.type]])
                
                val leftR = ih(left)
                val rightR = ih(right)
                
                nodeCase[left.type, right.type](a)(leftR)(rightR).asInstanceOf[R[tree.type]]


  object test:

    println("==================================================")
    println("     БИНАРНЫЕ ДЕРЕВЬЯ (T = 1 + A × T × T)        ")
    println("==================================================")

    // ===== Семейство типов: кортеж листьев дерева =====
    // Для TreeLeaf — пустой кортеж, для TreeNode — A *: (левый кортеж) *: (правый кортеж)
    type LeafTupleFamily[+I <: Tree[Option[Int]]] <: Tuple = (I @uncheckedVariance) match
      case 𝕎.sup[Option[Option[Int]], TreeArity[Option[Int]], Option[Nothing], Nothing] => EmptyTuple
      case 𝕎.sup[Option[Option[Int]], TreeArity[Option[Int]], Some[Option[Int]], _] =>
        Option[Int] *: LeafTupleFamily[Tree[Option[Int]]]

    // Построение деревьев
    val leaf = Tree.leaf[Option[Int]]
    val tNode1 = Tree.node(Some(1), leaf, leaf)
    val tNode2 = Tree.node(Some(2), leaf, leaf)
    val tNodeRoot = Tree.node(Some(0), tNode1, tNode2)

    // ===== Подсчёт листьев через зависимую индукцию =====
    type LeafCount = Const[Int]

    val leafCount: ℿ[Tree[Option[Int]], LeafCount] = Tree.ind[Option[Int], LeafCount](
      leafCase = 1,
      nodeCase = [TL, TR] => _ => l => r => l + r
    )

    println("--- Подсчёт листьев ---")
    println(s"leaves(leaf)        = ${leafCount(leaf)}") // 1
    println(s"leaves(node(l,r))   = ${leafCount(tNode1)}") // 2
    println(s"leaves(root)        = ${leafCount(tNodeRoot)}") // 4

    // ===== Накопление листьев в кортеже (зависимый мотив) =====
    type AccumFamily[+I <: Tree[Option[Int]]] <: Tuple = (I @uncheckedVariance) match
      case 𝕎.sup[Option[Option[Int]], TreeArity[Option[Int]], Option[Nothing], Nothing] => EmptyTuple
      case 𝕎.sup[Option[Option[Int]], TreeArity[Option[Int]], Some[Option[Int]], t] =>
        Option[Int] *: LeafTupleFamily[𝕎.sup[Option[Option[Int]], TreeArity[Option[Int]], Some[Option[Int]], t]]

    // Исправленная версия с правильным рекурсивным вызовом
    def accumLeaves[I <: Tree[Option[Int]]](tree: I): Tuple = tree match
      case 𝕎.sup(None, _) => EmptyTuple
      case 𝕎.sup(optA@Some(a), subtrees) =>
        val left = subtrees(optA)(false.asInstanceOf[TreeArity[Option[Int]][optA.type]])
        val right = subtrees(optA)(true.asInstanceOf[TreeArity[Option[Int]][optA.type]])
        a *: accumLeaves(left) ++ accumLeaves(right)

    // ===== Проверки подтипов =====
    summon[tNode1.type <:< Tree[Option[Int]]]
    summon[tNodeRoot.type <:< Tree[Option[Int]]]

    println("--- Накопление листьев в кортеже ---")
    println(s"leaves(tLeaf)       = ${accumLeaves(leaf)}") // ()
    println(s"leaves(tNode1)      = ${accumLeaves(tNode1)}") // (Some(1))
    println(s"leaves(tNodeRoot)   = ${accumLeaves(tNodeRoot)}") // (Some(0), Some(1), Some(2))

    println("==================================================")

  end test