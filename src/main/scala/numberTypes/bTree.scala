package numberTypes

import numberTypes.*
import numberTypes.piTypes.ℿ
import numberTypes.wellFoundedNew.*

import scala.Tuple.++
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

    def rec[A, R] = ind[A, Const[R]]


  object test:

    println("==================================================")
    println("     БИНАРНЫЕ ДЕРЕВЬЯ (T = 1 + A × T × T)        ")
    println("==================================================")

    // Построение деревьев
    val leaf = Tree.leaf[Int]
    val tNode1 = Tree.node(1, leaf, leaf)
    val tNode2 = Tree.node(2, leaf, leaf)
    val tNodeRoot = Tree.node(0, tNode1, tNode2)

    // ===== Подсчёт листьев через зависимую индукцию =====
    val leafCount = Tree.rec[Int, Int](1, [TL, TR] => _ => l => r => l + r)

    println("--- Подсчёт листьев ---")
    println(s"leaves(leaf)        = ${leafCount(leaf)}") // 1
    println(s"leaves(node(l,r))   = ${leafCount(tNode1)}") // 2
    println(s"leaves(root)        = ${leafCount(tNodeRoot)}") // 4

    // ===== Семейство типов: кортеж листьев дерева =====
    type LeafTupleFamily[I <: Tree[Int]] <: Tuple = I match
      case 𝕎.sup[Option[Int], TreeArity[Int], Option[Nothing], Nothing] => EmptyTuple
      case 𝕎.sup[Option[Int], TreeArity[Int], Some[Int], t] =>
        Int *: (LeafTupleFamily[t] ++ LeafTupleFamily[t])

    // ===== Накопление листьев в кортеже (зависимый мотив) =====
    def accumLeaves = Tree.ind[Int, LeafTupleFamily](
      leafCase = EmptyTuple,
      nodeCase = [TL <: Tree[Int], TR <: Tree[Int]] => a => lTup => rTup =>
        (a *: (lTup ++ rTup))
          .asInstanceOf[LeafTupleFamily[TreeNode[Int][TL, TR]]]
    )

    // ===== Проверки подтипов =====
    summon[tNode1.type <:< Tree[Int]]
    summon[tNodeRoot.type <:< TreeNode[Int][tNode1.type, tNode2.type]]
    
    val r1 = accumLeaves(leaf): EmptyTuple
    val r2 = accumLeaves(tNode1)//: Tuple1[Int]
    val r3 = accumLeaves(tNodeRoot)//: (Int, Int, Int)

    println("--- Накопление листьев в кортеже ---")
    println(s"leaves(tLeaf)       = $r1") // ()
    println(s"leaves(tNode1)      = $r2") // (Some(1))
    println(s"leaves(tNodeRoot)   = $r3") // (Some(0), Some(1), Some(2))

    println("==================================================")

  end test