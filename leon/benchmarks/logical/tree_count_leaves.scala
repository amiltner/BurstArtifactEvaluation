import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Blah {
  
sealed abstract class Nat
case class S(nat: Nat) extends Nat
case object Z extends Nat
  
sealed abstract class Boolean
case object T extends Boolean
case object F extends Boolean
  
sealed abstract class BooleanTree
case object Leaf extends BooleanTree
case class Node(left: BooleanTree, n: Boolean, right: BooleanTree) extends BooleanTree
  
def nat_add(n1: Nat, n2: Nat): Nat =
  n1 match {
    case Z    => n2
    case S(m) => S (nat_add(m, n2))
  }
  
def tree_count_leaves(t: BooleanTree): Nat = { choose { (out:Nat) => 

   t match {
    case Leaf => out == S(Z)
    case Node(Leaf,x,Leaf) => out == S(S(Z))
    case Node(Node(Leaf,a,Leaf),x,Leaf) => out == S(S(S(Z)))
    case Node(Leaf,x,Node(Leaf,b,Leaf)) => out == S(S(S(Z)))
    case _ => true
   }

} }

}