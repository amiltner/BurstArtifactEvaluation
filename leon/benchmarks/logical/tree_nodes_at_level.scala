import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Blah {
  
sealed abstract class Boolean
case object T extends Boolean
case object F extends Boolean
  
sealed abstract class BooleanTree
case object Leaf extends BooleanTree
case class Node(left: BooleanTree, n: Boolean, right: BooleanTree) extends BooleanTree
  
sealed abstract class Nat
case class S(nat: Nat) extends Nat
case object Z extends Nat
  
def nat_add(n1: Nat, n2: Nat): Nat =
  n1 match {
    case Z    => n2
    case S(m) => S (nat_add(m, n2))
  }

def tree_nodes_at_level(t: BooleanTree,n:Nat): Nat = { choose { (out:Nat) => 

  t match {
    case Leaf => out == Z
    case Node(Leaf,_,Leaf) =>
      n match {
        case Z => out == S(Z)
        case _ => out == Z
      }
    case Node(Node(Leaf,_,Leaf),_,Leaf) =>
      n match {
        case Z => out == S(Z)
        case S(Z) => out == S(Z)
        case _ => out == Z
      }
    case Node(Leaf,_,Node(Leaf,_,Leaf)) =>
      n match {
        case Z => out == S(Z)
        case S(Z) => out == S(Z)
        case _ => out == Z
      }
    case _ => true
}

} }

}