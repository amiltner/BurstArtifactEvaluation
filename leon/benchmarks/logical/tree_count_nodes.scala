import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Blah {
  
sealed abstract class Nat
case class S(nat: Nat) extends Nat
case object Z extends Nat
  
sealed abstract class NatTree
case object Leaf extends NatTree
case class Node(left: NatTree, n: Nat, right: NatTree) extends NatTree
  
def nat_add(n1: Nat, n2: Nat): Nat =
  n1 match {
    case Z    => n2
    case S(m) => S (nat_add(m, n2))
  }
  
def tree_count_nodes(t: NatTree): Nat = { choose { (out:Nat) => 

   t match {
    case Leaf => out == Z
    case Node(Leaf,x,Leaf) => out == S(Z)
    case Node(Node(Leaf,a,Leaf),x,Leaf) => out == S(S(Z))
    case Node(Leaf,x,Node(Leaf,b,Leaf)) => out == S(S(Z))
    case _ => true
   }

} }

}