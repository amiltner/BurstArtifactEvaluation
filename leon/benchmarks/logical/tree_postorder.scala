import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Blah {
  
sealed abstract class Nat
case class S(nat: Nat) extends Nat
case object Z extends Nat
  
sealed abstract class NatList
case class Cons(head: Nat, tail: NatList) extends NatList
case object Nil extends NatList
  
sealed abstract class NatTree
case object Leaf extends NatTree
case class Node(left: NatTree, n: Nat, right: NatTree) extends NatTree
  
def list_append(l1: NatList, l2: NatList): NatList =
  l1 match {
    case Nil              => l2
    case Cons(head, tail) => Cons (head, list_append(tail, l2))
  }

def tree_postorder(t: NatTree): NatList = { choose { (out:NatList) => 

t match {
  case Leaf => out == Nil
  case Node(Node (Leaf, a, Leaf), b, Leaf) => out == Cons (a, Cons (b, Nil))
  case Node(Leaf, a, Node (Leaf, b, Leaf)) => out == Cons (b, Cons (a, Nil))
  case _ => true
}

} }

}