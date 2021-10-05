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
  
sealed abstract class BooleanList
case class Cons(head: Boolean, tail: BooleanList) extends BooleanList
case object Nil extends BooleanList
  
def list_append(l1: BooleanList, l2: BooleanList): BooleanList =
  l1 match {
    case Nil              => l2
    case Cons(head, tail) => Cons (head, list_append(tail, l2))
  }

def tree_collect_leaves(t: BooleanTree): BooleanList = { choose { (out:BooleanList) => 

  t match {
    case Leaf => out == Nil
    case Node(l,x,r) =>
      l match {
        case Leaf =>
          r match {
            case Leaf => out == Cons(x,Nil)
            case Node(l2,x2,r2) => true
          }
        case Node(l1,x1,r1) =>
          r match {
            case Leaf => true
            case Node(l2,x2,r2) =>
              (l1 == Leaf && r1 == Leaf && l2 == Leaf && r2 == Leaf) ==>
              (out == Cons(x1, Cons(x, Cons(x2,Nil))))
          }
      }
  }

} }

}