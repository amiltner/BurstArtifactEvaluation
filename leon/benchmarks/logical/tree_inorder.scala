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

def tree_inorder(t: NatTree): NatList = { choose { (out:NatList) => 

  def tree_content(t:NatTree) : Set[Nat] = t match {
    case Leaf => Set.empty[Nat]
    case Node(l,x,r) => Set(x) ++ tree_content(l) ++ tree_content(r)
  }

  def list_content(l: NatList): Set[Nat] = l match {
    case Nil => Set.empty[Nat]
    case Cons(i, t) => Set(i) ++ list_content(t)
  }

  def nat_to_int(x: Nat): Int =
    x match {
      case Z => 0
      case S(m) => nat_to_int(m) + 1
    }

  def list_sorted(xs: NatList) : Boolean =
       xs match {
         case Nil => true
         case Cons(h,t) => t match {
                           case Nil => list_sorted(t)
                           case Cons(t1,t2) =>
                                   if (((nat_to_int(h)) <= (nat_to_int(t1)))) {
                                       list_sorted(t)
                                   } else {
                                       false
                                   }
                       }
       }

  def get_min(t: NatTree) : Int =
    t match {
      case Leaf => Int.MaxValue
      case Node(l,x,r) =>
        def z:Int = if (get_min(l) < nat_to_int(x)) { get_min(l) } else { nat_to_int(x) }
        if (get_min(r) < z) { get_min(r) } else { z }
    }

  def get_max(t: NatTree) : Int =
    t match {
      case Leaf => Int.MinValue
      case Node(l,x,r) =>
        def z:Int = if (get_max(l) > nat_to_int(x)) { get_max(l) } else { nat_to_int(x) }
        if (get_max(r) > z) { get_max(r) } else { z }
    }

  def is_bst(t:NatTree) : Boolean =
    t match {
      case Leaf => true
      case Node(l,x,r) => get_max(l) < nat_to_int(x) && get_min(r) > nat_to_int(x) && is_bst(l) && is_bst(r)
    }

  (tree_content(t) == list_content(out)) && (!(is_bst(t)) || list_sorted(out))

} }

}