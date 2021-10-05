import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Blah {
  
sealed abstract class Nat
case class S(nat: Nat) extends Nat
case object Z extends Nat
  
sealed abstract class Cmp
case object LT extends Cmp
case object EQ extends Cmp
case object GT extends Cmp

sealed abstract class Boolean
case object T extends Boolean
case object F extends Boolean

sealed abstract class NatTree
case object Leaf extends NatTree
case class Node(left: NatTree, n: Nat, right: NatTree) extends NatTree
  
def nat_compare(n1: Nat, n2: Nat): Cmp =
  n1 match {
    case Z =>
      n2 match {
        case Z    => EQ
        case S(_) => LT
      }
    case S(m1) =>
      n2 match {
        case Z     => GT
        case S(m2) => nat_compare(m1, m2)
      }
  }
  
def tree_binsert(t: NatTree,x: Nat): NatTree = { choose { (out:NatTree) => 

   def in_order(tr: NatTree): Boolean =
      tr match {
          case Leaf => T
          case Node(Node (l1, a, r1), b, Leaf) =>
            if (nat_compare(a,b) != GT) {
                (in_order(Node (l1, a, r1)))
            } else { F }
          case Node(Leaf, a, Node (l2, b, r2)) =>
            if (nat_compare(a,b) != LT) {
                (in_order(Node (l2, a, r2)))
            } else { F }
          case Node(Node (l1, b, r1), a, Node (l2, c, r2)) =>
            if ((nat_compare(a,b) != LT) && (nat_compare(a,c) != LT)) {
                if (in_order(Node (l1, b, r1)) == T) {
                    (in_order(Node (l1, b, r1)))
                } else { F }
            } else { F }
      }

    def contains(tr: NatTree, n: Nat): Boolean =
        tr match {
            case Leaf => F
            case Node(l,x,r) =>
                if (x == n) { T }
                else {
                    if (contains(l,n) == T) { T }
                    else { contains(r,n) }
                }
        }

    def size_values(tr: NatTree): Int =
        tr match {
            case Leaf => 0
            case Node(l,x,r) => size_values(l) + size_values(r) + 1
        }

  def tree_content(t:NatTree) : Set[Nat] = t match {
    case Leaf => Set.empty[Nat]
    case Node(l,x,r) => Set(x) ++ tree_content(l) ++ tree_content(r)
  }

    ((in_order(t) == T) ==> (in_order(out) == T)) && ((tree_content(t) ++ Set(x)) subsetOf tree_content(out))

} }

}