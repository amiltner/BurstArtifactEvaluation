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
  
def div2(n: Nat): Nat =
  n match {
    case Z => Z
    case S(Z) => Z
    case S(S(n)) => S(div2(n))
  }

def inc(n:Nat):Nat = S(n)
  
def tree_map(f:Nat => Nat,t: NatTree): NatTree = { choose { (out:NatTree) =>

  def plus(n1:Nat,n2:Nat):Nat =
    n1 match {
      case Z => n2
      case S(n1p) => S(plus(n1p,n2))
    }

  def sum(nl:NatList):Nat =
    nl match {
      case Nil => Z
      case Cons(h,t) => plus(h,(sum(t)))
    }

  def size(l:NatList):Nat =
    l match {
      case Nil => Z
      case Cons(_,t) => S(size(t))
    }

  def is_zero(l:NatList) : Boolean =
    l match {
      case Nil => true
      case Cons(h,t) => (h==Z) && (is_zero(t))
    }

  def append(l1:NatList,l2:NatList) : NatList =
    l1 match {
      case Nil => l2
      case Cons(h,t) => Cons(h,append(t,l2))
    }

  def inorder(t:NatTree) : NatList =
    t match {
      case Leaf => Nil
      case Node(l,x,r) => append((inorder(l)),(Cons (x,inorder(r))))
    }

  def zero(n:Nat) : Nat = Z

  size(inorder(t)) == size(inorder(out)) &&
  (if (f == ((x:Nat) => zero(x))) { is_zero(inorder(out)) } else { if (f == ((x:Nat) => inc(x))) { sum(inorder(out))==plus(sum(inorder(t)),size(inorder(t))) } else {true} })

} }

}