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

def tree_preorder(t: NatTree): NatList = { choose { (out:NatList) =>

def to_pair_set(n:Nat,ns:NatList) : Set[(Nat,Nat)] =
  ns match {
    case Nil => Set.empty[(Nat,Nat)]
    case Cons(h,t) => Set((n,h)) ++ to_pair_set(n,t)
  }

def to_pair_set_rev(n:Nat,ns:NatList) : Set[(Nat,Nat)] =
  ns match {
    case Nil => Set.empty[(Nat,Nat)]
    case Cons(h,t) => Set((h,n)) ++ to_pair_set_rev(n,t)
  }

def get_afters(ns:NatList) : Set[(Nat,Nat)] =
  ns match {
    case Nil => Set.empty[(Nat,Nat)]
    case Cons(h,t) => to_pair_set(h,t) ++ get_afters(t)
  }

def get_tree_afters(nt:NatTree,nl:NatList) : Set[(Nat,Nat)] =
  nt match {
    case Leaf => Set.empty[(Nat,Nat)]
    case Node(l,x,r) =>
      get_tree_afters(l,Cons(x,nl)) ++ get_tree_afters(r,Cons(x,nl)) ++
      to_pair_set_rev(x,nl)
  }

  def tree_content(t:NatTree) : Set[Nat] = t match {
    case Leaf => Set.empty[Nat]
    case Node(l,x,r) => Set(x) ++ tree_content(l) ++ tree_content(r)
  }

  def list_content(l: NatList): Set[Nat] = l match {
    case Nil => Set.empty[Nat]
    case Cons(i, t) => Set(i) ++ list_content(t)
  }

get_tree_afters(t,Nil) == get_afters(out) && tree_content(t) == list_content(out)

} }

}