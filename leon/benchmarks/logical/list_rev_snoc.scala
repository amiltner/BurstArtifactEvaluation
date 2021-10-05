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
  
sealed abstract class NatList
case class Cons(head: Nat, tail: NatList) extends NatList
case object Nil extends NatList
  
def list_snoc(xs: NatList, n: Nat): NatList =
  xs match {
    case Nil             => Cons (n, Nil)
    case Cons(head,tail) => Cons (head, list_snoc(tail,n))
  }
  
def list_rev_snoc(xs: NatList): NatList = { choose { (out:NatList) => 

   def len(xs: NatList): Int =
      xs match {
        case Nil => 0
        case Cons(h,t) => len(t) + 1
      }

   def list_last(xs : NatList): Nat = {
     xs match {
       case Nil =>
         Z
       case Cons(head, tail) =>
         tail match {
           case Nil => head
           case Cons(head2,tail2) => list_last(tail)
         }
     }
   }

  xs match {
    case Nil => out == Nil
    case Cons(h,t) =>
      len(xs)==len(out) && (h == list_last(out))
  }

} }

}