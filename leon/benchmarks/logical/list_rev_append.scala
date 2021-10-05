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
  
def list_append(l1: NatList, l2: NatList): NatList =
  l1 match {
    case Nil              => l2
    case Cons(head, tail) => Cons (head, list_append(tail, l2))
  }

def list_rev_append(l1: NatList): NatList = { choose { (out:NatList) => 

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

  l1 match {
    case Nil => out == Nil
    case Cons(h,t) =>
      len(l1)==len(out) && (h == list_last(out))
  }

} }

}