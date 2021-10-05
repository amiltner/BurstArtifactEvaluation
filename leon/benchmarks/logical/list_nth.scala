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
  
def list_nth(xs: NatList, n: Nat): Nat = { choose { (out:Nat) => 

   def len(xs: NatList): Int =
      xs match {
        case Nil => 0
        case Cons(h,t) => len(t) + 1
      }

    def nat_to_int(x: Nat): Int =
      x match {
        case Z => 0
        case S(m) => nat_to_int(m) + 1
      }

    def hd(xs: NatList): Nat =
      xs match {
        case Nil => Z
        case Cons(h,t) => h
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

    if (len(xs) < nat_to_int(n)) {
      (out == Z)
    } else {
      if (len(xs) == nat_to_int(n)+1) {
        out == list_last(xs)
      } else {
        true
      }

} }

}
}