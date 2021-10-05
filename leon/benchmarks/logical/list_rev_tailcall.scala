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
  
def list_rev_tailcall(xs: NatList, acc: NatList): NatList = { choose { (out:NatList) => 

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

   def lastn(xs:NatList,i:Int) : NatList =
     if (i < len(xs)) {
       xs match {
         case Nil => Nil
         case Cons(h,t) => lastn(t,i)
       }
     } else {
       xs
     }

    (len(out) == len(xs) + len(acc)) &&
    (xs match {
      case Nil => true
      case Cons(h,t) => lastn(out,(1+len(acc))) == Cons(h,acc)
    })

} }

}