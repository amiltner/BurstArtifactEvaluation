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
  
def list_snoc(xs: NatList, n: Nat): NatList = { choose { (out:NatList) => 

   def len(xs: NatList): Nat =
      xs match {
        case Nil => Z
        case Cons(h,t) => S(len(t))
      }

    def hd(xs: NatList): Nat =
      xs match {
        case Nil => Z
        case Cons(h,t) => h
      }

    def tl(xs: NatList): Nat =
      xs match {
        case Nil => Z
        case Cons(h,t) =>
             if (t == Nil) { h }
             else { tl(t) }
      }

    (len(out) == S(len(xs))) && (tl(out) == n)

} }

}