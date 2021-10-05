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
  
sealed abstract class NatListList
case class LCons(head: NatList, tail: NatListList) extends NatListList
case object LNil extends NatListList
  
def list_append(l1: NatList, l2: NatList): NatList =
  l1 match {
    case Nil              => l2
    case Cons(head, tail) => Cons (head, list_append(tail, l2))
  }

def list_concat(xss: NatListList): NatList = { choose { (out:NatList) => 

   def contained_in(x:Nat,xs:NatList) : Boolean =
      xs match {
        case Nil => false
        case Cons(h,t) =>
          if (h == x) {
            true
          } else {
            contained_in(x,t)
          }
      }

    def full_contained_in(xs:NatList,ys:NatList) : Boolean =
      xs match {
        case Nil => true
        case Cons(h,t) =>
          if (contained_in(h,ys)) {
            full_contained_in(t,ys)
          } else {
            false
          }
      }

    def all_full_contained(xss:NatListList,xs:NatList) : Boolean =
        xss match {
            case LNil => true
            case LCons(h,t) =>
                if (full_contained_in(h,xs)) {
                    all_full_contained(t,xs)
                } else {
                  false
                }
        }

    all_full_contained(xss,out)

} }

}