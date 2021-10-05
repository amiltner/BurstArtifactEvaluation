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
  
sealed abstract class Cmp
case object LT extends Cmp
case object EQ extends Cmp
case object GT extends Cmp
  
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
  
def list_sorted_insert(xs: NatList, n: Nat): NatList = { choose { (out:NatList) => 
   def list_sorted(xs: NatList) : Boolean =
        xs match {
          case Nil => true
          case Cons(h,t) => t match {
                            case Nil => list_sorted(t)
                            case Cons(t1,t2) =>
                                    if (nat_compare(h,t1) != GT) {
                                        list_sorted(t)
                                    } else {
                                        false
                                    }
                        }
        }

  def content(l: NatList): Set[Nat] = l match {
    case Nil => Set.empty[Nat]
    case Cons(i, t) => Set(i) ++ content(t)
  }

    ((!(list_sorted(xs))) || list_sorted(out)) && (content(Cons(n,xs)) subsetOf content(out))

} }

}