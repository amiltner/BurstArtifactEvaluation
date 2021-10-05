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

def zero(n:Nat) : Nat = Z

def inc(n:Nat) : Nat = S(n)

def list_fold(f:(Nat,Nat)=>Nat,x:Nat,xs: NatList): Nat = { choose { (out:Nat) => 

  def sum(n1:Nat,n2:Nat):Nat =
    n1 match {
      case Z => n2
      case S(n1p) => S(sum(n1p,n2))
    }

  def zero(n1:Nat,n2:Nat):Nat = Z

  def count(n1:Nat,n2:Nat):Nat = S(n1)

  def size(l:NatList):Nat =
    l match {
      case Nil => Z
      case Cons(_,t) => S(size(t))
    }

    (if (f == ((x1:Nat,x2:Nat) => zero(x1,x2))) {
      (x == Z) ==> (out == Z)
    } else {
      if (f == ((x1:Nat,x2:Nat) => count(x1,x2))) {
        out==sum(size(xs),x)
      } else {
        if (f == ((x1:Nat,x2:Nat) => sum(x1,x2))) {
          xs match {
            case Cons(a,Cons(b,Cons(c,Nil))) =>
              out == sum (x,(sum(a,sum(b,c))))
          }
        } else {
          true
        }
      }
    })

} }

}