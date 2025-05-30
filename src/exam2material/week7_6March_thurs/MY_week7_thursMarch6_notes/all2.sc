// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

//∀ x (P(x) ⋀ Q(x))    equivalent to     (∀ x P(x)) ⋀ (∀ x Q(x))
//prove two directions, taking turns which is the premise and
//which is the conclusion

@pure def all2part1[T](P: T=>B @pure, Q: T=>B @pure): Unit = {
  Deduce(
    (
      ∀((x: T) => (P(x) & Q(x)))
    )
      |-
    (
       ∀((x: T) => P(x)) & ∀((x: T) => Q(x))
    )
    Proof(
      1 (∀((x: T) => (P(x) & Q(x)))) by Premise,

      //Goal: ∀((x: T) => P(x))
      2 Let((random: T) => SubProof(
        3 (P(random) & Q(random)) by AllE[T](1),
        4 (P(random)) by AndE1(3),
        
        //Goal: P(random)
      )),
      5 ( ∀((x: T) => P(x))) by AllI[T](2),

      //Goal: ∀((x: T) => Q(x)
      6 Let((random: T) => SubProof(
        7 (P(random) & Q(random)) by AllE[T](1),
        8 (Q(random)) by AndE2(7),
        //Goal: P(random)
      )),
      9 ( ∀((x: T) => Q(x))) by AllI[T](6),
      10 ( ∀((x: T) => P(x)) & ∀((x: T) => Q(x))) by AndI(5, 9)

    )
  )
}

@pure def all2part2[T](P: T=>B @pure, Q: T=>B @pure): Unit = {
  Deduce(
    (
      ∀((x: T) => P(x)) & ∀((x: T) => Q(x))
    )
      |-
    (
      ∀((x: T) => (P(x) & Q(x)))
    )
    Proof(
      1 (  ∀((x: T) => P(x)) & ∀((x: T) => Q(x))  ) by Premise,

      2 (∀((x: T) => P(x))) by AndE1(1),
      3 (∀((x: T) => Q(x))) by AndE2(1),

      4 Let ((a:T) => SubProof(
        5 ( P(a) ) by AllE[T](2),
        6 ( Q(a) ) by AllE[T](3),
        7 ( P(a) & Q(a)) by AndI(5,6)
      //P(a) & Q(a)
      )),
      8 (∀((x: T) => (P(x) & Q(x))) by AllI[T](4))
    )
  )
}