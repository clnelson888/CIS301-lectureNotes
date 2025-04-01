// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

// ∀ x ¬P(x)   equivalent to   ¬(∃ x P(x))

//first direction is very similar to exists2.sc
@pure def demorgan1A[T](P: T=>B @pure): Unit = {
  Deduce(
    (
      ∀((x: T) => !P(x))
    )
    |-
    (
      !(∃((x: T) => P(x)))
    )
    Proof(
      1 ( ∀((x: T) => !P(x)) ) by Premise,

      //use NegI to build !(∃((x: T) => P(x)))
      2 SubProof(
        3 Assume ( ∃((x: T) => P(x)) ),

        //now what can we do with line 3?
        //use ExistsE
        4 Let ((alias: T) => SubProof(
          5 Assume ( P(alias) ),
          6 ( !P(alias) ) by AllE[T](1),
          7 ( F ) by NegE(5, 6)
          //goal: F (same as afterwards)
        )),
        8 ( F ) by ExistsE[T](3, 4)
        //goal: F
      ),
      9 ( !(∃((x: T) => P(x)) )           ) by NegI(2)
    )
  )
}

@pure def demorgan1B[T](P: T=>B @pure): Unit = {
  Deduce(
    (
      !(∃((x: T) => P(x)))
    )
      |-
    (
      ∀((x: T) => !P(x))
    )
    Proof(
      1 (  !(∃((x: T) => P(x)))   ) by Premise,
      
      //use AllI to get ∀((x: T) => !P(x))
      2 Let ((a: T) => SubProof(
        3 SubProof(
          4 Assume( P(a) ),
          5 ( ∃((x: T) => P(x)) ) by ExistsI[T](4),
          6 (F) by NegE(5, 1)

          //goal: F
        ),
        7 (!P(a)) by NegI(3)
        //use NegI to conclude !P(a)

        //goal: !P(a)
      )),
      8 ( ∀((x: T) => !P(x)) ) by AllI[T](2)
      //use AllI to conclude ∀((x: T) => !P(x))
    )
  )
}