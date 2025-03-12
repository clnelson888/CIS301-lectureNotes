// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._



@pure def allBig[T](P: T=>B @pure, Q: T=>B @pure, R: T=>B @pure, B: T=>B @pure, C: T=>B @pure): Unit = {
  Deduce(
    (
        ∀((x: T) => (P(x) __>: B(x)  )),
        ∀((x: T) => (Q(x) __>: C(x)  )),
        ∀((x: T) => (R(x) __>: !B(x) & !C(x)  ))
    )
      |-
    (
      ∀((x: T) => (P(x) | Q(x) __>: !R(x)  ))
    )
    Proof(
      1 ( ∀((x: T) => (P(x) __>: B(x)  )) ) by Premise,
      2 ( ∀((x: T) => (Q(x) __>: C(x)  )) ) by Premise,
      3 ( ∀((x: T) => (R(x) __>: !B(x) & !C(x)  )) ) by Premise,

      //use AllI to build for all in conclusion
      4 Let((random: T) => SubProof(
        5 (  P(random) __>: B(random)  ) by AllE[T](1),
        6 (  Q(random) __>: C(random)  ) by AllE[T](2),
        7 (  R(random) __>: !B(random) & !C(random)  )  by AllE[T](3),

        //use ImplyI to build goal
        8 SubProof(
          9 Assume(  P(random) | Q(random)  ),

          //good strategy: OrE with P(random) | Q(random)

          //try NegI to get goal
          10 SubProof(
            11 Assume (  R(random)  ),

            //now try OrE with P(random) | Q(random)

            12 SubProof(
              13 Assume( P(random) ),
              14 ( B(random) ) by ImplyE(5, 13),
              15 ( !B(random) & !C(random) ) by ImplyE(7, 11),
              16 ( !B(random) ) by AndE1(15),
              17 ( F ) by NegE(14, 16)
              //goal: F
            ),
            18 SubProof(
              19 Assume( Q(random) ),
              20 ( C(random) ) by ImplyE(6, 19),
              21 ( !B(random) & !C(random) ) by ImplyE(7, 11),
              22 ( !C(random) ) by AndE2(21),
              23 ( F ) by NegE(20, 22)
              //goal: F
            ),
            24 ( F ) by OrE(9, 12, 18)

            //next: assume Q(random), also try to get F

            //goal: F
          ),
          25 ( !R(random) ) by NegI(10)

          //goal: !R(random)
        ),
        26 ( P(random) | Q(random) __>: !R(random) ) by ImplyI(8)

        //goal: P(random) | Q(random) __>: !R(random)
      )),
      27 ( ∀((x: T) => (P(x) | Q(x) __>: !R(x) ) )) by AllI[T](4)
    )
  )
}