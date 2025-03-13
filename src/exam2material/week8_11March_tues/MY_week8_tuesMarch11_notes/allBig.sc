// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

// ¬(∃ x P(x)) |- ∀ x ¬P(x)

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

      4 Let ((a:T) => SupProof(

        50 (P(a) __>: B(a)) by AllE[T](1),
        51 (Q(a) __>: C(a)) by AllE[T](2),
        52 (R(a) __>: !B(a) & !C(a)) by AllE[T](3),


        5 SubProof(
          6 Assume(P(a) | Q(a)),

          7 SubProof(
            8 Assume(R(a)),
            9 (!B(a) & !C(a)) by ImpyE(52, 8),
            10 (!B(a)) by AndE1(9),
            11 (!C(a)) by AndE2(9),

            12 SubProof(
              13 Assume(P(a)),
              14 (B(a)) by ImmplyE(50, 13),
              15 (F) by NegE(14, 10)
              //Goal: F
            ),
            16 SubProof(
              17 Assume(Q(a)),
              18 (C(a)) by ImplyE(51, 17),
              19 (F) by NegE(18, 11)
              //Goal: F
            ),
            20 (F) by OrE(6, 12, 16),          
          //Goal: F
          ),

          21 (!R(a)) by NegI(7),
      
          //Goal: !R(a)
          ),

          22 (P(a) | Q(a) __>: !R(a)) by ImplyI(5)
          //Goal: (P(a) | Q(a) __>: !R(a))
        )      
      ),
      23 (∀((x: T) => (P(x) | Q(x) __>: !R(x)  ))) by AllI[T](4)

    )
  )

  
}