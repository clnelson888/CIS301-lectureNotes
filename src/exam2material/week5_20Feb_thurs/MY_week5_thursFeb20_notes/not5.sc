// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def not5(p: B, q: B, r: B): Unit = {
  Deduce(
    ( !(!p | !q) ) |- ( p & q )
      Proof(
        1 (  !(!p | !q) ) by Premise,

        //prove p
        // no obvioius strategy; Try PbC
        2 SubProof(
          3 Assume (!p),
          4 (!p | !q) by OrI1(3),
          5 ( F ) by NegE(4, 1)

          // Goal: F
        ),
        6 (p) by PbC(2),
        7 ()





        //prove q (Exactly the same as subproof 2)


        //Use AndI to prove p and q
    )
  )
}