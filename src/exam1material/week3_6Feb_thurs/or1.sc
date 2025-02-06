// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//Prove OR is commutative


@pure def or1(p: B, q: B): Unit = {
  Deduce(
    (p | q) |- (q | p)
      Proof(
        //PROOF GOES HERE
        1 ( p | q ) by Premise,

        //use OrE on p | q to prove q | p in both cases

        2 SubProof(
          3 Assume ( p ),
          4 ( q | p ) by OrI2(3)
          //goal: q | p
        ),
        //afterwards, subproof where I assume q
        5 SubProof(
          6 Assume ( q ),
          7 ( q | p ) by OrI1(6)
          //goal: q | p
        ),
        8 ( q | p ) by OrE(1, 2, 5)
    )
  )
}