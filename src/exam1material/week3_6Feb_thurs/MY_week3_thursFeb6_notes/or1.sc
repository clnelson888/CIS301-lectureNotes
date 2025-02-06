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
              
                            //Use OrE on p v p to prove q | p in both cases
        2 SubProof(         // goal: q | p
          3 Assume( p ),
          4 ( q | p ) by OrI2(3)
        ),    
                      // afterwards, subproof where I assume q
        5 SubProof(         // goal: p | q
          6 Assume ( q ),
          7 ( p | q ) by OrI2(6)
        ),

        8 ( q | p ) by OrE(1, 2, 5)
    )
  )
}