// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//Prove AND is commutative


@pure def andCommute(p: B, q: B): Unit = {
  Deduce(
    (p & q) |- (q & p)
      Proof(
        //PROOF GOES HERE
        
    )
  )
}