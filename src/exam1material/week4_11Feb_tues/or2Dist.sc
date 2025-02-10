// #Sireum #Logika
//@Logika: --manual --background type

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//Second part proof of distributive law:
//p ∨ (q ∧ r)     is equivalent to
// (p ∨ q) ∧ (p ∨ r)


@pure def orDist2(p: B, q: B, r: B): Unit = {
  Deduce(
    ((p | q) & (p | r)) |- (p | (q & r))
      Proof(

      //PROOF GOES HERE
      1 (  (p | q) & (p | r)  ) by Premise,
      
      2 (  p | q              ) by AndE1(1),
      3 (  p | r             ) by AndE2(1),
      

    )
  )
}