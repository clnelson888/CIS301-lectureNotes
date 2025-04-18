// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def not4(p: B, q: B, r: B): Unit = {
  Deduce(
      ( !q __>: !p )|- ( p __>: q )
      Proof(
        1 (  !q __>: !p ) by Premise,

        //use IMplyI to prove p__>:q

        2 SubProof(
          3 Assume ( p ), //assume LHS of goal implies

          //Use PbC to try to get q
          4 SubProof(
            5 Assume (!q),
            6 (!p) by ImplyE(1, 5),
            7 ( F ) by NegE(3, 6)
            //Goal: F
          ),
          8 ( q ) by PbC(4),
        ),
        9 (p __>: q) by ImplyI(2)


          //Goal: q (RHS of goal implies)
        ),
  )
}