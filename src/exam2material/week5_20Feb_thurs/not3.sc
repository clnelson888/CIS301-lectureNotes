// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//proves the contrapositive
@pure def not3(p: B, q: B, r: B): Unit = {
  Deduce(
    ( p __>: q ) |- ( !q __>: !p  )
      Proof(
      1 (  p __>: q ) by Premise,

      //use ImplyI to build the conclusion

      2 SubProof(
        3 Assume( !q ), //assume LHS of goal implies

        //use NegI to construct !p
        4 SubProof(
          5 Assume( p ),
          6 ( q ) by ImplyE(1, 5),
          7 ( F ) by NegE(6, 3)

          //goal: F
        ),
        8 ( !p ) by NegI(4)

        //goal: RHS of goal implies (!p)
      ),
      9 ( !q __>: !p ) by ImplyI(2)
    )
  )
}