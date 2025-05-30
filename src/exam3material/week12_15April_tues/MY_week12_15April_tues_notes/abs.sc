// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

var num: Z = Z.prompt("Enter a number: ")
val numOrig : Z = num


if (num < 0) {
  num = num * -1

  Deduce(
    1 ( Old(num) < 0 ) by Premise,
    2 ( num == Old(num) * -1 ) by Premise,
    3 ( numOrig == Old(num) ) by Premise,


    // Goal: num >= 0
    4 ( num >= 0 ) by Algebra*(1,2),

    //Goal: num == -1*numOrig
    5 ( num == -1 * numOrig) by Algebra*(2,3)
  )

} else {
  //no code, just for verification
  Deduce(
    //Goal: num >= 0
    1 ( !(num < 0) ) by Premise, // if condition is false
    2 ( numOrig == num ) by Premise,
    3 ( num >= 0 ) by Algebra*(1),

    //Goal: num == numOrig
    4 ( num == numOrig ) by Algebra*(2)

  )


}

//summarize what we learned
Deduce(
    1 ( num >= 0 ) by Premise,
    2 ( num == numOrig | num == -1 * numOrig ) by Premise //One side from if, one side from else
)

//How can we assert that num is the absolute value of the input?
//(what was the original input?)
assert( num >= 0 )
assert( num == numOrig | num == -1 * numOrig )