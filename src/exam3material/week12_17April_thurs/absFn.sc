// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

def absVal(numOrig: Z) : Z = {
  //what do we need here?
  Contract(
    Ensures(Res[Z] >= 0, Res[Z] == numOrig | Res[Z] == -1 * numOrig)
  )

  var num: Z = numOrig

  //update num to be the absolute value of the input
  if (num < 0) {
    num = num * -1

    Deduce(
      1 ( num == Old(num) * -1) by Premise, //from assignment
      2 ( Old(num) < 0) by Premise, //from condition

      3 ( num >= 0 ) by Algebra*(1, 2),
      4 ( Old(num) == numOrig) by Premise,
      5 ( num== -1 * numOrig ) by Algebra*(1, 4)
    )
  } else {
    //do nothing -- num is already its own absolute value

    Deduce(
      1 (!(num < 0)) by Premise, //condition is false
      2 ( num >= 0 ) by Algebra*(1),
      3 ( num == numOrig ) by Premise
    )
  }

  //summarize what we learned
  Deduce(
    //also shows the postconditions
    1 ( num >= 0) by Premise, //true in both branches
    2 ( num == numOrig | num == -1 * numOrig ) by Premise //one side from if,
                                                      //one side from else
  )

  //what can we say here?
  //what do we need to prove by the end of the function?

  return num

}

////////////////// Test code //////////////

val x: Z = -4

//use function to get absolute value of x
//what *should* the absolute value be?

//no requirements

val ans: Z = absVal(x)

Deduce(
  1 ( ans >= 0 ) by Premise, //first postcondition
  2 ( ans == x | ans == -1 * x) by Premise, //second postcondition


  //NEED TO FINISH THIS
)

assert(ans == 4)

//what should we be able to assert?
//goal: ans is 4 (will finish on Thursday)