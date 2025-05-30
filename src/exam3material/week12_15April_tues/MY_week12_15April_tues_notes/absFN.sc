// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

def absVal(numOrig: Z) : Z = {
  //what do we need here?
  Contract(
    Ensures(Res[Z] >= 0, Res[Z] == numOrig | Res[Z] == -1 numOrig )

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

  //what can we say here?
  //what do we need to prove by the end of the function?

  Deduce(
    1 ( num >= 0) by Premise,
    2 ( num == numOrig)
  )

  return num

}

////////////////// Test code //////////////

val x: Z = -4

//use function to get absolute value of x
//what *should* the absolute value be?

    //No requirements

val ans: Z = absVal(x)

Deduce(
    1 (ans >= 0 ) by Premise,
    2 (ans == x | ans == -1 * x) by 
)


//what should we be able to assert?
assert(num)