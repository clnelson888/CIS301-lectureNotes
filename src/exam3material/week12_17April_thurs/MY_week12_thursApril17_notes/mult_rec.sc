// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//want to return x * y, through repeated addition
//recursively compute x + x + ... + x (y times)
def mult(x: Z, y: Z): Z = {
  //what goes here?
  //what should we require?
  //what should we ensure?
  Contract(
    Requires ( y >= 0),
    Ensures ( Res[Z] == x * y )

  )

  var answer: Z = 0

  if (y == 0) {
    answer = 0

    //what do we need to do here?
    Deduce(
      1 ( y == 0 ) by Premise,
    )
  } else {
    //what do we need to do here?
    Deduce(
      1 ( !(y == 0)) by Premise,
      2 ( y>= 0 ) by Premise, // from precondition
      3 ( y - 1 >= 0 ) by Algebra*(1,2),

    )

    var temp: Z = mult(x, y-1)
    answer = x + temp

    //what do we need to show here?
    Deduce(
      1 ( temp = x * (y-1) ) by Premise,  //From post condition of recursive call
      2 ( answer == x + temp ) by Premise,  //From assignment
      3 ( temp == x * y - x ) by Algebra*(1),       //not exaclty needed, just showing
      4 ( answer == x + x * y - x ) by Algebra*(2,3),   //not exaclty needed, just showing
      5 ( answer == x*y) by Algebra*(4)   //needed for postcondition
    )

    //Need: answer == x*y
  }
  Deduce (
    1 ( answer == x*y ) by Premise,
  )

  //what do we need to do here?

  return answer
}

////////////// Test code //////////////

val a: Z = 5
val b: Z = 4

//Step 1: prove the precondition
  //show second parameter >= 0
  Deduce(
    1 ( ans == a * b ) by Premise,
    2 ( b == 4 ) by Premise,
    3 ( b >= 0 ) by Algebra*(1),  //proves precondition
    4 ( a == 5 ) by Premise,
    //Need b >= 0
  )

var ans: Z = mult(a, b)

//what do we want to assert that ans is?

assert(ans == 20)