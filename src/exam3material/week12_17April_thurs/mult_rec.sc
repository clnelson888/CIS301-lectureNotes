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
    Requires( y >= 0),
    Ensures( Res[Z] == x*y )
  )

  var answer: Z = 0

  if (y == 0) {
    answer = 0

    //what do we need to do here?

    Deduce(
      1 ( y == 0 ) by Premise, //condition is true
      2 ( x*y == 0 ) by Algebra*(1),
      3 ( answer == 0 ) by Premise, //assignment statement
      4 ( answer == x*y ) by Algebra*(2, 3)
    )

    //need: answer == x*y
  } else {
    //what do we need to do here?
    //prove precondition before recursive call

    Deduce(
      1 ( !(y == 0) ) by Premise, //if condition is false
      2 ( y >= 0 ) by Premise, //from the precondition
      3 ( y - 1 >= 0 ) by Algebra*(1, 2) //proves precondition for recursive call
    )

    //need: y-1 >= 0

    var temp: Z = mult(x, y-1)
    answer = x + temp

    //what do we need to show here?

    Deduce(
      1 ( temp == x * (y-1)) by Premise, //from postcondition of recursive call
      2 ( answer == x + temp ) by Premise, //from assignment
      3 ( temp == x*y - x) by Algebra*(1),
      4 ( answer == x + x*y - x ) by Algebra*(2, 3),
      5 ( answer == x*y ) by Algebra*(4) //needed for postconditoin
    )

    //need: answer == x*y
  }

  Deduce(
    1 ( answer == x*y ) by Premise //true in both branches
                                  //proves postcondition
  )

  //what do we need to do here?
  //need: answer == x*y

  return answer
}

////////////// Test code //////////////

val a: Z = 5
val b: Z = 4

//Step 1: prove the precondition

Deduce(
  1 ( b == 4 ) by Premise,
  2 ( b >= 0 ) by Algebra*(1) //proves precondition
  //need b >= 0
)

//show 2nd parameter >= 0

var ans: Z = mult(a, b)

//what do we want to assert that ans is?
Deduce(
  1 ( ans == a*b ) by Premise, //postcondition from function call
  2 ( a == 5 ) by Premise,
  3 ( b == 4 ) by Premise,
  4 ( ans == 20 ) by Algebra*(1,2,3)

  //Res[Z] == x*y
)

assert(ans == 20)