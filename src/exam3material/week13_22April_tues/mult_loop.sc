// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//finding x*y by doing x + x + x + ... + x (y times)
def mult(x: Z, y: Z): Z = {
  //What can we use as the function contract?
  Contract(
    Requires( y >= 0),
    Ensures( Res[Z] == x*y )
  )

  var total: Z = 0
  var i: Z = 0

  //prove invariant holds

  Deduce(
    1 ( total == 0 ) by Premise,
    2 ( i == 0 ) by Premise,
    3 ( total == i*x ) by Algebra*(1,2), //proves invariant holds before loop
    4 ( y >= 0 ) by Premise, //from precondition
    5 ( i <= y ) by Algebra*(2, 4) //proves 2nd invariant
  )

  //assert that invariant holds before loop begins
  assert(total == i*x)

  while (i < y) {
    Invariant(
      Modifies(i, total),
      total == i*x,
      i <= y
    )


    total = total + x

    Deduce(
      1 ( total == Old(total) + x ) by Premise, //from assignment
      2 ( Old(total) == i*x ) by Premise, //loop invariant was true
                              //at beginning of iteration, total has since changed
      3 ( total == i*x + x ) by Algebra*(1,2) //summarizes without Old
    )

    i = i + 1

    Deduce(
      1 ( i == Old(i) + 1 ) by Premise, //from update
      2 ( total == Old(i) * x + x ) by Premise, //from previous block
      3 ( Old(i) == i - 1 ) by Algebra*(1),
      4 ( total == (i-1) * x + x ) by Algebra*(2,3),
      5 ( total == i*x - x + x ) by Algebra*(4),
      6 ( total == i*x ) by Algebra*(5), //proves invariant still holds at end of iteration
    
      7 ( Old(i) <= y ) by Premise, //2nd invariant was true at beginning of iteration
      8 ( Old(i) < y ) by Premise, //from loop condition
      9 ( i <= y  ) by Algebra*(1, 7, 8) //proves 2nd invariant
    )

    //prove invariant holds at end of iteration

    assert(total == i*x)
    assert(i <= y)
  }

  //STOPPED HERE
  //still need to prove the postcondition
  //ensures was: Res[Z] == x*y

  Deduce(
    1 ( total == i*x ) by Premise, //invariant is true 
    2 ( !(i < y) ) by Premise, //loop condition is false
    3 ( i <= y ) by Premise, //2nd invariant is true
    4 ( i == y ) by Algebra*(2, 3),
    5 ( total == x*y ) by Algebra*(1, 4) //proves postcondition
  )

  //need: total == x*y

  return total
}

//////////// test code /////////

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