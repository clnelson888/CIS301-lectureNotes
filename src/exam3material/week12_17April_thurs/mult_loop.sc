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
    3 ( total == i*x ) by Algebra(1,2) //proves invariant
  )

  assert(total == i*x)

  while (i != y) {
    Invariant(
      Modifies(i, total),
      total == i*x
    )


    total = total + x

    Deduce(
      1 ( total = Old(total) + x ) by Premise, //from assignment
      2 ( i != y ) by Premise, //loop condition is true
      3 ( Old(total) == i*x ) by Premise, //loop invariant was true
                              //at beginning of iteration, total has since changed
      4 ( total == i*x + x ) by Algebra*(1,3) //summarizes without Old
    )

    i = i + 1

    Deduce(
      1 ( i == Old(i) + 1 ) by Premise, //from update
      2 ( total == Old(i) * x + x ) by Premise, //from previous block
      3 ( Old(i) == i - 1 ) by Algebra*(1),
      4 ( total == (i-1) * x + x ) by Algebra*(2,3),
      5 ( total == i*x - x + x ) by Algebra*(4),
      6 ( total == i*x ) by Algebra*(5) 
    )

    //prove invariant holds

    assert(total == i*x)
  }

  //STOPPED HERE
  //still need to prove the postcondition

  return total
}

//////////// test code /////////

val a: Z = 5
val b: Z = 4

var ans: Z = mult(a, b)

//what do we want to assert that ans is?