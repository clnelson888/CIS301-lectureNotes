// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//adult tickets: $50
//kid tickets: $30
def getTicketCosts(adult: Z, kid: Z): Z = {
  //what do we want for our function contract?
  Contract(
    Requires( adult >= 0, kid >= 0),
    Ensures( Res[Z] == adult * 50 + kid * 30, Res[Z] >= 0 ) // returning adult*50 + kid*30
  )


  //what to do here?


  //get the total ticket cost
  val overall: Z = adult*50 + kid*30

  //what to do here?


  return overall
}

////////////// Test code /////////////////

val k: Z = 3 //$30 each
val a: Z = 2 //$50 each

//what to do here?
    //We must prove all of the Postconditions (ensures)
    // Goal: Res[Z] == adult * 50 + kid * 30
    //Goal: overall >= 0

    Deduce(
        1 ( overall == adult * 50 + kid * 30 ) by Premise,
        2 ( adult >= 0 ) by Premise,                // first precondition
        3 ( kid >= 0 ) by Premise,                  //second precondition
        4 ( overall >= 0 ) by Algebra*(1, 2, 3)     // proves the 2nd postcondition
    )

val cost: Z = getTicketCosts(a, k)

//what to do here?
Deduce(
    1 ( cost == a * 50 + k * 30 ) by Premise,       // Postcondition as a premise
    2 ( k == 3 ) by Premise,
    3 ( a == 2 ) by Premise,
    4 ( cost == 190 ) by Algebra*(1,2,3)
)

Deduce(
    1 ( k == 3 ) by Premise,
    2 ( a == 2 ) by Premise,
    3 ( a >= 0 ) by Algebra*(2), // Proves the first precondition
    4 ( k >= 0 ) by Algebra*(1)  // Proves the second precondition

    // adult >= 0, kid >= 0

)


//what *should* cost be?
assert(cost == 190)