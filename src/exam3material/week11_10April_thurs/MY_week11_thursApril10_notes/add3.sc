// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

var x: Z = Z.prompt("Enter a positive number: ")

assume(x > 0)


//orig will always be the original user input value
val orig: Z = x

//do we need a proof block here? 

x = x + 1

Deduce(
    1 (x == Old(x) + 1) by Premise,
    2 (orig == Old(x)) by Premise,
    3 ( Old(x) > 0) by Premise,
    4 ( x == orig + 1) by Algebra*(1,2), // Subst_>(2,1)
    5 ( x > 0 ) by Algebra*(1,3)
)


//what can we put in a proof block here?
//what should we be able to assert about x and orig?

x = x + 2

Deduce(
    1 ( x == Old(x) + 2) by Premise, // From Assignment
    2 ( Old(x) == orig + 1) by Premise, //From previous block
    3 ( x == orig + 3) by Algebra*(1,2), // or using Subst: x == orig + 2 + 1
    4 ( Old(x) > 0) by Premise,
    5 ( x > 0 ) by Algebra*(1,4)
)




assert(x == orig + 3)
assert(x > 0)

//what can we put in a proof block here?

//what do we want to assert? How has x changed?

//Once it is working - if x was originally positive,
//how could we assert that x was still positive at the end?
