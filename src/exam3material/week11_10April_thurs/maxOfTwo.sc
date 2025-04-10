// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._


val a: Z = Z.prompt("Enter first number: ")
val b: Z = Z.prompt("Enter second number: ")

var max: Z = 0

if (a > b) {
  max = a

  Deduce(
    1 ( a > b ) by Premise, //from condition
    2 ( max == a ) by Premise, //from assignment
    3 ( max >= a ) by Algebra*(2), //for the first assert
    4 ( max >= b ) by Algebra*(1, 2) //for the second assert
  )
} else {
  max = b

  Deduce(
    1 ( !(a > b) ) by Premise, //condition is false
    2 ( max == b ) by Premise, //from assignment
    3 ( b >= a ) by Algebra*(1),
    4 ( max >= b ) by Algebra*(2), //for the first assert
    5 ( max >= a ) by Algebra*(2, 3), //for the first assert
  )
}

Deduce(
    1 ( max >= a ) by Premise, //true in both branches
    2 ( max >= b ) by Premise, //true in both branches
    3 ( max == a | max == b ) by Premise, //LHS was true in if, RHS was true else
    4 ( max >= a & max >= b ) by AndI(1, 2) //for the 1st assert
)

//summarize what I learned, build my asserts

//need proof block with the two assert statements

//max >= a
//max >= b


//assert that we have found the max
assert(max >= a & max >= b)
assert(max == a | max == b)