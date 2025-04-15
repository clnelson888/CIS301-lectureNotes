// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//just the code for finding the biggest of 3 numbers

val a: Z = Z.read()    //suppose a is 3
val b: Z = Z.read()    //suppose b is 5
val c: Z = Z.read()    //suppose c is 10
var max: Z = 0

/*
    mark where logic blocks would go
    finish the verification in the next file
*/

if (a >= b) {
  if (a >= c) {
    max = a

    //need max >= a, max >= b, max >= c
    //ONE OF max == a, max == b, max == c
  } else {
    max = c

    //need max >= a, max >= b, max >= c
    //ONE OF max == a, max == b, max == c
  }
  //summary of inner if/else
} else {
  if (b >= c) {
    max = b

    //need max >= a, max >= b, max >= c
    //ONE OF max == a, max == b, max == c
  } else {
    max = c

    //need max >= a, max >= b, max >= c
    //ONE OF max == a, max == b, max == c
  }

  //summary of what was true in the inner if/else
}

//overall summary here

println("Max between ", a, ", ", b, " and ", c, " is ", max)

//How do we know we have the max?
//what assert(s) do we want?

//need the first 3 in EVERY branch
//need ONE of the last assert in every branch

assert(max >= a)
assert(max >= b)
assert(max >= c)
assert(max == a | max == b | max == c)