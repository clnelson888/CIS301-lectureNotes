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
} else {
  max = b
}

//summarize what I learned, build my asserts


//assert that we have found the max
assert(max >= a & max >= b)
assert(max == a | max == b)