// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

val x: Z = Z.prompt("Enter first number: ")
val y: Z = Z.prompt("Enter second number: ")

//x = 3, y = 4

//how do we assume x is bigger than y?
assume(x > y)

val max: Z = x

Deduce(
  1 ( max == x ) by Premise,
  2 ( max == x | max == y ) by OrI1(1),
  3 ( max >= x ) by Algebra*(1),
  4 ( x > y ) by Premise,
  5 ( max >= y ) by Algebra*(3, 4),
  6 ( max >= x & max >= y ) by AndI(3, 5)
)


//max is 3

//what can we put in a proof block here?

//how do we assert max is the biggest between our two inputs?
assert(max == x | max == y)
assert(max >= x & max >= y)