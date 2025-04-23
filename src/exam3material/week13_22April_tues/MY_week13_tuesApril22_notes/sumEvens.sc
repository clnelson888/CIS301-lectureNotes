// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//sum of first n even numbers
def sumEvens(n: Z): Z = {
  //What can we use as the function contract?
  Contract(
    Requires( n >= 0),
    Ensures(Res[Z] == n*(n+1))
  )

  var sum: Z = 0
  var cur: Z = 0

  //Premises: sum == 0, cu == 0, n >= 0
  //Need to prove: Invarient: sum == cur * (cur+1)

  while (cur != n) {
    //what about our loop invariant?
    Invariant(
      Modifies(cur, sum),
      sum == cur * (cur+1)
    )

    //Premises: cur != n, sum == cur * (cur+1), n >= 0

    cur = cur + 1
    sum = sum + 2*cur

    //Need to prove: sum == cur * (cur+1) (invariant still holds)
  }

  //Premises: !(cur != n), sum == cur * (cur + 1), n >= 0
  //Need to prove: sum == n*(n+1)

  return sum
}

//////////// test code /////////

val num: Z = 5

//Premise: Num == 5
//Need to prove: num >= 0,

var sum5evens: Z = sumEvens(num)

//Premise: sum5evens == num * (num+1), num == 5
//Need to prove: sum5evens == 30

//sum of first 5 evens: 2 + 4 + 6 + 8 + 10 = 30
assert(sum5evens == 30)