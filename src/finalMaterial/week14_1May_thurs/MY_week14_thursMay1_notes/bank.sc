// #Sireum #Logika

import org.sireum._

var balance: Z = 0
var elite: B = F
val eliteMin: Z = 1000000 // $1M is the minimum balance for elite members

//these are the global invariants
@spec def inv = Invariant(
  balance >= 0,
  elite == (balance >= eliteMin)
)

def deposit(amount: Z): Unit = {
  //what can we assume about the global invariants here?

  balance = balance + amount

  if (balance >= eliteMin) {
    elite = true
  }

  //what must be true about the global invariants here?
}

def withdraw(amount: Z): Unit = {

  balance = balance - amount

  if (balance >= eliteMin) {
    elite = true
  } else {
    elite = false
  }

}

//////////////// Test code /////////////////////

deposit(500000)
assert(balance == 500000 & !elite)
deposit(600000)
assert(balance == 1100000 & elite)
withdraw(150000)
assert(balance == 950000 & !elite)
deposit(200000)
assert(balance == 1150000 & elite)