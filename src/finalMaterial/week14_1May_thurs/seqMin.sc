// #Sireum #Logika

import org.sireum._

//return the smallest element in list
def min(list: ZS): Z = {
  Contract(
    Requires(list.size > 0),
    Ensures(
      //whatever we are returning is <= everything in the list
      ∀(0 until list.size)(k => Res[Z] <= list(k)),

      //whatever we are returning is one of the list elements
      ∃(0 until list.size)(k => Res[Z] == list(k))
    )
  )

  var small: Z = list(0)
  var i: Z = 1
  
  while (i < list.size) {
    Invariant(
      Modifies(small, i),
      i >= 1,
      i <= list.size,
      ∀(0 until i)(k => small <= list(k)),
      ∃(0 until i)(k => small == list(k))
    )

    if (list(i) < small) {
      small = list(i)
    }
    i = i + 1
  }

  return small
}

////////////// Calling code ///////////////////

var test: ZS = ZS(8,1,0,10,9,2,0)
var testMin: Z = min(test)

//what should testMin be?
assert(testMin == 0)