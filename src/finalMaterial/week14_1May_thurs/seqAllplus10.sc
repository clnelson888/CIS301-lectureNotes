// #Sireum #Logika

import org.sireum._

//set all elements to 10
def all10(nums: ZS): Unit = {
  //function contract?
  Contract(
    //don't need to require anything
    Modifies(nums),
    Ensures(
      //at end of function, all elements in nums are 10 more than
      //they were initially
      ∀(0 until nums.size)(k => nums(k) == In(nums)(k) + 10)
    )
  )

  var i: Z = 0
  while (i < nums.size) {
    //loop invariant block?
    Invariant(
      Modifies(nums, i),
      i >= 0, //lower bound of loop counter (list the loop bounds first)
      i <= nums.size, //upper bound of loop counter
      nums.size == In(nums).size, //the size doesn't change (needed if sequence changes in loop)
      ∀(0 until i)(k => nums(k) == In(nums)(k) + 10), //what HAS changed
      ∀(i until nums.size)(k => nums(k) == In(nums)(k)) //what has NOT changed
    )

    nums(i) = nums(i) + 10
    i = i + 1

    //set all the later positions to 0
  }
}

///////////////////////////

var test: ZS = ZS(4,1,3,8,10,2)

all10(test)

//what do we want to assert?
assert(test == ZS(14, 11, 13, 18, 20, 12))
    i = i + 1
  }
}

///////////////////////////

var test: ZS = ZS(4,1,3,8,10,2)

all10(test)

//what do we want to assert?