// #Sireum #Logika

import org.sireum._

//set all elements to 10
def all10(nums: ZS): Unit = {
  //function contract?
  Contract(
    //Don't need to require anything
    Modifies(nums),
    Ensures( 
      ∀(0 until nums.size)(k => nums(k) == In(nums)(k) + 10)
    )
  )

  var i: Z = 0
  while (i < nums.size) {
    //loop invariant block?
      Invariant(
        Modifies(nums, i),
        
        i >= 0,                                           //Bounding the loop counter
        i <= nums.size,                                   //Bounding the loop counter EQUAL TO, at the end of the last itteration, 
                                                              //'i' WILL equal the size
        nums.size == In(nums).size,                       // the size doesn't change
        ∀(0 until i)(k => nums(k) == In(nums)(k) + 10),     // what HAS changed
        ∀(i until nums.size)(k => nums(k) == In(nums)(k)),  // What has NOT changed
      )

    nums(i) = nums(i) + 10
    i = i + 1
  }
}

///////////////////////////

var test: ZS = ZS(4,1,3,8,10,2)

all10(test)

//what do we want to assert?
assert(test == ZS(14,11,13,18,20,12))