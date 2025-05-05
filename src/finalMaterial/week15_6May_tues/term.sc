// #Sireum #Logika

import org.sireum._


def mult(x: Z, y: Z): Z = {
    Contract(
        Requires(y >= 0),
        Ensures(Res[Z] == x*y)
    )

    var sum: Z = 0
    var count: Z = 0

    //measure of work? (how many more iterations left?)

    while (count < y) {
        Invariant(
            Modifies(sum, count),
            count <= y,
            sum == x*count
        )

        sum = sum + x
        count = count + 1

        //measure should decrease with each iteration

        //when I have no work left, then my loop should be done
    }

    return sum
}

def collatz(n: Z): Z = {
    Contract(
        Requires(n > 0),
        //Ensures(Res[Z] == 1)
    )

    //what if n is 52?
    //cur = 52->26->13->40->20->10->5->16->8->4->2->1

    var cur: Z = n
    while (cur > 1) {
        Invariant(
            Modifies(cur),
            cur >= 1        //what else could we say?
        )

        if (cur % 2 == 0) {
            cur = cur / 2
        } else {
            cur = 3 * cur + 1
        }
    }

    return cur
}
