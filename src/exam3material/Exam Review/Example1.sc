import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

Var x:Z = Prompt("input")
Var input: Z = x
assume(x > 0)

x = x + 2

    Deduce(
        1 ( Old(x) > 0 ) by Premise,
        2 ( x == Old(x) + 2 ) by Premise,
        3 ( input == Old(x) ) by Premise,
        4 ( x == input + 2 ) by Algebra*(2,3),
        5 ( x > 2 ) by Algebra*(1,2)
    )

x = x * 2

    Deduce(
        1 ( x == Old(x) * 2) by Premise,
        2 ( Old(x) > 2 ) by Premise,
        3 ( Old(x) == input * 2 )
        4 (( x == input + 2) * 2) by Algebra*(1,3),
        5 ( x == input * 2 + 4 ) by Algebra*(4),
        6 ( x > 5 ) by Algebra(2,1)
        7 ( x == input * 2 + 4 & )
    )

    assert(x == input * 2 + 4 & x > 5)