// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

var num: Z = Z.prompt("Enter a number: ")
val numOrig : Z = num


if (num < 0) {
  num = num * -1
} else {
  //no code, just for verification
  Deduce(
    1 ( !(num < 0)) by Premise,
    2 ( numOrig == num) by Premise,
    3 ( num >= 0) by Algebra*(1),
  )

  Deduce(
    1 ( !(num < 0 ) ) by Premise, //condition is false
    2 ( numOrig == num ) by Premise, //assignment statement
    3 ( num >= 0 ) by Algebra*(1),
    4 ( num == numOrig ) by Algebra*(2)
  )

  //need: num >= 0 
  //need: num == numOrig 
}

Deduce(
  1 ( num >= 0 ) by Premise, //true in both branches
  2 ( num == -1*numOrig | num == numOrig ) by Premise, //LHS true in if, RHS true in else
  //need: num >= 0
  //need: num == -1*numOrig | num == numOrig
)

Deduce(

)
assert( num >= 0)
//How can we assert that num is the absolute value of the input?
//(what was the original input?)

assert(num >= 0)
assert(num == -1*numOrig | num == numOrig)