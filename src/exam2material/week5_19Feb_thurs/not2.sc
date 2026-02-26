// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def not2(p: B, q: B, r: B): Unit = {
  Deduce(
    //what is this? DeMorgan's 
    //does this prove equivalence?

    //HW: !(p | q) |- ( !p & !q )
    //if have p, then get p | q

    ( !p & !q ) |- ( !(p | q)  )
      Proof(
        1 (  !p & !q ) by Premise,

    )
  )
}