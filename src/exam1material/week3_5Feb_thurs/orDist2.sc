// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._



@pure def orDist2(p: B, q: B, r: B): Unit = {
  Deduce(
    ( (p | q ) & (p | r) ) |- ( p | (q & r) )
      Proof(
        //PROOF GOES HERE
        1 ( (p | q ) & (p | r) ) by Premise,
        2 ( p | q ) by AndE1(1),
        3 ( p | r ) by AndE2(1),

        
        4 SubProof(
          5 Assume( p ),
          6 ( p | (q & r)) by OrI1(5)
        ),
        7 SubProof(
          8 Assume ( q ),
          9 SubProof(
            10 Assume ( r ),
            11 ( q & r ) by AndI(8,10),
            12 ( p | (q & r)) by OrI2(11)
          ),
          13 SubProof( 
            14 Assume ( p ),
            15 ( p | (q & r)) by OrI1(14)
          ),
          16 ( p | (q & r)) by OrE(3,13,9),
          
        ),
        17 ( p | (q & r)) by OrE(2,4,7)
        
    )
  )
}