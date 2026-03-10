// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

//∀ x (P(x) ⋀ Q(x))    equivalent to     (∀ x P(x)) ⋀ (∀ x Q(x))

@pure def all2part1[T](P: T=>B @pure, Q: T=>B @pure): Unit = {
  Deduce(
    (
      ∀((x: T) => (P(x) & Q(x)))
    )
      |-
    (
       ∀((x: T) => P(x)) & ∀((x: T) => Q(x))
    )
    Proof(
      1 (∀((x: T) => (P(x) & Q(x)))) by Premise,
      2 Let( (random: T) => SubProof(
        3 (P(random) & Q(random)) by AllE[T](1),
        4 ( P(random)) by AndE1(3)
      )),
      5 (∀((x: T) => P(x))) by AllI[T](2),
      6 Let( (random2: T) => SubProof(
        7 (P(random2) & Q(random2)) by AllE[T](1),
        8 ( Q(random2)) by AndE2(7)
      )),
      9 (∀((x: T) => Q(x))) by AllI[T](6),
      10 (∀((x: T) => P(x)) & ∀((x: T) => Q(x))) by AndI(5,9)
    )
  )
}


