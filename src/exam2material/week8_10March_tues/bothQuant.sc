// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

// ¬(∃ x P(x)) |- ∀ x ¬P(x)

@pure def bothQuant[T](indiv: T,G: T=>B @pure, L: T=>B @pure, H: T=>B @pure, K: T=>B @pure): Unit = {
  Deduce(
(
∀ ((x: T) => (!G(x) __>: H(x))),
∀ ((x: T) => (K(x) __>: L(x) & !G(x))),
K(indiv)
)
⊢
( ∃ ((x: T) => H(x)) )
    Proof(
      1 (∀ ((x: T) => (!G(x) __>: H(x)))) by Premise,
      2 (∀ ((x: T) => (K(x) __>: L(x) & !G(x)))) by Premise,
      3 (K(indiv) ) by Premise,
      4 (K(indiv) __>: L(indiv) & !G(indiv)) by AllE[T](2),
      5 (L(indiv) & !G(indiv)) by ImplyE(4,3),
      6 (!G(indiv)) by AndE2(5),
      7 (!G(indiv) __>: H(indiv)) by AllE[T](1),
      8 ( H(indiv)) by ImplyE(7,6),
      9 ( ∃ ((x: T) => H(x))) by ExistsI[T](8)
      
    )
  )
}