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
      1 ( !(∃((x: T) => P(x))) ) by Premise,

      
    )
  )
}