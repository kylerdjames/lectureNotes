// #Sireum #Logika
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//(c ∧ n) → t, h ∧ ¬s, h ∧ ¬(s ∨ c) → p ⊢ (n ∧ ¬t) → p


@pure def big(p: B, q: B, r : B, w : B) : Unit = {
  Deduce(
    (r __>: !(p & q), w __>: (r __>: q) |-
    ( w __>: !(p & r))
    )
      Proof(
        1 (r __>: !(p & q)) by Premise,
        2 (w __>: (r __>: q)) by Premise,
        3 SubProof(
          4 Assume( p )
        )
      )
  )
}