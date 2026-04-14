// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._



@pure def allBig[T](P: T=>B @pure, Q: T=>B @pure, R: T=>B @pure, B: T=>B @pure, C: T=>B @pure): Unit = {
  Deduce(
    (
        ∀((x: T) => (P(x) __>: B(x)  )),
        ∀((x: T) => (Q(x) __>: C(x)  )),
        ∀((x: T) => (R(x) __>: !B(x) & !C(x)  ))
    )
      |-
    (
      ∀((x: T) => (P(x) | Q(x) __>: !R(x)  ))
    )
    Proof(
      1 ( ∀((x: T) => (P(x) __>: B(x)  )) ) by Premise,
      2 ( ∀((x: T) => (Q(x) __>: C(x)  )) ) by Premise,
      3 ( ∀((x: T) => (R(x) __>: !B(x) & !C(x)  )) ) by Premise,
      4 Let ( ( a: T) => SubProof(
        5 SubProof(
          6 Assume ( P(a) | Q(a)),
          7 SubProof(
            8 Assume ( R(a)),
            9 (R(a) __>: !B(a) & !C(a)  ) by AllE[T](3),
            10 ( !B(a) & !C(a)) by ImplyE(9,8),
            11 ( !B(a)) by AndE1(10),
            12 (!C(a)) by AndE2(10),
            
            13 SubProof(
              14 Assume (P(a)),
              15 (P(a) __>: B(a)  ) by AllE[T](1),
              16 ( B(a)) by ImplyE(15,14),
              17 ( F ) by NegE(16,11)
            ),
            18 SubProof(
              19 Assume (Q(a)),
              20 (Q(a) __>: C(a)  ) by AllE[T](2),
              21 ( C(a)) by ImplyE(20,19),
              22 ( F ) by NegE(21,12)
            ),
          23 ( F ) by OrE(6,13,18),
          ),
          24 (!R(a)) by NegI(7)
        ),
        25 (P(a) | Q(a) __>: !R(a)) by ImplyI(5)
      )),
      26 (∀((x: T) => (P(x) | Q(x) __>: !R(x)  ))) by AllI[T](4)
    )
  )
}