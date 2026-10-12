/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Class
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Hasse

/-!
# The second Stiefel–Whitney class and the Hasse invariant

For a regular quadratic form over a field `K` in which `2` is invertible, the second
Stiefel–Whitney class is the image of its Hasse invariant under the canonical comparison
`TauCeti.brauer2EquivH2 K : Additive Br(K)[2] ≃+ H²(G_K, 𝔽₂)`. Both invariants are defined
on `TauCeti.RegularFormClass K`, so this identity requires no choice of diagonalization.
In particular, two regular forms have the same `w₂` exactly when their Hasse invariants agree,
and `w₂` vanishes exactly when the Hasse invariant is trivial.

The Hasse invariant here is Lam's `s(q) = ∏_{i<j} [(aᵢ,aⱼ)]`, also Serre's `ε`, not the
Witt–Clifford invariant `c(q)`. The latter differs by dimension-dependent correction terms.
The comparison follows termwise from `TauCeti.brauerCohomologyEquiv_quaternionClass`:
products of quaternion symbols become sums of Kummer cup products.

## Main results

* `TauCeti.brauerCohomologyEquiv_hasseInvariant`: the comparison with multiplicative
  coefficients sends the Hasse invariant to `h2MuToUnits K (w₂(q))`.
* `TauCeti.brauer2EquivH2_hasseInvariant`: the two-torsion comparison sends `s(q)` to `w₂(q)`.
* `TauCeti.sw2Class_eq_iff_hasseInvariant_eq` and
  `TauCeti.sw2Class_eq_zero_iff_hasseInvariant_eq_one`: equality and vanishing criteria.

## References

* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. 9 (1970), §3.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, GSM 67 (2005), V.3.17–18.
* J.-P. Serre, *Local Fields*, GTM 67 (1979), XIV §2, Proposition 5.
-/

public section

namespace TauCeti

open Finset _root_.ContinuousCohomology

variable {K : Type} [Field K] [Invertible (2 : K)]

/-- The comparison with multiplicative coefficients sends the Hasse invariant of a regular
form class to the image of its second Stiefel–Whitney class under the Kummer injection. -/
theorem brauerCohomologyEquiv_hasseInvariant (q : RegularFormClass K) :
    brauerCohomologyEquiv K (Additive.ofMul q.hasseInvariant) =
      (h2MuToUnits K).hom (sw2Class q) := by
  induction q using Quotient.inductionOn with
  | h p =>
    rw [RegularFormClass.hasseInvariant_mk, sw2Class_mk, sw2_def]
    simp only [ofMul_prod, map_sum, brauerCohomologyEquiv_quaternionClass,
      kummerCup_squareClass_squareClass]

/-- **The second Stiefel–Whitney class is the image of the Hasse invariant.** The source is
`Br(K)[2]`, with membership supplied by the two-torsion theorem for the Hasse invariant. -/
@[simp]
theorem brauer2EquivH2_hasseInvariant (q : RegularFormClass K) :
    brauer2EquivH2 K (Additive.ofMul
      ⟨q.hasseInvariant, BrauerGroup.mem_twoTorsion.mpr (q.hasseInvariant_sq)⟩) =
      sw2Class q := by
  apply h2MuToUnits_injective K
  rw [brauer2EquivH2_h2MuToUnits, brauerCohomologyEquiv_hasseInvariant]

/-- Two regular form classes have the same second Stiefel–Whitney class exactly when their
Hasse invariants agree. No equality of ranks or discriminants is required. -/
theorem sw2Class_eq_iff_hasseInvariant_eq (q r : RegularFormClass K) :
    sw2Class q = sw2Class r ↔ q.hasseInvariant = r.hasseInvariant := by
  rw [← (h2MuToUnits_injective K).eq_iff, ← brauerCohomologyEquiv_hasseInvariant,
    ← brauerCohomologyEquiv_hasseInvariant, (brauerCohomologyEquiv K).injective.eq_iff,
    EmbeddingLike.apply_eq_iff_eq]

/-- The second Stiefel–Whitney class vanishes exactly when the Hasse invariant is trivial. -/
theorem sw2Class_eq_zero_iff_hasseInvariant_eq_one (q : RegularFormClass K) :
    sw2Class q = 0 ↔ q.hasseInvariant = 1 := by
  simpa only [sw2Class_zero, RegularFormClass.hasseInvariant_zero] using
    sw2Class_eq_iff_hasseInvariant_eq q 0

end TauCeti
