/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.EnhancedState.Basic
import TauCeti.KnotTheory.PDCode.ResolvedCircle.Planar

/-!
# Component parity of enhanced-state quantum degrees

For an oriented planar diagram with `c` link components, every enhanced state has quantum
degree congruent to `c` modulo two. Consequently the coefficients of `enhancedStateSum` vanish in
quantum degrees of the opposite parity.

The planar normalization-sign parity
`TauCeti.OrientedPDCode.card_false_add_negativeCrossingCount_add_stateLoopCount_mod_two`
gives `(|S(s)| + n₋ + k(s)) % 2 = (n + c) % 2`. Together with `n = n₊ + n₋`, this implies
`(stateQuantumShift s + k(s)) % 2 = c % 2`. Labelling a circle by `X` instead of `1` changes the
degree by two. Crossing-free circles are counted throughout, including for the empty diagram.

## Main results

* `TauCeti.OrientedPDCode.stateQuantumShift_add_stateLoopCount_mod_two`: the normalized quantum
  shift plus the number of resolution circles has the parity of `D.componentCount`.
* `TauCeti.OrientedPDCode.enhancedQuantumDegree_mod_two`: every enhanced state of a planar
  diagram has quantum degree congruent modulo two to `D.componentCount`.
* `TauCeti.OrientedPDCode.coeff_enhancedStateSum_eq_zero_of_mod_two_ne`: every coefficient of
  `D.enhancedStateSum` in a quantum degree of the opposite parity vanishes.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000),
  §§2–3 (enhanced states and their grading).
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §2 (the parity of the quantum grading).
-/

public section

namespace TauCeti.OrientedPDCode

open Finset

variable {n : ℕ} (D : OrientedPDCode n)

/-- The normalized quantum shift plus the number of resolution circles has the parity of
the number of link components, independently of the state. -/
theorem stateQuantumShift_add_stateLoopCount_mod_two (hD : D.toPDCode.IsPlanar)
    (s : Fin n → Bool) :
    (D.stateQuantumShift s + D.stateLoopCount s) % 2 = (D.componentCount : ℤ) % 2 := by
  have hpar := D.card_false_add_negativeCrossingCount_add_stateLoopCount_mod_two hD s
  have hcrossings := D.positiveCrossingCount_add_negativeCrossingCount
  rw [stateQuantumShift_def]
  omega

/-- Every enhanced state of a planar diagram has quantum degree congruent modulo two to
the number of link components. -/
theorem enhancedQuantumDegree_mod_two (hD : D.toPDCode.IsPlanar)
    (e : D.toPDCode.EnhancedState) :
    D.enhancedQuantumDegree e % 2 = (D.componentCount : ℤ) % 2 := by
  have h := D.stateQuantumShift_add_stateLoopCount_mod_two hD e.1
  rw [enhancedQuantumDegree_def, Khovanov.labelingQuantumDegree_eq,
    PDCode.card_resolvedCircle]
  omega

/-- Every coefficient of `D.enhancedStateSum` in a quantum degree whose parity differs from
`D.componentCount` vanishes. -/
theorem coeff_enhancedStateSum_eq_zero_of_mod_two_ne (hD : D.toPDCode.IsPlanar) {j : ℤ}
    (hj : j % 2 ≠ (D.componentCount : ℤ) % 2) :
    D.enhancedStateSum.coeff j = 0 := by
  classical
  rw [enhancedStateSum_def, AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  refine Finset.sum_eq_zero fun e _ ↦ ?_
  have hne : D.enhancedQuantumDegree e ≠ j := fun h ↦
    hj (h ▸ D.enhancedQuantumDegree_mod_two hD e)
  rw [AddMonoidAlgebra.coeff_smul_apply, LaurentPolynomial.T, AddMonoidAlgebra.coeff_single]
  simp [hne]

end TauCeti.OrientedPDCode
