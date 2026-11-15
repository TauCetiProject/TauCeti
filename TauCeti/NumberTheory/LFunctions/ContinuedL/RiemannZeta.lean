/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.ContinuedL.Basic
public import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta

/-!
# Identification of the continued L-function of the Riemann zeta card

`riemannZetaData` records the completed Riemann zeta function `completedRiemannZeta` with conductor
`1`, gamma factor `Γ_ℝ(s)`, and simple poles at `0` and `1`. At `s = 0`, the simple pole of `Λ` is
cancelled by the simple pole of `Γ_ℝ`, so `riemannZetaData.continuedL 0` takes the analytic normal
form value `-1/2 = ζ(0)` rather than the raw quotient `completedRiemannZeta 0 / Gammaℝ 0 = 0`. At
`s = 1`, `Γ_ℝ(1) ≠ 0` leaves the pole uncancelled, so `riemannZetaData.continuedL 1` retains the raw
quotient `completedRiemannZeta 1 / Gammaℝ 1 = riemannZeta 1`. Consequently,
`riemannZetaData.continuedL` agrees with Mathlib's `riemannZeta` at every point of `ℂ`.

## Main results

* `TauCeti.LFunctions.riemannZetaData_continuedL`: `riemannZetaData.continuedL = riemannZeta`.
-/

public section

open Complex Filter Topology

namespace TauCeti.LFunctions

/-- **The continued uncompleted L-function of `riemannZetaData` is `riemannZeta` everywhere on
`ℂ`**, including at the cancelled pole `0` (`ζ(0) = -1/2`), the uncancelled pole `1`, and the
trivial zeros `-2(n + 1)`. -/
@[simp]
theorem riemannZetaData_continuedL : riemannZetaData.continuedL = riemannZeta := by
  ext s
  rcases eq_or_ne s 0 with rfl | hs0
  · have hΓ0 : Gammaℝ 0 = 0 := (Gammaℝ_eq_zero_iff (s := 0)).mpr ⟨0, by norm_num⟩
    have hlt : meromorphicOrderAt riemannZetaData.gammaFactor 0 < 0 :=
      (riemannZetaData.meromorphicOrderAt_gammaFactor_neg_iff 0).mpr (by simp [hΓ0])
    lift meromorphicOrderAt riemannZetaData.gammaFactor 0 to ℤ using
      riemannZetaData.meromorphicOrderAt_gammaFactor_ne_top 0 with k hk
    have hle : (riemannZetaData.polarOrder 0 : WithTop ℤ) ≤
        meromorphicOrderAt riemannZetaData.invGammaFactor 0 := by
      have hk0 : k < 0 := WithTop.coe_lt_coe.mp hlt
      rw [riemannZetaData.meromorphicOrderAt_invGammaFactor, ← hk,
        ← WithTop.LinearOrderedAddCommGroup.coe_neg]
      simpa using WithTop.coe_le_coe.mpr (by omega : (1 : ℤ) ≤ -k)
    rw [riemannZetaData.continuedL_of_polarOrder_ne_zero (by simp) hle]
    refine (analyticOn_riemannZeta 0 zero_ne_one).toMeromorphicNFAt_apply_of_eventuallyEq ?_
    filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ 0)
    simp [riemannZetaData.invGammaFactor_def, riemannZeta_def_of_ne_zero hz, div_eq_mul_inv]
  · rcases eq_or_ne s 1 with rfl | hs1
    · rw [riemannZetaData.continuedL_of_gammaFactor_ne_zero (by simp)]
      simp [riemannZeta_def_of_ne_zero one_ne_zero, div_eq_mul_inv]
    · have hp : riemannZetaData.polarOrder s = 0 := by simp [Ne.symm hs0, Ne.symm hs1]
      rw [riemannZetaData.continuedL_of_polarOrder_eq_zero hp]
      simp [riemannZetaData.invGammaFactor_def, riemannZeta_def_of_ne_zero hs0, div_eq_mul_inv]

-- At `s = 0`, `continuedL` recovers the analytic continuation value `-1/2`, whereas the raw
-- quotient `completedRiemannZeta 0 / Gammaℝ 0` evaluates to the junk value `0`.
example : riemannZetaData.continuedL 0 = -1 / 2 ∧ completedRiemannZeta 0 / Gammaℝ 0 = 0 := by
  have hΓ0 : Gammaℝ 0 = 0 := Gammaℝ_eq_zero_iff.mpr ⟨0, by norm_num⟩
  simp [riemannZeta_zero, hΓ0]

-- At the trivial zero `s = -2`, `continuedL` vanishes while the completed function is regular and
-- nonzero (order `0`).
example :
    riemannZetaData.continuedL (-2) = 0 ∧
      meromorphicOrderAt riemannZetaData.completed (-2) = 0 := by
  have htriv : (-2 : ℂ) = -2 * ((0 : ℕ) + 1) := by norm_num
  rw [riemannZetaData_continuedL, riemannZetaData_completed, htriv]
  exact ⟨riemannZeta_neg_two_mul_nat_add_one 0,
    TauCeti.meromorphicOrderAt_completedRiemannZeta_neg_two_mul_nat_add_one 0⟩

end TauCeti.LFunctions
