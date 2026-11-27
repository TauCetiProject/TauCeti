/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Complex analyticity of the Gamma prefactor `Γ(2b) / Γ(b)²`

Since `Complex.Gamma` is complex analytic away from the nonpositive integers
(`Complex.analyticAt_Gamma` in `TauCeti.Analysis.SpecialFunctions.Gamma.Basic`) and does not
vanish away from `-ℕ`, the zero-balanced prefactor `b ↦ Γ(2b) / Γ(b)²` is analytic wherever `2b`
avoids `-ℕ` (`TauCeti.analyticAt_Gamma_two_mul_div_Gamma_sq`,
`TauCeti.analyticOnNhd_Gamma_two_mul_div_Gamma_sq`).

## Main results

* `TauCeti.ne_neg_natCast_of_two_mul_ne`: if `2 * a ∉ -ℕ`, then `a ∉ -ℕ`.
* `TauCeti.analyticAt_Gamma_two_mul_div_Gamma_sq` and
  `TauCeti.analyticOnNhd_Gamma_two_mul_div_Gamma_sq`: complex analyticity of
  `b ↦ Γ(2b) / Γ(b)²` away from `2b ∈ -ℕ`.
-/

public section

namespace TauCeti

/-- If `2 * a` is not a nonpositive integer, then `a` is not a nonpositive integer. -/
theorem ne_neg_natCast_of_two_mul_ne {α : Type*} [CommRing α] {a : α}
    (ha : ∀ n : ℕ, 2 * a ≠ -(n : α)) (m : ℕ) : a ≠ -(m : α) := fun hm ↦
  ha (2 * m) (by push_cast; linear_combination 2 * hm)

/-- The zero-balanced prefactor `b ↦ Γ(2b) / Γ(b)²` is analytic wherever `2b` is not a nonpositive
integer. -/
theorem analyticAt_Gamma_two_mul_div_Gamma_sq {b : ℂ} (hb : ∀ n : ℕ, 2 * b ≠ -(n : ℂ)) :
    AnalyticAt ℂ (fun z : ℂ ↦ Complex.Gamma (2 * z) / Complex.Gamma z ^ 2) b := by
  have hb' := ne_neg_natCast_of_two_mul_ne hb
  exact ((Complex.analyticAt_Gamma hb).comp (analyticAt_const.mul analyticAt_id)).div
    ((Complex.analyticAt_Gamma hb').pow 2) (pow_ne_zero 2 (Complex.Gamma_ne_zero hb'))

/-- The zero-balanced prefactor `b ↦ Γ(2b) / Γ(b)²` is analytic on
`{b : ℂ | ∀ n : ℕ, 2 * b ≠ -(n : ℂ)}`. -/
theorem analyticOnNhd_Gamma_two_mul_div_Gamma_sq :
    AnalyticOnNhd ℂ (fun b : ℂ ↦ Complex.Gamma (2 * b) / Complex.Gamma b ^ 2)
      {b : ℂ | ∀ n : ℕ, 2 * b ≠ -(n : ℂ)} :=
  fun _ hb ↦ analyticAt_Gamma_two_mul_div_Gamma_sq hb

end TauCeti
