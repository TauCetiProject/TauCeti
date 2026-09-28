/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Class number one from a small discriminant

Minkowski's bound, in the form of Mathlib's
`NumberField.RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt`, makes `𝓞 K` a principal ideal
domain as soon as `|discr K| < (2 (π/4)^{r₂} nⁿ/n!)²`, where `n = [K : ℚ]` and `r₂` is the
number of complex places. In degree two the right-hand side is `16` for `r₂ = 0` and `π² > 9`
for `r₂ = 1`; in degree three it is `81` for `r₂ = 0` and `(9π/4)² > 49` for `r₂ = 1`. This
file records the two integer thresholds: a quadratic field with `|discr K| ≤ 9` and a cubic
field with `|discr K| ≤ 49` have class number `1`.

The proofs follow the pattern of Mathlib's `IsCyclotomicExtension.Rat.three_pid` and `five_pid`
in `Mathlib.NumberTheory.NumberField.Cyclotomic.PID`, with the signature left free and the
discriminant bounded by an integer instead of computed.

## Main results

* `TauCeti.NumberField.isPrincipalIdealRing_of_finrank_eq_two_of_natAbs_discr_le_nine`: a
  quadratic field with `|discr K| ≤ 9` has `𝓞 K` a principal ideal domain.
* `TauCeti.NumberField.isPrincipalIdealRing_of_finrank_eq_three_of_natAbs_discr_le_forty_nine`:
  a cubic field with `|discr K| ≤ 49` has `𝓞 K` a principal ideal domain.
-/

public section

open NumberField NumberField.InfinitePlace Real Nat

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Quadratic fields of discriminant at most `9` in absolute value have class number `1`.**
Minkowski's bound is `16` when `K` is real and `π² > 9` when `K` is imaginary. -/
theorem isPrincipalIdealRing_of_finrank_eq_two_of_natAbs_discr_le_nine
    (hfin : Module.finrank ℚ K = 2) (hdisc : (discr K).natAbs ≤ 9) :
    IsPrincipalIdealRing (𝓞 K) := by
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  have h9 : (|discr K| : ℝ) ≤ 9 := by
    have : |discr K| ≤ (9 : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hdisc
    exact_mod_cast this
  have hr : nrComplexPlaces K = 0 ∨ nrComplexPlaces K = 1 := by
    have := card_add_two_mul_card_eq_rank K
    rw [hfin] at this
    omega
  rw [hfin, Int.cast_abs]
  simp only [Nat.cast_ofNat, factorial_two]
  rcases hr with hr | hr <;> rw [hr] <;> refine h9.trans_lt ?_
  · norm_num
  · nlinarith [pi_gt_three]

/-- **Cubic fields of discriminant at most `49` in absolute value have class number `1`.**
Minkowski's bound is `81` when `K` is totally real and `(9π/4)² > 49` when `K` has a complex
place. -/
theorem isPrincipalIdealRing_of_finrank_eq_three_of_natAbs_discr_le_forty_nine
    (hfin : Module.finrank ℚ K = 3) (hdisc : (discr K).natAbs ≤ 49) :
    IsPrincipalIdealRing (𝓞 K) := by
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  have h49 : (|discr K| : ℝ) ≤ 49 := by
    have : |discr K| ≤ (49 : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hdisc
    exact_mod_cast this
  have hr : nrComplexPlaces K = 0 ∨ nrComplexPlaces K = 1 := by
    have := card_add_two_mul_card_eq_rank K
    rw [hfin] at this
    omega
  have hfac : (3 : ℕ)! = 6 := by norm_num [Nat.factorial]
  rw [hfin, Int.cast_abs]
  simp only [Nat.cast_ofNat, hfac]
  rcases hr with hr | hr <;> rw [hr] <;> refine h49.trans_lt ?_
  · norm_num
  · nlinarith [pi_gt_d2]

end TauCeti.NumberField
