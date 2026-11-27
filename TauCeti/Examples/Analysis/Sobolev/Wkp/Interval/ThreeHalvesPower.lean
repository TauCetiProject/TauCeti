/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Interval.Power

/-!
# The power `x ^ (3/2)` on `(0, 1)`: in `W^{1,2}` but not in `W^{2,2}`

On `(0, 1)` the function `x ^ (3/2)` has derivative `(3/2) x ^ (1/2)`, which is bounded, and second
derivative `(3/4) x ^ (-1/2)`, whose square `(9/16) x⁻¹` is not integrable at `0`. So
`x ^ (3/2)` lies in `W^{1,2}(0, 1)`
(`TauCeti.Examples.UnitIntervalThreeHalvesPower.exists_value_ae_eq_rpow_three_halves_one`) but not
in `W^{2,2}(0, 1)`
(`TauCeti.Examples.UnitIntervalThreeHalvesPower.not_exists_value_ae_eq_rpow_three_halves_two`).
Hence the inclusion `W^{2,2}(0, 1) → W^{1,2}(0, 1)` is not surjective
(`TauCeti.Examples.UnitIntervalThreeHalvesPower.not_surjective_toOrderL`): the density of smooth
functions in the order-two space is a statement about a strictly smaller space than in the
order-one space.

Both memberships are the instances `s = 3/2`, `p = 2`, `k = 1, 2` of the description of the Sobolev
classes containing a power, `TauCeti.Wkp.exists_value_ae_eq_rpow_const_Ioo_iff`: `x ^ s` lies in
`W^{k,p}(0, b)` exactly when `s` is one of `0, …, k - 1` or `-1 < (s - k) p`, and
`(3/2 - 2) · 2 = -1` is the borderline case.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti.Examples.UnitIntervalThreeHalvesPower

/-- `x ^ (3/2)` lies in `W^{1,2}(0, 1)`. -/
theorem exists_value_ae_eq_rpow_three_halves_one :
    ∃ u : Wkp volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ 2 1,
      (Wkp.value 1 u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo 0 1)] fun x => x ^ (3 / 2 : ℝ) :=
  (Wkp.exists_value_ae_eq_rpow_const_Ioo_iff (p := 2) one_pos ENNReal.ofNat_ne_top 1).2
    (.inr (by norm_num))

/-- `x ^ (3/2)` does not lie in `W^{2,2}(0, 1)`: its second derivative `(3/4) x ^ (-1/2)` is not
square integrable. -/
theorem not_exists_value_ae_eq_rpow_three_halves_two :
    ¬ ∃ u : Wkp volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ 2 2,
      (Wkp.value 2 u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo 0 1)] fun x => x ^ (3 / 2 : ℝ) := by
  rw [Wkp.exists_value_ae_eq_rpow_const_Ioo_iff (p := 2) one_pos ENNReal.ofNat_ne_top 2]
  rintro (⟨m, hm, h⟩ | h)
  · interval_cases m <;> norm_num at h
  · norm_num at h

/-- The inclusion `W^{2,2}(0, 1) → W^{1,2}(0, 1)` is not surjective: `x ^ (3/2)` is not in its
range. -/
theorem not_surjective_toOrderL :
    ¬ Function.Surjective
      (Wkp.toOrderL (mu := volume) (Omega := ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩) (p := 2)
        (by norm_num : 1 ≤ 2)) := by
  intro h
  obtain ⟨u, hu⟩ := exists_value_ae_eq_rpow_three_halves_one
  obtain ⟨v, rfl⟩ := h u
  exact not_exists_value_ae_eq_rpow_three_halves_two ⟨v, by rwa [Wkp.value_toOrderL] at hu⟩

end TauCeti.Examples.UnitIntervalThreeHalvesPower
