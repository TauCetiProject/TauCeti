/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Scaling the unit half-open interval

For `ε > 0`, multiplication by `ε` is a homeomorphism `[0, 1) ≃ₜ [0, ε)` with inverse `s ↦ s / ε`
(`TauCeti.icoScale`). It rescales a depth parameter in `[0, 1)`, as for collars, to an interval
`[0, ε)` and back.

## Main definitions

* `TauCeti.icoScale`: the homeomorphism `[0, 1) ≃ₜ [0, ε)`, `t ↦ ε t`.
-/

public section

open Set

namespace TauCeti

variable {ε : ℝ}

/-- The scaling `t ↦ ε t` of half-open intervals, `[0, 1) ≃ₜ [0, ε)`, for `ε > 0`. -/
noncomputable def icoScale (hε : 0 < ε) : ↥(Ico (0 : ℝ) 1) ≃ₜ ↥(Ico (0 : ℝ) ε) where
  toFun t := ⟨ε * t, mul_nonneg hε.le t.2.1, mul_lt_of_lt_one_right hε t.2.2⟩
  invFun s := ⟨s / ε, div_nonneg s.2.1 hε.le, (div_lt_one hε).2 s.2.2⟩
  left_inv t := Subtype.ext (mul_div_cancel_left₀ _ hε.ne')
  right_inv s := Subtype.ext (mul_div_cancel₀ _ hε.ne')
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The scaling of `[0, 1)` onto `[0, ε)` is multiplication by `ε`. -/
@[simp]
theorem coe_icoScale (hε : 0 < ε) (t : ↥(Ico (0 : ℝ) 1)) : (icoScale hε t : ℝ) = ε * t :=
  (rfl)

/-- The inverse of the scaling of `[0, 1)` onto `[0, ε)` is division by `ε`. -/
@[simp]
theorem coe_icoScale_symm (hε : 0 < ε) (s : ↥(Ico (0 : ℝ) ε)) :
    ((icoScale hε).symm s : ℝ) = s / ε :=
  (rfl)

end TauCeti
