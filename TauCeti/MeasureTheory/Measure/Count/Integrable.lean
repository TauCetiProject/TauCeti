/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Integer-valued functions integrable for counting measure

An integer-valued function that is integrable on a set `K` for counting measure, as a real
function, is nonzero at only finitely many points of `K`: its absolute value is at least one on
its support, so its support in `K` has finite counting measure.

## Main declarations

* `MeasureTheory.IntegrableOn.finite_inter_support_of_count`: an integer-valued function
  integrable on `K` for counting measure has finite support in `K`.
-/

public section

open Set

namespace MeasureTheory.IntegrableOn

/-- An integer-valued function that is integrable on `K` as a real function for counting measure
is nonzero at only finitely many points of `K`, since its absolute value is at least one there. -/
theorem finite_inter_support_of_count {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] {θ : X → ℤ} {K : Set X}
    (h : IntegrableOn (fun x ↦ (θ x : ℝ)) K Measure.count) : (K ∩ Function.support θ).Finite := by
  have hsub : K ∩ Function.support θ ⊆ {x | 1 ≤ ‖(θ x : ℝ)‖} ∩ K := fun x hx ↦
    ⟨by simpa [Real.norm_eq_abs] using (Int.cast_le (R := ℝ)).2 (Int.one_le_abs hx.2), hx.1⟩
  exact Measure.count_apply_lt_top.1 (((measure_mono hsub).trans
    (Measure.le_restrict_apply _ _)).trans_lt (h.measure_norm_ge_lt_top one_pos))

end MeasureTheory.IntegrableOn
