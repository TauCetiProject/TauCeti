/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-!
# Best constants of weighted estimates

For a family of linear maps `L i : E → F` into a normed space and positive weights `w i`, the
best constant `C ≥ 0` in the estimates `‖L i a‖ ≤ C * w i` for all `i` is a seminorm
`Seminorm.weightedSup L w hw hL` on `E`, provided that every `a` satisfies some such estimate.
It is the supremum of `‖L i a‖ / w i`.

This is the common shape of the seminorms of spaces of functions defined by weighted bounds on
their derivatives, such as symbol classes: `i` runs over the points, `L i` evaluates a derivative
there and `w i` is the weight at that point.
-/

public section

noncomputable section

namespace Seminorm

variable {𝕜 E F ι : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  (L : ι → E →ₗ[𝕜] F) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (hL : ∀ a, ∃ C, ∀ i, ‖L i a‖ ≤ C * w i)

include hw hL in
private theorem bddAbove_range_norm_div (a : E) :
    BddAbove (Set.range fun i => ‖L i a‖ / w i) :=
  let ⟨C, hC⟩ := hL a
  ⟨C, Set.forall_mem_range.2 fun i => (div_le_iff₀ (hw i)).2 (hC i)⟩

include hw in
private theorem iSup_norm_div_nonneg (a : E) : 0 ≤ ⨆ i, ‖L i a‖ / w i :=
  Real.iSup_nonneg fun i => div_nonneg (norm_nonneg _) (hw i).le

/-- The best constant `C ≥ 0` in the estimates `‖L i a‖ ≤ C * w i` for all `i`, for linear maps
`L i` and positive weights `w i`: the supremum of `‖L i a‖ / w i`. -/
def weightedSup : Seminorm 𝕜 E :=
  Seminorm.ofSMulLE (fun a => ⨆ i, ‖L i a‖ / w i) (by simp)
    (fun a b => Real.iSup_le (fun i => calc
        ‖L i (a + b)‖ / w i ≤ ‖L i a‖ / w i + ‖L i b‖ / w i := by
          rw [map_add, ← add_div]
          exact div_le_div_of_nonneg_right (norm_add_le _ _) (hw i).le
        _ ≤ _ := add_le_add (le_ciSup (bddAbove_range_norm_div L w hw hL a) i)
          (le_ciSup (bddAbove_range_norm_div L w hw hL b) i))
      (add_nonneg (iSup_norm_div_nonneg L w hw a) (iSup_norm_div_nonneg L w hw b)))
    (fun c a => Real.iSup_le (fun i => by
        rw [map_smul, norm_smul, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (le_ciSup (bddAbove_range_norm_div L w hw hL a) i)
          (norm_nonneg c))
      (mul_nonneg (norm_nonneg c) (iSup_norm_div_nonneg L w hw a)))

/-- The seminorm `weightedSup L w hw hL` is the supremum of `‖L i a‖ / w i`. -/
@[simp]
theorem weightedSup_apply (a : E) : weightedSup L w hw hL a = ⨆ i, ‖L i a‖ / w i :=
  (rfl)

/-- The seminorm `weightedSup L w hw hL` is a constant in the estimates `‖L i a‖ ≤ C * w i`. -/
theorem norm_le_weightedSup (a : E) (i : ι) : ‖L i a‖ ≤ weightedSup L w hw hL a * w i :=
  (div_le_iff₀ (hw i)).1 (le_ciSup (bddAbove_range_norm_div L w hw hL a) i)

/-- A constant `C ≥ 0` in the estimates `‖L i a‖ ≤ C * w i` bounds `weightedSup L w hw hL a`. -/
theorem weightedSup_le {a : E} {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ‖L i a‖ ≤ C * w i) :
    weightedSup L w hw hL a ≤ C :=
  Real.iSup_le (fun i => (div_le_iff₀ (hw i)).2 (h i)) hC

/-- The seminorm `weightedSup L w hw hL a` is at most `C ≥ 0` exactly when `C` is a constant in
the estimates `‖L i a‖ ≤ C * w i`. -/
theorem weightedSup_le_iff {a : E} {C : ℝ} (hC : 0 ≤ C) :
    weightedSup L w hw hL a ≤ C ↔ ∀ i, ‖L i a‖ ≤ C * w i :=
  ⟨fun h i => (norm_le_weightedSup L w hw hL a i).trans
    (mul_le_mul_of_nonneg_right h (hw i).le), weightedSup_le L w hw hL hC⟩

end Seminorm
