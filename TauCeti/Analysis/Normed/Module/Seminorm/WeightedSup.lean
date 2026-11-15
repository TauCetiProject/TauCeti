/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Norm

/-!
# Best constants of weighted estimates

For a family of linear maps `L i : E → F` into a normed space and positive weights `w i`, the
best constant `C ≥ 0` in the estimates `‖L i a‖ ≤ C * w i` for all `i` is a seminorm
`Seminorm.weightedSup L w hw` on `E`, provided that every `a` satisfies some such estimate. It is
the supremum, in the lattice of seminorms, of the seminorms `a ↦ ‖L i a‖ / w i`.

This is the common shape of the seminorms of spaces of functions defined by weighted bounds on
their derivatives, such as symbol classes: `i` runs over the points, `L i` evaluates a derivative
there and `w i` is the weight at that point.
-/

public section

noncomputable section

open scoped NNReal

namespace Seminorm

variable {𝕜 E F ι : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  (L : ι → E →ₗ[𝕜] F) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (hL : ∀ a, ∃ C, ∀ i, ‖L i a‖ ≤ C * w i)

/-- The coefficient `(w i)⁻¹` of the seminorm `a ↦ ‖L i a‖ / w i`, as a nonnegative real. -/
private def invWeight (i : ι) : ℝ≥0 := ⟨(w i)⁻¹, inv_nonneg.2 (hw i).le⟩

private theorem coe_invWeight (i : ι) : (invWeight w hw i : ℝ) = (w i)⁻¹ :=
  NNReal.coe_mk _ _

/-- The best constant `C ≥ 0` in the estimates `‖L i a‖ ≤ C * w i` for all `i`, for linear maps
`L i` and positive weights `w i`: the supremum of the seminorms `a ↦ ‖L i a‖ / w i`. When every
`a` satisfies some such estimate, it is the supremum of `‖L i a‖ / w i`
(`Seminorm.weightedSup_apply`). -/
def weightedSup : Seminorm 𝕜 E :=
  ⨆ i, invWeight w hw i • (normSeminorm 𝕜 F).comp (L i)

/-- The seminorms `a ↦ ‖L i a‖ / w i` whose supremum is `weightedSup L w hw`. -/
private theorem smul_comp_normSeminorm_apply (i : ι) (a : E) :
    (invWeight w hw i • (normSeminorm 𝕜 F).comp (L i)) a =
      ‖L i a‖ / w i := by
  simp [NNReal.smul_def, coe_invWeight, div_eq_inv_mul]

/-- The seminorms `a ↦ ‖L i a‖ / w i` are bounded above exactly when every `a` satisfies an
estimate `‖L i a‖ ≤ C * w i` for all `i`. -/
private theorem bddAbove_range_smul_comp_normSeminorm_iff :
    BddAbove (Set.range fun i => invWeight w hw i • (normSeminorm 𝕜 F).comp (L i)) ↔
      ∀ a, ∃ C, ∀ i, ‖L i a‖ ≤ C * w i := by
  simp_rw [Seminorm.bddAbove_range_iff, smul_comp_normSeminorm_apply L w hw, bddAbove_def,
    Set.forall_mem_range, div_le_iff₀ (hw _)]

include hL in
/-- The seminorm `weightedSup L w hw` is the supremum of `‖L i a‖ / w i`. -/
theorem weightedSup_apply (a : E) : weightedSup L w hw a = ⨆ i, ‖L i a‖ / w i := by
  rw [weightedSup, Seminorm.iSup_apply ((bddAbove_range_smul_comp_normSeminorm_iff L w hw).2 hL)]
  simp_rw [smul_comp_normSeminorm_apply L w hw]

include hL in
/-- The seminorm `weightedSup L w hw` is a constant in the estimates `‖L i a‖ ≤ C * w i`. -/
theorem norm_le_weightedSup (a : E) (i : ι) : ‖L i a‖ ≤ weightedSup L w hw a * w i := by
  rw [weightedSup_apply L w hw hL, ← div_le_iff₀ (hw i)]
  obtain ⟨C, hC⟩ := hL a
  exact le_ciSup ⟨C, Set.forall_mem_range.2 fun j => (div_le_iff₀ (hw j)).2 (hC j)⟩ i

/-- Without an estimate `‖L i a‖ ≤ C * w i` for every `a`, the supremum `weightedSup L w hw` is
the junk value `⊥`. Mathlib has no API for unbounded suprema of seminorms, so this unfolds the
definition of `Seminorm.instSupSet`. -/
private theorem weightedSup_eq_bot (h : ¬∀ a, ∃ C, ∀ i, ‖L i a‖ ≤ C * w i) :
    weightedSup L w hw = ⊥ := by
  have hb := Seminorm.bddAbove_iff.not.1
    ((bddAbove_range_smul_comp_normSeminorm_iff L w hw).not.2 h)
  simp only [weightedSup, iSup, sSup, hb, dite_false]

/-- A constant `C ≥ 0` in the estimates `‖L i a‖ ≤ C * w i` bounds `weightedSup L w hw a`. -/
theorem weightedSup_le {a : E} {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ‖L i a‖ ≤ C * w i) :
    weightedSup L w hw a ≤ C := by
  by_cases hL : ∀ b, ∃ C, ∀ i, ‖L i b‖ ≤ C * w i
  · rw [weightedSup_apply L w hw hL]
    exact Real.iSup_le (fun i => (div_le_iff₀ (hw i)).2 (h i)) hC
  rw [weightedSup_eq_bot L w hw hL, coe_bot, Pi.zero_apply]
  exact hC

include hL in
/-- The seminorm `weightedSup L w hw a` is at most `C ≥ 0` exactly when `C` is a constant in
the estimates `‖L i a‖ ≤ C * w i`. -/
theorem weightedSup_le_iff {a : E} {C : ℝ} (hC : 0 ≤ C) :
    weightedSup L w hw a ≤ C ↔ ∀ i, ‖L i a‖ ≤ C * w i :=
  ⟨fun h i => (norm_le_weightedSup L w hw hL a i).trans
    (mul_le_mul_of_nonneg_right h (hw i).le), weightedSup_le L w hw hC⟩

end Seminorm
