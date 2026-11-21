/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Analysis.Normed.Lp.PiLp

/-!
# Bochner integral moment identities and bounds for `PiLp`

For a finite family of seminormed additive groups `E : ι → Type*` and `0 < p < ∞`, lifting
`PiLp.norm_rpow_eq_sum` to Bochner integrals yields `TauCeti.integrable_piLp_norm_rpow_iff`,
`TauCeti.sum_integral_norm_rpow_eq_integral_norm_rpow`, and moment bounds against an integrable
majorant (`TauCeti.sum_integral_norm_rpow_le_integral`) or a.e. constant norm bound on a finite or
probability space (`TauCeti.sum_integral_norm_rpow_le_measureReal_mul_rpow`,
`TauCeti.sum_integral_norm_rpow_le_rpow`).
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype ι]
  {p : ℝ≥0∞} {E : ι → Type*} [∀ i, SeminormedAddGroup (E i)]

/-- For `0 < p.toReal` and `f : α → PiLp p E` with `t ↦ ‖f t i‖` a.e. measurable for each `i`,
`t ↦ ‖f t‖ ^ p.toReal` is integrable iff every coordinate power `t ↦ ‖f t i‖ ^ p.toReal` is. -/
theorem integrable_piLp_norm_rpow_iff (hp : 0 < p.toReal) {f : α → PiLp p E}
    (hm : ∀ i, AEMeasurable (fun t ↦ ‖f t i‖) μ) :
    Integrable (fun t ↦ ‖f t‖ ^ p.toReal) μ ↔ ∀ i, Integrable (fun t ↦ ‖f t i‖ ^ p.toReal) μ := by
  refine ⟨fun hf i ↦ hf.mono' ((hm i).pow_const p.toReal).aestronglyMeasurable
    (.of_forall fun t ↦ ?_), fun hf ↦ (integrable_finsetSum _ fun i _ ↦ hf i).congr
    (.of_forall fun t ↦ (PiLp.norm_rpow_eq_sum hp (f t)).symm)⟩
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), PiLp.norm_rpow_eq_sum hp]
  exact Finset.single_le_sum (fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) (Finset.mem_univ i)

/-- For `0 < p.toReal` and `f : α → PiLp p E` with integrable coordinate powers, the sum of the
coordinate `p.toReal`-th moment integrals equals `∫ t, ‖f t‖ ^ p.toReal ∂μ`. -/
theorem sum_integral_norm_rpow_eq_integral_norm_rpow (hp : 0 < p.toReal) {f : α → PiLp p E}
    (hf : ∀ i, Integrable (fun t ↦ ‖f t i‖ ^ p.toReal) μ) :
    ∑ i, ∫ t, ‖f t i‖ ^ p.toReal ∂μ = ∫ t, ‖f t‖ ^ p.toReal ∂μ :=
  (integral_finsetSum _ fun i _ ↦ hf i).symm.trans <|
    integral_congr_ae (.of_forall fun t ↦ (PiLp.norm_rpow_eq_sum hp (f t)).symm)

/-- For `0 < p.toReal` and an integrable majorant `g` with `‖f t‖ ^ p.toReal ≤ g t` a.e.,
`∑ i, ∫ t, ‖f t i‖ ^ p.toReal ∂μ ≤ ∫ t, g t ∂μ`. Non-integrable coordinates have integral `0`, so
no measurability hypothesis on `f` is needed. -/
theorem sum_integral_norm_rpow_le_integral (hp : 0 < p.toReal) {f : α → PiLp p E} {g : α → ℝ}
    (hg : Integrable g μ) (hf : ∀ᵐ t ∂μ, ‖f t‖ ^ p.toReal ≤ g t) :
    ∑ i, ∫ t, ‖f t i‖ ^ p.toReal ∂μ ≤ ∫ t, g t ∂μ := by
  classical
  let s := Finset.univ.filter fun i : ι ↦ Integrable (fun t ↦ ‖f t i‖ ^ p.toReal) μ
  have hint (i : ι) (hi : i ∈ s) := (Finset.mem_filter.1 hi).2
  rw [← Finset.sum_subset (Finset.filter_subset _ _) fun _ _ hi ↦
      integral_undef (by simpa [s] using hi), ← integral_finsetSum s hint]
  exact integral_mono_ae (integrable_finsetSum s hint) hg <| hf.mono fun t ht ↦
    ((Finset.sum_le_univ_sum_of_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _).trans_eq
      (PiLp.norm_rpow_eq_sum hp (f t)).symm).trans ht

/-- On a finite measure space, if `0 < p.toReal` and `‖f t‖ ≤ C` a.e., then
`∑ i, ∫ t, ‖f t i‖ ^ p.toReal ∂μ ≤ μ.real Set.univ * C ^ p.toReal`. -/
theorem sum_integral_norm_rpow_le_measureReal_mul_rpow [IsFiniteMeasure μ] (hp : 0 < p.toReal)
    {f : α → PiLp p E} {C : ℝ} (hf : ∀ᵐ t ∂μ, ‖f t‖ ≤ C) :
    ∑ i, ∫ t, ‖f t i‖ ^ p.toReal ∂μ ≤ μ.real Set.univ * C ^ p.toReal := by
  simpa [integral_const, smul_eq_mul] using sum_integral_norm_rpow_le_integral hp
    (integrable_const (C ^ p.toReal))
    (hf.mono fun _ ht ↦ Real.rpow_le_rpow (PiLp.norm_nonneg' _) ht hp.le)

/-- On a probability space, if `0 < p.toReal` and `‖f t‖ ≤ C` a.e., then
`∑ i, ∫ t, ‖f t i‖ ^ p.toReal ∂μ ≤ C ^ p.toReal`. -/
theorem sum_integral_norm_rpow_le_rpow [IsProbabilityMeasure μ] (hp : 0 < p.toReal)
    {f : α → PiLp p E} {C : ℝ} (hf : ∀ᵐ t ∂μ, ‖f t‖ ≤ C) :
    ∑ i, ∫ t, ‖f t i‖ ^ p.toReal ∂μ ≤ C ^ p.toReal := by
  simpa using sum_integral_norm_rpow_le_measureReal_mul_rpow hp hf

end TauCeti
