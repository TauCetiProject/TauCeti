/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# `ℓ^p` norms as `L^p` seminorms of the counting measure

On a countable type with measurable singletons, the `L^p` seminorm `eLpNorm f p count` of a
function `f` for the counting measure is its `ℓ^p` norm: the sum `(∑' i, ‖f i‖ ^ p) ^ (1 / p)` for
finite `p` and the supremum `⨆ i, ‖f i‖` for `p = ∞`. This file records these formulas and the
resulting comparison with Mathlib's sequence spaces `lp`: `f` lies in `ℓ^p` exactly when its
counting-measure seminorm is finite, and for `f ∈ lp` the seminorm is the `lp` norm.

This lets estimates proved with the measure-theoretic `L^p` machinery, such as Schur's test for
integral kernels, be read as estimates in `lp`.

## Main results

* `MeasureTheory.eLpNorm_count_eq_tsum`, `MeasureTheory.eLpNorm_count_top`: the two formulas.
* `MeasureTheory.memℓp_iff_eLpNorm_count_lt_top`: `Memℓp f p ↔ eLpNorm f p count < ∞`.
* `lp.eLpNorm_count`: `eLpNorm f p count = ‖f‖ₑ` for `f ∈ lp`.
-/

public section

open MeasureTheory Measure Set
open scoped ENNReal NNReal

variable {α ε E : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  [TopologicalSpace ε] [ContinuousENorm ε] [NormedAddCommGroup E] {p : ℝ≥0∞}

namespace MeasureTheory

/-- For finite `p ≠ 0`, the `L^p` seminorm for the counting measure is
`(∑' i, ‖f i‖ ^ p) ^ (1 / p)`. -/
theorem eLpNorm_count_eq_tsum (hp0 : p ≠ 0) (hp : p ≠ ∞) (f : α → ε) :
    eLpNorm f p count = (∑' i, ‖f i‖ₑ ^ p.toReal) ^ (1 / p.toReal) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp .of_discrete, lintegral_count]

/-- The `L^∞` seminorm for the counting measure is the supremum `⨆ i, ‖f i‖`. -/
theorem eLpNorm_count_top (f : α → ε) : eLpNorm f ∞ count = ⨆ i, ‖f i‖ₑ := by
  rw [eLpNorm_exponent_top .of_discrete, eLpNormEssSup_count]

/-- A function lies in `ℓ^p` exactly when its `L^p` seminorm for the counting measure is
finite. -/
theorem memℓp_iff_eLpNorm_count_lt_top {f : α → E} (hp : p ≠ 0) :
    Memℓp f p ↔ eLpNorm f p count < ∞ := by
  rcases eq_or_ne p ∞ with rfl | hp_top
  · simp only [memℓp_infty_iff, eLpNorm_count_top, ← ofReal_norm, ← coe_nnnorm,
      ENNReal.ofReal_coe_nnreal, ENNReal.iSup_coe_lt_top]
    rw [← NNReal.bddAbove_coe, ← range_comp]
    rfl
  have hp' : 0 < p.toReal := ENNReal.toReal_pos hp hp_top
  have hterm (i : α) : ‖f i‖ₑ ^ p.toReal = ((‖f i‖₊ ^ p.toReal : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_rpow_of_nonneg _ hp'.le, enorm_eq_nnnorm]
  rw [memℓp_gen_iff hp', eLpNorm_count_eq_tsum hp hp_top,
    ENNReal.rpow_lt_top_iff_of_pos (one_div_pos.2 hp'), lt_top_iff_ne_top]
  simp only [hterm, ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe,
    NNReal.coe_rpow, coe_nnnorm]

end MeasureTheory

namespace lp

/-- For `f ∈ ℓ^p`, the `L^p` seminorm of `f` for the counting measure is its `ℓ^p` norm. -/
theorem eLpNorm_count [Fact (1 ≤ p)] (f : lp (fun _ : α ↦ E) p) :
    eLpNorm (⇑f) p count = ‖f‖ₑ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  rcases eq_or_ne p ∞ with rfl | hp_top
  · refine (eLpNorm_count_top _).trans (le_antisymm (iSup_le fun i ↦ ?_) ?_)
    · simpa only [enorm_le_iff_norm_le] using lp.norm_apply_le_norm hp0 f i
    · have hfin : (⨆ i, ‖f i‖ₑ) ≠ ∞ := by
        rw [← eLpNorm_count_top]
        exact ((memℓp_iff_eLpNorm_count_lt_top hp0).1 (lp.memℓp f)).ne
      rw [← ofReal_norm, ← ENNReal.ofReal_toReal hfin]
      refine ENNReal.ofReal_le_ofReal (lp.norm_le_of_forall_le ENNReal.toReal_nonneg fun i ↦ ?_)
      rw [← toReal_enorm]
      exact ENNReal.toReal_mono hfin (le_iSup (fun i ↦ ‖f i‖ₑ) i)
  have hp' : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have hsum : Summable fun i ↦ ‖f i‖ ^ p.toReal := (memℓp_gen_iff hp').1 (lp.memℓp f)
  rw [eLpNorm_count_eq_tsum hp0 hp_top, ← ofReal_norm, lp.norm_eq_tsum_rpow hp',
    ← ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg fun i ↦ by positivity) (by positivity),
    ENNReal.ofReal_tsum_of_nonneg (fun i ↦ by positivity) hsum]
  simp only [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp'.le]

end lp
