/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Algebra.Order.Group.MinMax
public import TauCeti.Algebra.Order.Field.Clipping
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence

/-!
# Bounds and convergence for clipping

`MeasureTheory.MemLp.max_min` shows that clipping a real `Lᵖ` function to `[-M, M]`, for
`0 ≤ M`, preserves `Lᵖ` membership for any measure. For `M > 0`,
`MeasureTheory.Integrable.integral_sq_sub_max_min_le` bounds the integrated squared clipping
error by the fourth moment divided by `16 M²`, using the pointwise inequality from
`TauCeti.Algebra.Order.Field.Clipping`. This controls the `L²` error of clipping Gaussian
linear observables in the truncation proof of Grothendieck's inequality.

`MeasureTheory.AEStronglyMeasurable.memLp_top_max_min` gives the essential bound for clipping
an a.e. strongly measurable real function. `TauCeti.tendsto_eLpNorm_max_min_smul_sub` gives
finite-exponent `Lᵖ` convergence of clipped scalar multipliers whenever the original product
lies in `Lᵖ`, without any topology on the domain.

The expression `max (-M) (min M x)` is the real-valued form of `Set.projIcc`.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §8.1.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}

/-- Clipping a real `Lᵖ` function to a symmetric interval preserves `Lᵖ` membership,
without a finiteness assumption on the measure. -/
theorem MemLp.max_min {p : ℝ≥0∞} (hf : MemLp f p μ) {M : ℝ} (hM : 0 ≤ M) :
    MemLp (fun x ↦ max (-M) (min M (f x))) p μ := by
  have hcont : Continuous (fun t : ℝ ↦ max (-M) (min M t)) := by fun_prop
  refine hf.norm.mono' (hcont.comp_aestronglyMeasurable hf.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun x ↦ TauCeti.abs_max_min_le_abs hM (f x)

/-- Clipping an a.e. strongly measurable real function at any real height is essentially
bounded, without a finiteness assumption on the measure. -/
theorem AEStronglyMeasurable.memLp_top_max_min (hf : AEStronglyMeasurable f μ) (M : ℝ) :
    MemLp (fun x ↦ max (-M) (min M (f x))) ∞ μ := by
  have hcont : Continuous (fun t : ℝ ↦ max (-M) (min M t)) := by fun_prop
  refine memLp_top_of_bound (hcont.comp_aestronglyMeasurable hf) |M| ?_
  exact Filter.Eventually.of_forall fun x ↦ TauCeti.abs_max_min_le M (f x)

/-- The squared `L²` clipping error is bounded by the fourth moment divided by `16 M²`. -/
theorem Integrable.integral_sq_sub_max_min_le
    (hf₄ : Integrable (fun x ↦ f x ^ 4) μ) {M : ℝ} (hM : 0 < M) :
    (∫ x, (f x - max (-M) (min M (f x))) ^ 2 ∂μ) ≤
      (∫ x, f x ^ 4 ∂μ) / (16 * M ^ 2) := by
  rw [← integral_div]
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
    (hf₄.div_const _)
    (Filter.Eventually.of_forall fun x ↦ TauCeti.sq_sub_max_min_le_pow_four_div hM (f x))

end MeasureTheory

namespace TauCeti

open Filter
open scoped Topology

/-- Clipped scalar multipliers converge in every finite-exponent `Lᵖ` space whenever the
original product lies there. No topology on the domain or integrability of the multiplier
alone is required. -/
theorem tendsto_eLpNorm_max_min_smul_sub {X F : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {b : X → ℝ} {f : X → F} {p : ℝ≥0∞}
    (hp : p ≠ ∞) (hb : AEStronglyMeasurable b μ) (hf : AEStronglyMeasurable f μ)
    (hbf : MemLp (fun x ↦ b x • f x) p μ) :
    Tendsto (fun M : ℝ ↦ eLpNorm
      (fun x ↦ max (-M) (min M (b x)) • f x - b x • f x) p μ) atTop (𝓝 0) := by
  have hcont (M : ℝ) : Continuous (fun t : ℝ ↦ max (-M) (min M t)) := by fun_prop
  refine tendsto_eLpNorm_sub_of_ae_tendsto (C := 2) hp
    (.of_forall fun M ↦ ((hcont M).comp_aestronglyMeasurable hb).smul hf) hbf
    ((eventually_ge_atTop 0).mono fun M hM ↦ .of_forall fun x ↦ ?_)
    (.of_forall fun x ↦ tendsto_const_nhds.congr' ?_)
  · simp only [ENNReal.coe_ofNat]
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc
      ‖max (-M) (min M (b x)) • f x - b x • f x‖ ≤
          ‖max (-M) (min M (b x)) • f x‖ + ‖b x • f x‖ := norm_sub_le _ _
      _ ≤ ‖b x • f x‖ + ‖b x • f x‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
        exact add_le_add
          (mul_le_mul_of_nonneg_right (abs_max_min_le_abs hM (b x)) (norm_nonneg (f x))) le_rfl
      _ = 2 * ‖b x • f x‖ := (two_mul _).symm
  · filter_upwards [eventually_ge_atTop |b x|] with M hM
    have h := abs_le.1 hM
    simp [min_eq_right h.2, max_eq_right h.1]

end TauCeti
