/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Integrable functions vanishing against bounded continuous functions

If an integrable function `f` on a topological space satisfies `∫ g • f ∂μ = 0` for every bounded
continuous real function `g`, then `f = 0` almost everywhere. This is the form in which uniqueness
theorems for integral transforms are usually applied: one first shows that the integrals of `f`
against a dense family of test functions vanish (for instance trigonometric polynomials on the
circle), extends this by continuity to all bounded continuous functions, and concludes here.

The space only needs indicators of closed sets to be pointwise limits of bounded continuous
functions with values in `[0, 1]` (Mathlib's `HasOuterApproxClosed`, which holds for every
pseudo-metrizable space). Dominated convergence then gives `∫_F f ∂μ = 0` for every closed set
`F`, and Mathlib's `MeasureTheory.ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero` concludes.
No finiteness of `μ` is needed beyond the integrability of `f`.

## Main results

* `MeasureTheory.Integrable.ae_eq_zero_of_forall_integral_smul_eq_zero`: an integrable function
  whose integrals against all bounded continuous real functions vanish is zero almost everywhere.
* `MeasureTheory.Integrable.ae_eq_of_forall_integral_smul_eq`: two integrable functions with the
  same integrals against all bounded continuous real functions agree almost everywhere.
-/

public section

open Filter Set Topology
open scoped BoundedContinuousFunction NNReal

namespace MeasureTheory

variable {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [HasOuterApproxClosed X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f g : X → E}

/-- **Integrable functions are determined by their integrals against bounded continuous
functions.** If `f` is integrable and `∫ x, φ x • f x ∂μ = 0` for every bounded continuous
`φ : X → ℝ`, then `f = 0` almost everywhere. -/
theorem Integrable.ae_eq_zero_of_forall_integral_smul_eq_zero (hf : Integrable f μ)
    (h : ∀ φ : X →ᵇ ℝ, ∫ x, φ x • f x ∂μ = 0) : f =ᵐ[μ] 0 := by
  refine ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero hf fun F hF ↦ ?_
  -- The real-valued versions of the continuous approximations of the indicator of `F`.
  let φ (n : ℕ) : X →ᵇ ℝ :=
    ⟨⟨fun x ↦ hF.apprSeq n x, NNReal.continuous_coe.comp (hF.apprSeq n).continuous⟩,
      (hF.apprSeq n).map_bounded'⟩
  have hφ (n : ℕ) (x : X) : φ n x = hF.apprSeq n x := rfl
  have hlim : Tendsto (fun n ↦ ∫ x, φ n x • f x ∂μ) atTop (𝓝 (∫ x in F, f x ∂μ)) := by
    rw [← integral_indicator hF.measurableSet]
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖f x‖)
      (fun n ↦ (φ n).continuous.aestronglyMeasurable.smul hf.aestronglyMeasurable) hf.norm
      (fun n ↦ ae_of_all _ fun x ↦ ?_) (ae_of_all _ fun x ↦ ?_)
    · rw [norm_smul, hφ, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (NNReal.coe_le_one.2 (HasOuterApproxClosed.apprSeq_apply_le_one hF n x))
    · have hx := (NNReal.continuous_coe.tendsto _).comp
        (tendsto_pi_nhds.1 (HasOuterApproxClosed.tendsto_apprSeq hF) x)
      by_cases hxF : x ∈ F
      · simpa [hφ, hxF] using hx.smul_const (f x)
      · simpa [hφ, hxF] using hx.smul_const (f x)
  simp only [h] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- Two integrable functions with the same integrals against every bounded continuous real
function agree almost everywhere. -/
theorem Integrable.ae_eq_of_forall_integral_smul_eq (hf : Integrable f μ) (hg : Integrable g μ)
    (h : ∀ φ : X →ᵇ ℝ, ∫ x, φ x • f x ∂μ = ∫ x, φ x • g x ∂μ) : f =ᵐ[μ] g := by
  have hfg : f - g =ᵐ[μ] 0 :=
    (hf.sub hg).ae_eq_zero_of_forall_integral_smul_eq_zero fun φ ↦ by
      have hφ (u : X → E) (hu : Integrable u μ) : Integrable (fun x ↦ φ x • u x) μ :=
        hu.bdd_smul ‖φ‖ φ.continuous.aestronglyMeasurable
          (ae_of_all _ fun x ↦ φ.norm_coe_le_norm x)
      simp_rw [Pi.sub_apply, smul_sub]
      rw [integral_sub (hφ f hf) (hφ g hg), h, sub_self]
  filter_upwards [hfg] with x hx
  simpa [sub_eq_zero] using hx

end MeasureTheory
