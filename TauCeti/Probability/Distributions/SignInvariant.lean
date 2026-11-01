/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Rademacher
public import TauCeti.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Comparing a symmetric sum with its largest summand

For independent symmetric real coefficients with finite first moments, the expected
norm of a vector-valued sum dominates the expected maximum norm of its summands.
In particular, if all the fixed vectors have norm at least `a ≥ 0`, this bounds the
expected norm below by `a` times the expected maximum absolute coefficient.

The product-measure formulation applies in particular to independent centered
Gaussian coefficients. It separates the scalar maximum estimate from the geometric
estimate on the vectors, as needed in lower bounds for mean norms on spheres.
The range space need not be complete or finite-dimensional.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §13.3.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace TauCeti

variable {ι E : Type*} [Fintype ι]
  [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  (μ : ι → Measure ℝ)

/-- Independent symmetric coefficients give the same expected norm after any fixed
choice of signs. -/
theorem integral_norm_sum_sign_eq [∀ i, SigmaFinite (μ i)] [∀ i, (μ i).IsNegInvariant]
    (v : ι → E) (ε : ι → Bool) :
    (∫ x : ι → ℝ, ‖∑ i, if ε i then x i • v i else -(x i • v i)‖ ∂Measure.pi μ) =
      ∫ x : ι → ℝ, ‖∑ i, x i • v i‖ ∂Measure.pi μ := by
  let f : (ι → ℝ) → (ι → ℝ) := fun x i ↦ if ε i then x i else -x i
  have hp : MeasurePreserving f (Measure.pi μ) (Measure.pi μ) := by
    refine measurePreserving_pi μ μ (f := fun i x ↦ if ε i then x else -x) ?_
    intro i
    cases h : ε i
    · simpa [h] using Measure.measurePreserving_neg (μ i)
    · simp only [↓reduceIte]
      exact MeasurePreserving.id (μ i)
  have hc : Continuous (fun x : ι → ℝ ↦ ‖∑ i, x i • v i‖) := by fun_prop
  calc
    _ = ∫ x : ι → ℝ, ‖∑ i, f x i • v i‖ ∂Measure.pi μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [f, ite_smul, neg_smul]
    _ = ∫ x : ι → ℝ, ‖∑ i, x i • v i‖ ∂(Measure.pi μ).map f :=
      (integral_map hp.measurable.aemeasurable hc.aestronglyMeasurable).symm
    _ = _ := by rw [hp.map_eq]

variable [Nonempty ι] [∀ i, IsProbabilityMeasure (μ i)] [∀ i, (μ i).IsNegInvariant]

open Classical in
/-- For independent symmetric real coefficients, the expected norm of the sum is at
least the expected maximum norm of a summand. Only finite first moments are required. -/
theorem integral_max_norm_smul_le_integral_norm_sum
    (hμ : ∀ i, Integrable id (μ i)) (v : ι → E) :
    (∫ x : ι → ℝ, Finset.univ.sup' Finset.univ_nonempty (fun i ↦ ‖x i • v i‖)
      ∂Measure.pi μ) ≤ ∫ x : ι → ℝ, ‖∑ i, x i • v i‖ ∂Measure.pi μ := by
  have hi (i : ι) : Integrable (fun x : ι → ℝ ↦ ‖x i • v i‖) (Measure.pi μ) := by
    simpa [norm_smul] using
      ((measurePreserving_eval μ i).integrable_comp_of_integrable (hμ i)).norm.mul_const ‖v i‖
  have hs := integrable_finsetSum Finset.univ (fun i _ ↦ hi i)
  have hsign (ε : ι → Bool) : Integrable
      (fun x : ι → ℝ ↦ ‖∑ i, if ε i then x i • v i else -(x i • v i)‖)
      (Measure.pi μ) := by
    have hc : Continuous (fun x : ι → ℝ ↦
        ‖∑ i, if ε i then x i • v i else -(x i • v i)‖) := by
      have hc' : Continuous (fun x : ι → ℝ ↦ ‖∑ i, x i • (if ε i then v i else -v i)‖) :=
        by fun_prop
      simpa only [smul_ite, smul_neg] using hc'
    apply hs.mono' hc.aestronglyMeasurable
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_norm, apply_ite norm, norm_neg, ite_self] using
      norm_sum_le (s := Finset.univ) (f := fun i ↦ if ε i then x i • v i else -(x i • v i))
  have hmax := Finset.integrable_sup' Finset.univ_nonempty (fun i _ ↦ hi i)
  have havg : Integrable (fun x : ι → ℝ ↦
      𝔼 ε : ι → Bool, ‖∑ i, if ε i then x i • v i else -(x i • v i)‖)
      (Measure.pi μ) := by
    simpa only [Fintype.expect_eq_sum_div_card] using
      (integrable_finsetSum Finset.univ (fun ε _ ↦ hsign ε)).div_const
        (Fintype.card (ι → Bool) : ℝ)
  calc
    _ ≤ ∫ x : ι → ℝ, (𝔼 ε : ι → Bool,
        ‖∑ i, if ε i then x i • v i else -(x i • v i)‖) ∂Measure.pi μ :=
      integral_mono hmax havg (fun x ↦ max_norm_le_expect_norm_sum_sign (fun i ↦ x i • v i))
    _ = _ := by
      simp only [Fintype.expect_eq_sum_div_card, integral_div,
        integral_finsetSum _ (fun ε _ ↦ hsign ε), integral_norm_sum_sign_eq,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

open Classical in
/-- A lower bound on the norms of the fixed vectors converts the scalar maximum
into a lower bound on the expected norm of their symmetric random sum. -/
theorem mul_integral_max_abs_le_integral_norm_sum
    (hμ : ∀ i, Integrable id (μ i)) (v : ι → E) {a : ℝ}
    (ha : 0 ≤ a) (hv : ∀ i, a ≤ ‖v i‖) :
    a * (∫ x : ι → ℝ, Finset.univ.sup' Finset.univ_nonempty (fun i ↦ |x i|)
      ∂Measure.pi μ) ≤ ∫ x : ι → ℝ, ‖∑ i, x i • v i‖ ∂Measure.pi μ := by
  have hi (i : ι) : Integrable (fun x : ι → ℝ ↦ ‖x i • v i‖) (Measure.pi μ) := by
    simpa [norm_smul] using
      ((measurePreserving_eval μ i).integrable_comp_of_integrable (hμ i)).norm.mul_const ‖v i‖
  have hmax := Finset.integrable_sup' Finset.univ_nonempty (fun i _ ↦ hi i)
  calc
    _ = ∫ x : ι → ℝ, a * Finset.univ.sup' Finset.univ_nonempty (fun i ↦ |x i|)
        ∂Measure.pi μ := (integral_const_mul _ _).symm
    _ ≤ ∫ x : ι → ℝ, Finset.univ.sup' Finset.univ_nonempty (fun i ↦ ‖x i • v i‖)
        ∂Measure.pi μ := by
      refine integral_mono_of_nonneg ?_ hmax ?_
      · exact Filter.Eventually.of_forall fun x ↦ mul_nonneg ha
          ((abs_nonneg (x (Classical.arbitrary ι))).trans
            (Finset.le_sup' (fun i ↦ |x i|) (Finset.mem_univ (Classical.arbitrary ι))))
      · filter_upwards [] with x
        obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i ↦ |x i|)
        rw [hi]
        calc
          a * |x i| ≤ ‖x i • v i‖ := by
            simpa [norm_smul, mul_comm] using
              mul_le_mul_of_nonneg_left (hv i) (abs_nonneg (x i))
          _ ≤ _ := Finset.le_sup' (fun j ↦ ‖x j • v j‖) (Finset.mem_univ i)
    _ ≤ _ := integral_max_norm_smul_le_integral_norm_sum μ hμ v

end TauCeti
