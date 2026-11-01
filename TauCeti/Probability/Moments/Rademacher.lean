/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Rademacher
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Expected norms of sums with independent symmetric coefficients

For independent integrable symmetric real coefficients, the expected norm of a finite vector
sum dominates the expected maximum length of its individual terms. The coefficients are the
coordinate maps on a product of finite measures invariant under negation. In particular, the
result applies to independent symmetric random variables by transporting their joint law.

This is the integrated Rademacher convexity inequality: each fixed sign pattern preserves the
product measure, so averaging over signs leaves the expected norm unchanged. It is useful for
lower bounds on Gaussian vector sums without any completeness hypothesis on the vector space.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §13.3.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace TauCeti.Probability

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For independent integrable symmetric coefficients, the expected maximum length of the
individual terms is at most the expected norm of their sum. The measures need only be finite,
not normalized, and the vector space need not be complete. -/
theorem integral_sup'_norm_smul_le_integral_norm_sum
    (μ : ι → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, (μ i).IsNegInvariant]
    (hμ : ∀ i, Integrable id (μ i)) (v : ι → E) :
    ∫ x, Finset.univ.sup' Finset.univ_nonempty (fun i ↦ ‖x i • v i‖) ∂Measure.pi μ ≤
      ∫ x, ‖∑ i, x i • v i‖ ∂Measure.pi μ := by
  classical
  -- Signed sums and their maximum are integrable, so the finite average commutes with integration.
  have hterm (i : ι) : Integrable (fun x : ι → ℝ ↦ x i • v i) (Measure.pi μ) :=
    (integrable_eval (hμ i)).smul_const _
  let f (ε : ι → Bool) (x : ι → ℝ) := ‖∑ i, if ε i then -(x i • v i) else x i • v i‖
  have hf (ε : ι → Bool) : Integrable (f ε) (Measure.pi μ) := by
    apply Integrable.norm
    apply integrable_finsetSum
    intro i _
    cases h : ε i
    · simpa [h] using hterm i
    · simpa [h] using (hterm i).neg
  have hmax : Integrable (fun x : ι → ℝ ↦
      Finset.univ.sup' Finset.univ_nonempty (fun i ↦ ‖x i • v i‖)) (Measure.pi μ) := by
    convert Finset.sup'_induction (p := fun f ↦ Integrable f (Measure.pi μ))
      Finset.univ_nonempty (fun i (x : ι → ℝ) ↦ ‖x i • v i‖)
      (fun _ hf _ hg ↦ hf.sup hg) (fun i _ ↦ (hterm i).norm) using 1
    exact funext fun x ↦ (Finset.sup'_apply Finset.univ_nonempty
      (fun i (y : ι → ℝ) ↦ ‖y i • v i‖) x).symm
  -- Independence and symmetry make each fixed sign change measure preserving.
  have hinvariant (ε : ι → Bool) :
      ∫ x, f ε x ∂Measure.pi μ = ∫ x, ‖∑ i, x i • v i‖ ∂Measure.pi μ := by
    let e : (ι → ℝ) ≃ᵐ (ι → ℝ) := MeasurableEquiv.piCongrRight
      (fun i ↦ if ε i then MeasurableEquiv.neg ℝ else MeasurableEquiv.refl ℝ)
    have he : MeasurePreserving e (Measure.pi μ) (Measure.pi μ) := by
      apply measurePreserving_pi
      intro i
      cases h : ε i
      · simpa [h] using MeasurePreserving.id (μ i)
      · simpa [h] using Measure.measurePreserving_neg (μ i)
    have he_apply (x : ι → ℝ) (i : ι) : e x i = if ε i then -x i else x i := by
      cases h : ε i <;> simp [e, MeasurableEquiv.piCongrRight, Equiv.piCongrRight, h]
    -- The measurable equivalence acts coordinatewise by the chosen signs.
    simpa only [he_apply, ite_smul, neg_smul] using
      he.integral_comp' (fun x ↦ ‖∑ i, x i • v i‖)
  -- Integrate the pointwise Rademacher inequality and remove the sign average.
  calc
    _ ≤ ∫ x, 𝔼 ε : ι → Bool, f ε x ∂Measure.pi μ := by
      apply integral_mono hmax (by
        simpa only [Fintype.expect_eq_sum_div_card] using
          (integrable_finsetSum Finset.univ fun ε _ ↦ hf ε).div_const
            (Fintype.card (ι → Bool) : ℝ))
      intro x
      exact TauCeti.sup'_norm_le_expect_norm_sum_sign (fun i ↦ x i • v i)
    _ = ∫ x, ‖∑ i, x i • v i‖ ∂Measure.pi μ := by
      simp_rw [Fintype.expect_eq_sum_div_card]
      rw [integral_div, integral_finsetSum _ (fun ε _ ↦ hf ε)]
      simp_rw [hinvariant]
      simp

end TauCeti.Probability
