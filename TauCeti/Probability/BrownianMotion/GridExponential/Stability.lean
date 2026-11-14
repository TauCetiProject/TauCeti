/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.GridExponential.Basic
public import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# Stability of Brownian grid likelihoods

The L¹ distance between two normalized exponential likelihoods is controlled by the
square energy of the difference of their predictable drifts. Under a common height bound,
the fourth power of this distance is at most a deterministic constant times the expected
square energy. On uniformly bounded horizons this makes the L¹ error small when the
drifts, compared on a common grid, are close in L². This is the stability estimate needed
to pass from elementary likelihoods to a normalized limiting density.

The proof uses the geometric mean of the likelihoods: it is the likelihood of the average
drift times the exponential of minus one eighth of the difference energy. No stochastic
integral, measure change, or convergence of likelihoods is assumed. All results allow
repeated dates and empty grids, and require no path continuity or usual filtration conditions.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.5, for exponential changes of measure and bounded drift approximation.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Finset Set
open scoped NNReal

namespace TauCeti.Probability

variable {Ω : Type*} {τ : ℕ → ℝ≥0} {θ η : ℕ → Ω → ℝ} {W : ℝ≥0 → Ω → ℝ}

/-- The geometric mean of two grid likelihoods is the average-drift likelihood penalized
by one eighth of the difference energy. This identity needs no probabilistic hypotheses. -/
theorem sqrt_gridExponential_mul_sqrt (n : ℕ) (ω : Ω) :
    √(gridExponential τ θ W n ω) * √(gridExponential τ η W n ω) =
      gridExponential τ (fun j ω ↦ (θ j ω + η j ω) / 2) W n ω *
        exp (-elementaryEnergy τ (fun j ω ↦ θ j ω - η j ω) n ω / 8) := by
  simp only [gridExponential_def, ← exp_half, ← exp_add, elementaryEnergy_def]
  congr 1
  simp only [sum_div, ← sum_neg_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  ring

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}

private theorem memLp_sqrt_gridExponential {n : ℕ}
    (hi : Integrable (gridExponential τ θ W n) P) :
    MemLp (fun ω ↦ √(gridExponential τ θ W n ω)) 2 P := by
  apply (memLp_two_iff_integrable_sq
    (continuous_sqrt.comp_aestronglyMeasurable hi.aestronglyMeasurable)).2
  simpa only [sq_sqrt (gridExponential_pos τ θ W n _).le] using hi

namespace IsFilteredPreBrownianReal

variable {K : ℝ} (hW : IsFilteredPreBrownianReal ℱ W P) (hτ : Monotone τ)
    (hθ : ∀ j, Measurable[ℱ (τ j)] (θ j)) (hη : ∀ j, Measurable[ℱ (τ j)] (η j))
    (hbθ : ∀ j, ∀ᵐ ω ∂P, |θ j ω| ≤ K) (hbη : ∀ j, ∀ᵐ ω ∂P, |η j ω| ≤ K)

include hW hτ hθ hη hbθ hbη

private theorem integral_sq_sqrt_sub_le (n : ℕ) :
    ∫ ω, (√(gridExponential τ θ W n ω) - √(gridExponential τ η W n ω)) ^ 2 ∂P ≤
      (∫ ω, gridExponential τ (fun j ω ↦ (θ j ω + η j ω) / 2) W n ω *
        elementaryEnergy τ (fun j ω ↦ θ j ω - η j ω) n ω ∂P) / 4 := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let A := gridExponential τ θ W n
  let B := gridExponential τ η W n
  let M := gridExponential τ (fun j ω ↦ (θ j ω + η j ω) / 2) W n
  let D := elementaryEnergy τ (fun j ω ↦ θ j ω - η j ω) n
  have hm := fun j ↦ ((hθ j).add (hη j)).div_const 2
  have hb : ∀ j, ∀ᵐ ω ∂P, |(θ j ω + η j ω) / 2| ≤ K := by
    intro j
    filter_upwards [hbθ j, hbη j] with ω hθω hηω
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      ((abs_add_le _ _).trans (by linarith))
  have hA := memLp_sqrt_gridExponential (hW.integrable_gridExponential hτ hθ hbθ n)
  have hB := memLp_sqrt_gridExponential (hW.integrable_gridExponential hτ hη hbη n)
  have hM := hW.memLp_two_gridExponential hτ hm hb n
  have hD : MemLp (elementaryEnergy τ (fun j ω ↦ θ j ω - η j ω) n) 2 P := by
    apply memLp_elementaryEnergy
    intro j _
    exact (MemLp.of_bound ((hθ j).mono (ℱ.le _) le_rfl).aestronglyMeasurable K
      (by simpa only [norm_eq_abs] using hbθ j)).sub
        (MemLp.of_bound ((hη j).mono (ℱ.le _) le_rfl).aestronglyMeasurable K
          (by simpa only [norm_eq_abs] using hbη j))
  have hpoint (ω : Ω) : (√(A ω) - √(B ω)) ^ 2 ≤
      A ω + B ω - 2 * M ω + M ω * D ω / 4 := by
    have hid := sqrt_gridExponential_mul_sqrt (τ := τ) (θ := θ) (η := η) (W := W) n ω
    have he := add_one_le_exp (-D ω / 8)
    have hpos : 0 ≤ M ω := (gridExponential_pos _ _ _ _ _).le
    have hmul := mul_le_mul_of_nonneg_left he hpos
    nlinarith [sq_sqrt (gridExponential_pos τ θ W n ω).le,
      sq_sqrt (gridExponential_pos τ η W n ω).le]
  have hiA := hW.integrable_gridExponential hτ hθ hbθ n
  have hiB := hW.integrable_gridExponential hτ hη hbη n
  have hiM := hW.integrable_gridExponential hτ hm hb n
  have hiD := hM.integrable_mul hD
  have hi := integral_mono ((hA.sub hB).integrable_sq)
    (((hiA.add hiB).sub (hiM.const_mul 2)).add (hiD.div_const 4)) hpoint
  rw [integral_add' ((hiA.add hiB).sub (hiM.const_mul 2)) (hiD.div_const 4),
    integral_sub' (hiA.add hiB) (hiM.const_mul 2), integral_add' hiA hiB,
    integral_const_mul, integral_div, hW.integral_gridExponential hτ hθ hbθ n,
    hW.integral_gridExponential hτ hη hbη n, hW.integral_gridExponential hτ hm hb n] at hi
  simpa only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply, one_add_one_eq_two,
    mul_one, sub_self, zero_add] using hi

/-- Weighted L¹ stability of grid likelihoods. The square of the L¹ error is controlled
by the difference energy weighted by the average-drift likelihood. -/
theorem sq_integral_abs_gridExponential_sub_le (n : ℕ) :
    (∫ ω, |gridExponential τ θ W n ω - gridExponential τ η W n ω| ∂P) ^ 2 ≤
      ∫ ω, gridExponential τ (fun j ω ↦ (θ j ω + η j ω) / 2) W n ω *
        elementaryEnergy τ (fun j ω ↦ θ j ω - η j ω) n ω ∂P := by
  have hA := memLp_sqrt_gridExponential (hW.integrable_gridExponential hτ hθ hbθ n)
  have hB := memLp_sqrt_gridExponential (hW.integrable_gridExponential hτ hη hbη n)
  have hCS := TauCeti.sq_integral_mul_le_integral_sq_mul_integral_sq
    (hA.sub hB).norm (hA.add hB).norm
  have heq (ω : Ω) :
      |gridExponential τ θ W n ω - gridExponential τ η W n ω| =
        ‖√(gridExponential τ θ W n ω) - √(gridExponential τ η W n ω)‖ *
          ‖√(gridExponential τ θ W n ω) + √(gridExponential τ η W n ω)‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, ← abs_mul]
    congr 1
    nlinarith [sq_sqrt (gridExponential_pos τ θ W n ω).le,
      sq_sqrt (gridExponential_pos τ η W n ω).le]
  have hsum : ∫ ω, (√(gridExponential τ θ W n ω) +
      √(gridExponential τ η W n ω)) ^ 2 ∂P ≤ 4 := by
    have h := integral_mono (hA.add hB).integrable_sq
      (((hW.integrable_gridExponential hτ hθ hbθ n).add
        (hW.integrable_gridExponential hτ hη hbη n)).const_mul 2)
      (fun ω ↦ by
        simp only [Pi.add_apply]
        nlinarith [sq_sqrt (gridExponential_pos τ θ W n ω).le,
          sq_sqrt (gridExponential_pos τ η W n ω).le,
          sq_nonneg (√(gridExponential τ θ W n ω) - √(gridExponential τ η W n ω))])
    simp only [Pi.add_apply] at h
    rw [integral_const_mul, integral_add (hW.integrable_gridExponential hτ hθ hbθ n)
      (hW.integrable_gridExponential hτ hη hbη n),
      hW.integral_gridExponential hτ hθ hbθ n, hW.integral_gridExponential hτ hη hbη n] at h
    norm_num at h ⊢
    exact h
  simp only [Pi.add_apply, Pi.sub_apply] at hCS
  simp_rw [← heq, Real.norm_eq_abs, sq_abs] at hCS
  have hdiff := integral_sq_sqrt_sub_le hW hτ hθ hη hbθ hbη n
  have hnonneg : 0 ≤ ∫ ω, (√(gridExponential τ θ W n ω) -
      √(gridExponential τ η W n ω)) ^ 2 ∂P := integral_nonneg fun _ ↦ sq_nonneg _
  nlinarith

/-- Quantitative L¹ stability under a common predictable height bound. The constant
is independent of the number and spacing of the dates; the right side is the expected
square energy of the drift error, not an assumption about the likelihood error. -/
theorem integral_abs_gridExponential_sub_pow_four_le (n : ℕ) :
    (∫ ω, |gridExponential τ θ W n ω - gridExponential τ η W n ω| ∂P) ^ 4 ≤
      4 * K ^ 2 * ((τ n : ℝ) - τ 0) * exp (K ^ 2 * ((τ n : ℝ) - τ 0)) *
        ∫ ω, elementaryEnergy τ (fun j ω ↦ θ j ω - η j ω) n ω ∂P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hm := fun j ↦ ((hθ j).add (hη j)).div_const 2
  have hb : ∀ j, ∀ᵐ ω ∂P, |(θ j ω + η j ω) / 2| ≤ K := by
    intro j
    filter_upwards [hbθ j, hbη j] with ω hθω hηω
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      ((abs_add_le _ _).trans (by linarith))
  have hM := hW.memLp_two_gridExponential hτ hm hb n
  have hD : MemLp (elementaryEnergy τ (fun j ω ↦ θ j ω - η j ω) n) 2 P := by
    apply memLp_elementaryEnergy
    intro j _
    exact (MemLp.of_bound ((hθ j).mono (ℱ.le _) le_rfl).aestronglyMeasurable K
      (by simpa only [norm_eq_abs] using hbθ j)).sub
        (MemLp.of_bound ((hη j).mono (ℱ.le _) le_rfl).aestronglyMeasurable K
          (by simpa only [norm_eq_abs] using hbη j))
  have hCS := TauCeti.sq_integral_mul_le_integral_sq_mul_integral_sq hM hD
  have hL := sq_integral_abs_gridExponential_sub_le hW hτ hθ hη hbθ hbη n
  have hEnonneg (ω : Ω) := elementaryEnergy_nonneg
    (a := fun j ω ↦ θ j ω - η j ω) (n := n) (hτ.monotoneOn _) ω
  have henergy := integral_mono_ae hD.integrable_sq
    ((hD.integrable (by norm_num)).const_mul (4 * K ^ 2 * ((τ n : ℝ) - τ 0))) (by
      filter_upwards [ae_all_iff.2 hbθ, ae_all_iff.2 hbη] with ω hθω hηω
      have hb : ∀ j < n, |θ j ω - η j ω| ≤ 2 * K := by
        intro j _
        exact (abs_sub _ _).trans (by linarith [hθω j, hηω j])
      have hbound := elementaryEnergy_le_of_bound (a := fun j ω ↦ θ j ω - η j ω) (n := n)
        (hτ.monotoneOn _) ω hb
      have := mul_le_mul_of_nonneg_right hbound (hEnonneg ω)
      nlinarith)
  rw [integral_const_mul] at henergy
  have hmoment := hW.integral_sq_gridExponential_le hτ hm hb n
  have hD2nonneg : 0 ≤ ∫ ω, elementaryEnergy τ (fun j ω ↦ θ j ω - η j ω) n ω ^ 2 ∂P :=
    integral_nonneg fun _ ↦ sq_nonneg _
  calc
    _ = ((∫ ω, |gridExponential τ θ W n ω - gridExponential τ η W n ω| ∂P) ^ 2) ^ 2 := by ring
    _ ≤ (∫ ω, gridExponential τ (fun j ω ↦ (θ j ω + η j ω) / 2) W n ω *
        elementaryEnergy τ (fun j ω ↦ θ j ω - η j ω) n ω ∂P) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) hL 2
    _ ≤ _ := hCS.trans ((mul_le_mul_of_nonneg_right hmoment hD2nonneg).trans (by
      have := mul_le_mul_of_nonneg_left henergy (exp_pos (K ^ 2 * ((τ n : ℝ) - τ 0))).le
      nlinarith))

end IsFilteredPreBrownianReal
end TauCeti.Probability
