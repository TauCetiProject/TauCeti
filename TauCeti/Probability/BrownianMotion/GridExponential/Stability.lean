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

For bounded predictable drifts on a common nondecreasing grid, the squared L¹ distance
between the likelihoods is at most the expected difference energy weighted by the
average-drift likelihood. With a common deterministic height bound, the fourth power
of the distance is at most a deterministic constant times the expected difference energy.
On uniformly bounded horizons this makes the L¹ error small when the drifts, compared on
common grids, are close in L².

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

open MeasureTheory ProbabilityTheory Real Set
open Finset hiding Iic mem_Iic
open scoped NNReal ENNReal

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
variable {n : ℕ} {K : ℝ}

namespace IsFilteredPreBrownianReal

variable (hW : IsFilteredPreBrownianReal ℱ W P) (hτ : MonotoneOn τ (Iic n))
    (hθ : ∀ j < n, Measurable[ℱ (τ j)] (θ j)) (hη : ∀ j < n, Measurable[ℱ (τ j)] (η j))
    (hbθ : ∀ j < n, ∀ᵐ ω ∂P, |θ j ω| ≤ K) (hbη : ∀ j < n, ∀ᵐ ω ∂P, |η j ω| ≤ K)

include hbθ hbη in
private theorem average_heights_bound (j : ℕ) (hj : j < n) :
    ∀ᵐ ω ∂P, |(θ j ω + η j ω) / 2| ≤ K := by
  filter_upwards [hbθ j hj, hbη j hj] with ω hθω hηω
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    ((abs_add_le _ _).trans (by linarith))

include hθ hη hbθ hbη in
private theorem memLp_two_differenceEnergy [IsFiniteMeasure P] :
    MemLp (elementaryEnergy τ (fun j ω ↦ θ j ω - η j ω) n) 2 P := by
  apply memLp_elementaryEnergy
  intro j hj
  exact (MemLp.of_bound ((hθ j hj).mono (ℱ.le _) le_rfl).aestronglyMeasurable K
    (by simpa only [norm_eq_abs] using hbθ j hj)).sub
      (MemLp.of_bound ((hη j hj).mono (ℱ.le _) le_rfl).aestronglyMeasurable K
        (by simpa only [norm_eq_abs] using hbη j hj))

include hW hτ hθ hη hbθ hbη in
private theorem integral_sq_sqrt_sub_le
    (hSq : Integrable (fun ω ↦
      (√(gridExponential τ θ W n ω) - √(gridExponential τ η W n ω)) ^ 2) P) :
    ∫ ω, (√(gridExponential τ θ W n ω) - √(gridExponential τ η W n ω)) ^ 2 ∂P ≤
      (∫ ω, gridExponential τ (fun j ω ↦ (θ j ω + η j ω) / 2) W n ω *
        elementaryEnergy τ (fun j ω ↦ θ j ω - η j ω) n ω ∂P) / 4 := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let A := gridExponential τ θ W n
  let B := gridExponential τ η W n
  let M := gridExponential τ (fun j ω ↦ (θ j ω + η j ω) / 2) W n
  let D := elementaryEnergy τ (fun j ω ↦ θ j ω - η j ω) n
  have hm := fun j hj ↦ ((hθ j hj).add (hη j hj)).div_const 2
  have hM₂ := hW.memLp_two_gridExponential hτ hm (average_heights_bound hbθ hbη)
  have hpoint (ω : Ω) : (√(A ω) - √(B ω)) ^ 2 ≤
      A ω + B ω - 2 * M ω + M ω * D ω / 4 := by
    have hid := sqrt_gridExponential_mul_sqrt (τ := τ) (θ := θ) (η := η) (W := W) n ω
    have he := add_one_le_exp (-D ω / 8)
    have hpos : 0 ≤ M ω := (gridExponential_pos _ _ _ _ _).le
    have hmul := mul_le_mul_of_nonneg_left he hpos
    nlinarith [sq_sqrt (gridExponential_pos τ θ W n ω).le,
      sq_sqrt (gridExponential_pos τ η W n ω).le]
  have hiA := hW.integrable_gridExponential hτ hθ
  have hiB := hW.integrable_gridExponential hτ hη
  have hiM := hW.integrable_gridExponential hτ hm
  have hiD := hM₂.integrable_mul (memLp_two_differenceEnergy (τ := τ) hθ hη hbθ hbη)
  have hi := integral_mono hSq
    (((hiA.add hiB).sub (hiM.const_mul 2)).add (hiD.div_const 4)) hpoint
  rw [integral_add' ((hiA.add hiB).sub (hiM.const_mul 2)) (hiD.div_const 4),
    integral_sub' (hiA.add hiB) (hiM.const_mul 2), integral_add' hiA hiB,
    integral_const_mul, integral_div, hW.integral_gridExponential hτ hθ,
    hW.integral_gridExponential hτ hη, hW.integral_gridExponential hτ hm] at hi
  simpa only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply, one_add_one_eq_two,
    mul_one, sub_self, zero_add] using hi

include hW hτ hθ hη hbθ hbη in
private theorem sq_integral_abs_gridExponential_sub_le_of_bound :
    (∫ ω, |gridExponential τ θ W n ω - gridExponential τ η W n ω| ∂P) ^ 2 ≤
      ∫ ω, gridExponential τ (fun j ω ↦ (θ j ω + η j ω) / 2) W n ω *
        elementaryEnergy τ (fun j ω ↦ θ j ω - η j ω) n ω ∂P := by
  have hiA := hW.integrable_gridExponential hτ hθ
  have hiB := hW.integrable_gridExponential hτ hη
  have hs (a : ℕ → Ω → ℝ) (hi : Integrable (gridExponential τ a W n) P) :
      MemLp (fun ω ↦ √(gridExponential τ a W n ω)) 2 P := by
    simpa only [Real.sqrt_eq_rpow, norm_eq_abs, abs_of_pos (gridExponential_pos τ a W n _),
      ENNReal.toReal_inv, ENNReal.toReal_ofNat, div_eq_mul_inv, inv_inv, one_mul] using
      (memLp_one_iff_integrable.mpr hi).norm_rpow_div (2 : ℝ≥0∞)⁻¹
  have hsA := hs θ hiA
  have hsB := hs η hiB
  have hCS := TauCeti.sq_integral_mul_le_integral_sq_mul_integral_sq
    (hsA.sub hsB).norm (hsA.add hsB).norm
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
    have h := integral_mono (hsA.add hsB).integrable_sq ((hiA.add hiB).const_mul 2)
      (fun ω ↦ by
        simpa only [Pi.add_apply, sq_sqrt (gridExponential_pos τ θ W n ω).le,
          sq_sqrt (gridExponential_pos τ η W n ω).le] using
          (add_sq_le (a := √(gridExponential τ θ W n ω)) (b := √(gridExponential τ η W n ω))))
    rw [integral_const_mul, integral_add' hiA hiB, hW.integral_gridExponential hτ hθ,
      hW.integral_gridExponential hτ hη] at h
    norm_num at h ⊢
    exact h
  simp only [Pi.add_apply, Pi.sub_apply] at hCS
  simp_rw [← heq, Real.norm_eq_abs, sq_abs] at hCS
  have hdiff := integral_sq_sqrt_sub_le hW hτ hθ hη hbθ hbη (hsA.sub hsB).integrable_sq
  have hnonneg : 0 ≤ ∫ ω, (√(gridExponential τ θ W n ω) -
      √(gridExponential τ η W n ω)) ^ 2 ∂P := integral_nonneg fun _ ↦ sq_nonneg _
  nlinarith

/-- For predictable drifts on a common nondecreasing grid with deterministically bounded
heights on each used interval, the squared L¹ error is at most the expected difference
energy weighted by the average-drift likelihood. -/
theorem sq_integral_abs_gridExponential_sub_le (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Iic n))
    (hθ : ∀ j < n, Measurable[ℱ (τ j)] (θ j)) (hη : ∀ j < n, Measurable[ℱ (τ j)] (η j))
    (hbθ : ∀ j < n, ∃ C, ∀ᵐ ω ∂P, |θ j ω| ≤ C)
    (hbη : ∀ j < n, ∃ C, ∀ᵐ ω ∂P, |η j ω| ≤ C) :
    (∫ ω, |gridExponential τ θ W n ω - gridExponential τ η W n ω| ∂P) ^ 2 ≤
      ∫ ω, gridExponential τ (fun j ω ↦ (θ j ω + η j ω) / 2) W n ω *
        elementaryEnergy τ (fun j ω ↦ θ j ω - η j ω) n ω ∂P := by
  classical
  have hb (j : ℕ) : ∃ C, j < n → (∀ᵐ ω ∂P, |θ j ω| ≤ C) ∧ (∀ᵐ ω ∂P, |η j ω| ≤ C) := by
    by_cases hj : j < n
    · obtain ⟨Cθ, hCθ⟩ := hbθ j hj
      obtain ⟨Cη, hCη⟩ := hbη j hj
      exact ⟨max Cθ Cη, fun _ ↦ ⟨hCθ.mono (fun _ h ↦ h.trans (le_max_left _ _)),
        hCη.mono (fun _ h ↦ h.trans (le_max_right _ _))⟩⟩
    · exact ⟨0, fun h ↦ (hj h).elim⟩
  choose C hC using hb
  have hC_le (j : ℕ) (hj : j < n) : C j ≤ ∑ i ∈ range n, |C i| :=
    (le_abs_self _).trans (single_le_sum (fun i _ ↦ abs_nonneg (C i)) (mem_range.mpr hj))
  exact sq_integral_abs_gridExponential_sub_le_of_bound hW hτ hθ hη
    (fun j hj ↦ (hC j hj).1.mono (fun _ h ↦ h.trans (hC_le j hj)))
    (fun j hj ↦ (hC j hj).2.mono (fun _ h ↦ h.trans (hC_le j hj)))

include hW hτ hθ hη hbθ hbη in
/-- For predictable heights with a common deterministic bound on the used intervals, the
fourth power of the L¹ error is bounded by expected difference energy times a constant
independent of the number and spacing of the dates. -/
theorem pow_four_integral_abs_gridExponential_sub_le :
    (∫ ω, |gridExponential τ θ W n ω - gridExponential τ η W n ω| ∂P) ^ 4 ≤
      4 * K ^ 2 * ((τ n : ℝ) - τ 0) * exp (K ^ 2 * ((τ n : ℝ) - τ 0)) *
        ∫ ω, elementaryEnergy τ (fun j ω ↦ θ j ω - η j ω) n ω ∂P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hm := fun j hj ↦ ((hθ j hj).add (hη j hj)).div_const 2
  have hbM := average_heights_bound hbθ hbη
  have hM := hW.memLp_two_gridExponential hτ hm hbM
  have hmoment := hW.integral_sq_gridExponential_le hτ hm hbM
  have hD := memLp_two_differenceEnergy (τ := τ) hθ hη hbθ hbη
  have hCS := TauCeti.sq_integral_mul_le_integral_sq_mul_integral_sq hM hD
  have hL := sq_integral_abs_gridExponential_sub_le_of_bound hW hτ hθ hη hbθ hbη
  have hEnonneg (ω : Ω) := elementaryEnergy_nonneg
    (a := fun j ω ↦ θ j ω - η j ω) hτ ω
  have henergy := integral_mono_ae hD.integrable_sq
    ((hD.integrable (by norm_num)).const_mul (4 * K ^ 2 * ((τ n : ℝ) - τ 0))) (by
      have hae (j : ℕ) : ∀ᵐ ω ∂P, j < n → |θ j ω - η j ω| ≤ 2 * K := by
        by_cases hj : j < n
        · filter_upwards [hbθ j hj, hbη j hj] with ω hθω hηω _
          exact (abs_sub _ _).trans (by linarith)
        · simp [hj]
      filter_upwards [ae_all_iff.2 hae] with ω hω
      have hbound := elementaryEnergy_le_of_bound (a := fun j ω ↦ θ j ω - η j ω) hτ ω hω
      have := mul_le_mul_of_nonneg_right hbound (hEnonneg ω)
      nlinarith)
  rw [integral_const_mul] at henergy
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
