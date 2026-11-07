/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Filtered
import TauCeti.Probability.Distributions.Gaussian.Moments
import TauCeti.Probability.Distributions.Gaussian.PolynomialMemLp
import Mathlib.Probability.Independence.Integration

/-!
# Centered weighted Brownian quadratic sums

For deterministic dates `tᵢ` and square-integrable heights `Hᵢ` measurable at `tᵢ`,
this file proves the exact identity

`E[(∑ᵢ Hᵢ ((B(tᵢ₊₁) - B(tᵢ))² - (tᵢ₊₁ - tᵢ)))²]
  = 2 ∑ᵢ E[Hᵢ²] (tᵢ₊₁ - tᵢ)²`.

The summands are orthogonal, not generally independent: the later height may depend on
all earlier increments. Specializing to `Hᵢ = B(tᵢ)` gives the centered quadratic error
in the partition proof of the cubic Itô formula. A mesh bound then gives mean-square
convergence to zero. Empty grids and repeated dates are allowed. Only the filtered
pre-Brownian laws are used; path continuity and usual filtration conditions are unnecessary.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter
open scoped Topology NNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

private theorem centered_sq_increment_moments (hB : IsFilteredPreBrownianReal ℱ B P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    MemLp (fun ω ↦ (B t ω - B s ω) ^ 2 - ((t : ℝ) - s)) 2 P ∧
      (∫ ω, (B t ω - B s ω) ^ 2 - ((t : ℝ) - s) ∂P) = 0 ∧
      (∫ ω, ((B t ω - B s ω) ^ 2 - ((t : ℝ) - s)) ^ 2 ∂P) =
        2 * ((t : ℝ) - s) ^ 2 := by
  have := (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  have hlaw := hB.toIsPreBrownianReal.hasLaw_sub_of_le hst
  have h4i : Integrable (fun ω ↦ (B t ω - B s ω) ^ 4) P := by
    simpa only [Function.comp_def, Pi.sub_apply] using
      hlaw.integrable_comp (integrable_pow_gaussianReal 0 (t - s) 4)
  have h2 : MemLp (fun ω ↦ (B t ω - B s ω) ^ 2) 2 P :=
    (memLp_two_iff_integrable_sq
      ((hlaw.aemeasurable.pow_const 2).aestronglyMeasurable)).2
      (by simpa only [← pow_mul, Pi.sub_def] using h4i)
  have h2i := h2.integrable (by norm_num)
  have hm2 : (∫ ω, (B t ω - B s ω) ^ 2 ∂P) = (t : ℝ) - s := by
    have h := hlaw.integral_comp (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
    simpa [Function.comp_def, Pi.sub_def, integral_sq_gaussianReal, NNReal.coe_sub hst] using h
  have hm4 : (∫ ω, (B t ω - B s ω) ^ 4 ∂P) = 3 * ((t : ℝ) - s) ^ 2 := by
    have h := hlaw.integral_comp (f := fun x : ℝ ↦ x ^ 4) (by fun_prop)
    have hm := integral_sub_pow_two_mul_gaussianReal 0 (t - s) 2
    norm_num [NNReal.coe_sub hst] at hm
    simpa only [Function.comp_def, Pi.sub_apply, hm, mul_comm] using h
  refine ⟨h2.sub (memLp_const _), ?_, ?_⟩
  · rw [integral_sub h2i (integrable_const _), hm2, integral_const]
    simp
  · have hexp : ∀ ω, ((B t ω - B s ω) ^ 2 - ((t : ℝ) - s)) ^ 2 =
        (B t ω - B s ω) ^ 4 - 2 * ((t : ℝ) - s) * (B t ω - B s ω) ^ 2 +
          ((t : ℝ) - s) ^ 2 := fun ω ↦ by ring
    simp_rw [hexp]
    have hsub : Integrable (fun ω ↦ (B t ω - B s ω) ^ 4 -
        2 * ((t : ℝ) - s) * (B t ω - B s ω) ^ 2) P := by
      simpa only [Pi.sub_def] using h4i.sub (h2i.const_mul (2 * ((t : ℝ) - s)))
    rw [integral_add hsub (integrable_const _),
      integral_sub h4i (h2i.const_mul _), integral_const_mul,
      hm4, hm2, integral_const]
    simp
    ring

private theorem indepFun_centered_sq_increment (hB : IsFilteredPreBrownianReal ℱ B P)
    {s t : ℝ≥0} (hst : s ≤ t) {Y : Ω → ℝ} (hY : Measurable[ℱ s] Y) :
    IndepFun Y (fun ω ↦ (B t ω - B s ω) ^ 2 - ((t : ℝ) - s)) P := by
  have h : IndepFun Y (B t - B s) P :=
    (IndepFun_iff_Indep _ _ _).2
      (indep_of_indep_of_le_left (hB.indep_sub hst).symm hY.comap_le)
  exact h.comp measurable_id ((measurable_id.pow_const 2).sub measurable_const)

/-- A past-measurable integrable height times the centered square of a future Brownian
increment has mean zero. No boundedness or second moment of the height is required. -/
theorem integral_mul_centered_sq_increment (hB : IsFilteredPreBrownianReal ℱ B P)
    {s t : ℝ≥0} (hst : s ≤ t) {Y : Ω → ℝ} (hY : Measurable[ℱ s] Y)
    (hYi : Integrable Y P) :
    (∫ ω, Y ω * ((B t ω - B s ω) ^ 2 - ((t : ℝ) - s)) ∂P) = 0 := by
  rw [(indepFun_centered_sq_increment hB hst hY).integral_fun_mul_eq_mul_integral
    hYi.aestronglyMeasurable (centered_sq_increment_moments hB hst).1.aestronglyMeasurable,
    (centered_sq_increment_moments hB hst).2.1,
    mul_zero]

/-- A square-integrable past height times a centered squared Brownian increment is
square integrable. -/
theorem memLp_mul_centered_sq_increment (hB : IsFilteredPreBrownianReal ℱ B P)
    {s t : ℝ≥0} (hst : s ≤ t) {Y : Ω → ℝ} (hY : Measurable[ℱ s] Y) (hYi : MemLp Y 2 P) :
    MemLp (fun ω ↦ Y ω * ((B t ω - B s ω) ^ 2 - ((t : ℝ) - s))) 2 P := by
  have hD := (centered_sq_increment_moments hB hst).1
  refine (memLp_two_iff_integrable_sq (hYi.aestronglyMeasurable.mul
    hD.aestronglyMeasurable)).2 ?_
  simpa only [mul_pow, Function.comp_def, id_eq, Pi.mul_def] using
    ((indepFun_centered_sq_increment hB hst hY).comp
    (measurable_id.pow_const 2) (measurable_id.pow_const 2)).integrable_mul
      hYi.integrable_sq hD.integrable_sq

/-- The second moment of a past-weighted centered squared increment factors exactly. -/
theorem integral_sq_mul_centered_sq_increment (hB : IsFilteredPreBrownianReal ℱ B P)
    {s t : ℝ≥0} (hst : s ≤ t) {Y : Ω → ℝ} (hY : Measurable[ℱ s] Y) (hYi : MemLp Y 2 P) :
    (∫ ω, (Y ω * ((B t ω - B s ω) ^ 2 - ((t : ℝ) - s))) ^ 2 ∂P) =
      2 * (∫ ω, Y ω ^ 2 ∂P) * ((t : ℝ) - s) ^ 2 := by
  simp_rw [mul_pow]
  have hind : IndepFun (fun ω ↦ Y ω ^ 2)
      (fun ω ↦ ((B t ω - B s ω) ^ 2 - ((t : ℝ) - s)) ^ 2) P :=
    (indepFun_centered_sq_increment hB hst hY).comp (measurable_id.pow_const 2)
      (measurable_id.pow_const 2)
  rw [hind.integral_fun_mul_eq_mul_integral hYi.integrable_sq.aestronglyMeasurable
    (centered_sq_increment_moments hB hst).1.integrable_sq.aestronglyMeasurable,
    (centered_sq_increment_moments hB hst).2.2]
  ring

/-- Exact mean-square identity for a finite centered quadratic sum with arbitrary
square-integrable predictable heights. The weighted summands need not be independent. -/
theorem integral_sq_sum_mul_centered_sq_increment (hB : IsFilteredPreBrownianReal ℱ B P)
    {n : ℕ} {t : ℕ → ℝ≥0} (ht : MonotoneOn t (Set.Iic n)) {H : ℕ → Ω → ℝ}
    (hH : ∀ i < n, Measurable[ℱ (t i)] (H i)) (hHi : ∀ i < n, MemLp (H i) 2 P) :
    (∫ ω, (∑ i ∈ range n, H i ω * ((B (t (i + 1)) ω - B (t i) ω) ^ 2 -
      ((t (i + 1) : ℝ) - t i))) ^ 2 ∂P) =
        2 * ∑ i ∈ range n, (∫ ω, H i ω ^ 2 ∂P) * ((t (i + 1) : ℝ) - t i) ^ 2 := by
  have := (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  let Z i ω := H i ω * ((B (t (i + 1)) ω - B (t i) ω) ^ 2 -
    ((t (i + 1) : ℝ) - t i))
  have hZi : ∀ i < n, MemLp (Z i) 2 P := fun i hi ↦
    hB.memLp_mul_centered_sq_increment (ht hi.le hi (Nat.le_succ i)) (hH i hi) (hHi i hi)
  have horth : ∀ i < n, ∀ j < n, i < j → (∫ ω, Z i ω * Z j ω ∂P) = 0 := by
    intro i hi j hj hij
    have hmeas : Measurable[ℱ (t j)] (fun ω ↦ Z i ω * H j ω) := by
      have h₀ := (hB.adapted (t i)).mono (ℱ.mono (ht hi.le hj.le hij.le)) le_rfl
      have h₁ := (hB.adapted (t (i + 1))).mono (ℱ.mono (ht hi hj.le hij)) le_rfl
      exact (((hH i hi).mono (ℱ.mono (ht hi.le hj.le hij.le)) le_rfl).mul
        (((h₁.sub h₀).pow_const 2).sub measurable_const)).mul (hH j hj)
    have hint : Integrable (fun ω ↦ Z i ω * H j ω) P := by
      simpa only [Pi.mul_def] using (hZi i hi).integrable_mul (hHi j hj)
    have h := hB.integral_mul_centered_sq_increment (ht hj.le hj (Nat.le_succ j)) hmeas hint
    convert h using 1
    congr 1
    ext ω
    dsimp [Z]
    ring
  suffices h : (∫ ω, (∑ i ∈ range n, Z i ω) ^ 2 ∂P) =
      ∑ i ∈ range n, ∫ ω, Z i ω ^ 2 ∂P by
    rw [h, mul_sum]
    exact sum_congr rfl fun i hi ↦ by
      rw [hB.integral_sq_mul_centered_sq_increment (ht (mem_range.1 hi).le (mem_range.1 hi)
        (Nat.le_succ i)) (hH i (mem_range.1 hi)) (hHi i (mem_range.1 hi))]
      ring
  -- Add one orthogonal summand at a time, keeping all products integrable.
  have hpartial : ∀ k ≤ n, (∫ ω, (∑ i ∈ range k, Z i ω) ^ 2 ∂P) =
      ∑ i ∈ range k, ∫ ω, Z i ω ^ 2 ∂P := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hk' : k < n := hk
      have hS : MemLp (fun ω ↦ ∑ i ∈ range k, Z i ω) 2 P :=
        memLp_finsetSum _ fun i hi ↦ hZi i ((mem_range.1 hi).trans hk')
      have hcrossI : Integrable (fun ω ↦ (∑ i ∈ range k, Z i ω) * Z k ω) P := by
        simpa only [Pi.mul_def] using hS.integrable_mul (hZi k hk')
      have hprod : ∀ i < k, Integrable (fun ω ↦ Z i ω * Z k ω) P := by
        intro i hi
        simpa only [Pi.mul_def] using (hZi i (hi.trans hk')).integrable_mul (hZi k hk')
      have hcross : (∫ ω, (∑ i ∈ range k, Z i ω) * Z k ω ∂P) = 0 := by
        simp_rw [sum_mul]
        rw [integral_finsetSum _ fun i hi ↦ hprod i (mem_range.1 hi)]
        exact sum_eq_zero fun i hi ↦ horth i ((mem_range.1 hi).trans hk') k hk' (mem_range.1 hi)
      simp_rw [sum_range_succ, add_sq, mul_assoc]
      rw [integral_add (hS.integrable_sq.fun_add (hcrossI.const_mul 2))
        (hZi k hk').integrable_sq, integral_add hS.integrable_sq
        (hcrossI.const_mul 2), integral_const_mul, hcross,
        ih (by omega)]
      ring
  exact hpartial n le_rfl

/-- For heights equal to the Brownian left endpoint, the exact error is
`2 ∑ᵢ tᵢ (tᵢ₊₁ - tᵢ)²`. -/
theorem integral_sq_sum_eval_mul_centered_sq_increment (hB : IsFilteredPreBrownianReal ℱ B P)
    {n : ℕ} {t : ℕ → ℝ≥0} (ht : MonotoneOn t (Set.Iic n)) :
    (∫ ω, (∑ i ∈ range n, B (t i) ω * ((B (t (i + 1)) ω - B (t i) ω) ^ 2 -
      ((t (i + 1) : ℝ) - t i))) ^ 2 ∂P) =
        2 * ∑ i ∈ range n, (t i : ℝ) * ((t (i + 1) : ℝ) - t i) ^ 2 := by
  rw [hB.integral_sq_sum_mul_centered_sq_increment ht (fun i _ ↦ hB.adapted (t i))
    (fun i _ ↦ (hB.toIsPreBrownianReal.hasLaw_eval (t i)).memLp
      (memLp_id_gaussianReal' 2 (by norm_num)))]
  congr 1
  apply sum_congr rfl
  intro i hi
  have h := (hB.toIsPreBrownianReal.hasLaw_eval (t i)).integral_comp
    (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
  have hm : (∫ ω, B (t i) ω ^ 2 ∂P) = t i := by
    simpa [Function.comp_def, integral_sq_gaussianReal] using h
  rw [hm]

/-- On a horizon bounded by `T`, mesh at most `δ` bounds the Brownian-weighted
centered quadratic error by `2 T² δ`. -/
theorem integral_sq_sum_eval_mul_centered_sq_increment_le (hB : IsFilteredPreBrownianReal ℱ B P)
    {n : ℕ} {t : ℕ → ℝ≥0} (ht : MonotoneOn t (Set.Iic n)) {T : ℝ≥0}
    (hT : t n ≤ T) {δ : ℝ} (hδ : 0 ≤ δ)
    (hmesh : ∀ i < n, (t (i + 1) : ℝ) - t i ≤ δ) :
    (∫ ω, (∑ i ∈ range n, B (t i) ω * ((B (t (i + 1)) ω - B (t i) ω) ^ 2 -
      ((t (i + 1) : ℝ) - t i))) ^ 2 ∂P) ≤ 2 * (T : ℝ) ^ 2 * δ := by
  rw [hB.integral_sq_sum_eval_mul_centered_sq_increment ht]
  have hsum : ∑ i ∈ range n, (t i : ℝ) * ((t (i + 1) : ℝ) - t i) ^ 2 ≤
      (T : ℝ) * δ * ∑ i ∈ range n, ((t (i + 1) : ℝ) - t i) := by
    rw [mul_sum]
    refine sum_le_sum fun i hi ↦ ?_
    have hi := mem_range.1 hi
    have hstep : 0 ≤ (t (i + 1) : ℝ) - t i :=
      sub_nonneg.2 (NNReal.coe_le_coe.2 (ht hi.le hi (Nat.le_succ i)))
    have hleft : (t i : ℝ) ≤ T := NNReal.coe_le_coe.2 ((ht hi.le Set.self_mem_Iic hi.le).trans hT)
    calc
      (t i : ℝ) * ((t (i + 1) : ℝ) - t i) ^ 2
          ≤ (T : ℝ) * (δ * ((t (i + 1) : ℝ) - t i)) := by
            gcongr
            nlinarith [hmesh i hi]
      _ = (T : ℝ) * δ * ((t (i + 1) : ℝ) - t i) := by ring
  rw [sum_range_sub (fun i ↦ (t i : ℝ))] at hsum
  have hn : (t n : ℝ) ≤ T := NNReal.coe_le_coe.2 hT
  have hbound : (T : ℝ) * δ * ((t n : ℝ) - t 0) ≤ (T : ℝ) * δ * T :=
    mul_le_mul_of_nonneg_left (by linarith [NNReal.coe_nonneg (t 0)]) (mul_nonneg T.coe_nonneg hδ)
  nlinarith

/-- The centered Brownian-weighted quadratic error tends to zero in mean square along
any deterministic vanishing-mesh family on a bounded horizon. -/
theorem tendsto_integral_sq_sum_eval_mul_centered_sq_increment
    (hB : IsFilteredPreBrownianReal ℱ B P)
    {α : Type*} {l : Filter α} {n : α → ℕ} {t : α → ℕ → ℝ≥0} {δ : α → ℝ} {T : ℝ≥0}
    (ht : ∀ a, MonotoneOn (t a) (Set.Iic (n a))) (hT : ∀ a, t a (n a) ≤ T)
    (hδ : ∀ a, 0 ≤ δ a) (hmesh : ∀ a, ∀ i < n a, (t a (i + 1) : ℝ) - t a i ≤ δ a)
    (hlim : Tendsto δ l (𝓝 0)) :
    Tendsto (fun a ↦ ∫ ω, (∑ i ∈ range (n a), B (t a i) ω *
      ((B (t a (i + 1)) ω - B (t a i) ω) ^ 2 - ((t a (i + 1) : ℝ) - t a i))) ^ 2 ∂P)
        l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hlim.const_mul (2 * (T : ℝ) ^ 2))
    (fun a ↦ integral_nonneg fun _ ↦ sq_nonneg _) ?_
  exact fun a ↦ hB.integral_sq_sum_eval_mul_centered_sq_increment_le (ht a) (hT a) (hδ a) (hmesh a)

end TauCeti.Probability.IsFilteredPreBrownianReal
