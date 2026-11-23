/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Filtered
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Independence.Integration

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
pre-Brownian laws are used for general heights; the Brownian-height specialization needs
only pre-Brownian laws. Path continuity and usual filtration conditions are unnecessary.

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

private theorem indepFun_sq_sub_sub (hB : IsFilteredPreBrownianReal ℱ B P)
    {s t : ℝ≥0} (hst : s ≤ t) {Y : Ω → ℝ} (hY : Measurable[ℱ s] Y) :
    IndepFun Y (fun ω ↦ (B t ω - B s ω) ^ 2 - ((t : ℝ) - s)) P :=
  (hB.indepFun_sub hst hY).comp measurable_id
    ((measurable_id.pow_const 2).sub measurable_const)

/-- A past-measurable height times the centered square of a future Brownian
increment has mean zero. No integrability assumption on the height is required. -/
theorem integral_mul_sq_sub_sub_eq_zero (hB : IsFilteredPreBrownianReal ℱ B P)
    {s t : ℝ≥0} (hst : s ≤ t) {Y : Ω → ℝ} (hY : Measurable[ℱ s] Y) :
    (∫ ω, Y ω * ((B t ω - B s ω) ^ 2 - ((t : ℝ) - s)) ∂P) = 0 := by
  rw [(indepFun_sq_sub_sub hB hst hY).integral_fun_mul_eq_mul_integral
    (hY.mono (ℱ.le s) le_rfl).aestronglyMeasurable
      hB.toIsPreBrownianReal.memLp_sq_sub_sub.aestronglyMeasurable,
    hB.toIsPreBrownianReal.integral_sq_sub_sub_eq_zero hst,
    mul_zero]

/-- A square-integrable past height times a centered squared Brownian increment is
square integrable. -/
theorem memLp_mul_sq_sub_sub (hB : IsFilteredPreBrownianReal ℱ B P)
    {s t : ℝ≥0} (hst : s ≤ t) {Y : Ω → ℝ} (hY : Measurable[ℱ s] Y) (hYi : MemLp Y 2 P) :
    MemLp (fun ω ↦ Y ω * ((B t ω - B s ω) ^ 2 - ((t : ℝ) - s))) 2 P := by
  exact (indepFun_sq_sub_sub hB hst hY).memLp_two_mul hYi
    hB.toIsPreBrownianReal.memLp_sq_sub_sub

/-- The second moment of a past-weighted centered squared increment factors exactly,
with no integrability assumption on the height. -/
theorem integral_sq_mul_sq_sub_sub (hB : IsFilteredPreBrownianReal ℱ B P)
    {s t : ℝ≥0} (hst : s ≤ t) {Y : Ω → ℝ} (hY : Measurable[ℱ s] Y) :
    (∫ ω, (Y ω * ((B t ω - B s ω) ^ 2 - ((t : ℝ) - s))) ^ 2 ∂P) =
      2 * (∫ ω, Y ω ^ 2 ∂P) * ((t : ℝ) - s) ^ 2 := by
  simp_rw [mul_pow]
  have hind : IndepFun (fun ω ↦ Y ω ^ 2)
      (fun ω ↦ ((B t ω - B s ω) ^ 2 - ((t : ℝ) - s)) ^ 2) P :=
    (indepFun_sq_sub_sub hB hst hY).comp (measurable_id.pow_const 2)
      (measurable_id.pow_const 2)
  rw [hind.integral_fun_mul_eq_mul_integral
    ((hY.mono (ℱ.le s) le_rfl).pow_const 2).aestronglyMeasurable
    hB.toIsPreBrownianReal.memLp_sq_sub_sub.integrable_sq.aestronglyMeasurable,
    hB.toIsPreBrownianReal.integral_sq_sq_sub_sub hst]
  ring

/-- Exact mean-square identity for a finite centered quadratic sum with arbitrary
square-integrable predictable heights. The weighted summands need not be independent. -/
theorem integral_sq_sum_mul_sq_sub_sub (hB : IsFilteredPreBrownianReal ℱ B P)
    {n : ℕ} {t : ℕ → ℝ≥0} (ht : MonotoneOn t (Set.Iic n)) {H : ℕ → Ω → ℝ}
    (hH : ∀ i < n, Measurable[ℱ (t i)] (H i)) (hHi : ∀ i < n, MemLp (H i) 2 P) :
    (∫ ω, (∑ i ∈ range n, H i ω * ((B (t (i + 1)) ω - B (t i) ω) ^ 2 -
      ((t (i + 1) : ℝ) - t i))) ^ 2 ∂P) =
        2 * ∑ i ∈ range n, (∫ ω, H i ω ^ 2 ∂P) * ((t (i + 1) : ℝ) - t i) ^ 2 := by
  have := (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  let Z i ω := H i ω * ((B (t (i + 1)) ω - B (t i) ω) ^ 2 -
    ((t (i + 1) : ℝ) - t i))
  have hZi : ∀ i < n, MemLp (Z i) 2 P := fun i hi ↦
    hB.memLp_mul_sq_sub_sub (ht hi.le hi (Nat.le_succ i)) (hH i hi) (hHi i hi)
  have horth : ∀ i < n, ∀ j < n, i < j → (∫ ω, Z i ω * Z j ω ∂P) = 0 := by
    intro i hi j hj hij
    have hmeas : Measurable[ℱ (t j)] (fun ω ↦ Z i ω * H j ω) := by
      have h₀ := (hB.adapted (t i)).mono (ℱ.mono (ht hi.le hj.le hij.le)) le_rfl
      have h₁ := (hB.adapted (t (i + 1))).mono (ℱ.mono (ht hi hj.le hij)) le_rfl
      exact (((hH i hi).mono (ℱ.mono (ht hi.le hj.le hij.le)) le_rfl).mul
        (((h₁.sub h₀).pow_const 2).sub measurable_const)).mul (hH j hj)
    have h := hB.integral_mul_sq_sub_sub_eq_zero (ht hj.le hj (Nat.le_succ j)) hmeas
    convert h using 1
    congr 1
    ext ω
    dsimp [Z]
    ring
  suffices h : (∫ ω, (∑ i ∈ range n, Z i ω) ^ 2 ∂P) =
      ∑ i ∈ range n, ∫ ω, Z i ω ^ 2 ∂P by
    rw [h, mul_sum]
    exact sum_congr rfl fun i hi ↦ by
      rw [hB.integral_sq_mul_sq_sub_sub (ht (mem_range.1 hi).le (mem_range.1 hi)
        (Nat.le_succ i)) (hH i (mem_range.1 hi))]
      ring
  apply integral_sq_sum_of_pairwise_integral_mul_eq_zero (fun i hi ↦ hZi i (mem_range.1 hi))
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact horth i (mem_range.1 hi) j (mem_range.1 hj) hij
  · simpa only [mul_comm] using horth j (mem_range.1 hj) i (mem_range.1 hi) hji

end TauCeti.Probability.IsFilteredPreBrownianReal

namespace ProbabilityTheory.IsPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Centered quadratic sums with Brownian heights are square integrable on every finite grid. -/
theorem memLp_sum_eval_mul_sq_sub_sub (hB : IsPreBrownianReal B P)
    (t : ℕ → ℝ≥0) (n : ℕ) :
    MemLp (fun ω ↦ ∑ i ∈ range n, B (t i) ω *
      ((B (t (i + 1)) ω - B (t i) ω) ^ 2 - ((t (i + 1) : ℝ) - t i))) 2 P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  let : ENNReal.HolderTriple 4 4 2 := .of_toReal (by norm_num [Real.holderTriple_iff])
  apply memLp_finsetSum
  intro i _
  have hs : MemLp (fun ω ↦ (B (t (i + 1)) ω - B (t i) ω) ^ 2) 4 P := by
    have h := ((hB.hasLaw_sub (t (i + 1)) (t i)).memLp
      (memLp_id_gaussianReal' 8 (by norm_num))).norm_rpow_div 2
    have he : (4 : ENNReal) = 8 / 2 :=
      (ENNReal.eq_div_iff (by norm_num) (by norm_num)).2 (by norm_num)
    simpa only [← he, ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs,
      sq_abs, Pi.sub_apply] using h
  exact (hB.memLp_eval (t i) (p := 4) (by norm_num)).fun_mul
    (hs.sub (memLp_const _))

/-- For heights equal to the Brownian left endpoint, the second moment of the centered
quadratic error is `2 ∑ᵢ tᵢ (tᵢ₊₁ - tᵢ)²`, without a prescribed filtration. -/
theorem integral_sq_sum_eval_mul_sq_sub_sub (hB : IsPreBrownianReal B P)
    {t : ℕ → ℝ≥0} {n : ℕ} (ht : MonotoneOn t (Set.Iic n)) :
    (∫ ω, (∑ i ∈ range n, B (t i) ω *
      ((B (t (i + 1)) ω - B (t i) ω) ^ 2 - ((t (i + 1) : ℝ) - t i))) ^ 2 ∂P) =
      2 * ∑ i ∈ range n, (t i : ℝ) * ((t (i + 1) : ℝ) - t i) ^ 2 := by
  -- Apply the filtered identity to a measurable modification and its natural filtration.
  let W (s : ℝ≥0) := (hB.aemeasurable s).mk (B s)
  have hW : IsPreBrownianReal W P := hB.congr fun s ↦ (hB.aemeasurable s).ae_eq_mk
  have hF := hW.isFilteredPreBrownianReal_natural
    (fun s ↦ (hB.aemeasurable s).measurable_mk.stronglyMeasurable)
  have heq : (fun ω ↦ ∑ i ∈ range n, B (t i) ω *
      ((B (t (i + 1)) ω - B (t i) ω) ^ 2 - ((t (i + 1) : ℝ) - t i))) =ᵐ[P]
      (fun ω ↦ ∑ i ∈ range n, W (t i) ω *
      ((W (t (i + 1)) ω - W (t i) ω) ^ 2 - ((t (i + 1) : ℝ) - t i))) := by
    simpa only [Finset.sum_fn, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply] using
      (eventuallyEq_sum (s := range n) fun i _ ↦
        ((hB.aemeasurable (t i)).ae_eq_mk.mul
          ((((hB.aemeasurable (t (i + 1))).ae_eq_mk.sub
            (hB.aemeasurable (t i)).ae_eq_mk).pow_const 2).sub
              (EventuallyEq.refl _ (fun _ : Ω ↦ (t (i + 1) : ℝ) - t i)))))
  calc
    _ = ∫ ω, (∑ i ∈ range n, W (t i) ω *
        ((W (t (i + 1)) ω - W (t i) ω) ^ 2 - ((t (i + 1) : ℝ) - t i))) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [heq] with ω hω
      rw [hω]
    _ = _ := by
      rw [hF.integral_sq_sum_mul_sq_sub_sub ht (fun i _ ↦ hF.adapted (t i))
        (fun i _ ↦ hW.memLp_eval (t i) (by norm_num))]
      simp_rw [hW.integral_sq_eval]

/-- The second moment of the centered Brownian-height quadratic error is bounded by twice
the last date times elapsed time times the mesh bound. No sign assumption on the mesh bound
is needed. -/
theorem integral_sq_sum_eval_mul_sq_sub_sub_le (hB : IsPreBrownianReal B P)
    {t : ℕ → ℝ≥0} {n : ℕ} (ht : MonotoneOn t (Set.Iic n)) {δ : ℝ}
    (hmesh : ∀ i < n, (t (i + 1) : ℝ) - t i ≤ δ) :
    (∫ ω, (∑ i ∈ range n, B (t i) ω *
      ((B (t (i + 1)) ω - B (t i) ω) ^ 2 - ((t (i + 1) : ℝ) - t i))) ^ 2 ∂P) ≤
      2 * (t n : ℝ) * ((t n : ℝ) - t 0) * δ := by
  rw [hB.integral_sq_sum_eval_mul_sq_sub_sub ht]
  have hsum : ∑ i ∈ range n, (t i : ℝ) * ((t (i + 1) : ℝ) - t i) ^ 2 ≤
      (t n : ℝ) * δ * ∑ i ∈ range n, ((t (i + 1) : ℝ) - t i) := by
    rw [mul_sum]
    refine sum_le_sum fun i hi ↦ ?_
    have hi := mem_range.1 hi
    have hstep : 0 ≤ (t (i + 1) : ℝ) - t i :=
      sub_nonneg.2 (NNReal.coe_le_coe.2 (ht hi.le hi (Nat.le_succ i)))
    have hleft : (t i : ℝ) ≤ t n :=
      NNReal.coe_le_coe.2 (ht hi.le Set.self_mem_Iic hi.le)
    calc
      (t i : ℝ) * ((t (i + 1) : ℝ) - t i) ^ 2
          ≤ (t n : ℝ) * (δ * ((t (i + 1) : ℝ) - t i)) := by
            gcongr
            nlinarith [hmesh i hi]
      _ = (t n : ℝ) * δ * ((t (i + 1) : ℝ) - t i) := by ring
  rw [sum_range_sub (fun i ↦ (t i : ℝ))] at hsum
  nlinarith

/-- The centered Brownian-weighted quadratic error tends to zero in mean square along
any deterministic vanishing-mesh family on a bounded horizon. -/
theorem tendsto_integral_sq_sum_eval_mul_sq_sub_sub (hB : IsPreBrownianReal B P)
    {α : Type*} {l : Filter α} {n : α → ℕ} {t : α → ℕ → ℝ≥0} {δ : α → ℝ} {T : ℝ≥0}
    (ht : ∀ a, MonotoneOn (t a) (Set.Iic (n a))) (hT : ∀ a, t a (n a) ≤ T)
    (hmesh : ∀ a, ∀ i < n a, (t a (i + 1) : ℝ) - t a i ≤ δ a)
    (hlim : Tendsto δ l (𝓝 0)) :
    Tendsto (fun a ↦ ∫ ω, (∑ i ∈ range (n a), B (t a i) ω *
      ((B (t a (i + 1)) ω - B (t a i) ω) ^ 2 - ((t a (i + 1) : ℝ) - t a i))) ^ 2 ∂P)
        l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hlim.abs.const_mul (2 * (T : ℝ) ^ 2))
    (fun a ↦ integral_nonneg fun _ ↦ sq_nonneg _) ?_
  intro a
  refine (hB.integral_sq_sum_eval_mul_sq_sub_sub_le (ht a)
    (fun i hi ↦ (hmesh a i hi).trans (le_abs_self _))).trans ?_
  have hspan : (t a (n a) : ℝ) - t a 0 ≤ T :=
    (sub_le_self _ (t a 0).coe_nonneg).trans (NNReal.coe_le_coe.2 (hT a))
  calc
    2 * (t a (n a) : ℝ) * ((t a (n a) : ℝ) - t a 0) * |δ a| ≤
        2 * (T : ℝ) * T * |δ a| := by
          gcongr
          · exact sub_nonneg.mpr (NNReal.coe_le_coe.2
              (ht a (Nat.zero_le _) Set.self_mem_Iic (Nat.zero_le _)))
          · exact hT a
    _ = 2 * (T : ℝ) ^ 2 * |δ a| := by ring

end ProbabilityTheory.IsPreBrownianReal
