/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SampleSecondMoment
public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.Probability.Moments.SubGaussian.SubExponential

/-!
# Entrywise concentration of sample covariances

For independent observations with a common second-moment matrix and sub-Gaussian coordinates,
each sample covariance entry has a Bernstein tail. A finite union bound gives simultaneous
control of all entries at scale `√(log p / n)`. Independence is required across observations.
The coordinates of each observation may be dependent.

## References

* M. J. Wainwright, *High-Dimensional Statistics* (2019), Lemma 6.26, p. 183.
* R. Vershynin, *High-Dimensional Probability* (2018), Lemma 2.7.7 and Theorem 2.8.1.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace ProbabilityTheory.iIndepFun

variable {Ω ι p : Type*} [MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} {x : ι → Ω → p → ℝ} {c : ℝ≥0} {cov : Matrix p p ℝ}

private theorem sampleCovariance_bernstein_exponent {N v δ : ℝ}
    (hN : 0 ≤ N) (hv : v ≠ 0) (hδ : 0 ≤ δ) :
    -(N * v * δ) ^ 2 / (4 * (N * (40 * v) ^ 2 + 40 * v * (N * v * δ))) ≤
      -(N / 6560) * min δ (δ ^ 2) := by
  rcases hN.eq_or_lt with rfl | hN
  · simp
  have hrate : min δ (δ ^ 2) * (6400 + 160 * δ) ≤ 6560 * δ ^ 2 := by
    rcases le_total δ 1 with h | h
    · have hsq : δ ^ 2 ≤ δ := by nlinarith [mul_nonneg hδ (sub_nonneg.mpr h)]
      rw [min_eq_right hsq]
      nlinarith [mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr h)]
    · have hsq : δ ≤ δ ^ 2 := by nlinarith [mul_nonneg hδ (sub_nonneg.mpr h)]
      rw [min_eq_left hsq]
      nlinarith
  have hform :
      -(N * v * δ) ^ 2 / (4 * (N * (40 * v) ^ 2 + 40 * v * (N * v * δ))) =
        -N * (δ ^ 2 / (6400 + 160 * δ)) := by
    field_simp [hN.ne', hv]
    ring
  have h : min δ (δ ^ 2) / 6560 ≤ δ ^ 2 / (6400 + 160 * δ) := by
    exact (div_le_div_iff₀ (by norm_num) (by positivity)).2 (by simpa [mul_comm] using hrate)
  calc
    _ = -(N * (δ ^ 2 / (6400 + 160 * δ))) := by rw [hform, neg_mul]
    _ ≤ -(N * (min δ (δ ^ 2) / 6560)) := neg_le_neg (mul_le_mul_of_nonneg_left h hN.le)
    _ = _ := by ring

private theorem measureReal_abs_sampleSecondMoment_sub_apply_pos_eq_zero [Nonempty ι]
    {i j : p} (hi : ∀ a, HasSubgaussianMGF (fun ω ↦ x a ω i) 0 μ)
    (hcov : ∀ a, ∫ ω, x a ω i * x a ω j ∂μ = cov i j) :
    μ.real {ω | 0 < |TauCeti.sampleSecondMoment (fun a ↦ x a ω) i j - cov i j|} = 0 := by
  have hz (a : ι) : (fun ω ↦ x a ω i * x a ω j) =ᵐ[μ] 0 := by
    filter_upwards [(hi a).ae_eq_zero_of_hasSubgaussianMGF_zero] with ω hω
    simp [hω]
  have hcovzero : cov i j = 0 := by
    rw [← hcov (Classical.choice ‹Nonempty ι›)]
    simpa using (integral_congr_ae (hz _))
  have hbad : μ {ω | 0 < |TauCeti.sampleSecondMoment (fun a ↦ x a ω) i j - cov i j|} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.2
    filter_upwards [ae_all_iff.2 hz] with ω hω
    have he : TauCeti.sampleSecondMoment (fun a ↦ x a ω) i j = 0 := by
      have hp (a : ι) : x a ω i * x a ω j = 0 := hω a
      simp [TauCeti.finiteMean_eq_inv_smul_sum, hp]
    intro hb
    have hb' : 0 < |TauCeti.sampleSecondMoment (fun a ↦ x a ω) i j - cov i j| := hb
    rw [he, hcovzero, sub_zero, abs_zero] at hb'
    exact (lt_irrefl (0 : ℝ)) hb'
  rw [Measure.real, hbad, ENNReal.toReal_zero]

/-- An individual entry of the empirical second-moment matrix has a two-sided Bernstein tail
about its common population value. The strict event includes the zero-proxy case. -/
theorem measureReal_abs_sampleSecondMoment_sub_apply_gt_le
    (hindep : iIndepFun x μ) {i j : p}
    (hi : ∀ a, HasSubgaussianMGF (fun ω ↦ x a ω i) c μ)
    (hj : ∀ a, HasSubgaussianMGF (fun ω ↦ x a ω j) c μ)
    (hcov : ∀ a, ∫ ω, x a ω i * x a ω j ∂μ = cov i j) (δ : ℝ) :
    μ.real {ω | (c : ℝ) * δ <
      |TauCeti.sampleSecondMoment (fun a ↦ x a ω) i j - cov i j|} ≤
        2 * exp (-(Fintype.card ι / 6560) * min δ (δ ^ 2)) := by
  classical
  have : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  rcases isEmpty_or_nonempty ι with hι | hι
  · norm_num
    exact measureReal_le_one.trans (by norm_num)
  rcases le_or_gt δ 0 with hδ | hδ
  · have hrate : 0 ≤ -(Fintype.card ι / 6560 : ℝ) * min δ (δ ^ 2) :=
      mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (by positivity)) ((min_le_left _ _).trans hδ)
    exact measureReal_le_one.trans (by linarith [Real.one_le_exp hrate])
  by_cases hc : c = 0
  · subst c
    simp only [NNReal.coe_zero, zero_mul]
    rw [measureReal_abs_sampleSecondMoment_sub_apply_pos_eq_zero hi hcov]
    positivity
  let N := (Fintype.card ι : ℝ)
  have hN : 0 < N := Nat.cast_pos.mpr (Fintype.card_pos (α := ι))
  let Y : ι → Ω → ℝ := fun a ω ↦ x a ω i * x a ω j - cov i j
  have hentry (ω : Ω) : TauCeti.sampleSecondMoment (fun a ↦ x a ω) i j - cov i j =
      N⁻¹ * ∑ a, Y a ω := by
    simp only [TauCeti.sampleSecondMoment_apply, star_trivial]
    rw [← TauCeti.finiteMean_sub_const]
    simp [TauCeti.finiteMean_eq_inv_smul_sum, Y, N]
  have hc' : 0 < (c : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  have hprod (a : ι) := (hi a).hasSubexponentialMGF_mul (hj a) (pos_iff_ne_zero.2 hc)
  have hsub (a : ι) : TauCeti.Probability.HasSubexponentialMGF (Y a) (40 * c) μ := by
    simpa only [Y, hcov a] using (hprod a).center
  have hmean (a : ι) : μ[Y a] = 0 := by
    simp [Y, integral_sub (hprod a).integrable (integrable_const _), hcov a]
  have hY : iIndepFun Y μ := hindep.comp
    (fun _ v ↦ v i * v j - cov i j) (fun _ ↦ by fun_prop)
  have hmono : {ω | (c : ℝ) * δ < |TauCeti.sampleSecondMoment (fun a ↦ x a ω) i j - cov i j|} ⊆
      {ω | N * c * δ ≤ |∑ a, Y a ω|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, hentry, abs_mul, abs_inv, abs_of_pos hN] at hω ⊢
    exact ((lt_inv_mul_iff₀ hN).1 hω).le.trans_eq' (by ring)
  exact (measureReal_mono hmono).trans
    ((hY.measureReal_abs_sum_ge_le_of_hasSubexponentialMGF (s := Finset.univ)
      (by positivity) (fun a _ ↦ hsub a) (fun a _ ↦ hmean a) (by positivity)).trans (by
        simp only [Finset.card_univ]
        exact mul_le_mul_of_nonneg_left
          (exp_le_exp.mpr (sampleCovariance_bernstein_exponent hN.le hc'.ne' hδ.le)) (by norm_num)))

/-- A union bound over all entries of the empirical second-moment matrix. This form gives the
dimension factor explicitly and applies to every normalized error threshold. -/
theorem measureReal_exists_abs_sampleSecondMoment_sub_gt_le [Fintype p]
    (hindep : iIndepFun x μ) (hsub : ∀ a i, HasSubgaussianMGF (fun ω ↦ x a ω i) c μ)
    (hcov : ∀ a i j, ∫ ω, x a ω i * x a ω j ∂μ = cov i j) (δ : ℝ) :
    μ.real {ω | ∃ i j, (c : ℝ) * δ <
      |TauCeti.sampleSecondMoment (fun a ↦ x a ω) i j - cov i j|} ≤
        2 * (Fintype.card p : ℝ) ^ 2 * exp (-(Fintype.card ι / 6560) * min δ (δ ^ 2)) := by
  let S : p × p → Set Ω := fun q ↦ {ω | (c : ℝ) * δ <
    |TauCeti.sampleSecondMoment (fun a ↦ x a ω) q.1 q.2 - cov q.1 q.2|}
  have hset : {ω | ∃ i j, (c : ℝ) * δ <
      |TauCeti.sampleSecondMoment (fun a ↦ x a ω) i j - cov i j|} = ⋃ q, S q := by
    ext ω
    simp [S, Prod.exists]
  rw [hset]
  calc
    _ ≤ ∑ q, μ.real (S q) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ : p × p, 2 * exp (-(Fintype.card ι / 6560) * min δ (δ ^ 2)) :=
      Finset.sum_le_sum fun q _ ↦ hindep.measureReal_abs_sampleSecondMoment_sub_apply_gt_le
        (fun a ↦ hsub a q.1) (fun a ↦ hsub a q.2) (fun a ↦ hcov a q.1 q.2) δ
    _ = _ := by simp [Fintype.card_prod, Nat.cast_mul]; ring

private theorem sampleCovariance_log_offset {L δ : ℝ} (hL' : L ≤ 1)
    (hδ : 0 ≤ δ) :
    13120 * L + min δ (δ ^ 2) ≤
      min (13120 * √L + δ) ((13120 * √L + δ) ^ 2) := by
  rcases lt_or_ge L 0 with hL | hL
  · rw [Real.sqrt_eq_zero_of_nonpos hL.le, mul_zero, zero_add]
    linarith
  have hsq := Real.sq_sqrt hL
  have hs := Real.sqrt_nonneg L
  have hroot : L ≤ √L := by
    have hle : √L ≤ 1 := by simpa using Real.sqrt_le_sqrt hL'
    nlinarith [mul_nonneg hs (sub_nonneg.mpr hle)]
  refine le_min ?_ ?_
  · linarith [min_le_left δ (δ ^ 2)]
  · nlinarith [min_le_right δ (δ ^ 2), mul_nonneg hs hδ]

/-- Simultaneous entrywise covariance concentration, with the number of entries absorbed
into the threshold. The observations need a common second moment and common coordinate
proxy, but may have different distributions. -/
theorem measureReal_max_abs_sampleCovariance_sub_gt_le [Fintype p]
    (hindep : iIndepFun x μ) (hsub : ∀ a i, HasSubgaussianMGF (fun ω ↦ x a ω i) c μ)
    (hcov : ∀ a i j, ∫ ω, x a ω i * x a ω j ∂μ = cov i j)
    (hn : log (Fintype.card p) ≤ Fintype.card ι) (δ : ℝ) :
    μ.real {ω | ∃ i j, (c : ℝ) * (13120 * √(log (Fintype.card p) / Fintype.card ι) + δ) <
      |TauCeti.sampleSecondMoment (fun a ↦ x a ω) i j - cov i j|} ≤
        2 * exp (-(Fintype.card ι / 6560) * min δ (δ ^ 2)) := by
  rcases isEmpty_or_nonempty p with hp | hp
  · have he : {ω | ∃ i j, (c : ℝ) * (13120 * √(log (Fintype.card p) / Fintype.card ι) + δ) <
        |TauCeti.sampleSecondMoment (fun a ↦ x a ω) i j - cov i j|} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 (fun _ ⟨i, _, _⟩ ↦ isEmptyElim i)
    rw [he, measureReal_empty]
    positivity
  have : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  rcases isEmpty_or_nonempty ι with hι | hι
  · norm_num
    exact measureReal_le_one.trans (by norm_num)
  rcases lt_or_ge δ 0 with hδ | hδ
  · have hrate : 0 ≤ -(Fintype.card ι / 6560 : ℝ) * min δ (δ ^ 2) :=
      mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (by positivity))
        ((min_le_left _ _).trans hδ.le)
    exact measureReal_le_one.trans (by linarith [Real.one_le_exp hrate])
  let N := (Fintype.card ι : ℝ)
  let P := (Fintype.card p : ℝ)
  let L := log P / N
  have hP : 0 < P := Nat.cast_pos.mpr (Fintype.card_pos (α := p))
  have hN : 0 < N := Nat.cast_pos.mpr (Fintype.card_pos (α := ι))
  have hL' : L ≤ 1 := (div_le_one hN).2 hn
  have hoff := sampleCovariance_log_offset hL' hδ
  have hrate : (N / 6560) * (13120 * L + min δ (δ ^ 2)) =
      2 * log P + (N / 6560) * min δ (δ ^ 2) := by
    dsimp [L]
    field_simp
    ring
  calc
    _ ≤ 2 * P ^ 2 * exp (-(N / 6560) *
        min (13120 * √L + δ) ((13120 * √L + δ) ^ 2)) :=
      hindep.measureReal_exists_abs_sampleSecondMoment_sub_gt_le hsub hcov (13120 * √L + δ)
    _ ≤ 2 * P ^ 2 * exp (-(N / 6560) * (13120 * L + min δ (δ ^ 2))) := by
      exact mul_le_mul_of_nonneg_left
        (exp_le_exp.mpr (mul_le_mul_of_nonpos_left hoff (neg_nonpos.mpr (by positivity))))
        (by positivity)
    _ = _ := by
      have hP2 : P ^ 2 = exp (2 * log P) := by
        rw [← Real.exp_log hP, Real.log_exp, ← Real.exp_natCast_mul]
        norm_num
      rw [hP2, mul_assoc 2, ← Real.exp_add, neg_mul, hrate]
      congr 2
      ring

/-- With probability at least one minus the two-sided tail bound, all sample covariance
entries lie within the same tolerance of their respective population entries. -/
theorem one_sub_exp_le_measureReal_forall_abs_sampleSecondMoment_sub_le [Fintype p]
    (hindep : iIndepFun x μ) (hsub : ∀ a i, HasSubgaussianMGF (fun ω ↦ x a ω i) c μ)
    (hcov : ∀ a i j, ∫ ω, x a ω i * x a ω j ∂μ = cov i j)
    (hn : log (Fintype.card p) ≤ Fintype.card ι) (δ : ℝ) :
    let threshold := (c : ℝ) * (13120 * √(log (Fintype.card p) / Fintype.card ι) + δ)
    1 - 2 * exp (-(Fintype.card ι / 6560) * min δ (δ ^ 2)) ≤ μ.real {ω |
      ∀ i j, |TauCeti.sampleSecondMoment (fun a ↦ x a ω) i j - cov i j| ≤ threshold} := by
  intro threshold
  have : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  let bad : Set Ω := {ω | ∃ i j,
    threshold < |TauCeti.sampleSecondMoment (fun a ↦ x a ω) i j - cov i j|}
  have hbad : NullMeasurableSet bad μ := by
    have hset : bad = ⋃ i, ⋃ j, {ω | threshold <
        |TauCeti.sampleSecondMoment (fun a ↦ x a ω) i j - cov i j|} := by
      ext ω
      simp [bad]
    rw [hset]
    refine NullMeasurableSet.iUnion fun i ↦ NullMeasurableSet.iUnion fun j ↦
      nullMeasurableSet_lt aemeasurable_const ?_
    refine continuous_abs.measurable.comp_aemeasurable ?_
    refine AEMeasurable.sub_const ?_ _
    simp only [TauCeti.sampleSecondMoment_apply, star_trivial,
      TauCeti.finiteMean_eq_inv_smul_sum, smul_eq_mul]
    have hsum : AEMeasurable (fun ω ↦ ∑ a, x a ω i * x a ω j) μ :=
      Finset.aemeasurable_fun_sum _ fun a _ ↦ (hsub a i).aemeasurable.mul (hsub a j).aemeasurable
    exact hsum.const_mul _
  have hgood : {ω | ∀ i j,
      |TauCeti.sampleSecondMoment (fun a ↦ x a ω) i j - cov i j| ≤ threshold} = badᶜ := by
    ext ω
    simp [bad, not_lt]
  rw [hgood, probReal_compl_eq_one_sub₀ hbad]
  exact sub_le_sub_left (hindep.measureReal_max_abs_sampleCovariance_sub_gt_le hsub hcov hn δ) _

end ProbabilityTheory.iIndepFun
