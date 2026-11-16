/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Probability.Martingale.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz
import TauCeti.Probability.Martingale.Basic

/-!
# Complex exponential martingales for bounded continuous martingales

Proves that for a bounded, almost-surely continuous real martingale `X` on a raw filtration `ℱ`
under a finite measure `P` and a strongly adapted nondecreasing Lipschitz process `A` with `A 0 = 0`
such that `X ^ 2 - A` is a martingale, `t ↦ exp (I * α * X t + α ^ 2 / 2 * A t)` is a martingale
for every `α : ℝ`, via uniform-partition telescoping and martingale increment orthogonality.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Theorem 3.3.16.
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Springer, 1999, Chapter IV, Theorem 3.6.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped NNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*}

section PureHelpers

private def expProc (X A : ℝ≥0 → Ω → ℝ) (α : ℝ) (t : ℝ≥0) (ω : Ω) : ℂ :=
  exp (I * α * X t ω + ((α ^ 2 / 2 * A t ω : ℝ) : ℂ))

private def expRem (α x a : ℝ) : ℂ :=
  exp (I * α * x + ((α ^ 2 / 2 * a : ℝ) : ℂ)) - 1 -
    (I * α * x + ((α ^ 2 / 2 : ℝ) : ℂ) * ((a - x ^ 2 : ℝ) : ℂ))

private def uniformGrid (s t : ℝ≥0) (m k : ℕ) : ℝ≥0 :=
  s + ((min k (m + 1) : ℕ) : ℝ≥0) / (m + 1 : ℝ≥0) * (t - s)

private def maxInc (X : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (m : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (m + 1)).sup' ⟨0, Finset.mem_range.2 (Nat.succ_pos m)⟩ fun k ↦
    |X (uniformGrid s t m (k + 1)) ω - X (uniformGrid s t m k) ω|

private lemma maxInc_nonneg (X : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (m : ℕ) (ω : Ω) :
    0 ≤ maxInc X s t m ω :=
  (abs_nonneg _).trans (Finset.le_sup' (f := fun k ↦
    |X (uniformGrid s t m (k + 1)) ω - X (uniformGrid s t m k) ω|)
    (Finset.mem_range.2 (Nat.succ_pos m)))

private lemma uniformGrid_zero (s t : ℝ≥0) (m : ℕ) :
    uniformGrid s t m 0 = s := by simp [uniformGrid]

private lemma uniformGrid_last {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) :
    uniformGrid s t m (m + 1) = t := by simp [uniformGrid, add_tsub_cancel_of_le hst]

private lemma uniformGrid_mono (s t : ℝ≥0) (m : ℕ) : Monotone (uniformGrid s t m) :=
  fun _ _ h ↦ by dsimp only [uniformGrid]; gcongr

private lemma uniformGrid_step {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) {k : ℕ} (hk : k < m + 1) :
    (uniformGrid s t m (k + 1) : ℝ) - uniformGrid s t m k = ((t : ℝ) - s) / (m + 1) := by
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  simp only [uniformGrid, min_eq_left hk.le, min_eq_left (Nat.add_one_le_of_lt hk),
    NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_one,
    NNReal.coe_sub hst, Nat.cast_add, Nat.cast_one]
  field_simp [hm]; ring

private lemma uniformGrid_mem_Icc {s t : ℝ≥0} (hst : s ≤ t) (m k : ℕ) :
    uniformGrid s t m k ∈ Set.Icc s t :=
  ⟨by simpa only [uniformGrid_zero] using uniformGrid_mono s t m (Nat.zero_le k),
    by simpa [uniformGrid] using
      (uniformGrid_mono s t m (min_le_right k (m + 1))).trans_eq (uniformGrid_last hst m)⟩

private lemma exists_norm_expRem_le (α R : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {D x a : ℝ}, |x| ≤ 2 * R → |x| ≤ D → 0 ≤ a → a ≤ L →
      ‖expRem α x a‖ ≤ K * (D * x ^ 2 + D * a + a ^ 2) := by
  let Ke : ℝ := Real.exp (2 * |α| * R + α ^ 2 / 2 * L)
  refine ⟨|α| ^ 3 / 2 + α ^ 4 / 8 + 4 * (|α| ^ 3 + (α ^ 2 / 2) ^ 3 * L) * Ke,
    by positivity, fun {D x a} hxR hxD ha0 haL ↦ ?_⟩
  let w : ℂ := I * α * x + ((α ^ 2 / 2 * a : ℝ) : ℂ)
  have hw : ‖w‖ ≤ |α| * |x| + α ^ 2 / 2 * a := (norm_add_le _ _).trans_eq <| by simp [ha0]
  have hcube : (|α| * |x| + α ^ 2 / 2 * a) ^ 3 ≤
      4 * (|α| ^ 3 * |x| ^ 3 + (α ^ 2 / 2) ^ 3 * a ^ 3) := by
    simp only [← mul_pow]
    nlinarith [sq_nonneg (|α| * |x| - α ^ 2 / 2 * a), show 0 ≤ |α| * |x| by positivity,
      show 0 ≤ α ^ 2 / 2 * a by positivity]
  have hrem : ‖exp w - ∑ j ∈ Finset.range 3, w ^ j / j.factorial‖ ≤
      4 * (|α| ^ 3 * |x| ^ 3 + (α ^ 2 / 2) ^ 3 * a ^ 3) * Ke :=
    (Complex.norm_exp_sub_sum_le_norm_mul_exp w 3).trans <|
      (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hw 3) (Real.exp_le_exp.2 (hw.trans (by
        linarith [mul_le_mul_of_nonneg_left hxR (abs_nonneg α),
          mul_le_mul_of_nonneg_left haL (show 0 ≤ α ^ 2 / 2 by positivity)])))
        (Real.exp_pos _).le (by positivity)).trans
        (mul_le_mul_of_nonneg_right hcube (by positivity))
  have hmid : ‖I * ((α ^ 3 / 2 * x * a : ℝ) : ℂ) + ((α ^ 4 / 8 * a ^ 2 : ℝ) : ℂ)‖ ≤
      |α| ^ 3 / 2 * |x| * a + α ^ 4 / 8 * a ^ 2 := (norm_add_le _ _).trans_eq <| by
    have h4 : |α| ^ 4 = α ^ 4 := by rw [show |α| ^ 4 = (|α| ^ 2) ^ 2 by ring, sq_abs]; ring
    simp [abs_of_nonneg ha0, h4]
  have htri : ‖expRem α x a‖ ≤
      4 * (|α| ^ 3 * |x| ^ 3 + (α ^ 2 / 2) ^ 3 * a ^ 3) * Ke +
        (|α| ^ 3 / 2 * |x| * a + α ^ 4 / 8 * a ^ 2) := by
    rw [show expRem α x a = (exp w - ∑ j ∈ Finset.range 3, w ^ j / j.factorial) +
        (I * ((α ^ 3 / 2 * x * a : ℝ) : ℂ) + ((α ^ 4 / 8 * a ^ 2 : ℝ) : ℂ)) by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, expRem, w]
      push_cast; ring_nf; simp [I_sq]; ring]
    exact (norm_add_le _ _).trans (add_le_add hrem hmid)
  have hD0 : 0 ≤ D := (abs_nonneg x).trans hxD
  have hx3 : |x| ^ 3 ≤ D * x ^ 2 := by rw [show |x| ^ 3 = |x| * |x| ^ 2 by ring, sq_abs]; gcongr
  have ha3 : a ^ 3 ≤ L * a ^ 2 := by rw [show a ^ 3 = a * a ^ 2 by ring]; gcongr
  nlinarith [mul_le_mul_of_nonneg_left hx3 (show 0 ≤ 4 * |α| ^ 3 * Ke by positivity),
    mul_le_mul_of_nonneg_left ha3 (show 0 ≤ 4 * (α ^ 2 / 2) ^ 3 * Ke by positivity),
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hxD ha0)
      (show 0 ≤ |α| ^ 3 / 2 by positivity),
    show 0 ≤ |α| ^ 3 / 2 by positivity, show 0 ≤ α ^ 4 / 8 by positivity,
    show 0 ≤ 4 * |α| ^ 3 * Ke by positivity, show 0 ≤ 4 * (α ^ 2 / 2) ^ 3 * L * Ke by positivity,
    show 0 ≤ D * x ^ 2 by positivity, show 0 ≤ D * a by positivity, sq_nonneg a]

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω}

private lemma ae_abs_increment_le {X : ℝ≥0 → Ω → ℝ} {R : ℝ}
    (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R) (u v : ℝ≥0) :
    ∀ᵐ ω ∂P, |X v ω - X u ω| ≤ 2 * R := by
  filter_upwards [hXR v, hXR u] with ω hv hu; exact (abs_sub _ _).trans (by linarith)

private lemma ae_maxInc_le {X : ℝ≥0 → Ω → ℝ} {R : ℝ} (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R)
    (s t : ℝ≥0) (m : ℕ) : ∀ᵐ ω ∂P, maxInc X s t m ω ≤ 2 * R :=
  (ae_all_iff.2 fun k : ℕ ↦
    ae_abs_increment_le hXR (uniformGrid s t m k) (uniformGrid s t m (k + 1))).mono
      fun _ h ↦ Finset.sup'_le _ _ fun k _ ↦ h k

private lemma ae_norm_expProc_le {X A : ℝ≥0 → Ω → ℝ} {c : ℝ} (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    (α : ℝ) (u : ℝ≥0) :
    ∀ᵐ ω ∂P, ‖expProc X A α u ω‖ ≤ Real.exp (α ^ 2 / 2 * (c * (u : ℝ))) := by
  filter_upwards [hA0, hA_step 0 u bot_le] with ω h0 hA
  simpa only [expProc, Complex.norm_exp, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, zero_add] using
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by simpa [h0] using hA.2) (by positivity))

end PureHelpers

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ℝ≥0 mΩ}

section Orthogonality

private lemma setIntegral_sub_smul_eq_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ P) {s t : ℝ≥0} (hst : s ≤ t)
    {E : Set Ω} (hE : MeasurableSet[ℱ s] E) {Z : Ω → F} (hZ : StronglyMeasurable[ℱ s] Z)
    {C : ℝ} (hb : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ C) : ∫ ω in E, (M t ω - M s ω) • Z ω ∂P = 0 := by
  have hcond : P[fun ω ↦ (M t ω - M s ω) • E.indicator Z ω | ℱ s] =ᵐ[P] fun _ ↦ (0 : F) := by
    have hpull := condExp_stronglyMeasurable_bilin_of_bound (ContinuousLinearMap.lsmul ℝ ℝ).flip
      (ℱ.le s) (hZ.indicator hE) ((hM.integrable t).sub (hM.integrable s)) (max C 0)
      (hb.mono fun ω hω ↦ by by_cases h : ω ∈ E <;> simp [h, hω.trans (le_max_left C 0)])
    filter_upwards [hpull, condExp_sub (m := ℱ s) (hM.integrable t) (hM.integrable s),
      hM.condExp_ae_eq hst] with ω hp hd hm
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply, Pi.sub_apply]
      at hp hd
    rw [hp, hd, hm, condExp_of_stronglyMeasurable (ℱ.le s) (hM.stronglyAdapted s)
      (hM.integrable s), sub_self, zero_smul]
  rw [← integral_indicator (ℱ.le s E hE),
    show E.indicator (fun ω ↦ (M t ω - M s ω) • Z ω) = fun ω ↦ (M t ω - M s ω) • E.indicator Z ω by
      ext ω; by_cases h : ω ∈ E <;> simp [h],
    ← integral_condExp (ℱ.le s), integral_congr_ae hcond, integral_zero]

private lemma setIntegral_sq_sub_smul_eq_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {X A : ℝ≥0 → Ω → ℝ} {R : ℝ} (hX : Martingale X ℱ P)
    (hQ : Martingale (fun u ω ↦ X u ω ^ 2 - A u ω) ℱ P) (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R)
    {s t : ℝ≥0} (hst : s ≤ t) {E : Set Ω} (hE : MeasurableSet[ℱ s] E)
    {Z : Ω → F} (hZ : StronglyMeasurable[ℱ s] Z) {C : ℝ} (hb : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ C) :
    ∫ ω in E, ((X t ω - X s ω) ^ 2 - (A t ω - A s ω)) • Z ω ∂P = 0 := by
  have hZ' : StronglyMeasurable[ℱ s] (fun ω ↦ (2 * X s ω) • Z ω) :=
    (stronglyMeasurable_const.mul (hX.stronglyAdapted s)).smul hZ
  have hb' : ∀ᵐ ω ∂P, ‖(2 * X s ω) • Z ω‖ ≤ 2 * max R 0 * max C 0 := by
    filter_upwards [hXR s, hb] with ω hR hC
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg zero_le_two]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hR.trans (le_max_left _ _)) zero_le_two)
      (hC.trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
  have hint {f : Ω → ℝ} {W : Ω → F} {D : ℝ} (hf : Integrable f P)
      (hW : StronglyMeasurable[ℱ s] W) (hWb : ∀ᵐ ω ∂P, ‖W ω‖ ≤ D) :
      IntegrableOn (fun ω ↦ f ω • W ω) E P :=
    ((hf.norm.const_mul (max D 0)).mono'
      (hf.aestronglyMeasurable.smul (hW.mono (ℱ.le s)).aestronglyMeasurable)
      (hWb.mono fun ω hω ↦ by
        change ‖f ω • W ω‖ ≤ _; rw [norm_smul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hω.trans (le_max_left _ _)) (norm_nonneg _))).integrableOn
  simp_rw [show ∀ ω, ((X t ω - X s ω) ^ 2 - (A t ω - A s ω)) • Z ω =
      ((X t ω ^ 2 - A t ω) - (X s ω ^ 2 - A s ω)) • Z ω -
        (X t ω - X s ω) • ((2 * X s ω) • Z ω) from fun _ ↦ by
    rw [smul_smul, ← sub_smul]; congr 1; ring]
  rw [integral_sub (hint (f := fun ω ↦ (X t ω ^ 2 - A t ω) - (X s ω ^ 2 - A s ω))
        ((hQ.integrable t).sub (hQ.integrable s)) hZ hb)
      (hint (f := fun ω ↦ X t ω - X s ω) ((hX.integrable t).sub (hX.integrable s)) hZ' hb'),
    setIntegral_sub_smul_eq_zero hQ hst hE hZ hb,
    setIntegral_sub_smul_eq_zero hX hst hE hZ' hb', sub_self]

end Orthogonality

section QuadraticSumBound

private lemma memLp_increment_sq {X : ℝ≥0 → Ω → ℝ} {R : ℝ} (hX : StronglyAdapted ℱ X)
    (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R) (u v : ℝ≥0) :
    MemLp (fun ω ↦ (X v ω - X u ω) ^ 2) 2 P :=
  MemLp.of_bound ((((hX v).mono (ℱ.le v)).sub ((hX u).mono (ℱ.le u))).aestronglyMeasurable.pow 2)
    ((2 * R) ^ 2) ((ae_abs_increment_le hXR u v).mono fun _ hω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]; gcongr)

private lemma integrable_increment_bracket {A : ℝ≥0 → Ω → ℝ} {c : ℝ} (hA : StronglyAdapted ℱ A)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    {u v : ℝ≥0} (huv : u ≤ v) : Integrable (fun ω ↦ A v ω - A u ω) P :=
  (integrable_const (c * ((v : ℝ) - u))).mono'
    (((hA v).mono (ℱ.le v)).sub ((hA u).mono (ℱ.le u))).aestronglyMeasurable
    ((hA_step u v huv).mono fun _ hω ↦ by rw [Real.norm_eq_abs, abs_of_nonneg hω.1]; exact hω.2)

private lemma integral_sq_sum_sq_le {X A : ℝ≥0 → Ω → ℝ} {R c : ℝ} (hc : 0 ≤ c)
    (hX : Martingale X ℱ P) (hQ : Martingale (fun u ω ↦ X u ω ^ 2 - A u ω) ℱ P)
    (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R) (hA : StronglyAdapted ℱ A)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    {g : ℕ → ℝ≥0} (hg : Monotone g) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n, (X (g (k + 1)) ω - X (g k) ω) ^ 2) ^ 2 ∂P ≤
      (4 * R ^ 2 * (c * ((g n : ℝ) - g 0)) + 2 * (c * ((g n : ℝ) - g 0)) ^ 2) * P.real univ := by
  let L : ℝ := c * ((g n : ℝ) - g 0)
  let d (k : ℕ) (ω : Ω) : ℝ := (X (g (k + 1)) ω - X (g k) ω) ^ 2
  let a (k : ℕ) (ω : Ω) : ℝ := A (g (k + 1)) ω - A (g k) ω
  let δ (k : ℕ) : ℝ := c * ((g (k + 1) : ℝ) - g k)
  let Sk (k : ℕ) (ω : Ω) : ℝ := ∑ j ∈ Finset.range k, d j ω
  have hd_int (k : ℕ) : Integrable (d k) P :=
    (memLp_increment_sq hX.stronglyAdapted hXR (g k) (g (k + 1))).integrable one_le_two
  have hd_bd (k : ℕ) : ∀ᵐ ω ∂P, ‖d k ω‖ ≤ (2 * R) ^ 2 :=
    (ae_abs_increment_le hXR (g k) (g (k + 1))).mono fun _ hω ↦ by
      dsimp only [d]; rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]; gcongr
  have ha_int (k : ℕ) : Integrable (a k) P :=
    integrable_increment_bracket hA hA_step (hg (Nat.le_succ k))
  have hstep_le (k : ℕ) {W : Ω → ℝ} {C : ℝ} (hW_sm : StronglyMeasurable[ℱ (g k)] W)
      (hW_bd : ∀ᵐ ω ∂P, ‖W ω‖ ≤ C) (hW_nn : ∀ ω, 0 ≤ W ω) (hW_int : Integrable W P) :
      ∫ ω, W ω * d k ω ∂P ≤ δ k * ∫ ω, W ω ∂P := by
    have hW_asm : AEStronglyMeasurable W P := (hW_sm.mono (ℱ.le _)).aestronglyMeasurable
    have h0 := setIntegral_sq_sub_smul_eq_zero (F := ℝ) hX hQ hXR (hg (Nat.le_succ k))
      MeasurableSet.univ hW_sm hW_bd
    simp only [Measure.restrict_univ, smul_eq_mul] at h0
    rw [show (fun ω ↦ (d k ω - a k ω) * W ω) = fun ω ↦ W ω * d k ω - W ω * a k ω by ext; ring,
      integral_sub ((hd_int k).bdd_mul hW_asm hW_bd) ((ha_int k).bdd_mul hW_asm hW_bd),
      sub_eq_zero] at h0
    rw [h0, ← integral_const_mul]
    exact integral_mono_ae ((ha_int k).bdd_mul hW_asm hW_bd) (hW_int.const_mul _)
      ((hA_step _ _ (hg (Nat.le_succ k))).mono fun ω hω ↦ by
        dsimp only [a, δ]; rw [mul_comm (c * _)]; exact mul_le_mul_of_nonneg_left hω.2 (hW_nn ω))
  have hd_le (k : ℕ) : ∫ ω, d k ω ∂P ≤ δ k * P.real Set.univ := by
    simpa [integral_const, mul_comm (P.real Set.univ)] using hstep_le k (W := fun _ ↦ (1 : ℝ))
      stronglyMeasurable_const (C := 1) (ae_of_all P fun _ ↦ by norm_num)
      (fun _ ↦ zero_le_one) (integrable_const 1)
  have hSk_sm (k : ℕ) : StronglyMeasurable[ℱ (g k)] (Sk k) :=
    Finset.stronglyMeasurable_fun_sum _ fun j hj ↦
      (((hX.stronglyAdapted (g (j + 1))).mono (ℱ.mono (hg (Nat.succ_le_of_lt
        (Finset.mem_range.1 hj))))).sub ((hX.stronglyAdapted (g j)).mono
        (ℱ.mono (hg (Finset.mem_range.1 hj).le)))).pow 2
  have hSk_bd (k : ℕ) : ∀ᵐ ω ∂P, ‖Sk k ω‖ ≤ (k : ℝ) * (2 * R) ^ 2 :=
    (ae_all_iff.2 hd_bd).mono fun _ hω ↦
      (norm_sum_le _ _).trans <| (Finset.sum_le_sum fun j _ ↦ hω j).trans_eq (by simp)
  have hS1 (k : ℕ) : ∫ ω, Sk k ω ∂P ≤ c * ((g k : ℝ) - g 0) * P.real Set.univ := by
    rw [integral_finsetSum _ fun j _ ↦ hd_int j]
    exact (Finset.sum_le_sum fun j _ ↦ hd_le j).trans_eq <| by
      rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_range_sub (fun i ↦ (g i : ℝ))]
  have hS2 : ∀ k ≤ n, ∫ ω, Sk k ω ^ 2 ∂P ≤
      (4 * R ^ 2 + 2 * L) * (c * ((g k : ℝ) - g 0)) * P.real Set.univ := fun k hk ↦ by
    induction k with
    | zero => simp [Sk]
    | succ k ih =>
      have hSk_int : Integrable (Sk k) P := integrable_finsetSum _ fun j _ ↦ hd_int j
      have hcross : ∫ ω, Sk k ω * d k ω ∂P ≤ δ k * (L * P.real Set.univ) :=
        (hstep_le k (hSk_sm k) (hSk_bd k) (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
          hSk_int).trans <| mul_le_mul_of_nonneg_left ((hS1 k).trans <| by
            dsimp only [L]; have := NNReal.coe_le_coe.2 (hg (Nat.le_of_succ_le hk)); gcongr)
          (mul_nonneg hc (sub_nonneg.2 (NNReal.coe_le_coe.2 (hg (Nat.le_succ k)))))
      have h4_int : Integrable (fun ω ↦ d k ω ^ 2) P := by
        simpa only [sq] using (hd_int k).bdd_mul (hd_int k).aestronglyMeasurable (hd_bd k)
      have hquart : ∫ ω, d k ω ^ 2 ∂P ≤ 4 * R ^ 2 * (δ k * P.real Set.univ) :=
        ((integral_mono_ae h4_int ((hd_int k).const_mul (4 * R ^ 2)) ((hd_bd k).mono fun ω hω ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hω
          nlinarith [sq_nonneg (X (g (k + 1)) ω - X (g k) ω)])).trans_eq
          (integral_const_mul _ _)).trans (mul_le_mul_of_nonneg_left (hd_le k) (by positivity))
      have hSk2_int : Integrable (fun ω ↦ Sk k ω ^ 2) P := by
        simpa only [sq] using hSk_int.bdd_mul hSk_int.aestronglyMeasurable (hSk_bd k)
      have hcross_int : Integrable (fun ω ↦ 2 * (Sk k ω * d k ω)) P :=
        ((hd_int k).bdd_mul hSk_int.aestronglyMeasurable (hSk_bd k)).const_mul 2
      simp_rw [show ∀ ω, Sk (k + 1) ω ^ 2 = Sk k ω ^ 2 + 2 * (Sk k ω * d k ω) + d k ω ^ 2 from
        fun ω ↦ by rw [show Sk (k + 1) ω = Sk k ω + d k ω from Finset.sum_range_succ _ k]; ring]
      rw [integral_add (show Integrable (fun ω ↦ Sk k ω ^ 2 + 2 * (Sk k ω * d k ω)) P from
        hSk2_int.add hcross_int) h4_int, integral_add hSk2_int hcross_int, integral_const_mul]
      linarith [ih (Nat.le_of_succ_le hk)]
  exact (hS2 n le_rfl).trans_eq (by ring)

end QuadraticSumBound

section ModulusAndPartition

private lemma memLp_maxInc {X : ℝ≥0 → Ω → ℝ} {R : ℝ} (hX : StronglyAdapted ℱ X)
    (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R) (s t : ℝ≥0) (m : ℕ) : MemLp (maxInc X s t m) 2 P := by
  have hsup {I : Finset ℕ} (hI : I.Nonempty) {f : ℕ → Ω → ℝ}
      (hf : ∀ i ∈ I, StronglyMeasurable (f i)) :
      StronglyMeasurable (fun ω ↦ I.sup' hI (f · ω)) := by
    induction hI using Finset.Nonempty.cons_induction with
    | singleton i => simpa using hf i (Finset.mem_singleton_self i)
    | cons i u hi hu ih =>
      convert (hf i (Finset.mem_cons_self i u)).sup
        (ih fun j hj ↦ hf j (Finset.mem_cons_of_mem hj)) using 1
      ext ω; exact Finset.sup'_cons ..
  exact MemLp.of_bound (show StronglyMeasurable (maxInc X s t m) from hsup _ fun k _ ↦ by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using
        ((show StronglyMeasurable (X (uniformGrid s t m (k + 1))) from (hX _).mono (ℱ.le _)).sub
          (show StronglyMeasurable (X (uniformGrid s t m k)) from (hX _).mono (ℱ.le _))).norm
      ).aestronglyMeasurable
    (2 * R) ((ae_maxInc_le hXR s t m).mono fun ω hω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (maxInc_nonneg X s t m ω)]; exact hω)

private lemma tendsto_integral_maxInc_sq {X : ℝ≥0 → Ω → ℝ} {R : ℝ} (hX : StronglyAdapted ℱ X)
    (hcont : ∀ᵐ ω ∂P, Continuous (X · ω)) (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R)
    {s t : ℝ≥0} (hst : s ≤ t) :
    Tendsto (fun m ↦ ∫ ω, maxInc X s t m ω ^ 2 ∂P) atTop (𝓝 0) := by
  have hD_lim : ∀ᵐ ω ∂P, Tendsto (fun m ↦ maxInc X s t m ω) atTop (𝓝 0) :=
    hcont.mono fun ω hω ↦ Metric.tendsto_atTop.2 fun ε hε ↦ by
      obtain ⟨δ, hδ, hδ_prop⟩ := Metric.uniformContinuousOn_iff.1
        ((isCompact_Icc (a := s) (b := t)).uniformContinuousOn_of_continuous hω.continuousOn) ε hε
      obtain ⟨N, hN⟩ := ((show Tendsto (fun m : ℕ ↦ ((t : ℝ) - s) / (m + 1)) atTop (𝓝 0) by
          simpa only [mul_zero, mul_one_div] using
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((t : ℝ) - s)).eventually
        (gt_mem_nhds hδ)).exists_forall_of_atTop
      refine ⟨N, fun m hm ↦ ?_⟩
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (maxInc_nonneg X s t m ω)]
      refine (Finset.sup'_lt_iff _).2 fun k hk ↦ ?_
      simpa [Real.dist_eq] using hδ_prop _ (uniformGrid_mem_Icc hst m (k + 1))
        _ (uniformGrid_mem_Icc hst m k) (by
          rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2
            (NNReal.coe_le_coe.2 (uniformGrid_mono s t m (Nat.le_succ k)))),
            uniformGrid_step hst m (Finset.mem_range.1 hk)]
          exact hN m hm)
  simpa only [integral_zero] using
    tendsto_integral_of_dominated_convergence (F := fun m ω ↦ maxInc X s t m ω ^ 2)
      (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ (2 * R) ^ 2)
      (fun m ↦ (memLp_maxInc hX hXR s t m).aestronglyMeasurable.pow 2) (integrable_const _)
      (fun m ↦ (ae_maxInc_le hXR s t m).mono fun ω h ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (maxInc_nonneg X s t m ω) h 2)
      (hD_lim.mono fun _ h ↦ by simpa using h.pow 2)

end ModulusAndPartition

/-- **Complex exponential martingale for a bounded continuous martingale with Lipschitz bracket.**
If `X` is a bounded, almost-surely continuous real martingale, `A` is a strongly adapted
nondecreasing Lipschitz process starting at `0`, and `X ^ 2 - A` is a martingale, then
`t ↦ exp (I * α * X t + α ^ 2 / 2 * A t)` is a martingale for every `α : ℝ`. -/
theorem exp_I_mul_add_of_bounded {X A : ℝ≥0 → Ω → ℝ} {R c : ℝ}
    (hX : Martingale X ℱ P) (hQ : Martingale (fun u ω ↦ X u ω ^ 2 - A u ω) ℱ P)
    (hcont : ∀ᵐ ω ∂P, Continuous (X · ω)) (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R)
    (hA_adapt : StronglyAdapted ℱ A) (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    (α : ℝ) :
    Martingale (fun t ω ↦ exp (I * α * X t ω + ((α ^ 2 / 2 * A t ω : ℝ) : ℂ))) ℱ P := by
  let c' : ℝ := max c 0
  have hc' : 0 ≤ c' := le_max_right c 0
  have hA_step' (u v : ℝ≥0) (huv : u ≤ v) :
      ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c' * ((v : ℝ) - u) :=
    (hA_step u v huv).mono fun _ hω ↦ ⟨hω.1, hω.2.trans (mul_le_mul_of_nonneg_right
      (le_max_left c 0) (sub_nonneg.2 (NNReal.coe_le_coe.2 huv)))⟩
  have hZ_adapt : StronglyAdapted ℱ (expProc X A α) := fun u ↦
    Complex.continuous_exp.comp_stronglyMeasurable
      ((stronglyMeasurable_const.mul (Complex.continuous_ofReal.comp_stronglyMeasurable
        (hX.stronglyAdapted u))).add (Complex.continuous_ofReal.comp_stronglyMeasurable
        (stronglyMeasurable_const.mul (hA_adapt u))))
  have hZ_int (u : ℝ≥0) : Integrable (expProc X A α u) P :=
    (integrable_const _).mono' ((hZ_adapt u).mono (ℱ.le u)).aestronglyMeasurable
      (ae_norm_expProc_le (X := X) hA0 hA_step' α u)
  change Martingale (expProc X A α) ℱ P
  rw [hZ_adapt.martingale_iff_setIntegral_eq hZ_int]
  intro s t hst E hE
  rw [eq_comm, ← sub_eq_zero, ← integral_sub (hZ_int t).integrableOn (hZ_int s).integrableOn,
    ← norm_eq_zero]
  let L : ℝ := c' * ((t : ℝ) - s)
  let Mz : ℝ := Real.exp (α ^ 2 / 2 * (c' * (t : ℝ)))
  let B : ℝ := (4 * R ^ 2 * L + 2 * L ^ 2) * P.real Set.univ
  have hL : 0 ≤ L := mul_nonneg hc' (sub_nonneg.2 (NNReal.coe_le_coe.2 hst))
  obtain ⟨K, hK0, hK⟩ := exists_norm_expRem_le α R hL
  have hstep {u v : ℝ≥0} (huv : u ≤ v) (hsu : s ≤ u) :
      IntegrableOn (fun ω ↦ expProc X A α u ω * expRem α (X v ω - X u ω) (A v ω - A u ω)) E P ∧
        ∫ ω in E, (expProc X A α v ω - expProc X A α u ω) ∂P =
          ∫ ω in E, expProc X A α u ω * expRem α (X v ω - X u ω) (A v ω - A u ω) ∂P := by
    have hZ_bd := ae_norm_expProc_le (X := X) hA0 hA_step' α u
    have hmul {f : Ω → ℝ} (hf : Integrable f P) (k : ℂ) :
        IntegrableOn (fun ω ↦ k * (f ω • expProc X A α u ω)) E P :=
      (((Complex.ofRealCLM.integrable_comp hf).mul_bdd
        ((hZ_adapt u).mono (ℱ.le u)).aestronglyMeasurable hZ_bd).const_mul k).integrableOn
    have hZ_sub : IntegrableOn (fun ω ↦ expProc X A α v ω - expProc X A α u ω) E P :=
      ((hZ_int v).sub (hZ_int u)).integrableOn
    have hlin1 := hmul (f := fun ω ↦ X v ω - X u ω)
      ((hX.integrable v).sub (hX.integrable u)) (I * (α : ℂ))
    have hlin2 := hmul (f := fun ω ↦ (X v ω - X u ω) ^ 2 - (A v ω - A u ω))
      (((memLp_increment_sq hX.stronglyAdapted hXR u v).integrable one_le_two).sub
        (integrable_increment_bracket hA_adapt hA_step' huv)) ((α ^ 2 / 2 : ℝ) : ℂ)
    have hdecomp (ω : Ω) : expProc X A α u ω * expRem α (X v ω - X u ω) (A v ω - A u ω) =
        (expProc X A α v ω - expProc X A α u ω) -
          (I * (α : ℂ)) * ((X v ω - X u ω) • expProc X A α u ω) +
          ((α ^ 2 / 2 : ℝ) : ℂ) *
            (((X v ω - X u ω) ^ 2 - (A v ω - A u ω)) • expProc X A α u ω) := by
      have : expProc X A α u ω * exp (I * α * ((X v ω - X u ω : ℝ) : ℂ) +
          ((α ^ 2 / 2 * (A v ω - A u ω) : ℝ) : ℂ)) = expProc X A α v ω := by
        dsimp only [expProc]; rw [← Complex.exp_add]; congr 1; push_cast; ring
      dsimp only [expRem]; rw [mul_sub, mul_sub, mul_one, this]
      simp only [Complex.real_smul]; push_cast; ring
    have hsub1 : IntegrableOn (fun ω ↦ (expProc X A α v ω - expProc X A α u ω) -
        (I * (α : ℂ)) * ((X v ω - X u ω) • expProc X A α u ω)) E P := hZ_sub.sub hlin1
    refine ⟨by simp_rw [hdecomp]; exact hsub1.add hlin2, ?_⟩
    simp_rw [hdecomp]
    rw [integral_add hsub1 hlin2, integral_sub hZ_sub hlin1, integral_const_mul, integral_const_mul,
      setIntegral_sub_smul_eq_zero hX huv (ℱ.mono hsu _ hE) (hZ_adapt u) hZ_bd,
      setIntegral_sq_sub_smul_eq_zero hX hQ hXR huv (ℱ.mono hsu _ hE) (hZ_adapt u) hZ_bd]; simp
  have hbd (m : ℕ) : ‖∫ ω in E, (expProc X A α t ω - expProc X A α s ω) ∂P‖ ≤
      Mz * K * (Real.sqrt B + L * Real.sqrt (P.real Set.univ)) *
        Real.sqrt (∫ ω, maxInc X s t m ω ^ 2 ∂P) +
      Mz * K * (L ^ 2 * P.real Set.univ) / (m + 1 : ℝ) := by
    let g := uniformGrid s t m
    let rem (k : ℕ) (ω : Ω) : ℂ := expProc X A α (g k) ω *
      expRem α (X (g (k + 1)) ω - X (g k) ω) (A (g (k + 1)) ω - A (g k) ω)
    let S (ω : Ω) : ℝ := ∑ k ∈ Finset.range (m + 1), (X (g (k + 1)) ω - X (g k) ω) ^ 2
    have hstepk (k : ℕ) :=
      hstep (uniformGrid_mono s t m (Nat.le_succ k)) (uniformGrid_mem_Icc hst m k).1
    have hD_memLp := memLp_maxInc hX.stronglyAdapted hXR s t m
    have hS_memLp : MemLp S 2 P :=
      memLp_finsetSum _ fun _ _ ↦ memLp_increment_sq hX.stronglyAdapted hXR _ _
    have hcs {f : Ω → ℝ} (hf : MemLp f 2 P) {M : ℝ} (hM : ∫ ω, f ω ^ 2 ∂P ≤ M) :
        ∫ ω, maxInc X s t m ω * f ω ∂P ≤
          Real.sqrt (∫ ω, maxInc X s t m ω ^ 2 ∂P) * Real.sqrt M := by
      rw [← Real.sqrt_mul (integral_nonneg fun _ ↦ sq_nonneg _)]
      exact Real.le_sqrt_of_sq_le <|
        (TauCeti.sq_integral_mul_le_integral_sq_mul_integral_sq hD_memLp hf).trans
          (mul_le_mul_of_nonneg_left hM (integral_nonneg fun _ ↦ sq_nonneg _))
    have hCS := hcs hS_memLp (by
      simpa only [S, g, B, L, uniformGrid_zero, uniformGrid_last hst] using
        integral_sq_sum_sq_le hc' hX hQ hXR hA_adapt hA_step' (uniformGrid_mono s t m) (m + 1))
    have hD1 : ∫ ω, maxInc X s t m ω ∂P ≤
        Real.sqrt (∫ ω, maxInc X s t m ω ^ 2 ∂P) * Real.sqrt (P.real Set.univ) := by
      simpa [integral_const, smul_eq_mul] using hcs (memLp_const (1 : ℝ)) (by simp)
    have hDS_int : Integrable (fun ω ↦ maxInc X s t m ω * S ω) P :=
      memLp_one_iff_integrable.1 (hD_memLp.mul hS_memLp)
    have hLD_int : Integrable (fun ω ↦ L * maxInc X s t m ω) P :=
      (hD_memLp.integrable one_le_two).const_mul L
    have h12_int : Integrable (fun ω ↦ maxInc X s t m ω * S ω + L * maxInc X s t m ω) P :=
      hDS_int.add hLD_int
    have hrhs_int : Integrable (fun ω ↦ Mz * K *
        (maxInc X s t m ω * S ω + L * maxInc X s t m ω + L ^ 2 / (m + 1 : ℝ))) P :=
      (h12_int.add (integrable_const _)).const_mul _
    rw [show ∫ ω in E, (expProc X A α t ω - expProc X A α s ω) ∂P =
        ∫ ω in E, (∑ k ∈ Finset.range (m + 1), rem k ω) ∂P by
      simp_rw [show ∀ ω, expProc X A α t ω - expProc X A α s ω =
          ∑ k ∈ Finset.range (m + 1), (expProc X A α (g (k + 1)) ω - expProc X A α (g k) ω) from
        fun ω ↦ by rw [Finset.sum_range_sub (fun k ↦ expProc X A α (g k) ω)]; dsimp only [g]
                   rw [uniformGrid_zero, uniformGrid_last hst]]
      rw [integral_finsetSum _ fun k _ ↦
            show IntegrableOn (fun ω ↦ expProc X A α (g (k + 1)) ω - expProc X A α (g k) ω) E P from
              ((hZ_int _).sub (hZ_int _)).integrableOn,
        integral_finsetSum _ fun k _ ↦ (hstepk k).1]
      exact Finset.sum_congr rfl fun k _ ↦ (hstepk k).2]
    refine ((norm_integral_le_integral_norm _).trans ((integral_mono_ae
      (integrable_finsetSum _ fun k _ ↦ (hstepk k).1).norm hrhs_int.integrableOn
      (ae_restrict_of_ae ?_)).trans (setIntegral_le_integral hrhs_int (ae_of_all P fun ω ↦ by
        have := maxInc_nonneg X s t m ω
        have : 0 ≤ S ω := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _; positivity)))).trans ?_
    · filter_upwards [ae_all_iff.2 fun k : ℕ ↦ ae_abs_increment_le hXR (g k) (g (k + 1)),
        ae_all_iff.2 fun k : Fin (m + 1) ↦ (hA_step' _ _ (uniformGrid_mono s t m
          (Nat.le_succ k.1))).mono fun ω hω ↦ by
            rw [uniformGrid_step hst m k.2] at hω
            exact And.intro hω.1 (show A (g (k.1 + 1)) ω - A (g k.1) ω ≤ L / (m + 1 : ℝ) by
              simpa only [L, mul_div_assoc] using hω.2),
        ae_all_iff.2 fun k : ℕ ↦ (ae_norm_expProc_le (X := X) hA0 hA_step' α (g k)).mono
          fun _ hω ↦ hω.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 (uniformGrid_mem_Icc hst m k).2) hc')
            (by positivity)))] with ω hXω hAω hZω
      have hmne : (m : ℝ) + 1 ≠ 0 := by positivity
      refine (norm_sum_le _ _).trans <| (Finset.sum_le_sum (g := fun k ↦ Mz * K *
          (maxInc X s t m ω * (X (g (k + 1)) ω - X (g k) ω) ^ 2 +
            maxInc X s t m ω * (L / (m + 1 : ℝ)) + (L / (m + 1 : ℝ)) ^ 2))
          fun k hk ↦ ?_).trans_eq ?_
      · have hk' := Finset.mem_range.1 hk
        have hrem := hK (D := maxInc X s t m ω) (hXω k)
          (Finset.le_sup' (f := fun j ↦ |X (g (j + 1)) ω - X (g j) ω|) hk) (hAω ⟨k, hk'⟩).1
          ((hAω ⟨k, hk'⟩).2.trans (div_le_self hL (by linarith [Nat.cast_nonneg (α := ℝ) m])))
        rw [norm_mul]
        refine (mul_le_mul (hZω k) hrem (norm_nonneg _) (Real.exp_pos _).le).trans ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by
          linarith [mul_le_mul_of_nonneg_left (hAω ⟨k, hk'⟩).2 (maxInc_nonneg X s t m ω),
            pow_le_pow_left₀ (hAω ⟨k, hk'⟩).1 (hAω ⟨k, hk'⟩).2 2]) hK0) (Real.exp_pos _).le
      · rw [← Finset.mul_sum]; congr 1
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ← Finset.mul_sum]
        push_cast; field_simp [hmne]; rfl
    · rw [integral_const_mul, integral_add h12_int (integrable_const _),
        integral_add hDS_int hLD_int, integral_const_mul, integral_const, smul_eq_mul]
      have hMrc : 0 ≤ Mz * K := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hD1 hL,
        show Mz * K * (P.real Set.univ * (L ^ 2 / (m + 1 : ℝ))) =
          Mz * K * (L ^ 2 * P.real Set.univ) / (m + 1 : ℝ) by ring]
  exact le_antisymm (ge_of_tendsto' (by
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero, mul_one_div, add_zero] using
      ((Real.continuous_sqrt.continuousAt.tendsto.comp
        (tendsto_integral_maxInc_sq hX.stronglyAdapted hcont hXR hst)).const_mul _).add
        ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul _)) hbd) (norm_nonneg _)

end MeasureTheory.Martingale
