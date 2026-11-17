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

private abbrev expProc (X A : ℝ≥0 → Ω → ℝ) (α : ℝ) (t : ℝ≥0) (ω : Ω) : ℂ :=
  exp (I * α * X t ω + ((α ^ 2 / 2 * A t ω : ℝ) : ℂ))

private def expRem (α x a : ℝ) : ℂ :=
  exp (I * α * x + ((α ^ 2 / 2 * a : ℝ) : ℂ)) - 1 -
    (I * α * x + ((α ^ 2 / 2 : ℝ) : ℂ) * ((a - x ^ 2 : ℝ) : ℂ))

private abbrev remTerm (X A : ℝ≥0 → Ω → ℝ) (α : ℝ) (u v : ℝ≥0) (ω : Ω) : ℂ :=
  expProc X A α u ω * expRem α (X v ω - X u ω) (A v ω - A u ω)

private def uniformGrid (s t : ℝ≥0) (m k : ℕ) : ℝ≥0 :=
  s + ((min k (m + 1) : ℕ) : ℝ≥0) / (m + 1 : ℝ≥0) * (t - s)

private def maxInc (X : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (m : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one fun k ↦
    |X (uniformGrid s t m (k + 1)) ω - X (uniformGrid s t m k) ω|

private lemma maxInc_nonneg (X : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (m : ℕ) (ω : Ω) : 0 ≤ maxInc X s t m ω :=
  (abs_nonneg _).trans (Finset.le_sup' (f := fun k ↦
    |X (uniformGrid s t m (k + 1)) ω - X (uniformGrid s t m k) ω|) (Finset.mem_range.2 m.succ_pos))

private lemma uniformGrid_zero (s t m) : uniformGrid s t m 0 = s := by simp [uniformGrid]
private lemma uniformGrid_last {s t} (hst : s ≤ t) (m) : uniformGrid s t m (m + 1) = t := by
  simp [uniformGrid, add_tsub_cancel_of_le hst]
private lemma uniformGrid_mono (s t m) : Monotone (uniformGrid s t m) :=
  fun _ _ h ↦ by dsimp only [uniformGrid]; gcongr

private lemma uniformGrid_step {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) {k : ℕ} (hk : k < m + 1) :
    (uniformGrid s t m (k + 1) : ℝ) - uniformGrid s t m k = ((t : ℝ) - s) / (m + 1) := by
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  simp only [uniformGrid, min_eq_left hk.le, min_eq_left (Nat.add_one_le_of_lt hk), NNReal.coe_add,
    NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_one, NNReal.coe_sub hst,
    Nat.cast_add, Nat.cast_one]; field_simp [hm]; ring

private lemma uniformGrid_mem_Icc {s t : ℝ≥0} (hst : s ≤ t) (m k : ℕ) :
    uniformGrid s t m k ∈ Set.Icc s t :=
  ⟨by simpa only [uniformGrid_zero] using uniformGrid_mono s t m (Nat.zero_le k), by
    simpa [uniformGrid] using
      (uniformGrid_mono s t m (min_le_right k (m + 1))).trans_eq (uniformGrid_last hst m)⟩

private lemma exists_norm_expRem_le (α R : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {D x a : ℝ}, |x| ≤ 2 * R → |x| ≤ D → 0 ≤ a → a ≤ L →
      ‖expRem α x a‖ ≤ K * (D * x ^ 2 + D * a + a ^ 2) := by
  let Ke := Real.exp (2 * |α| * R + α ^ 2 / 2 * L); let c₃ := |α| ^ 3 / 2; let c₄ := |α| ^ 4 / 8
  let c₁ := 4 * |α| ^ 3 * Ke; let c₂ := 4 * (α ^ 2 / 2) ^ 3 * L * Ke
  refine ⟨c₁ + c₂ + c₃ + c₄, by positivity, fun {D x a} hxR hxD ha0 haL ↦ ?_⟩
  -- Split `expRem α x a` into the cubic Taylor remainder and the higher terms of `w^2/2`.
  let w : ℂ := I * α * x + ((α ^ 2 / 2 * a : ℝ) : ℂ)
  have hw : ‖w‖ ≤ |α| * |x| + α ^ 2 / 2 * a := (norm_add_le _ _).trans_eq <| by simp [ha0]
  have hrem : ‖exp w - ∑ j ∈ Finset.range 3, w ^ j / j.factorial‖ ≤
      4 * (|α| ^ 3 * |x| ^ 3 + (α ^ 2 / 2) ^ 3 * a ^ 3) * Ke :=
    (Complex.norm_exp_sub_sum_le_norm_mul_exp w 3).trans <| (mul_le_mul
      (pow_le_pow_left₀ (norm_nonneg _) hw 3) (Real.exp_le_exp.2 (hw.trans (by
        nlinarith [abs_nonneg α, sq_nonneg α]))) (Real.exp_pos _).le (by positivity)).trans <|
      mul_le_mul_of_nonneg_right (by
        simp only [← mul_pow]; nlinarith [sq_nonneg (|α| * |x| - α ^ 2 / 2 * a),
          show 0 ≤ |α| * |x| by positivity, show 0 ≤ α ^ 2 / 2 * a by positivity]) (by positivity)
  have hmid : ‖I * ((α ^ 3 / 2 * x * a : ℝ) : ℂ) + ((α ^ 4 / 8 * a ^ 2 : ℝ) : ℂ)‖ ≤
      c₃ * |x| * a + c₄ * a ^ 2 := (norm_add_le _ _).trans_eq <| by simp [c₃, c₄, abs_of_nonneg ha0]
  rw [show expRem α x a = (exp w - ∑ j ∈ Finset.range 3, w ^ j / j.factorial) +
      (I * ((α ^ 3 / 2 * x * a : ℝ) : ℂ) + ((α ^ 4 / 8 * a ^ 2 : ℝ) : ℂ)) by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, expRem, w]
    push_cast; ring_nf; simp [I_sq]; ring]
  -- Absorb `|x|^3 ≤ D * x^2`, `|x| * a ≤ D * a`, and `a^3 ≤ L * a^2`.
  have hD0 : 0 ≤ D := (abs_nonneg x).trans hxD
  have hx3 : |x| ^ 3 ≤ D * x ^ 2 := by rw [pow_succ, sq_abs, mul_comm]; gcongr
  have ha3 : a ^ 3 ≤ L * a ^ 2 := by rw [pow_succ, mul_comm]; gcongr
  have h1 : 4 * (|α| ^ 3 * |x| ^ 3 + (α ^ 2 / 2) ^ 3 * a ^ 3) * Ke + (c₃ * |x| * a + c₄ * a ^ 2) ≤
      4 * (|α| ^ 3 * (D * x ^ 2) + (α ^ 2 / 2) ^ 3 * (L * a ^ 2)) * Ke +
        (c₃ * D * a + c₄ * a ^ 2) := by gcongr
  exact (norm_add_le _ _).trans <| (add_le_add hrem hmid).trans <| h1.trans <|
    sub_nonneg.1 ((show 0 ≤ (c₂ + c₃ + c₄) * (D * x ^ 2) + (c₁ + c₂ + c₄) * (D * a) +
      (c₁ + c₃) * a ^ 2 by positivity).trans_eq <| by dsimp only [c₁, c₂, c₃, c₄]; ring)

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω}

private lemma ae_abs_increment_le {X : ℝ≥0 → Ω → ℝ} {R : ℝ} (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R)
    (u v : ℝ≥0) : ∀ᵐ ω ∂P, |X v ω - X u ω| ≤ 2 * R :=
  (hXR v).mp <| (hXR u).mono fun _ hu hv ↦ (abs_sub _ _).trans (by linarith)

private lemma ae_maxInc_le {X : ℝ≥0 → Ω → ℝ} {R : ℝ} (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R)
    (s t : ℝ≥0) (m : ℕ) : ∀ᵐ ω ∂P, maxInc X s t m ω ≤ 2 * R :=
  (ae_all_iff.2 fun k : ℕ ↦ ae_abs_increment_le hXR (uniformGrid s t m k)
    (uniformGrid s t m (k + 1))).mono fun _ h ↦ Finset.sup'_le _ _ fun k _ ↦ h k

private lemma ae_norm_expProc_le {X A : ℝ≥0 → Ω → ℝ} {c : ℝ} (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    (α : ℝ) (u : ℝ≥0) : ∀ᵐ ω ∂P, ‖expProc X A α u ω‖ ≤ Real.exp (α ^ 2 / 2 * (c * (u : ℝ))) :=
  hA0.mp <| (hA_step 0 u bot_le).mono fun _ hA h0 ↦ by
    simpa [expProc, Complex.norm_exp, ← Complex.ofReal_pow] using Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left (a := α ^ 2 / 2) (by simpa [h0] using hA.2) (by positivity))

private lemma exists_ae_norm_sum_expRem_le {X A : ℝ≥0 → Ω → ℝ} {R c : ℝ}
    (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R) (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    (hc : 0 ≤ c) (α : ℝ) {s t : ℝ≥0} (hst : s ≤ t) :
    ∃ K ≥ 0, ∀ m : ℕ, ∀ᵐ ω ∂P, ‖∑ k ∈ Finset.range (m + 1),
        remTerm X A α (uniformGrid s t m k) (uniformGrid s t m (k + 1)) ω‖ ≤
      Real.exp (α ^ 2 / 2 * (c * (t : ℝ))) * K * (maxInc X s t m ω * (∑ k ∈ Finset.range (m + 1),
        (X (uniformGrid s t m (k + 1)) ω - X (uniformGrid s t m k) ω) ^ 2) +
          c * ((t : ℝ) - s) * maxInc X s t m ω + (c * ((t : ℝ) - s)) ^ 2 / (m + 1 : ℝ)) := by
  let L := c * ((t : ℝ) - s); let Mz := Real.exp (α ^ 2 / 2 * (c * (t : ℝ)))
  have hL : 0 ≤ L := mul_nonneg hc (sub_nonneg.2 (NNReal.coe_le_coe.2 hst))
  obtain ⟨K, hK0, hK⟩ := exists_norm_expRem_le α R hL; refine ⟨K, hK0, fun m ↦ ?_⟩
  let g := uniformGrid s t m
  filter_upwards [ae_all_iff.2 fun k : ℕ ↦ ae_abs_increment_le hXR (g k) (g (k + 1)),
      ae_all_iff.2 fun k : Fin (m + 1) ↦
        (hA_step _ _ (uniformGrid_mono s t m (Nat.le_succ k.1))).mono fun _ hω ↦ by
          rw [uniformGrid_step hst m k.2, ← mul_div_assoc] at hω; exact hω,
      ae_all_iff.2 fun k : ℕ ↦ (ae_norm_expProc_le (X := X) hA0 hA_step α (g k)).mono fun _ hω ↦
        hω.trans (Real.exp_le_exp.2 <| mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (NNReal.coe_le_coe.2 (uniformGrid_mem_Icc hst m k).2) hc) (by positivity))]
    with ω hXω hAω hZω
  let D := maxInc X s t m ω; have hD0 : 0 ≤ D := maxInc_nonneg X s t m ω
  have hMz : 0 ≤ Mz := (Real.exp_pos _).le; have hmne : (m : ℝ) + 1 ≠ 0 := by positivity
  refine (norm_sum_le _ _).trans <| (Finset.sum_le_sum (g := fun k ↦ Mz * K *
      (D * (X (g (k + 1)) ω - X (g k) ω) ^ 2 + D * (L / (m + 1 : ℝ)) + (L / (m + 1 : ℝ)) ^ 2))
      fun k hk ↦ ?_).trans_eq ?_
  · obtain ⟨h1, h2⟩ := hAω ⟨k, Finset.mem_range.1 hk⟩
    have hrem := hK (D := D) (hXω k)
      (Finset.le_sup' (f := fun j ↦ |X (g (j + 1)) ω - X (g j) ω|) hk) h1
      (h2.trans (div_le_self hL (by linarith [Nat.cast_nonneg (α := ℝ) m])))
    exact ((norm_mul _ _).trans_le (mul_le_mul (hZω k) hrem (norm_nonneg _) hMz)).trans
      (by rw [mul_assoc]; gcongr)
  · rw [← Finset.mul_sum]; congr 1; simp only [Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]; push_cast; field_simp [hmne]
    dsimp only [L, g, D]; ring

variable [IsFiniteMeasure P] {ℱ : Filtration ℝ≥0 mΩ}

private lemma setIntegral_sub_smul_eq_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ P) {s t : ℝ≥0} (hst : s ≤ t)
    {E : Set Ω} (hE : MeasurableSet[ℱ s] E) {Z : Ω → F} (hZ : StronglyMeasurable[ℱ s] Z)
    {C : ℝ} (hb : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ C) : ∫ ω in E, (M t ω - M s ω) • Z ω ∂P = 0 := by
  have hpull := condExp_stronglyMeasurable_bilin_of_bound (ContinuousLinearMap.lsmul ℝ ℝ).flip
    (ℱ.le s) (hZ.indicator hE) ((hM.integrable t).sub (hM.integrable s)) (max C 0)
    (hb.mono fun ω hω ↦ by by_cases h : ω ∈ E <;> simp [h, hω.trans (le_max_left C 0)])
  rw [← integral_indicator (ℱ.le s E hE), show E.indicator (fun ω ↦ (M t ω - M s ω) • Z ω) =
        fun ω ↦ (M t ω - M s ω) • E.indicator Z ω by ext ω; by_cases h : ω ∈ E <;> simp [h],
    ← integral_condExp (ℱ.le s), integral_congr_ae (g := fun _ ↦ (0 : F)) ?_, integral_zero]
  filter_upwards [hpull, condExp_sub (m := ℱ s) (hM.integrable t) (hM.integrable s),
    hM.condExp_ae_eq hst] with ω hp hd hm
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply, Pi.sub_apply] at *
  rw [hp, hd, hm, condExp_of_stronglyMeasurable (ℱ.le s) (hM.stronglyAdapted s) (hM.integrable s),
    sub_self, zero_smul]

private lemma setIntegral_sq_sub_smul_eq_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {X A : ℝ≥0 → Ω → ℝ} {R : ℝ} (hX : Martingale X ℱ P)
    (hQ : Martingale (fun u ω ↦ X u ω ^ 2 - A u ω) ℱ P) (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R)
    {s t : ℝ≥0} (hst : s ≤ t) {E : Set Ω} (hE : MeasurableSet[ℱ s] E)
    {Z : Ω → F} (hZ : StronglyMeasurable[ℱ s] Z) {C : ℝ} (hb : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ C) :
    ∫ ω in E, ((X t ω - X s ω) ^ 2 - (A t ω - A s ω)) • Z ω ∂P = 0 := by
  have hZ' : StronglyMeasurable[ℱ s] (fun ω ↦ (2 * X s ω) • Z ω) :=
    (stronglyMeasurable_const.mul (hX.stronglyAdapted s)).smul hZ
  have hb' : ∀ᵐ ω ∂P, ‖(2 * X s ω) • Z ω‖ ≤ 2 * max R 0 * max C 0 := (hXR s).mp <|
    hb.mono fun _ hC hR ↦ by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg zero_le_two]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hR.trans (le_max_left _ _)) zero_le_two)
        (hC.trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
  have hint {f : Ω → ℝ} {W : Ω → F} {D : ℝ} (hf : Integrable f P) (hW : StronglyMeasurable[ℱ s] W)
      (hWb : ∀ᵐ ω ∂P, ‖W ω‖ ≤ D) : IntegrableOn (fun ω ↦ f ω • W ω) E P :=
    ((hf.norm.const_mul (max D 0)).mono' (hf.aestronglyMeasurable.smul
      (hW.mono (ℱ.le s)).aestronglyMeasurable) (hWb.mono fun _ hω ↦ (norm_smul (f _) (W _)).trans_le
        (by rw [mul_comm]; gcongr; exact hω.trans (le_max_left _ _)))).integrableOn
  simp_rw [show ∀ ω, ((X t ω - X s ω) ^ 2 - (A t ω - A s ω)) • Z ω =
      ((X t ω ^ 2 - A t ω) - (X s ω ^ 2 - A s ω)) • Z ω - (X t ω - X s ω) • ((2 * X s ω) • Z ω)
    from fun _ ↦ by rw [smul_smul, ← sub_smul]; congr 1; ring]
  rw [integral_sub (hint (f := fun ω ↦ (X t ω ^ 2 - A t ω) - (X s ω ^ 2 - A s ω))
      ((hQ.integrable t).sub (hQ.integrable s)) hZ hb)
    (hint (f := fun ω ↦ X t ω - X s ω) ((hX.integrable t).sub (hX.integrable s)) hZ' hb'),
    setIntegral_sub_smul_eq_zero hQ hst hE hZ hb,
    setIntegral_sub_smul_eq_zero hX hst hE hZ' hb', sub_self]

private lemma memLp_increment_sq {X : ℝ≥0 → Ω → ℝ} {R : ℝ} (hX : StronglyAdapted ℱ X)
    (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R) (u v : ℝ≥0) : MemLp (fun ω ↦ (X v ω - X u ω) ^ 2) 2 P :=
  MemLp.of_bound ((((hX v).mono (ℱ.le v)).sub ((hX u).mono (ℱ.le u))).aestronglyMeasurable.pow 2)
    ((2 * R) ^ 2) ((ae_abs_increment_le hXR u v).mono fun _ hω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]; gcongr)

private lemma integrable_increment_bracket {A : ℝ≥0 → Ω → ℝ} {c : ℝ} (hA : StronglyAdapted ℱ A)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    {u v : ℝ≥0} (huv : u ≤ v) : Integrable (fun ω ↦ A v ω - A u ω) P :=
  (integrable_const (c * ((v : ℝ) - u))).mono'
    (((hA v).mono (ℱ.le v)).sub ((hA u).mono (ℱ.le u))).aestronglyMeasurable
    ((hA_step u v huv).mono fun _ hω ↦ by rw [Real.norm_eq_abs, abs_of_nonneg hω.1]; exact hω.2)

private lemma memLp_maxInc {X : ℝ≥0 → Ω → ℝ} {R : ℝ} (hX : StronglyAdapted ℱ X)
    (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R) (s t : ℝ≥0) (m : ℕ) : MemLp (maxInc X s t m) 2 P := by
  have hXm : ∀ u, Measurable (X u) := fun u ↦ ((hX u).mono (ℱ.le u)).measurable
  exact MemLp.of_bound (Finset.measurable_range_sup''
      (f := fun k ω ↦ |X (uniformGrid s t m (k + 1)) ω - X (uniformGrid s t m k) ω|)
      fun _ _ ↦ continuous_abs.measurable.comp ((hXm _).sub (hXm _))).aestronglyMeasurable
    (2 * R) ((ae_maxInc_le hXR s t m).mono fun ω hω ↦ by
      rwa [Real.norm_eq_abs, abs_of_nonneg (maxInc_nonneg X s t m ω)])

private lemma tendsto_integral_maxInc_sq {X : ℝ≥0 → Ω → ℝ} {R : ℝ} (hX : StronglyAdapted ℱ X)
    (hcont : ∀ᵐ ω ∂P, Continuous (X · ω)) (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R)
    {s t : ℝ≥0} (hst : s ≤ t) : Tendsto (fun m ↦ ∫ ω, maxInc X s t m ω ^ 2 ∂P) atTop (𝓝 0) := by
  have hD_lim : ∀ᵐ ω ∂P, Tendsto (fun m ↦ maxInc X s t m ω) atTop (𝓝 0) :=
    hcont.mono fun ω hω ↦ Metric.tendsto_atTop.2 fun ε hε ↦ by
      obtain ⟨δ, hδ, hδp⟩ := Metric.uniformContinuousOn_iff.1
        ((isCompact_Icc (a := s) (b := t)).uniformContinuousOn_of_continuous hω.continuousOn) ε hε
      obtain ⟨N, hN⟩ := (((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        ((t : ℝ) - s)).eventually (gt_mem_nhds (by simpa using hδ))).exists_forall_of_atTop
      exact ⟨N, fun m hm ↦ by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (maxInc_nonneg X s t m ω)]
        exact (Finset.sup'_lt_iff _).2 fun k hk ↦ by
          simpa [Real.dist_eq] using hδp _ (uniformGrid_mem_Icc hst m (k + 1)) _
            (uniformGrid_mem_Icc hst m k) (by
              rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2
                (uniformGrid_mono s t m (Nat.le_succ k)))),
                uniformGrid_step hst m (Finset.mem_range.1 hk)]
              simpa only [mul_one_div] using hN m hm)⟩
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (F := fun m ω ↦ maxInc X s t m ω ^ 2) (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ (2 * R) ^ 2)
    (fun m ↦ (memLp_maxInc hX hXR s t m).aestronglyMeasurable.pow 2) (integrable_const _)
    (fun m ↦ (ae_maxInc_le hXR s t m).mono fun ω h ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (maxInc_nonneg X s t m ω) h 2)
    (hD_lim.mono fun _ h ↦ by simpa using h.pow 2)

section PartitionEstimates

variable {X A : ℝ≥0 → Ω → ℝ} {R c : ℝ}
  (hX : Martingale X ℱ P) (hQ : Martingale (fun u ω ↦ X u ω ^ 2 - A u ω) ℱ P)
  (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R) (hA : StronglyAdapted ℱ A)
  (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))

include hX hQ hXR hA hA_step

private lemma integral_mul_increment_sq_le {u v : ℝ≥0} (huv : u ≤ v) {W : Ω → ℝ} {C : ℝ}
    (hW_sm : StronglyMeasurable[ℱ u] W) (hW_bd : ∀ᵐ ω ∂P, W ω ≤ C) (hW_nn : ∀ ω, 0 ≤ W ω) :
    ∫ ω, W ω * (X v ω - X u ω) ^ 2 ∂P ≤ c * ((v : ℝ) - u) * ∫ ω, W ω ∂P := by
  have hd := (memLp_increment_sq hX.stronglyAdapted hXR u v).integrable one_le_two
  have ha := integrable_increment_bracket (P := P) hA hA_step huv
  have hW_asm : AEStronglyMeasurable W P := (hW_sm.mono (ℱ.le _)).aestronglyMeasurable
  have hW_nbd : ∀ᵐ ω ∂P, ‖W ω‖ ≤ C :=
    hW_bd.mono fun ω h ↦ by rwa [Real.norm_eq_abs, abs_of_nonneg (hW_nn ω)]
  have h0 := setIntegral_sq_sub_smul_eq_zero (F := ℝ) hX hQ hXR huv MeasurableSet.univ hW_sm hW_nbd
  rw [Measure.restrict_univ, show (fun ω ↦ ((X v ω - X u ω) ^ 2 - (A v ω - A u ω)) • W ω) =
        fun ω ↦ W ω * (X v ω - X u ω) ^ 2 - W ω * (A v ω - A u ω) by ext; simp; ring,
    integral_sub (hd.bdd_mul hW_asm hW_nbd) (ha.bdd_mul hW_asm hW_nbd), sub_eq_zero] at h0
  rw [h0, ← integral_const_mul]
  exact integral_mono_ae (ha.bdd_mul hW_asm hW_nbd)
    (((integrable_const C).mono' hW_asm hW_nbd).const_mul _) ((hA_step u v huv).mono fun ω hω ↦ by
      dsimp only; rw [mul_comm (c * _)]; exact mul_le_mul_of_nonneg_left hω.2 (hW_nn ω))

private lemma integral_sq_sum_sq_le (hc : 0 ≤ c) {g : ℕ → ℝ≥0} (hg : Monotone g) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n, (X (g (k + 1)) ω - X (g k) ω) ^ 2) ^ 2 ∂P ≤
      (4 * R ^ 2 * (c * ((g n : ℝ) - g 0)) + 2 * (c * ((g n : ℝ) - g 0)) ^ 2) * P.real univ := by
  let L := c * ((g n : ℝ) - g 0)
  let d k ω := (X (g (k + 1)) ω - X (g k) ω) ^ 2; let Sk k ω := ∑ j ∈ Finset.range k, d j ω
  have hd_lp k := memLp_increment_sq hX.stronglyAdapted hXR (g k) (g (k + 1))
  have hd_bd k : ∀ᵐ ω ∂P, d k ω ≤ (2 * R) ^ 2 :=
    (ae_abs_increment_le hXR _ _).mono fun _ hω ↦ by dsimp only [d]; rw [← sq_abs]; gcongr
  have hd_le k : ∫ ω, d k ω ∂P ≤ c * ((g (k + 1) : ℝ) - g k) * P.real univ := by
    simpa [integral_const, mul_comm (P.real univ)] using integral_mul_increment_sq_le hX hQ hXR
      hA hA_step (hg (Nat.le_succ k)) (W := fun _ ↦ (1 : ℝ)) stronglyMeasurable_const (C := 1)
      (ae_of_all P fun _ ↦ le_rfl) (fun _ ↦ zero_le_one)
  -- Induct on `k ≤ n`, expanding `Sk (k + 1)^2 = Sk k^2 + 2 * Sk k * d k + d k^2`.
  suffices ∀ k ≤ n, ∫ ω, Sk k ω ^ 2 ∂P ≤
      ((2 * R) ^ 2 + 2 * L) * (c * ((g k : ℝ) - g 0)) * P.real univ from
    (this n le_rfl).trans_eq (by ring)
  intro k hk; induction k with | zero => simp [Sk] | succ k ih =>
    have hSk_lp : MemLp (Sk k) 2 P := memLp_finsetSum _ fun j _ ↦ hd_lp j
    have hSk_sm : StronglyMeasurable[ℱ (g k)] (Sk k) := Finset.stronglyMeasurable_fun_sum _
      fun _ hj ↦ (((hX.stronglyAdapted _).mono (ℱ.mono (hg (Finset.mem_range.1 hj)))).sub
        ((hX.stronglyAdapted _).mono (ℱ.mono (hg (Finset.mem_range.1 hj).le)))).pow 2
    have hcross : ∫ ω, Sk k ω * d k ω ∂P ≤ c * ((g (k + 1) : ℝ) - g k) * (L * P.real univ) :=
      (integral_mul_increment_sq_le hX hQ hXR hA hA_step (hg (Nat.le_succ k)) hSk_sm
        (C := (k : ℝ) * (2 * R) ^ 2) ((ae_all_iff.2 hd_bd).mono fun _ hω ↦
          (Finset.sum_le_sum fun j _ ↦ hω j).trans_eq (by simp))
        fun _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _).trans <| mul_le_mul_of_nonneg_left (by
          rw [integral_finsetSum _ fun j _ ↦ (hd_lp j).integrable one_le_two]
          refine (Finset.sum_le_sum fun j _ ↦ hd_le j).trans ?_
          rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_range_sub (fun i ↦ (g i : ℝ))]
          dsimp only [L]; have := NNReal.coe_le_coe.2 (hg (Nat.le_of_succ_le hk)); gcongr)
        (mul_nonneg hc (sub_nonneg.2 (NNReal.coe_le_coe.2 (hg (Nat.le_succ k)))))
    have hquart : ∫ ω, d k ω ^ 2 ∂P ≤ (2 * R) ^ 2 * (c * ((g (k + 1) : ℝ) - g k) * P.real univ) :=
      ((integral_mono_ae (hd_lp k).integrable_sq
        (((hd_lp k).integrable one_le_two).const_mul ((2 * R) ^ 2)) <|
        (hd_bd k).mono fun _ hω ↦ (by
          dsimp only; rw [sq]; exact mul_le_mul_of_nonneg_right hω (sq_nonneg _))).trans_eq
        (integral_const_mul _ _)).trans (by gcongr; exact hd_le k)
    simp_rw [show ∀ ω, Sk (k + 1) ω ^ 2 = Sk k ω ^ 2 + 2 * (Sk k ω * d k ω) + d k ω ^ 2 from
      fun ω ↦ by rw [show Sk (k + 1) ω = Sk k ω + d k ω from Finset.sum_range_succ _ k]; ring]
    rw [integral_add (f := fun ω ↦ Sk k ω ^ 2 + 2 * (Sk k ω * d k ω))
        (hSk_lp.integrable_sq.add ((hSk_lp.integrable_mul (hd_lp k)).const_mul 2))
        (hd_lp k).integrable_sq,
      integral_add (g := fun ω ↦ 2 * (Sk k ω * d k ω)) hSk_lp.integrable_sq
        ((hSk_lp.integrable_mul (hd_lp k)).const_mul 2),
      integral_const_mul]; linarith [ih (Nat.le_of_succ_le hk)]

private lemma setIntegral_expProc_step (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0) (α : ℝ)
    (hZ_adapt : StronglyAdapted ℱ (expProc X A α)) (hZ_int : ∀ u, Integrable (expProc X A α u) P)
    {s u v : ℝ≥0} (huv : u ≤ v) (hsu : s ≤ u) {E : Set Ω} (hE : MeasurableSet[ℱ s] E) :
    IntegrableOn (fun ω ↦ remTerm X A α u v ω) E P ∧
      ∫ ω in E, (expProc X A α v ω - expProc X A α u ω) ∂P = ∫ ω in E, remTerm X A α u v ω ∂P := by
  have hZ_bd := ae_norm_expProc_le (X := X) hA0 hA_step α u
  have hmul {f : Ω → ℝ} (hf : Integrable f P) (c₀ : ℂ) :
      IntegrableOn (fun ω ↦ c₀ * (f ω • expProc X A α u ω)) E P :=
    (((Complex.ofRealCLM.integrable_comp hf).mul_bdd
      ((hZ_adapt u).mono (ℱ.le u)).aestronglyMeasurable hZ_bd).const_mul c₀).integrableOn
  have hZs : IntegrableOn (fun ω ↦ expProc X A α v ω - expProc X A α u ω) E P :=
    ((hZ_int v).sub (hZ_int u)).integrableOn
  have h1 := hmul (f := fun ω ↦ X v ω - X u ω) ((hX.integrable v).sub (hX.integrable u)) (I * α)
  have h2 := hmul (f := fun ω ↦ (X v ω - X u ω) ^ 2 - (A v ω - A u ω))
    (((memLp_increment_sq hX.stronglyAdapted hXR u v).integrable one_le_two).sub
      (integrable_increment_bracket (P := P) hA hA_step huv)) ((α ^ 2 / 2 : ℝ) : ℂ)
  -- Split `remTerm u v` into `expProc v - expProc u` minus the martingale-increment terms.
  have hdec ω : remTerm X A α u v ω = (expProc X A α v ω - expProc X A α u ω) -
      (I * (α : ℂ)) * ((X v ω - X u ω) • expProc X A α u ω) +
      ((α ^ 2 / 2 : ℝ) : ℂ) * (((X v ω - X u ω) ^ 2 - (A v ω - A u ω)) • expProc X A α u ω) := by
    dsimp only [remTerm, expRem]; rw [mul_sub, mul_sub, mul_one, show expProc X A α u ω *
      exp (I * α * ((X v ω - X u ω : ℝ) : ℂ) + ((α ^ 2 / 2 * (A v ω - A u ω) : ℝ) : ℂ)) =
      expProc X A α v ω by rw [← Complex.exp_add]; congr 1; push_cast; ring]
    simp [Complex.real_smul]; ring
  have hZs1 : IntegrableOn (fun ω ↦ (expProc X A α v ω - expProc X A α u ω) -
      (I * (α : ℂ)) * ((X v ω - X u ω) • expProc X A α u ω)) E P := hZs.sub h1
  refine ⟨by simp_rw [hdec]; exact hZs1.add h2, ?_⟩; simp_rw [hdec]
  rw [integral_add hZs1 h2, integral_sub hZs h1, integral_const_mul, integral_const_mul,
    setIntegral_sub_smul_eq_zero hX huv (ℱ.mono hsu _ hE) (hZ_adapt u) hZ_bd,
    setIntegral_sq_sub_smul_eq_zero hX hQ hXR huv (ℱ.mono hsu _ hE) (hZ_adapt u) hZ_bd]; simp

private lemma integral_maxInc_remBound_le (hc : 0 ≤ c) {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) :
    let L := c * ((t : ℝ) - s)
    let f ω := maxInc X s t m ω * (∑ k ∈ Finset.range (m + 1),
      (X (uniformGrid s t m (k + 1)) ω - X (uniformGrid s t m k) ω) ^ 2) +
        L * maxInc X s t m ω + L ^ 2 / (m + 1 : ℝ)
    Integrable f P ∧ ∫ ω, f ω ∂P ≤
      (Real.sqrt ((4 * R ^ 2 * L + 2 * L ^ 2) * P.real univ) + L * Real.sqrt (P.real univ)) *
        Real.sqrt (∫ ω, maxInc X s t m ω ^ 2 ∂P) + L ^ 2 * P.real univ / (m + 1 : ℝ) := by
  intro L f; let g := uniformGrid s t m; let D := maxInc X s t m
  let S ω := ∑ k ∈ Finset.range (m + 1), (X (g (k + 1)) ω - X (g k) ω) ^ 2
  have hL : 0 ≤ L := mul_nonneg hc (sub_nonneg.2 (NNReal.coe_le_coe.2 hst))
  have hD_lp := memLp_maxInc hX.stronglyAdapted hXR s t m
  have hS_lp : MemLp S 2 P :=
    memLp_finsetSum _ fun _ _ ↦ memLp_increment_sq hX.stronglyAdapted hXR _ _
  have hcs {h : Ω → ℝ} (hh : MemLp h 2 P) {M : ℝ} (hM : ∫ ω, h ω ^ 2 ∂P ≤ M) :
      ∫ ω, D ω * h ω ∂P ≤ Real.sqrt (∫ ω, D ω ^ 2 ∂P) * Real.sqrt M :=
    (Real.sqrt_mul (integral_nonneg fun _ ↦ sq_nonneg _) _).symm ▸ Real.le_sqrt_of_sq_le
      ((TauCeti.sq_integral_mul_le_integral_sq_mul_integral_sq hD_lp hh).trans
        (mul_le_mul_of_nonneg_left hM (integral_nonneg fun _ ↦ sq_nonneg _)))
  have hCS := hcs hS_lp <| by
    simpa only [S, g, L, uniformGrid_zero, uniformGrid_last hst] using
      integral_sq_sum_sq_le hX hQ hXR hA hA_step hc (uniformGrid_mono s t m) (m + 1)
  have hD1 : ∫ ω, D ω ∂P ≤ Real.sqrt (∫ ω, D ω ^ 2 ∂P) * Real.sqrt (P.real univ) := by
    simpa [integral_const, smul_eq_mul] using hcs (memLp_const (1 : ℝ)) (by simp)
  have hDS := hD_lp.integrable_mul hS_lp; have hLD := (hD_lp.integrable one_le_two).const_mul L
  refine ⟨(hDS.add hLD).add (integrable_const _), ?_⟩
  rw [show ∫ ω, f ω ∂P = ∫ ω, (D ω * S ω + L * D ω) ∂P + ∫ _, L ^ 2 / (m + 1 : ℝ) ∂P from
      integral_add (f := fun ω ↦ D ω * S ω + L * D ω) (hDS.add hLD) (integrable_const _),
    integral_add (f := fun ω ↦ D ω * S ω) hDS hLD, integral_const_mul, integral_const, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left hD1 hL,
    show P.real univ * (L ^ 2 / (m + 1 : ℝ)) = L ^ 2 * P.real univ / (m + 1 : ℝ) by ring]

private lemma exists_norm_setIntegral_expProc_sub_le (hc : 0 ≤ c) (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0)
    (α : ℝ) (hZ_adapt : StronglyAdapted ℱ (expProc X A α))
    (hZ_int : ∀ u, Integrable (expProc X A α u) P) {s t : ℝ≥0} (hst : s ≤ t)
    {E : Set Ω} (hE : MeasurableSet[ℱ s] E) :
    ∃ C₁ C₂ : ℝ, ∀ m : ℕ, ‖∫ ω in E, (expProc X A α t ω - expProc X A α s ω) ∂P‖ ≤
      C₁ * Real.sqrt (∫ ω, maxInc X s t m ω ^ 2 ∂P) + C₂ / (m + 1 : ℝ) := by
  let L := c * ((t : ℝ) - s); let Mz := Real.exp (α ^ 2 / 2 * (c * (t : ℝ)))
  obtain ⟨K, hK0, hK⟩ := exists_ae_norm_sum_expRem_le hXR hA0 hA_step hc α hst
  refine ⟨Mz * K * (Real.sqrt ((4 * R ^ 2 * L + 2 * L ^ 2) * P.real univ) +
      L * Real.sqrt (P.real univ)), Mz * K * (L ^ 2 * P.real univ), fun m ↦ ?_⟩
  let g := uniformGrid s t m
  -- Telescope `expProc t - expProc s` into `remTerm` sums, then apply the L² remainder bound.
  have hstepk k := setIntegral_expProc_step hX hQ hXR hA hA_step hA0 α hZ_adapt hZ_int
    (uniformGrid_mono s t m (Nat.le_succ k)) (uniformGrid_mem_Icc hst m k).1 hE
  obtain ⟨hf_int, hf_le⟩ := integral_maxInc_remBound_le hX hQ hXR hA hA_step hc hst m
  have hL : 0 ≤ L := mul_nonneg hc (sub_nonneg.2 (NNReal.coe_le_coe.2 hst))
  rw [show ∫ ω in E, (expProc X A α t ω - expProc X A α s ω) ∂P =
      ∫ ω in E, ∑ k ∈ Finset.range (m + 1), remTerm X A α (g k) (g (k + 1)) ω ∂P by
    rw [integral_finsetSum _ fun k _ ↦ (hstepk k).1, ← Finset.sum_congr rfl fun k _ ↦ (hstepk k).2,
      ← integral_finsetSum (f := fun k ω ↦ expProc X A α (g (k + 1)) ω - expProc X A α (g k) ω) _
        fun _ _ ↦ ((hZ_int _).sub (hZ_int _)).integrableOn]
    congr 1; ext ω; rw [Finset.sum_range_sub (fun k ↦ expProc X A α (g k) ω)]
    simp [g, uniformGrid_zero, uniformGrid_last hst]]
  refine ((norm_integral_le_integral_norm _).trans ((integral_mono_ae
    (integrable_finsetSum _ fun k _ ↦ (hstepk k).1).norm (hf_int.const_mul (Mz * K)).integrableOn
    (ae_restrict_of_ae (hK m))).trans (setIntegral_le_integral (hf_int.const_mul (Mz * K))
      (ae_of_all P fun ω ↦ by
        have := maxInc_nonneg X s t m ω
        have : 0 ≤ ∑ k ∈ Finset.range (m + 1), (X (g (k + 1)) ω - X (g k) ω) ^ 2 :=
          Finset.sum_nonneg fun _ _ ↦ sq_nonneg _; positivity)))).trans ?_
  rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left hf_le (by positivity)).trans_eq (by ring)

end PartitionEstimates

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
  -- Replace `c` by `max c 0` for a nonnegative Lipschitz bound and pass `m → ∞` on uniform grids.
  have hA_step' u v (huv : u ≤ v) := (hA_step u v huv).mono fun _ hω ↦ And.intro hω.1 <| hω.2.trans
    (mul_le_mul_of_nonneg_right (le_max_left c 0) (sub_nonneg.2 (NNReal.coe_le_coe.2 huv)))
  have hZ_adapt : StronglyAdapted ℱ (expProc X A α) := fun u ↦
    Complex.continuous_exp.comp_stronglyMeasurable <| (stronglyMeasurable_const.mul <|
      Complex.continuous_ofReal.comp_stronglyMeasurable (hX.stronglyAdapted u)).add <|
      Complex.continuous_ofReal.comp_stronglyMeasurable (stronglyMeasurable_const.mul (hA_adapt u))
  have hZ_int u : Integrable (expProc X A α u) P := (integrable_const _).mono'
    ((hZ_adapt u).mono (ℱ.le u)).aestronglyMeasurable (ae_norm_expProc_le (X := X) hA0 hA_step' α u)
  rw [hZ_adapt.martingale_iff_setIntegral_eq hZ_int]; intro s t hst E hE
  rw [eq_comm, ← sub_eq_zero, ← integral_sub (hZ_int t).integrableOn (hZ_int s).integrableOn,
    ← norm_eq_zero]
  obtain ⟨C₁, C₂, hbd⟩ := exists_norm_setIntegral_expProc_sub_le hX hQ hXR hA_adapt hA_step'
    (le_max_right c 0) hA0 α hZ_adapt hZ_int hst hE
  exact le_antisymm (ge_of_tendsto' (by
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero, mul_one_div, add_zero] using
      ((Real.continuous_sqrt.continuousAt.tendsto.comp
        (tendsto_integral_maxInc_sq hX.stronglyAdapted hcont hXR hst)).const_mul C₁).add
        ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C₂)) hbd) (norm_nonneg _)

end MeasureTheory.Martingale
