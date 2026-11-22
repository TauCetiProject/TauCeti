/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import TauCeti.Probability.Process.QuadraticVariation
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.Probability.Martingale.Basic

/-!
# Discrete quadratic-variation estimates for real martingales

Provides set-integral and second-moment bounds for the discrete quadratic sum
`TauCeti.Probability.quadraticSum Y g` along finite nondecreasing time grids:

* `MeasureTheory.Martingale.setIntegral_sq_sub_eq_quadraticSum`: over any event in `ℱ s`, the
  set integral of `Y t ^ 2 - Y s ^ 2` for an `L²` real martingale equals that of its discrete
  quadratic sum along any nondecreasing finite grid from `s` to `t`.
* `MeasureTheory.Martingale.integral_mul_increment_sq_le`: a nonnegative bounded `ℱ u`-measurable
  weight multiplied by `(Y v - Y u) ^ 2` has expectation bounded by `c * (v - u) * E[W]` when
  `Y ^ 2 - A` is a martingale and `A` has `c`-Lipschitz increments.
* `MeasureTheory.Martingale.integral_quadraticSum_sq_le`: a bounded continuous-bracket real
  martingale satisfies an `L²` bound on `quadraticSum Y g` depending only on the uniform bound on
  `Y` and the Lipschitz bracket increment `c * (g (Fin.last n) - g 0)`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability
open scoped NNReal

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}

/-- Over any event `E ∈ ℱ s`, the set integral of `Y t ^ 2 - Y s ^ 2` for a real martingale `Y`
with square-integrable values on the grid `g` equals the set integral of `quadraticSum Y g`. -/
theorem setIntegral_sq_sub_eq_quadraticSum [SigmaFiniteFiltration μ ℱ] {Y : ℝ≥0 → Ω → ℝ}
    (hY : Martingale Y ℱ μ) {s t : ℝ≥0} {E : Set Ω} (hE : MeasurableSet[ℱ s] E)
    {n : ℕ} {g : Fin (n + 1) → ℝ≥0} (hg : Monotone g) (hg0 : g 0 = s) (hgl : g (Fin.last n) = t)
    (hmem : ∀ k, MemLp (Y (g k)) 2 μ) :
    ∫ ω in E, (Y t ω ^ 2 - Y s ω ^ 2) ∂μ = ∫ ω in E, quadraticSum Y g ω ∂μ := by
  have hI2 (k : Fin (n + 1)) : IntegrableOn (fun ω ↦ Y (g k) ω ^ 2) E μ :=
    (hmem k).integrable_sq.integrableOn
  have hinc_int (i : Fin n) :
      Integrable (fun ω ↦ (Y (g i.succ) ω - Y (g i.castSucc) ω) ^ 2) μ := by
    simpa only [Pi.sub_apply] using ((hmem i.succ).sub (hmem i.castSucc)).integrable_sq
  have hstep (i : Fin n) :
      ∫ ω in E, (Y (g i.succ) ω ^ 2 - Y (g i.castSucc) ω ^ 2) ∂μ =
        ∫ ω in E, (Y (g i.succ) ω - Y (g i.castSucc) ω) ^ 2 ∂μ := by
    have hEu : MeasurableSet[ℱ (g i.castSucc)] E := ℱ.mono (hg0 ▸ hg (Fin.zero_le _)) E hE
    have h1 := setIntegral_congr_ae (ℱ.le _ E hEu)
      ((hY.condExp_sq (hg (Fin.castSucc_le_succ i)) (hmem i.succ)).mono fun _ hω _ ↦ hω)
    rw [setIntegral_condExp (ℱ.le _) (hmem i.succ).integrable_sq hEu,
      integral_add (hI2 i.castSucc) integrable_condExp.integrableOn,
      setIntegral_condExp (ℱ.le _) (hinc_int i) hEu] at h1
    rw [integral_sub (hI2 i.succ) (hI2 i.castSucc)]
    linarith
  have hsub_int (i : Fin n) :
      IntegrableOn (fun ω ↦ Y (g i.succ) ω ^ 2 - Y (g i.castSucc) ω ^ 2) E μ :=
    (hI2 i.succ).sub (hI2 i.castSucc)
  rw [quadraticSum_def, integral_finsetSum _ fun i _ ↦ (hinc_int i).integrableOn,
    ← Finset.sum_congr rfl fun i _ ↦ hstep i,
    ← integral_finsetSum Finset.univ
      (f := fun (i : Fin n) ω ↦ Y (g i.succ) ω ^ 2 - Y (g i.castSucc) ω ^ 2)
      fun i _ ↦ hsub_int i]
  congr 1; ext ω
  rw [Fin.sum_univ_succ_sub_castSucc (fun i ↦ Y (g i) ω ^ 2), hg0, hgl]

private lemma integrableOn_mul_of_bound {f W : Ω → ℝ} {S : Set Ω} {C : ℝ}
    (hf : Integrable f μ) (hW : AEStronglyMeasurable W μ) (hb : ∀ᵐ ω ∂μ, ‖W ω‖ ≤ C) :
    IntegrableOn (fun ω ↦ f ω * W ω) S μ := by
  have heq : (fun ω ↦ f ω * W ω) = fun ω ↦ W ω * f ω := funext fun ω ↦ mul_comm _ _
  rw [heq]
  exact (hf.bdd_mul hW hb).integrableOn

/-- For a real `L²` martingale `Y` whose compensated square `Y ^ 2 - A` is a martingale with
`c`-Lipschitz increments `A v - A u ≤ c * (v - u)`, multiplying `(Y v - Y u) ^ 2` by any bounded
nonnegative `ℱ u`-measurable weight `W` yields expectation at most `c * (v - u) * ∫ W ∂μ`. -/
theorem integral_mul_increment_sq_le [IsFiniteMeasure μ] {Y A : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hY : Martingale Y ℱ μ) (hQ : Martingale (fun u ω ↦ Y u ω ^ 2 - A u ω) ℱ μ)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂μ, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    {u v : ℝ≥0} (huv : u ≤ v) (hYu : MemLp (Y u) 2 μ) (hYv : MemLp (Y v) 2 μ)
    {W : Ω → ℝ} {C : ℝ} (hW_sm : StronglyMeasurable[ℱ u] W)
    (hW_bd : ∀ᵐ ω ∂μ, W ω ≤ C) (hW_nn : ∀ ω, 0 ≤ W ω) :
    ∫ ω, W ω * (Y v ω - Y u ω) ^ 2 ∂μ ≤ c * ((v : ℝ) - u) * ∫ ω, W ω ∂μ := by
  have hA : StronglyAdapted ℱ A := fun w ↦ by
    convert ((hY.stronglyAdapted w).pow 2).sub (hQ.stronglyAdapted w); ext ω; simp
  have hd : Integrable (fun ω ↦ (Y v ω - Y u ω) ^ 2) μ := by
    simpa only [Pi.sub_apply] using (hYv.sub hYu).integrable_sq
  have ha : Integrable (fun ω ↦ A v ω - A u ω) μ := hA.integrable_sub_of_nonneg_le (hA_step u v huv)
  have hW_asm : AEStronglyMeasurable W μ := (hW_sm.mono (ℱ.le _)).aestronglyMeasurable
  have hW_nbd : ∀ᵐ ω ∂μ, ‖W ω‖ ≤ C :=
    hW_bd.mono fun ω h ↦ by rwa [Real.norm_eq_abs, abs_of_nonneg (hW_nn ω)]
  have h0 := hY.setIntegral_sq_sub_smul_eq_zero hQ huv MeasurableSet.univ hW_sm.aestronglyMeasurable
    (integrableOn_mul_of_bound ((hQ.integrable v).sub (hQ.integrable u)) hW_asm hW_nbd)
    (by
      have hmul : Integrable (fun ω ↦ (Y v ω - Y u ω) * Y u ω) μ := by
        convert (hYv.sub hYu).integrable_mul hYu
      simpa only [smul_eq_mul, mul_assoc] using integrableOn_mul_of_bound hmul hW_asm hW_nbd)
  have hmul_eq (ω : Ω) :
      ((Y v ω - Y u ω) ^ 2 - (A v ω - A u ω)) • W ω =
        W ω * (Y v ω - Y u ω) ^ 2 - W ω * (A v ω - A u ω) := by
    simp only [smul_eq_mul]; ring
  simp_rw [Measure.restrict_univ, hmul_eq] at h0
  rw [integral_sub (hd.bdd_mul hW_asm hW_nbd) (ha.bdd_mul hW_asm hW_nbd), sub_eq_zero] at h0
  rw [h0, ← integral_const_mul]
  exact integral_mono_ae (ha.bdd_mul hW_asm hW_nbd)
    (((integrable_const C).mono' hW_asm hW_nbd).const_mul _) ((hA_step u v huv).mono fun ω hω ↦ by
      dsimp only
      rw [mul_comm (c * _)]
      exact mul_le_mul_of_nonneg_left hω.2 (hW_nn ω))

private lemma stronglyMeasurable_quadraticSum {Y : ℝ≥0 → Ω → ℝ}
    (hY : StronglyAdapted ℱ Y) {n : ℕ} {g : Fin (n + 1) → ℝ≥0} (hg : Monotone g) :
    StronglyMeasurable[ℱ (g (Fin.last n))] (quadraticSum Y g) := by
  rw [quadraticSum_def]
  exact Finset.stronglyMeasurable_fun_sum _ fun j _ ↦
    (((hY (g j.succ)).mono (ℱ.mono (hg (Fin.le_last _)))).sub
      ((hY (g j.castSucc)).mono (ℱ.mono (hg (Fin.le_last _))))).pow 2

private lemma integral_quadraticSum_le [IsFiniteMeasure μ] {Y A : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hY : Martingale Y ℱ μ) (hQ : Martingale (fun u ω ↦ Y u ω ^ 2 - A u ω) ℱ μ)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂μ, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    {n : ℕ} {g : Fin (n + 1) → ℝ≥0} (hg : Monotone g) (hmem : ∀ k, MemLp (Y (g k)) 2 μ) :
    ∫ ω, quadraticSum Y g ω ∂μ ≤ c * ((g (Fin.last n) : ℝ) - g 0) * μ.real Set.univ := by
  have hd_le (i : Fin n) :
      ∫ ω, (Y (g i.succ) ω - Y (g i.castSucc) ω) ^ 2 ∂μ ≤
        c * ((g i.succ : ℝ) - g i.castSucc) * μ.real Set.univ := by
    simpa [integral_const, mul_comm (μ.real Set.univ)] using
      hY.integral_mul_increment_sq_le hQ hA_step (hg (Fin.castSucc_le_succ i))
        (hmem i.castSucc) (hmem i.succ) (W := fun _ ↦ (1 : ℝ))
        stronglyMeasurable_const (C := 1) (ae_of_all μ fun _ ↦ le_rfl) (fun _ ↦ zero_le_one)
  rw [quadraticSum_def, integral_finsetSum _ fun j _ ↦ by
    simpa only [Pi.sub_apply] using ((hmem j.succ).sub (hmem j.castSucc)).integrable_sq]
  refine (Finset.sum_le_sum fun j _ ↦ hd_le j).trans_eq ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum, Fin.sum_univ_succ_sub_castSucc (fun k ↦ (g k : ℝ))]

/-- Second-moment bound for the discrete quadratic sum of a uniformly bounded real martingale `Y`
along a nondecreasing finite grid `g : Fin (n + 1) → ℝ≥0`, when `Y ^ 2 - A` is a martingale and
`A` has nonnegative `c`-Lipschitz increments (`0 ≤ c`). -/
theorem integral_quadraticSum_sq_le [IsFiniteMeasure μ] {Y A : ℝ≥0 → Ω → ℝ} {R c : ℝ}
    (hY : Martingale Y ℱ μ) (hQ : Martingale (fun u ω ↦ Y u ω ^ 2 - A u ω) ℱ μ)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂μ, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    (hc : 0 ≤ c) {n : ℕ} {g : Fin (n + 1) → ℝ≥0} (hg : Monotone g)
    (hYR : ∀ k, ∀ᵐ ω ∂μ, |Y (g k) ω| ≤ R) :
    ∫ ω, quadraticSum Y g ω ^ 2 ∂μ ≤
      (4 * R ^ 2 * (c * ((g (Fin.last n) : ℝ) - g 0)) +
        2 * (c * ((g (Fin.last n) : ℝ) - g 0)) ^ 2) * μ.real Set.univ := by
  induction n with
  | zero =>
    simp [quadraticSum_zero, Fin.last_zero]
  | succ n ih =>
    let g' : Fin (n + 1) → ℝ≥0 := g ∘ Fin.castSucc
    have hg' : Monotone g' := fun _ _ hij ↦ hg (Fin.castSucc_le_castSucc_iff.mpr hij)
    have hYR' : ∀ k, ∀ᵐ ω ∂μ, |Y (g' k) ω| ≤ R := fun k ↦ hYR k.castSucc
    have ih' := ih hg' hYR'
    have hmem (k : Fin (n + 2)) : MemLp (Y (g k)) 2 μ :=
      MemLp.of_bound ((hY.stronglyAdapted (g k)).mono (ℱ.le _)).aestronglyMeasurable R
        ((hYR k).mono fun _ hω ↦ by rwa [Real.norm_eq_abs])
    let d (ω : Ω) : ℝ := (Y (g (Fin.last (n + 1))) ω - Y (g (Fin.last n).castSucc) ω) ^ 2
    have hd_bd : ∀ᵐ ω ∂μ, d ω ≤ (2 * R) ^ 2 :=
      ae_sq_sub_le (hYR (Fin.last (n + 1))) (hYR (Fin.last n).castSucc)
    have hd_lp : MemLp d 2 μ :=
      memLp_sub_sq_of_bound 2 (hmem (Fin.last (n + 1))).aestronglyMeasurable
        (hmem (Fin.last n).castSucc).aestronglyMeasurable
        (hYR (Fin.last (n + 1))) (hYR (Fin.last n).castSucc)
    have hS'_lp : MemLp (quadraticSum Y g') 2 μ :=
      memLp_quadraticSum_of_bound 2 g' (fun k ↦ (hmem k.castSucc).aestronglyMeasurable) hYR'
    have hstep_le : (g (Fin.last n).castSucc : ℝ≥0) ≤ g (Fin.last (n + 1)) := by
      simpa [Fin.succ_last] using hg (Fin.castSucc_le_succ (Fin.last n))
    have hcross : ∫ ω, quadraticSum Y g' ω * d ω ∂μ ≤
        c * ((g (Fin.last (n + 1)) : ℝ) - g (Fin.last n).castSucc) *
          (c * ((g (Fin.last n).castSucc : ℝ) - g 0) * μ.real Set.univ) := by
      refine (hY.integral_mul_increment_sq_le hQ hA_step hstep_le
        (hmem (Fin.last n).castSucc) (hmem (Fin.last (n + 1)))
        (stronglyMeasurable_quadraticSum hY.stronglyAdapted hg')
        (ae_quadraticSum_le_of_bound g' hYR') (fun _ ↦ quadraticSum_nonneg Y g' _)).trans ?_
      exact mul_le_mul_of_nonneg_left
        (by simpa only [g', Function.comp_apply, Fin.castSucc_zero] using
          integral_quadraticSum_le hY hQ hA_step hg' fun k ↦ hmem k.castSucc)
        (mul_nonneg hc (sub_nonneg.2 (NNReal.coe_le_coe.2 hstep_le)))
    have hquart : ∫ ω, d ω ^ 2 ∂μ ≤
        (2 * R) ^ 2 * (c * ((g (Fin.last (n + 1)) : ℝ) - g (Fin.last n).castSucc) *
          μ.real Set.univ) := by
      have hd_last : ∫ ω, d ω ∂μ ≤
          c * ((g (Fin.last (n + 1)) : ℝ) - g (Fin.last n).castSucc) * μ.real Set.univ := by
        simpa [d, integral_const, mul_comm (μ.real Set.univ)] using
          hY.integral_mul_increment_sq_le hQ hA_step hstep_le
            (hmem (Fin.last n).castSucc) (hmem (Fin.last (n + 1)))
            (W := fun _ ↦ (1 : ℝ)) stronglyMeasurable_const (C := 1)
            (ae_of_all μ fun _ ↦ le_rfl) (fun _ ↦ zero_le_one)
      refine ((integral_mono_ae hd_lp.integrable_sq
        ((hd_lp.integrable one_le_two).const_mul ((2 * R) ^ 2)) (hd_bd.mono fun _ hω ↦ by
          dsimp only; rw [sq]; exact mul_le_mul_of_nonneg_right hω (sq_nonneg _))).trans_eq
        (integral_const_mul _ _)).trans ?_
      gcongr
    have hS_sq (ω : Ω) : quadraticSum Y g ω ^ 2 =
        quadraticSum Y g' ω ^ 2 + 2 * (quadraticSum Y g' ω * d ω) + d ω ^ 2 := by
      have hS_succ : quadraticSum Y g ω = quadraticSum Y g' ω + d ω := by
        simp only [quadraticSum_def, g', d, Fin.sum_univ_castSucc, Fin.succ_last]; rfl
      rw [hS_succ]; ring
    simp_rw [hS_sq]
    rw [integral_add (f := fun ω ↦ quadraticSum Y g' ω ^ 2 + 2 * (quadraticSum Y g' ω * d ω))
        (hS'_lp.integrable_sq.add ((hS'_lp.integrable_mul hd_lp).const_mul 2))
        hd_lp.integrable_sq,
      integral_add (g := fun ω ↦ 2 * (quadraticSum Y g' ω * d ω)) hS'_lp.integrable_sq
        ((hS'_lp.integrable_mul hd_lp).const_mul 2),
      integral_const_mul]
    simp only [g', Function.comp_apply, Fin.castSucc_zero] at ih'
    have hL0 : 0 ≤ c * ((g (Fin.last n).castSucc : ℝ) - g 0) :=
      mul_nonneg hc (sub_nonneg.2 (NNReal.coe_le_coe.2 (hg (Fin.zero_le _))))
    have hδ0 : 0 ≤ c * ((g (Fin.last (n + 1)) : ℝ) - g (Fin.last n).castSucc) :=
      mul_nonneg hc (sub_nonneg.2 (NNReal.coe_le_coe.2 hstep_le))
    have hsplit : (g (Fin.last (n + 1)) : ℝ) - g 0 =
        ((g (Fin.last n).castSucc : ℝ) - g 0) +
          ((g (Fin.last (n + 1)) : ℝ) - g (Fin.last n).castSucc) := by ring
    have hμ0 : 0 ≤ μ.real Set.univ := ENNReal.toReal_nonneg
    have h4R : (2 * R) ^ 2 = 4 * R ^ 2 := by ring
    rw [h4R] at hquart
    nlinarith [ih', hcross, hquart, hsplit, mul_nonneg (mul_nonneg hL0 hδ0) hμ0,
      mul_nonneg (sq_nonneg (c * ((g (Fin.last (n + 1)) : ℝ) - g (Fin.last n).castSucc))) hμ0]

end MeasureTheory.Martingale
