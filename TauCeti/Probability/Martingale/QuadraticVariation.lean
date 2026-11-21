/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import TauCeti.Probability.Process.QuadraticVariation
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
  rw [Finset.sum_sub_distrib]
  linarith [Fin.sum_univ_succ (fun i ↦ Y (g i) ω ^ 2),
    Fin.sum_univ_castSucc (fun i ↦ Y (g i) ω ^ 2),
    congrArg (fun u ↦ Y u ω ^ 2) hg0, congrArg (fun u ↦ Y u ω ^ 2) hgl]

private lemma integrableOn_mul_of_bound {f W : Ω → ℝ} {S : Set Ω} {C : ℝ}
    (hf : Integrable f μ) (hW : AEStronglyMeasurable W μ) (hb : ∀ᵐ ω ∂μ, ‖W ω‖ ≤ C) :
    IntegrableOn (fun ω ↦ f ω * W ω) S μ := by
  have heq : (fun ω ↦ f ω * W ω) = fun ω ↦ W ω * f ω := funext fun ω ↦ mul_comm _ _
  rw [heq]
  exact (hf.bdd_mul hW hb).integrableOn

private lemma integrable_increment_bracket [IsFiniteMeasure μ] {A : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hA : StronglyAdapted ℱ A)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂μ, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    {u v : ℝ≥0} (huv : u ≤ v) : Integrable (fun ω ↦ A v ω - A u ω) μ :=
  (integrable_const (c * ((v : ℝ) - u))).mono'
    (((hA v).mono (ℱ.le v)).sub ((hA u).mono (ℱ.le u))).aestronglyMeasurable
    ((hA_step u v huv).mono fun _ hω ↦ by rw [Real.norm_eq_abs, abs_of_nonneg hω.1]; exact hω.2)

/-- For a real `L²` martingale `Y` whose compensated square `Y ^ 2 - A` is a martingale with
`c`-Lipschitz increments `A v - A u ≤ c * (v - u)`, multiplying `(Y v - Y u) ^ 2` by any bounded
nonnegative `ℱ u`-measurable weight `W` yields expectation at most `c * (v - u) * ∫ W ∂μ`. -/
theorem integral_mul_increment_sq_le [IsFiniteMeasure μ] {Y A : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hY : Martingale Y ℱ μ) (hQ : Martingale (fun u ω ↦ Y u ω ^ 2 - A u ω) ℱ μ)
    (hA : StronglyAdapted ℱ A)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂μ, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    {u v : ℝ≥0} (huv : u ≤ v) (hYu : MemLp (Y u) 2 μ) (hYv : MemLp (Y v) 2 μ)
    {W : Ω → ℝ} {C : ℝ} (hW_sm : StronglyMeasurable[ℱ u] W)
    (hW_bd : ∀ᵐ ω ∂μ, W ω ≤ C) (hW_nn : ∀ ω, 0 ≤ W ω) :
    ∫ ω, W ω * (Y v ω - Y u ω) ^ 2 ∂μ ≤ c * ((v : ℝ) - u) * ∫ ω, W ω ∂μ := by
  have hd : Integrable (fun ω ↦ (Y v ω - Y u ω) ^ 2) μ := by
    simpa only [Pi.sub_apply] using (hYv.sub hYu).integrable_sq
  have ha : Integrable (fun ω ↦ A v ω - A u ω) μ := integrable_increment_bracket hA hA_step huv
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

/-- Second-moment bound for the discrete quadratic sum of a uniformly bounded real martingale `Y`
along a nondecreasing finite grid `g : Fin (n + 1) → ℝ≥0`, when `Y ^ 2 - A` is a martingale and
`A` has nonnegative `c`-Lipschitz increments (`0 ≤ c`). -/
theorem integral_quadraticSum_sq_le [IsFiniteMeasure μ] {Y A : ℝ≥0 → Ω → ℝ} {R c : ℝ}
    (hY : Martingale Y ℱ μ) (hQ : Martingale (fun u ω ↦ Y u ω ^ 2 - A u ω) ℱ μ)
    (hA : StronglyAdapted ℱ A)
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
    let d (ω : Ω) : ℝ := (Y (g (Fin.last (n + 1))) ω - Y (g (Fin.last n).castSucc) ω) ^ 2
    have hmem_lp (k : Fin (n + 2)) : MemLp (Y (g k)) 2 μ :=
      MemLp.of_bound ((hY.stronglyAdapted (g k)).mono (ℱ.le _)).aestronglyMeasurable R
        ((hYR k).mono fun _ hω ↦ by rwa [Real.norm_eq_abs])
    have hd_bd : ∀ᵐ ω ∂μ, d ω ≤ (2 * R) ^ 2 :=
      (hYR (Fin.last (n + 1))).mp ((hYR (Fin.last n).castSucc).mono fun ω hu hv ↦ by
        have hinc : |Y (g (Fin.last (n + 1))) ω - Y (g (Fin.last n).castSucc) ω| ≤ 2 * R :=
          (abs_sub _ _).trans (by linarith)
        dsimp only [d]; rw [← sq_abs]; gcongr)
    have hd_lp : MemLp d 2 μ :=
      MemLp.of_bound
        (((hmem_lp (Fin.last (n + 1))).aestronglyMeasurable.sub
          (hmem_lp (Fin.last n).castSucc).aestronglyMeasurable).pow 2)
        ((2 * R) ^ 2)
        (hd_bd.mono fun ω hω ↦ by
          rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)])
    have hd_le (i : Fin (n + 1)) :
        ∫ ω, (Y (g i.succ) ω - Y (g i.castSucc) ω) ^ 2 ∂μ ≤
          c * ((g i.succ : ℝ) - g i.castSucc) * μ.real Set.univ := by
      simpa [integral_const, mul_comm (μ.real Set.univ)] using
        hY.integral_mul_increment_sq_le hQ hA hA_step (hg (Fin.castSucc_le_succ i))
          (hmem_lp i.castSucc) (hmem_lp i.succ) (W := fun _ ↦ (1 : ℝ))
          stronglyMeasurable_const (C := 1) (ae_of_all μ fun _ ↦ le_rfl) (fun _ ↦ zero_le_one)
    have hS'_lp : MemLp (quadraticSum Y g') 2 μ := by
      rw [quadraticSum_def]
      exact memLp_finsetSum _ fun j _ ↦ MemLp.of_bound
        (((hmem_lp j.succ.castSucc).aestronglyMeasurable.sub
          (hmem_lp j.castSucc.castSucc).aestronglyMeasurable).pow 2)
        ((2 * R) ^ 2)
        ((hYR' j.succ).mp ((hYR' j.castSucc).mono fun ω hu hv ↦ by
          dsimp only [g', Function.comp_apply] at hu hv ⊢
          have hinc : |Y (g j.succ.castSucc) ω - Y (g j.castSucc.castSucc) ω| ≤ 2 * R :=
            (abs_sub _ _).trans (by linarith)
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
          gcongr))
    have hS'_sm : StronglyMeasurable[ℱ (g (Fin.last n).castSucc)] (quadraticSum Y g') := by
      rw [quadraticSum_def]
      refine Finset.stronglyMeasurable_fun_sum _ fun j _ ↦ ?_
      have h1 : g' j.succ ≤ g (Fin.last n).castSucc := hg' (Fin.le_last _)
      have h2 : g' j.castSucc ≤ g (Fin.last n).castSucc := hg' (Fin.le_last _)
      exact (((hY.stronglyAdapted (g' j.succ)).mono (ℱ.mono h1)).sub
        ((hY.stronglyAdapted (g' j.castSucc)).mono (ℱ.mono h2))).pow 2
    have hS'_int : ∫ ω, quadraticSum Y g' ω ∂μ ≤
        c * ((g (Fin.last n).castSucc : ℝ) - g 0) * μ.real Set.univ := by
      rw [quadraticSum_def, integral_finsetSum _ fun j _ ↦ by
        convert ((hmem_lp j.succ.castSucc).sub (hmem_lp j.castSucc.castSucc)).integrable_sq
        simp [g']]
      refine (Finset.sum_le_sum fun j _ ↦ hd_le j.castSucc).trans ?_
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      have htele : ∑ j : Fin n, ((g j.castSucc.succ : ℝ) - g j.castSucc.castSucc) =
          (g (Fin.last n).castSucc : ℝ) - g 0 := by
        simp_rw [← Fin.castSucc_succ, Finset.sum_sub_distrib]
        have hs := Fin.sum_univ_succ (fun k : Fin (n + 1) ↦ (g k.castSucc : ℝ))
        have hc' := Fin.sum_univ_castSucc (fun k : Fin (n + 1) ↦ (g k.castSucc : ℝ))
        simp only [Fin.castSucc_zero] at hs
        linarith
      rw [htele]
    have hS'_bd : ∀ᵐ ω ∂μ, quadraticSum Y g' ω ≤ (n : ℝ) * (2 * R) ^ 2 := by
      have hd_bd_j (j : Fin n) :
          ∀ᵐ ω ∂μ, (Y (g' j.succ) ω - Y (g' j.castSucc) ω) ^ 2 ≤ (2 * R) ^ 2 :=
        (hYR' j.succ).mp ((hYR' j.castSucc).mono fun ω hu hv ↦ by
          have hinc : |Y (g' j.succ) ω - Y (g' j.castSucc) ω| ≤ 2 * R :=
            (abs_sub _ _).trans (by linarith)
          rw [← sq_abs]; gcongr)
      rw [quadraticSum_def]
      refine (ae_all_iff.2 hd_bd_j).mono fun ω hω ↦ ?_
      exact (Finset.sum_le_sum fun j _ ↦ hω j).trans_eq (by simp)
    have hcross : ∫ ω, quadraticSum Y g' ω * d ω ∂μ ≤
        c * ((g (Fin.last (n + 1)) : ℝ) - g (Fin.last n).castSucc) *
          (c * ((g (Fin.last n).castSucc : ℝ) - g 0) * μ.real Set.univ) := by
      have hstep_le : (g (Fin.last n).castSucc : ℝ≥0) ≤ g (Fin.last (n + 1)) := by
        simpa [Fin.succ_last] using hg (Fin.castSucc_le_succ (Fin.last n))
      refine (hY.integral_mul_increment_sq_le hQ hA hA_step hstep_le
        (hmem_lp (Fin.last n).castSucc) (hmem_lp (Fin.last (n + 1))) hS'_sm
        hS'_bd (fun _ ↦ quadraticSum_nonneg Y g' _)).trans ?_
      exact mul_le_mul_of_nonneg_left hS'_int
        (mul_nonneg hc (sub_nonneg.2 (NNReal.coe_le_coe.2 hstep_le)))
    have hquart : ∫ ω, d ω ^ 2 ∂μ ≤
        (2 * R) ^ 2 * (c * ((g (Fin.last (n + 1)) : ℝ) - g (Fin.last n).castSucc) *
          μ.real Set.univ) := by
      have hd_last : ∫ ω, d ω ∂μ ≤
          c * ((g (Fin.last (n + 1)) : ℝ) - g (Fin.last n).castSucc) * μ.real Set.univ := by
        simpa [d, Fin.succ_last] using hd_le (Fin.last n)
      refine ((integral_mono_ae hd_lp.integrable_sq
        ((hd_lp.integrable one_le_two).const_mul ((2 * R) ^ 2)) (hd_bd.mono fun _ hω ↦ by
          dsimp only; rw [sq]; exact mul_le_mul_of_nonneg_right hω (sq_nonneg _))).trans_eq
        (integral_const_mul _ _)).trans ?_
      gcongr
    have hS_succ (ω : Ω) : quadraticSum Y g ω = quadraticSum Y g' ω + d ω := by
      simp only [quadraticSum_def, g', d, Fin.sum_univ_castSucc, Fin.succ_last]; rfl
    have hS_sq (ω : Ω) : quadraticSum Y g ω ^ 2 =
        quadraticSum Y g' ω ^ 2 + 2 * (quadraticSum Y g' ω * d ω) + d ω ^ 2 := by
      rw [hS_succ ω]; ring
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
      mul_nonneg hc (sub_nonneg.2 (NNReal.coe_le_coe.2
        (hg (Fin.castSucc_le_succ (Fin.last n) |>.trans (by simp [Fin.succ_last])))))
    have hsplit : (g (Fin.last (n + 1)) : ℝ) - g 0 =
        ((g (Fin.last n).castSucc : ℝ) - g 0) +
          ((g (Fin.last (n + 1)) : ℝ) - g (Fin.last n).castSucc) := by ring
    have hμ0 : 0 ≤ μ.real Set.univ := ENNReal.toReal_nonneg
    have h4R : (2 * R) ^ 2 = 4 * R ^ 2 := by ring
    rw [h4R] at hquart
    nlinarith [ih', hcross, hquart, hsplit, mul_nonneg (mul_nonneg hL0 hδ0) hμ0,
      mul_nonneg (sq_nonneg (c * ((g (Fin.last (n + 1)) : ℝ) - g (Fin.last n).castSucc))) hμ0]

end MeasureTheory.Martingale
