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
import TauCeti.Probability.Martingale.QuadraticVariation
import TauCeti.Probability.Process.QuadraticVariation
import TauCeti.Topology.Instances.Real.UniformGrid

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

open Complex Filter MeasureTheory Set TauCeti TauCeti.Probability
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

private def maxInc (X : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (m : ℕ) (ω : Ω) : ℝ :=
  (Finset.univ : Finset (Fin (m + 1))).sup' Finset.univ_nonempty fun k ↦
    |X (uniformGridFin s t m k.succ) ω - X (uniformGridFin s t m k.castSucc) ω|

private def remBound (X : ℝ≥0 → Ω → ℝ) (c : ℝ) (s t : ℝ≥0) (m : ℕ) (ω : Ω) : ℝ :=
  maxInc X s t m ω * quadraticSum X (uniformGridFin s t m) ω +
    c * ((t : ℝ) - s) * maxInc X s t m ω + (c * ((t : ℝ) - s)) ^ 2 / (m + 1 : ℝ)

private lemma remBound_eq (X : ℝ≥0 → Ω → ℝ) (c : ℝ) (s t : ℝ≥0) (m : ℕ) (ω : Ω) :
    remBound X c s t m ω = maxInc X s t m ω * quadraticSum X (uniformGridFin s t m) ω +
      c * ((t : ℝ) - s) * maxInc X s t m ω + (c * ((t : ℝ) - s)) ^ 2 / (m + 1 : ℝ) :=
  rfl

private lemma maxInc_nonneg (X : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (m : ℕ) (ω : Ω) :
    0 ≤ maxInc X s t m ω :=
  (abs_nonneg _).trans (Finset.le_sup' (f := fun k : Fin (m + 1) ↦
    |X (uniformGridFin s t m k.succ) ω - X (uniformGridFin s t m k.castSucc) ω|)
    (Finset.mem_univ 0))

private lemma exists_norm_expRem_le (α R : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {D x a : ℝ}, |x| ≤ 2 * R → |x| ≤ D → 0 ≤ a → a ≤ L →
      ‖expRem α x a‖ ≤ K * (D * x ^ 2 + D * a + a ^ 2) := by
  let Ke := Real.exp (2 * |α| * R + α ^ 2 / 2 * L)
  let c₃ := |α| ^ 3 / 2
  let c₄ := |α| ^ 4 / 8
  let c₁ := 4 * |α| ^ 3 * Ke
  let c₂ := 4 * (α ^ 2 / 2) ^ 3 * L * Ke
  refine ⟨c₁ + c₂ + c₃ + c₄, by positivity, fun {D x a} hxR hxD ha0 haL ↦ ?_⟩
  let w : ℂ := I * α * x + ((α ^ 2 / 2 * a : ℝ) : ℂ)
  let u := |α| * |x|
  let v := α ^ 2 / 2 * a
  have hw : ‖w‖ ≤ u + v := (norm_add_le _ _).trans_eq <| by simp [u, v, ha0]
  have huv : 0 ≤ u + v := by positivity
  have hrem : ‖exp w - ∑ j ∈ Finset.range 3, w ^ j / j.factorial‖ ≤
      4 * (u ^ 3 + v ^ 3) * Ke :=
    (Complex.norm_exp_sub_sum_le_norm_mul_exp w 3).trans <| (mul_le_mul
      (pow_le_pow_left₀ (norm_nonneg _) hw 3) (Real.exp_le_exp.2 (hw.trans (by
        dsimp only [u, v]; nlinarith [abs_nonneg α, sq_nonneg α]))) (Real.exp_pos _).le
      (by positivity)).trans <| mul_le_mul_of_nonneg_right
      (by nlinarith [sq_nonneg (u - v), huv]) (by positivity)
  have hmid : ‖I * ((α ^ 3 / 2 * x * a : ℝ) : ℂ) + ((α ^ 4 / 8 * a ^ 2 : ℝ) : ℂ)‖ ≤
      c₃ * |x| * a + c₄ * a ^ 2 :=
    (norm_add_le _ _).trans_eq <| by simp [c₃, c₄, abs_of_nonneg ha0]
  have hexp : expRem α x a = (exp w - ∑ j ∈ Finset.range 3, w ^ j / j.factorial) +
      (I * ((α ^ 3 / 2 * x * a : ℝ) : ℂ) + ((α ^ 4 / 8 * a ^ 2 : ℝ) : ℂ)) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, expRem, w]
    push_cast; ring_nf; simp [I_sq]; ring
  rw [hexp]
  have hD0 : 0 ≤ D := (abs_nonneg x).trans hxD
  have hx3 : |x| ^ 3 ≤ D * x ^ 2 := by rw [pow_succ, sq_abs, mul_comm]; gcongr
  have ha3 : a ^ 3 ≤ L * a ^ 2 := by rw [pow_succ, mul_comm]; gcongr
  have h1 : 4 * (u ^ 3 + v ^ 3) * Ke + (c₃ * |x| * a + c₄ * a ^ 2) ≤
      c₁ * (D * x ^ 2) + c₂ * a ^ 2 + (c₃ * D * a + c₄ * a ^ 2) := by
    simp only [u, v, mul_pow, c₁, c₂]
    have hcube : 4 * (|α| ^ 3 * |x| ^ 3 + (α ^ 2 / 2) ^ 3 * a ^ 3) * Ke ≤
        4 * (|α| ^ 3 * (D * x ^ 2) + (α ^ 2 / 2) ^ 3 * (L * a ^ 2)) * Ke := by gcongr
    have hcross : c₃ * |x| * a ≤ c₃ * D * a := by gcongr
    linarith
  have hrem_nonneg : 0 ≤ (c₂ + c₃ + c₄) * (D * x ^ 2) + (c₁ + c₂ + c₄) * (D * a) +
      (c₁ + c₃) * a ^ 2 := by positivity
  exact (norm_add_le _ _).trans <| (add_le_add hrem hmid).trans <| h1.trans <|
    sub_nonneg.1 (hrem_nonneg.trans_eq <| by ring)

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω}

private lemma ae_abs_increment_le {X : ℝ≥0 → Ω → ℝ} {R : ℝ} (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R)
    (u v : ℝ≥0) : ∀ᵐ ω ∂P, |X v ω - X u ω| ≤ 2 * R :=
  (hXR v).mp <| (hXR u).mono fun _ hu hv ↦ (abs_sub _ _).trans (by linarith)

private lemma ae_maxInc_le {X : ℝ≥0 → Ω → ℝ} {R : ℝ} (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R)
    (s t : ℝ≥0) (m : ℕ) : ∀ᵐ ω ∂P, maxInc X s t m ω ≤ 2 * R :=
  (ae_all_iff.2 fun k : Fin (m + 1) ↦
    ae_abs_increment_le hXR (uniformGridFin s t m k.castSucc)
      (uniformGridFin s t m k.succ)).mono fun _ h ↦ Finset.sup'_le _ _ fun k _ ↦ h k

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
    ∃ K ≥ 0, ∀ m : ℕ, ∀ᵐ ω ∂P,
      ‖∑ k : Fin (m + 1),
        remTerm X A α (uniformGridFin s t m k.castSucc) (uniformGridFin s t m k.succ) ω‖ ≤
      Real.exp (α ^ 2 / 2 * (c * (t : ℝ))) * K * remBound X c s t m ω := by
  let L := c * ((t : ℝ) - s)
  let Mz := Real.exp (α ^ 2 / 2 * (c * (t : ℝ)))
  have hL : 0 ≤ L := mul_nonneg hc (sub_nonneg.2 (NNReal.coe_le_coe.2 hst))
  obtain ⟨K, hK0, hK⟩ := exists_norm_expRem_le α R hL
  refine ⟨K, hK0, fun m ↦ ?_⟩
  let g := uniformGridFin s t m
  filter_upwards [ae_all_iff.2 fun k : Fin (m + 1) ↦
      ae_abs_increment_le hXR (g k.castSucc) (g k.succ),
    ae_all_iff.2 fun k : Fin (m + 1) ↦
      (hA_step _ _ (uniformGridFin_monotone s t m (Fin.castSucc_le_succ k))).mono fun _ hω ↦ by
        rw [coe_uniformGridFin_succ_sub_castSucc hst m k, ← mul_div_assoc] at hω
        exact hω,
    ae_all_iff.2 fun k : Fin (m + 1) ↦
      (ae_norm_expProc_le (X := X) hA0 hA_step α (g k.castSucc)).mono fun _ hω ↦
        hω.trans (Real.exp_le_exp.2 <| mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (NNReal.coe_le_coe.2 (uniformGridFin_mem_Icc hst m k.castSucc).2) hc) (by positivity))]
    with ω hXω hAω hZω
  let D := maxInc X s t m ω
  have hD0 := maxInc_nonneg X s t m ω
  have hMz : 0 ≤ Mz := (Real.exp_pos _).le
  have hmne : (m : ℝ) + 1 ≠ 0 := by positivity
  refine (norm_sum_le _ _).trans <| (Finset.sum_le_sum (g := fun k : Fin (m + 1) ↦ Mz * K *
      (D * (X (g k.succ) ω - X (g k.castSucc) ω) ^ 2 +
        D * (L / (m + 1 : ℝ)) + (L / (m + 1 : ℝ)) ^ 2)) fun k hk ↦ ?_).trans_eq ?_
  · obtain ⟨h1, h2⟩ := hAω k
    have hrem := hK (D := D) (hXω k)
      (Finset.le_sup' (f := fun j : Fin (m + 1) ↦ |X (g j.succ) ω - X (g j.castSucc) ω|) hk) h1
      (h2.trans (div_le_self hL (by linarith [Nat.cast_nonneg (α := ℝ) m])))
    exact ((norm_mul _ _).trans_le (mul_le_mul (hZω k) hrem (norm_nonneg _) hMz)).trans
      (by rw [mul_assoc]; gcongr)
  · rw [← Finset.mul_sum]
    congr 1
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
    push_cast
    rw [remBound_eq, quadraticSum_def]
    dsimp only [L, g, D]
    field_simp [hmne]

private lemma integrableOn_smul_of_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Ω → ℝ} {W : Ω → F} {S : Set Ω} {C : ℝ} (hf : Integrable f P)
    (hW : AEStronglyMeasurable W P) (hb : ∀ᵐ ω ∂P, ‖W ω‖ ≤ C) :
    IntegrableOn (fun ω ↦ f ω • W ω) S P :=
  ((hf.norm.const_mul (max C 0)).mono' (hf.aestronglyMeasurable.smul hW)
    (hb.mono fun _ hω ↦ (norm_smul (f _) (W _)).trans_le
      (by rw [mul_comm]; gcongr; exact hω.trans (le_max_left _ _)))).integrableOn

private lemma ae_norm_smul_le_of_abs_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Ω → ℝ} {W : Ω → F} {R C : ℝ} (hf : ∀ᵐ ω ∂P, |f ω| ≤ R) (hW : ∀ᵐ ω ∂P, ‖W ω‖ ≤ C) :
    ∀ᵐ ω ∂P, ‖f ω • W ω‖ ≤ max R 0 * max C 0 :=
  hf.mp <| hW.mono fun _ hC hR ↦ by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hR.trans (le_max_left _ _)) (hC.trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)

variable [IsFiniteMeasure P] {ℱ : Filtration ℝ≥0 mΩ}

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
  have hm_eq : maxInc X s t m = (Finset.univ : Finset (Fin (m + 1))).sup' Finset.univ_nonempty
      fun k ω ↦ |X (uniformGridFin s t m k.succ) ω - X (uniformGridFin s t m k.castSucc) ω| := by
    ext ω; simp [maxInc]
  refine MemLp.of_bound (hm_eq ▸ Finset.measurable_sup' Finset.univ_nonempty
    fun (k : Fin (m + 1)) _ ↦ continuous_abs.measurable.comp
      ((((hX (uniformGridFin s t m k.succ)).mono (ℱ.le _)).measurable).sub
        (((hX (uniformGridFin s t m k.castSucc)).mono
          (ℱ.le _)).measurable))).aestronglyMeasurable
    (2 * R) ((ae_maxInc_le hXR s t m).mono fun ω hω ↦ by
      rwa [Real.norm_eq_abs, abs_of_nonneg (maxInc_nonneg X s t m ω)])

private lemma tendsto_integral_maxInc_sq {X : ℝ≥0 → Ω → ℝ} {R : ℝ} (hX : StronglyAdapted ℱ X)
    (hcont : ∀ᵐ ω ∂P, Continuous (X · ω)) (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R)
    {s t : ℝ≥0} (hst : s ≤ t) : Tendsto (fun m ↦ ∫ ω, maxInc X s t m ω ^ 2 ∂P) atTop (𝓝 0) := by
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (F := fun m ω ↦ maxInc X s t m ω ^ 2) (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ (2 * R) ^ 2)
    (fun m ↦ (memLp_maxInc hX hXR s t m).aestronglyMeasurable.pow 2) (integrable_const _)
    (fun m ↦ (ae_maxInc_le hXR s t m).mono fun ω h ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (maxInc_nonneg X s t m ω) h 2)
    (hcont.mono fun ω hω ↦ by
      rw [← zero_pow two_ne_zero]
      exact (Metric.tendsto_atTop.2 fun ε hε ↦ by
        obtain ⟨δ, hδ, hδp⟩ := Metric.uniformContinuousOn_iff.1
          ((isCompact_Icc (a := s) (b := t)).uniformContinuousOn_of_continuous hω.continuousOn)
          ε hε
        obtain ⟨N, hN⟩ := ((tendsto_uniformGrid_mesh s t).eventually
          (gt_mem_nhds hδ)).exists_forall_of_atTop
        refine ⟨N, fun m hm ↦ ?_⟩
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (maxInc_nonneg X s t m ω)]
        exact (Finset.sup'_lt_iff _).2 fun k _ ↦ by
          have hdist :
              dist (uniformGridFin s t m k.succ) (uniformGridFin s t m k.castSucc) < δ := by
            rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2
                (uniformGridFin_monotone s t m (Fin.castSucc_le_succ k)))),
              coe_uniformGridFin_succ_sub_castSucc hst m k]
            simpa only [Nat.cast_add, Nat.cast_one] using hN m hm
          simpa [Real.dist_eq] using hδp _ (uniformGridFin_mem_Icc hst m k.succ) _
            (uniformGridFin_mem_Icc hst m k.castSucc) hdist).pow 2)

section PartitionEstimates

variable {X A : ℝ≥0 → Ω → ℝ} {R c : ℝ} (hX : Martingale X ℱ P)
  (hQ : Martingale (fun u ω ↦ X u ω ^ 2 - A u ω) ℱ P) (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R)
  (hA : StronglyAdapted ℱ A)
  (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
include hX hQ hXR hA hA_step

private lemma setIntegral_expProc_step (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0) (α : ℝ)
    (hZ_adapt : StronglyAdapted ℱ (expProc X A α)) (hZ_int : ∀ u, Integrable (expProc X A α u) P)
    {s u v : ℝ≥0} (huv : u ≤ v) (hsu : s ≤ u) {E : Set Ω} (hE : MeasurableSet[ℱ s] E) :
    IntegrableOn (fun ω ↦ remTerm X A α u v ω) E P ∧
      ∫ ω in E, (expProc X A α v ω - expProc X A α u ω) ∂P =
        ∫ ω in E, remTerm X A α u v ω ∂P := by
  have hZ_bd := ae_norm_expProc_le (X := X) hA0 hA_step α u
  have hZ_asm : AEStronglyMeasurable (expProc X A α u) P :=
    ((hZ_adapt u).mono (ℱ.le u)).aestronglyMeasurable
  have hmul {f : Ω → ℝ} (hf : Integrable f P) (c₀ : ℂ) :
      IntegrableOn (fun ω ↦ c₀ * (f ω • expProc X A α u ω)) E P :=
    (((Complex.ofRealCLM.integrable_comp hf).mul_bdd hZ_asm hZ_bd).const_mul c₀).integrableOn
  have hZs : IntegrableOn (fun ω ↦ expProc X A α v ω - expProc X A α u ω) E P :=
    ((hZ_int v).sub (hZ_int u)).integrableOn
  have h1 := hmul (f := fun ω ↦ X v ω - X u ω) ((hX.integrable v).sub (hX.integrable u)) (I * α)
  have h2 := hmul (f := fun ω ↦ (X v ω - X u ω) ^ 2 - (A v ω - A u ω))
    (((memLp_increment_sq hX.stronglyAdapted hXR u v).integrable one_le_two).sub
      (integrable_increment_bracket (P := P) hA hA_step huv)) ((α ^ 2 / 2 : ℝ) : ℂ)
  have hdec (ω : Ω) : remTerm X A α u v ω = (expProc X A α v ω - expProc X A α u ω) -
      (I * (α : ℂ)) * ((X v ω - X u ω) • expProc X A α u ω) +
      ((α ^ 2 / 2 : ℝ) : ℂ) * (((X v ω - X u ω) ^ 2 - (A v ω - A u ω)) • expProc X A α u ω) := by
    have hexp_mul : expProc X A α u ω *
        exp (I * α * ((X v ω - X u ω : ℝ) : ℂ) + ((α ^ 2 / 2 * (A v ω - A u ω) : ℝ) : ℂ)) =
        expProc X A α v ω := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    dsimp only [remTerm, expRem]
    rw [mul_sub, mul_sub, mul_one, hexp_mul]
    simp [Complex.real_smul]; ring
  have hZs1 : IntegrableOn (fun ω ↦ (expProc X A α v ω - expProc X A α u ω) -
      (I * (α : ℂ)) * ((X v ω - X u ω) • expProc X A α u ω)) E P := hZs.sub h1
  refine ⟨by simp_rw [hdec]; exact hZs1.add h2, ?_⟩
  simp_rw [hdec]
  rw [integral_add hZs1 h2, integral_sub hZs h1, integral_const_mul, integral_const_mul,
    hX.setIntegral_sub_smul_eq_zero huv (ℱ.mono hsu _ hE) (hZ_adapt u).aestronglyMeasurable
      (integrableOn_smul_of_bound ((hX.integrable v).sub (hX.integrable u)) hZ_asm hZ_bd),
    hX.setIntegral_sq_sub_smul_eq_zero hQ huv (ℱ.mono hsu _ hE) (hZ_adapt u).aestronglyMeasurable
      (integrableOn_smul_of_bound ((hQ.integrable v).sub (hQ.integrable u)) hZ_asm hZ_bd)
      (integrableOn_smul_of_bound ((hX.integrable v).sub (hX.integrable u))
        (((hX.stronglyAdapted u).mono (ℱ.le u)).aestronglyMeasurable.smul hZ_asm)
        (ae_norm_smul_le_of_abs_le (hXR u) hZ_bd))]
  simp

private lemma integral_maxInc_remBound_le (hc : 0 ≤ c) {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) :
    let L := c * ((t : ℝ) - s)
    Integrable (remBound X c s t m) P ∧ ∫ ω, remBound X c s t m ω ∂P ≤
      (√((4 * R ^ 2 * L + 2 * L ^ 2) * P.real univ) + L * √(P.real univ)) *
        √(∫ ω, maxInc X s t m ω ^ 2 ∂P) + L ^ 2 * P.real univ / (m + 1 : ℝ) := by
  intro L
  let g := uniformGridFin s t m
  let D := maxInc X s t m
  have hXa := hX.stronglyAdapted
  let S := quadraticSum X g
  have hL : 0 ≤ L := mul_nonneg hc (sub_nonneg.2 (NNReal.coe_le_coe.2 hst))
  have hD_lp := memLp_maxInc hXa hXR s t m
  have hS_lp : MemLp S 2 P := by
    rw [show S = fun ω ↦ ∑ k : Fin (m + 1), (X (g k.succ) ω - X (g k.castSucc) ω) ^ 2 from
      quadraticSum_def X g]
    exact memLp_finsetSum _ fun _ _ ↦ memLp_increment_sq hXa hXR _ _
  have hCS := (le_abs_self (∫ ω, D ω * S ω ∂P)).trans <|
    (abs_integral_mul_le_sqrt_integral_sq_mul_sqrt_integral_sq hD_lp hS_lp).trans <|
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt <| by
        simpa only [S, g, L, uniformGridFin_zero, uniformGridFin_last hst] using
          hX.integral_quadraticSum_sq_le hQ hA hA_step hc (uniformGridFin_monotone s t m)
            (fun _ ↦ hXR _))
        (Real.sqrt_nonneg _)
  have hD1 : ∫ ω, D ω ∂P ≤ √(∫ ω, D ω ^ 2 ∂P) * √(P.real univ) := by
    simpa only [Measure.restrict_univ] using (le_abs_self _).trans
      (abs_setIntegral_le_sqrt_integral_sq_mul_sqrt_measureReal hD_lp (measure_ne_top P univ))
  have hDS := hD_lp.integrable_mul hS_lp
  have hLD := (hD_lp.integrable one_le_two).const_mul L
  have hterm : P.real univ * (L ^ 2 / (m + 1 : ℝ)) = L ^ 2 * P.real univ / (m + 1 : ℝ) := by ring
  have hrem_fn : remBound X c s t m = fun ω ↦ D ω * S ω + L * D ω + L ^ 2 / (m + 1 : ℝ) :=
    funext (remBound_eq X c s t m)
  refine ⟨hrem_fn ▸ (hDS.add hLD).add (integrable_const _), ?_⟩
  rw [hrem_fn, integral_add (f := fun ω ↦ D ω * S ω + L * D ω) (hDS.add hLD) (integrable_const _),
    integral_add (f := fun ω ↦ D ω * S ω) hDS hLD, integral_const_mul, integral_const, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left hD1 hL, hterm]

private lemma exists_norm_setIntegral_expProc_sub_le (hc : 0 ≤ c) (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0)
    (α : ℝ) (hZ_adapt : StronglyAdapted ℱ (expProc X A α))
    (hZ_int : ∀ u, Integrable (expProc X A α u) P) {s t : ℝ≥0} (hst : s ≤ t)
    {E : Set Ω} (hE : MeasurableSet[ℱ s] E) :
    ∃ C₁ C₂ : ℝ, ∀ m : ℕ, ‖∫ ω in E, (expProc X A α t ω - expProc X A α s ω) ∂P‖ ≤
      C₁ * √(∫ ω, maxInc X s t m ω ^ 2 ∂P) + C₂ / (m + 1 : ℝ) := by
  let L := c * ((t : ℝ) - s)
  let Mz := Real.exp (α ^ 2 / 2 * (c * (t : ℝ)))
  obtain ⟨K, hK0, hK⟩ := exists_ae_norm_sum_expRem_le hXR hA0 hA_step hc α hst
  refine ⟨Mz * K * (√((4 * R ^ 2 * L + 2 * L ^ 2) * P.real univ) + L * √(P.real univ)),
    Mz * K * (L ^ 2 * P.real univ), fun m ↦ ?_⟩
  let g := uniformGridFin s t m
  have hstepk (k : Fin (m + 1)) := setIntegral_expProc_step hX hQ hXR hA hA_step hA0 α hZ_adapt
    hZ_int (uniformGridFin_monotone s t m (Fin.castSucc_le_succ k))
    (uniformGridFin_mem_Icc hst m k.castSucc).1 hE
  obtain ⟨hf_int, hf_le⟩ := integral_maxInc_remBound_le hX hQ hXR hA hA_step hc hst m
  have hL : 0 ≤ L := mul_nonneg hc (sub_nonneg.2 (NNReal.coe_le_coe.2 hst))
  have htele : ∫ ω in E, (expProc X A α t ω - expProc X A α s ω) ∂P =
      ∫ ω in E, ∑ k : Fin (m + 1), remTerm X A α (g k.castSucc) (g k.succ) ω ∂P := by
    rw [integral_finsetSum _ fun k _ ↦ (hstepk k).1, ← Finset.sum_congr rfl fun k _ ↦ (hstepk k).2,
      ← integral_finsetSum Finset.univ
        (f := fun (k : Fin (m + 1)) ω ↦ expProc X A α (g k.succ) ω - expProc X A α (g k.castSucc) ω)
        fun _ _ ↦ ((hZ_int _).sub (hZ_int _)).integrableOn]
    congr 1; ext ω
    have hs := Fin.sum_univ_succ (fun k : Fin (m + 2) ↦ expProc X A α (g k) ω)
    have hc' := Fin.sum_univ_castSucc (fun k : Fin (m + 2) ↦ expProc X A α (g k) ω)
    have hsum := hs.symm.trans hc'
    dsimp only [g] at hsum
    rw [uniformGridFin_zero, uniformGridFin_last hst] at hsum
    rw [Finset.sum_sub_distrib, sub_eq_sub_iff_add_eq_add, add_comm, hsum.symm, add_comm]
  rw [htele]
  refine ((norm_integral_le_integral_norm _).trans ((integral_mono_ae
    (integrable_finsetSum _ fun k _ ↦ (hstepk k).1).norm (hf_int.const_mul (Mz * K)).integrableOn
    (ae_restrict_of_ae (hK m))).trans (setIntegral_le_integral (hf_int.const_mul (Mz * K))
      (ae_of_all P fun ω ↦ by
        dsimp only [Pi.zero_apply]
        have hinc_nn := maxInc_nonneg X s t m ω
        have hqs_nn := quadraticSum_nonneg X g ω
        rw [remBound_eq]
        positivity)))).trans ?_
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
  have hA_step' u v (huv : u ≤ v) := (hA_step u v huv).mono fun _ hω ↦ And.intro hω.1 <| hω.2.trans
    (mul_le_mul_of_nonneg_right (le_max_left c 0) (sub_nonneg.2 (NNReal.coe_le_coe.2 huv)))
  have hZ_adapt : StronglyAdapted ℱ (expProc X A α) := fun u ↦
    Complex.continuous_exp.comp_stronglyMeasurable <| (stronglyMeasurable_const.mul <|
      Complex.continuous_ofReal.comp_stronglyMeasurable (hX.stronglyAdapted u)).add <|
      Complex.continuous_ofReal.comp_stronglyMeasurable (stronglyMeasurable_const.mul (hA_adapt u))
  have hZ_int u : Integrable (expProc X A α u) P := (integrable_const _).mono'
    ((hZ_adapt u).mono (ℱ.le u)).aestronglyMeasurable (ae_norm_expProc_le (X := X) hA0 hA_step' α u)
  rw [hZ_adapt.martingale_iff_setIntegral_eq hZ_int]
  intro s t hst E hE
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
