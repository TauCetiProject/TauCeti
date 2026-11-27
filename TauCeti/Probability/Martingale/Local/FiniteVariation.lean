/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import TauCeti.Probability.Martingale.Local.Arithmetic
public import TauCeti.Probability.Martingale.Local.Bounded
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Lattice.Nat
import Mathlib.Probability.Process.HittingTime
import TauCeti.Probability.Martingale.CountableStopping
import TauCeti.Probability.Process.ContinuousAE
import TauCeti.Probability.Process.Stopping
import TauCeti.Topology.EMetricSpace.BoundedVariation

/-!
# Continuous local martingales of finite variation are constant

Under a finite measure, any a.s. continuous native local martingale on `ℝ≥0` with bounded variation
on compact intervals `[0, T]` is indistinguishable from its initial value, with no usual-conditions
or initial-measurability assumptions. Stopping a bounded centered real martingale when dyadic
variation exceeds `M` bounds stopped squared increments by `(M + 2 C) · max_i |Δ_i W|`, and bounded
native localization plus Hahn–Banach lift this to any real Banach space `E`.

## References

* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 1999, Ch. IV, Prop. 1.2.
* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., 1991, §1.5.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.Locally

section DyadicHelpers

private def dyadicPt (T : ℝ≥0) (k j : ℕ) : ℝ≥0 := ((min j (2 ^ k) : ℕ) : ℝ≥0) / (2 ^ k : ℝ≥0) * T

private theorem dyadicPt_mono (T : ℝ≥0) (k : ℕ) : Monotone (dyadicPt T k) := fun _ _ hij ↦ by
  dsimp only [dyadicPt]; gcongr

private theorem dyadicPt_mem_Icc (T : ℝ≥0) (k j : ℕ) : dyadicPt T k j ∈ Icc 0 T := by
  have hdiv : ((min j (2 ^ k) : ℕ) : ℝ≥0) / (2 ^ k : ℝ≥0) ≤ 1 :=
    (div_le_one₀ (by positivity)).2 (by exact_mod_cast min_le_right j (2 ^ k))
  exact ⟨bot_le, by simpa only [dyadicPt, one_mul] using mul_le_mul_of_nonneg_right hdiv bot_le⟩

private theorem dist_dyadicPt_succ_le (T : ℝ≥0) (k i : ℕ) :
    dist (dyadicPt T k (i + 1)) (dyadicPt T k i) ≤ (T : ℝ) / (2 : ℝ) ^ k := by
  rw [NNReal.dist_eq,
    abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 (dyadicPt_mono T k i.le_succ)))]
  have hmin : ((min (i + 1) (2 ^ k) : ℕ) : ℝ) ≤ ((min i (2 ^ k) : ℕ) : ℝ) + 1 := by
    exact_mod_cast (by omega : min (i + 1) (2 ^ k) ≤ min i (2 ^ k) + 1)
  have hstep : ((min (i + 1) (2 ^ k) : ℕ) - (min i (2 ^ k) : ℕ) : ℝ) ≤ 1 := by linarith
  have hexp : (dyadicPt T k (i + 1) : ℝ) - (dyadicPt T k i : ℝ) =
      ((min (i + 1) (2 ^ k) : ℕ) - (min i (2 ^ k) : ℕ) : ℝ) * ((T : ℝ) / 2 ^ k) := by
    simp only [dyadicPt, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat,
      NNReal.coe_natCast]; ring
  simpa only [hexp, one_mul] using mul_le_mul_of_nonneg_right hstep (by positivity)

private def gridOsc {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (k : ℕ) (ω : Ω) : ℝ≥0 :=
  (Finset.range (2 ^ k)).sup fun i ↦ ‖W (dyadicPt T k (i + 1)) ω - W (dyadicPt T k i) ω‖₊

private theorem stronglyMeasurable_gridOsc {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {W : ℝ≥0 → Ω → ℝ} (hW : ∀ t, StronglyMeasurable (W t)) (T : ℝ≥0) (k : ℕ) :
    StronglyMeasurable fun ω ↦ (gridOsc W T k ω : ℝ) := by
  suffices ∀ s : Finset ℕ, StronglyMeasurable fun ω ↦
      ((s.sup fun i ↦ ‖W (dyadicPt T k (i + 1)) ω - W (dyadicPt T k i) ω‖₊ : ℝ≥0) : ℝ) from this _
  intro s; induction s using Finset.induction_on with
  | empty => simpa using stronglyMeasurable_const
  | insert a s _ ih =>
    convert (((hW (dyadicPt T k (a + 1))).sub (hW (dyadicPt T k a))).norm).sup ih using 1
    ext; simp [Finset.sup_insert]

private theorem tendsto_gridOsc {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {ω : Ω}
    (hf : Continuous (W · ω)) : Tendsto (fun k : ℕ ↦ (gridOsc W T k ω : ℝ)) atTop (𝓝 0) := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous (s := Icc 0 T) hf.continuousOn
  rw [Metric.tendsto_atTop]; intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.1 huc (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1
    (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two) :
      Tendsto (fun k : ℕ ↦ (T : ℝ) / 2 ^ k) atTop (𝓝 0)) δ hδ
  refine ⟨N, fun k hk ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)]
  let B : ℝ≥0 := ⟨ε / 2, (half_pos hε).le⟩
  refine lt_of_le_of_lt (b := (B : ℝ)) (NNReal.coe_le_coe.2 <| Finset.sup_le fun i _ ↦ ?_)
    (half_lt_self hε)
  rw [← NNReal.coe_le_coe, coe_nnNorm, Real.norm_eq_abs, ← Real.dist_eq]
  exact (hmod _ (dyadicPt_mem_Icc T k (i + 1)) _ (dyadicPt_mem_Icc T k i)
    ((dist_dyadicPt_succ_le T k i).trans_lt
      (by simpa [Real.dist_eq, abs_of_nonneg (by positivity : 0 ≤ (T : ℝ) / 2 ^ k)] using
        hN k hk))).le

private theorem gridOsc_le_two_mul {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {k : ℕ} {C : ℝ}
    {ω : Ω} (hC0 : 0 ≤ C) (hb : ∀ t, |W t ω| ≤ C) : (gridOsc W T k ω : ℝ) ≤ 2 * C := by
  rw [← NNReal.coe_mk (2 * C) (by positivity)]
  exact NNReal.coe_le_coe.2 <| Finset.sup_le fun i _ ↦ by
    rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_mk, Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by linarith [hb (dyadicPt T k (i + 1)), hb (dyadicPt T k i)])

private def gridVar {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (k j : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range j, |W (dyadicPt T k (i + 1)) ω - W (dyadicPt T k i) ω|

private theorem gridVar_mono {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (k : ℕ) (ω : Ω) :
    Monotone (gridVar W T k · ω) := fun _ _ hij ↦
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij) fun _ _ _ ↦ abs_nonneg _

private def gridHit {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (k M : ℕ) : Ω → WithTop ℕ :=
  hittingAfter (gridVar W T k) (Ioi (M : ℝ)) 0

private theorem gridHit_le_iff {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {k M i : ℕ} {ω : Ω} :
    gridHit W T k M ω ≤ WithTop.some i ↔ (M : ℝ) < gridVar W T k i ω := by
  rw [gridHit, hittingAfter_le_iff]
  exact ⟨fun ⟨j, hj, hlt⟩ ↦ hlt.trans_le (gridVar_mono W T k ω hj.2),
    fun hlt ↦ ⟨i, ⟨Nat.zero_le _, le_rfl⟩, hlt⟩⟩

private theorem stopped_gridHit_sub_eq {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {k M i : ℕ} {ω : Ω} :
    let Z := stoppedProcess (fun j ↦ W (dyadicPt T k j)) (gridHit W T k M)
    Z (i + 1) ω - Z i ω =
      if gridVar W T k i ω ≤ M then W (dyadicPt T k (i + 1)) ω - W (dyadicPt T k i) ω else 0 := by
  intro Z; dsimp only [Z]
  by_cases hle : gridVar W T k i ω ≤ M
  · have hlt : WithTop.some i < gridHit W T k M ω := not_le.1 (mt gridHit_le_iff.1 hle.not_gt)
    have hle' : WithTop.some (i + 1) ≤ gridHit W T k M ω := by
      cases hτ : gridHit W T k M ω with
      | top => exact le_top
      | coe m => exact WithTop.coe_le_coe.2 (Nat.succ_le_of_lt (WithTop.coe_lt_coe.1 (hτ ▸ hlt)))
    simp only [hle, ↓reduceIte, stoppedProcess_eq_of_le hle', stoppedProcess_eq_of_le hlt.le]
  · have hge : gridHit W T k M ω ≤ WithTop.some i := gridHit_le_iff.2 (lt_of_not_ge hle)
    have hge' := hge.trans (WithTop.coe_le_coe.2 i.le_succ)
    simp only [hle, ↓reduceIte, stoppedProcess_eq_of_ge hge', stoppedProcess_eq_of_ge hge, sub_self]

private theorem stopped_gridHit_sq_sum_le {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {k M : ℕ}
    {C : ℝ} {ω : Ω} (hC0 : 0 ≤ C) (hb : ∀ t, |W t ω| ≤ C) :
    let Z := stoppedProcess (fun j ↦ W (dyadicPt T k j)) (gridHit W T k M)
    ∑ i ∈ Finset.range (2 ^ k), (Z (i + 1) ω - Z i ω) ^ 2 ≤
      (M + 2 * C) * (gridOsc W T k ω : ℝ) := by
  intro Z
  have hinc_le (i : ℕ) : |Z (i + 1) ω - Z i ω| ≤
      |W (dyadicPt T k (i + 1)) ω - W (dyadicPt T k i) ω| := by
    dsimp only [Z]; rw [stopped_gridHit_sub_eq]; split_ifs <;> simp
  have hsum_le (n : ℕ) : ∑ i ∈ Finset.range n, |Z (i + 1) ω - Z i ω| ≤ M + 2 * C := by
    induction n with
    | zero => simp only [Finset.range_zero, Finset.sum_empty]; positivity
    | succ n ih =>
      rw [Finset.sum_range_succ]; by_cases hn : gridVar W T k n ω ≤ M
      · exact add_le_add ((Finset.sum_le_sum fun i _ ↦ hinc_le i).trans hn)
          ((hinc_le n).trans ((abs_sub _ _).trans
            (by linarith [hb (dyadicPt T k (n + 1)), hb (dyadicPt T k n)])))
      · have h0 : Z (n + 1) ω - Z n ω = 0 := by
          dsimp only [Z]; rw [stopped_gridHit_sub_eq]; simp [hn]
        simpa only [h0, abs_zero, add_zero] using ih
  refine (Finset.sum_le_sum (g := fun i ↦ (gridOsc W T k ω : ℝ) * |Z (i + 1) ω - Z i ω|)
    fun i hi ↦ ?_).trans ?_
  · have hi_osc : |Z (i + 1) ω - Z i ω| ≤ (gridOsc W T k ω : ℝ) := (hinc_le i).trans <| by
      simpa only [gridOsc, Real.norm_eq_abs, coe_nnNorm] using NNReal.coe_le_coe.2
        (Finset.le_sup (f := fun j ↦ ‖W (dyadicPt T k (j + 1)) ω - W (dyadicPt T k j) ω‖₊) hi)
    rw [← sq_abs]; simpa only [sq] using mul_le_mul_of_nonneg_right hi_osc (abs_nonneg _)
  · rw [← Finset.mul_sum, mul_comm]
    exact mul_le_mul_of_nonneg_right (hsum_le _) (NNReal.coe_nonneg _)

end DyadicHelpers

section RealEngine

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}

private theorem stronglyMeasurable_gridVar {W : ℝ≥0 → Ω → ℝ}
    (hW : StronglyAdapted ℱ W) (T : ℝ≥0) (k j : ℕ) :
    StronglyMeasurable[ℱ (dyadicPt T k j)] (gridVar W T k j) := by
  let : MeasurableSpace Ω := ℱ (dyadicPt T k j)
  convert Finset.stronglyMeasurable_sum (Finset.range j) (fun i hi ↦ by
    have hij : i + 1 ≤ j := Nat.succ_le_of_lt (Finset.mem_range.1 hi)
    exact (((hW _).mono (ℱ.mono (dyadicPt_mono T k hij))).sub
      ((hW _).mono (ℱ.mono (dyadicPt_mono T k (i.le_succ.trans hij))))).norm) using 1
  ext ω; simp [gridVar, Finset.sum_apply, Real.norm_eq_abs]

private theorem isStoppingTime_gridHit {W : ℝ≥0 → Ω → ℝ}
    (hW : StronglyAdapted ℱ W) (T : ℝ≥0) (k M : ℕ) :
    IsStoppingTime (ℱ.comp (dyadicPt_mono T k)) (gridHit W T k M) :=
  Adapted.isStoppingTime_hittingAfter (fun j ↦ ((stronglyMeasurable_gridVar hW T k j).mono
    (Filtration.comp_apply (ℱ := ℱ) (hτ := dyadicPt_mono T k) j).ge).measurable) measurableSet_Ioi

private theorem aestronglyMeasurable_mul_gridOsc {W : ℝ≥0 → Ω → ℝ}
    (hW : Martingale W ℱ P) (C : ℝ) (T : ℝ≥0) (k M : ℕ) :
    AEStronglyMeasurable (fun ω ↦ ((M : ℝ) + 2 * C) * (gridOsc W T k ω : ℝ)) P :=
  ((stronglyMeasurable_gridOsc (fun t ↦ (hW.stronglyAdapted t).mono (ℱ.le t)) T k).const_mul
    ((M : ℝ) + 2 * C)).aestronglyMeasurable

private theorem ae_norm_mul_gridOsc_le {W : ℝ≥0 → Ω → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂P, ∀ t, |W t ω| ≤ C) (T : ℝ≥0) (k M : ℕ) :
    ∀ᵐ ω ∂P, ‖((M : ℝ) + 2 * C) * (gridOsc W T k ω : ℝ)‖ ≤ 2 * C * (M + 2 * C) :=
  hb.mono fun _ hω ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm (2 * C)]
    exact mul_le_mul_of_nonneg_left (gridOsc_le_two_mul hC hω) (by positivity)

variable [IsFiniteMeasure P]

private theorem martingale_stopped_gridHit {W : ℝ≥0 → Ω → ℝ}
    (hW : Martingale W ℱ P) (T : ℝ≥0) (k M : ℕ) :
    Martingale (stoppedProcess (fun j ↦ W (dyadicPt T k j)) (gridHit W T k M))
      (ℱ.comp (dyadicPt_mono T k)) P :=
  (hW.comp (dyadicPt_mono T k)).stoppedProcess_of_countable_range
    (isStoppingTime_gridHit hW.stronglyAdapted T k M) (to_countable _)

private theorem memLp_stopped_gridHit {W : ℝ≥0 → Ω → ℝ}
    (hW : Martingale W ℱ P) {C : ℝ} (hb : ∀ᵐ ω ∂P, ∀ t, |W t ω| ≤ C) (T : ℝ≥0) (k M j : ℕ) :
    MemLp (stoppedProcess (fun i ↦ W (dyadicPt T k i)) (gridHit W T k M) j) 2 P :=
  memLp_of_bounded (a := -C) (b := C)
    (hb.mono fun _ hω ↦ stoppedProcess_mem (s := Icc (-C) C) (fun _ _ ↦ abs_le.1 (hω _)) j)
    (((martingale_stopped_gridHit hW T k M).stronglyAdapted j).mono
      ((ℱ.comp (dyadicPt_mono T k)).le j)).aestronglyMeasurable 2

private theorem integral_stopped_gridHit_sq_le {W : ℝ≥0 → Ω → ℝ}
    (hW : Martingale W ℱ P) (hW0 : ∀ ω, W 0 ω = 0) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂P, ∀ t, |W t ω| ≤ C) (T : ℝ≥0) (k M : ℕ) :
    ∫ ω, stoppedProcess (fun j ↦ W (dyadicPt T k j)) (gridHit W T k M) (2 ^ k) ω ^ 2 ∂P ≤
      ∫ ω, ((M : ℝ) + 2 * C) * (gridOsc W T k ω : ℝ) ∂P := by
  let Z := stoppedProcess (fun j ↦ W (dyadicPt T k j)) (gridHit W T k M)
  have hZ : Martingale Z (ℱ.comp (dyadicPt_mono T k)) P := martingale_stopped_gridHit hW T k M
  have hZbdd (j : ℕ) : MemLp (Z j) 2 P := memLp_stopped_gridHit hW hb T k M j
  have hZ0 : ∫ ω, Z 0 ω ^ 2 ∂P = 0 := by
    have h0 (ω : Ω) : Z 0 ω = 0 :=
      (congr_fun (stoppedProcess_bot (fun j ↦ W (dyadicPt T k j)) (gridHit W T k M)) ω).trans
        (by simp [dyadicPt, hW0 ω])
    simp [h0]
  have htele := hZ.sum_integral_sq_sub (g := id) (n := 2 ^ k) (monotone_id.monotoneOn _) (hZbdd _)
  have hint (i : ℕ) : Integrable (fun ω ↦ (Z (i + 1) ω - Z i ω) ^ 2) P :=
    ((hZbdd _).sub (hZbdd _)).integrable_sq
  have hg_int : Integrable (fun ω ↦ ((M : ℝ) + 2 * C) * (gridOsc W T k ω : ℝ)) P :=
    (integrable_const _).mono' (aestronglyMeasurable_mul_gridOsc hW C T k M)
      (ae_norm_mul_gridOsc_le hC hb T k M)
  simp only [id_eq, hZ0, sub_zero] at htele
  rw [← htele, ← integral_finsetSum (Finset.range (2 ^ k)) fun i _ ↦ hint i]
  exact integral_mono_ae (integrable_finsetSum (Finset.range (2 ^ k)) fun i _ ↦ hint i)
    hg_int (hb.mono fun _ hω ↦ stopped_gridHit_sq_sum_le hC hω)

private theorem integral_indicator_sq_le_stopped_gridHit {W : ℝ≥0 → Ω → ℝ}
    (hW : Martingale W ℱ P) {C : ℝ} (hb : ∀ᵐ ω ∂P, ∀ t, |W t ω| ≤ C) (T : ℝ≥0) (k M : ℕ) :
    ∫ ω, (⋂ m : ℕ, {ω' | gridVar W T m (2 ^ m) ω' ≤ M}).indicator (fun ω' ↦ W T ω' ^ 2) ω ∂P ≤
      ∫ ω, stoppedProcess (fun j ↦ W (dyadicPt T k j)) (gridHit W T k M) (2 ^ k) ω ^ 2 ∂P := by
  refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ indicator_nonneg (fun _ _ ↦ sq_nonneg _) _)
    (memLp_stopped_gridHit hW hb T k M (2 ^ k)).integrable_sq (ae_of_all _ fun ω ↦ ?_)
  by_cases hω : ω ∈ ⋂ m : ℕ, {ω' | gridVar W T m (2 ^ m) ω' ≤ M}
  · have hle : WithTop.some (2 ^ k) ≤ gridHit W T k M ω :=
      (not_le.1 (mt gridHit_le_iff.1 (mem_iInter.1 hω k).not_gt)).le
    have hEq : stoppedProcess (fun j ↦ W (dyadicPt T k j)) (gridHit W T k M) (2 ^ k) ω = W T ω := by
      rw [stoppedProcess_eq_of_le hle]; simp [dyadicPt, pow_ne_zero k (two_ne_zero : (2 : ℝ≥0) ≠ 0)]
    simp [hω, hEq]
  · simp [hω, sq_nonneg]

private theorem ae_eq_zero_of_bounded_centered_real_martingale {W : ℝ≥0 → Ω → ℝ}
    (hW : Martingale W ℱ P) (hW0 : ∀ ω, W 0 ω = 0) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂P, ∀ t, |W t ω| ≤ C) (hc : ∀ᵐ ω ∂P, Continuous (W · ω))
    (T : ℝ≥0) (hbv : ∀ᵐ ω ∂P, BoundedVariationOn (W · ω) (Icc 0 T)) :
    W T =ᵐ[P] 0 := by
  have hWT_L2 : MemLp (W T) 2 P :=
    memLp_of_bounded (a := -C) (b := C) (hb.mono fun ω hω ↦ abs_le.1 (hω T))
      ((hW.stronglyAdapted T).mono (ℱ.le T)).aestronglyMeasurable 2
  -- Step 1: On the event `E_M` where every dyadic grid variation stays below `M`, `W T = 0` a.e.
  have hM_zero (M : ℕ) :
      (⋂ k : ℕ, {ω | gridVar W T k (2 ^ k) ω ≤ M}).indicator (fun ω ↦ W T ω ^ 2) =ᵐ[P] 0 := by
    let E : Set Ω := ⋂ k : ℕ, {ω | gridVar W T k (2 ^ k) ω ≤ M}
    -- Dominated convergence sends the oscillation majorant `(M + 2 C) * gridOsc` to `0` in `L¹`.
    have hg_lim : Tendsto (fun k ↦ ∫ ω, ((M : ℝ) + 2 * C) * (gridOsc W T k ω : ℝ) ∂P)
        atTop (𝓝 0) := by
      simpa only [integral_const, smul_zero] using
        tendsto_integral_of_dominated_convergence
          (F := fun k ω ↦ ((M : ℝ) + 2 * C) * (gridOsc W T k ω : ℝ)) (fun _ ↦ 2 * C * (M + 2 * C))
          (fun k ↦ aestronglyMeasurable_mul_gridOsc hW C T k M) (integrable_const _)
          (fun k ↦ ae_norm_mul_gridOsc_le hC hb T k M) (f := fun _ ↦ (0 : ℝ))
          (hc.mono fun _ hω ↦ by
            simpa only [mul_zero] using (tendsto_gridOsc (T := T) hω).const_mul ((M : ℝ) + 2 * C))
    -- Compare the `E`-restricted square against the stopped dyadic martingale and pass to `k → ∞`.
    have hE : MeasurableSet E := MeasurableSet.iInter fun k ↦ measurableSet_le
      ((stronglyMeasurable_gridVar hW.stronglyAdapted T k (2 ^ k)).mono (ℱ.le _)).measurable
      measurable_const
    refine (integral_eq_zero_iff_of_nonneg (fun _ ↦ indicator_nonneg (fun _ _ ↦ sq_nonneg _) _)
      (hWT_L2.integrable_sq.indicator hE)).1 (le_antisymm (ge_of_tendsto' hg_lim fun k ↦
        (integral_indicator_sq_le_stopped_gridHit hW hb T k M).trans
          (integral_stopped_gridHit_sq_le hW hW0 hC hb T k M))
        (integral_nonneg fun _ ↦ indicator_nonneg (fun _ _ ↦ sq_nonneg _) _))
  -- Step 2: Exhaust almost every finite-variation path by the countable union of events `E_M`.
  filter_upwards [hbv, ae_all_iff.2 hM_zero] with ω hbvω h0ω
  obtain ⟨M, hM⟩ := ENNReal.exists_nat_gt hbvω
  have hmem : ω ∈ ⋂ k : ℕ, {ω' | gridVar W T k (2 ^ k) ω' ≤ M} := mem_iInter.2 fun k ↦ by
    have hofReal : ENNReal.ofReal (gridVar W T k (2 ^ k) ω) ≤ M :=
      (le_trans (by
        rw [gridVar, ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ abs_nonneg _]
        exact Finset.sum_le_sum fun _ _ ↦ by simp [edist_dist, Real.dist_eq])
        (eVariationOn.sum_le (f := (W · ω)) (s := Icc 0 T) (n := 2 ^ k)
          (dyadicPt_mono T k) (dyadicPt_mem_Icc T k))).trans hM.le
    simpa using (ENNReal.ofReal_le_iff_le_toReal (ENNReal.natCast_ne_top M)).1 hofReal
  exact sq_eq_zero_iff.1 (by simpa [hmem] using h0ω M)

private theorem indist_const_real_localMartingale {M : ℝ≥0 → Ω → ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P) (hc : ∀ᵐ ω ∂P, Continuous (M · ω))
    (hbv : ∀ T : ℝ≥0, ∀ᵐ ω ∂P, BoundedVariationOn (M · ω) (Icc 0 T)) :
    M ≡ᵐ[P] fun _ ↦ M 0 := by
  obtain ⟨ρ, hρ, hmart, hbound⟩ := exists_isLocalizingSequence_bounded_martingale hM hc
  let Z (n : ℕ) := stoppedProcess (fun t ↦ {ω | 0 < ρ n ω}.indicator (M t)) (ρ n)
  have hZpath (n : ℕ) (ω : Ω) :
      (Z n · ω) = if 0 < ρ n ω then (stoppedProcess M (ρ n) · ω) else 0 := by
    ext t; dsimp only [Z]; rw [stoppedProcess_indicator_comm]
    by_cases hpos : 0 < ρ n ω <;> simp [hpos]
  have hZconst (n : ℕ) : (fun t ω ↦ Z n t ω - Z n 0 ω) ≡ᵐ[P] 0 := by
    let W (t : ℝ≥0) (ω : Ω) := Z n t ω - Z n 0 ω
    have hW : Martingale W ℱ P := (hmart n).sub
      (martingale_const_fun ℱ P ((hmart n).stronglyMeasurable 0) ((hmart n).integrable 0))
    have hcW : ∀ᵐ ω ∂P, Continuous (W · ω) := hc.mono fun ω hω ↦
      Continuous.sub (by rw [hZpath n ω]; split_ifs; exacts [hω.stoppedProcess, continuous_const])
        continuous_const
    refine TauCeti.indist_of_forall_ae_eq hcW (ae_of_all _ fun _ ↦ continuous_const)
      fun T ↦ ae_eq_zero_of_bounded_centered_real_martingale hW (fun _ ↦ sub_self _)
        (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
        (hbound.mono fun ω hω t ↦ by simpa only [W, Real.norm_eq_abs] using (hω n t).1)
        hcW T ((hbv T).mono fun ω hω ↦ ?_)
    refine (LipschitzWith.id.sub (LipschitzWith.const (Z n 0 ω))).comp_boundedVariationOn
      (g := (Z n · ω)) ?_
    rw [hZpath n ω]; split_ifs
    exacts [hω.stoppedProcess_Icc, TauCeti.boundedVariationOn_const 0 (Icc 0 T)]
  filter_upwards [hρ.tendsto_top, ae_all_iff.2 hZconst] with ω htop hZω t
  obtain ⟨n, hn⟩ := (htop.eventually (eventually_gt_nhds (WithTop.coe_lt_top t))).exists
  have hpos : 0 < ρ n ω := lt_of_le_of_lt (WithTop.coe_le_coe.2 bot_le) hn
  have hZeq (r : ℝ≥0) (hr : (r : WithTop ℝ≥0) ≤ ρ n ω) : Z n r ω = M r ω := by
    dsimp only [Z]; rw [stoppedProcess_eq_of_le hr]; simp [hpos]
  have h0 : Z n t ω - Z n 0 ω = 0 := hZω n t
  linarith [hZeq t hn.le, hZeq 0 ((WithTop.coe_le_coe.2 bot_le).trans hn.le)]

end RealEngine

section BanachSpace

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → E}

/-- Under a finite measure, any almost-surely continuous Banach-valued native local martingale on
`ℝ≥0` whose paths have bounded variation on every compact interval `[0, T]` is indistinguishable
from its initial value. -/
theorem indist_const_of_boundedVariationOn
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P) (hc : ∀ᵐ ω ∂P, Continuous (M · ω))
    (hbv : ∀ T : ℝ≥0, ∀ᵐ ω ∂P, BoundedVariationOn (M · ω) (Icc 0 T)) :
    M ≡ᵐ[P] fun _ ↦ M 0 := by
  obtain ⟨Y, hY, hYM⟩ := hM.exists_stronglyAdapted_ae_eq fun _ h ↦ h.stronglyAdapted
  refine TauCeti.indist_of_forall_ae_eq hc (ae_of_all _ fun _ ↦ continuous_const) fun t ↦ ?_
  have hsep : TopologicalSpace.IsSeparable (range (Y t - Y 0)) :=
    ((hY t).sub ((hY 0).mono (ℱ.mono bot_le))).isSeparable_range
  refine (ae_eq_zero_of_forall_dual_of_isSeparable ℝ hsep (fun L ↦ ?_)
    (hYM.mono fun ω hω ↦ ⟨ω, by simp [hω t, hω 0]⟩)).mono fun _ ↦ sub_eq_zero.1
  exact ((indist_const_real_localMartingale (L.comp_locally_martingale hM)
    (hc.mono fun _ hω ↦ L.continuous.comp hω)
    fun T ↦ (hbv T).mono fun _ hω ↦ L.lipschitzWith.comp_boundedVariationOn hω).ae_eq_eval t).mono
    fun _ hω ↦ by simpa [map_sub, sub_eq_zero] using hω

/-- A Banach-valued almost-surely continuous native local martingale with almost-surely locally
bounded variation paths on `Set.univ` is indistinguishable from its initial value. -/
theorem indist_const_of_locallyBoundedVariationOn
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P) (hc : ∀ᵐ ω ∂P, Continuous (M · ω))
    (hbv : ∀ᵐ ω ∂P, LocallyBoundedVariationOn (M · ω) univ) :
    M ≡ᵐ[P] fun _ ↦ M 0 :=
  hM.indist_const_of_boundedVariationOn hc fun T ↦ hbv.mono fun _ h ↦ by
    simpa only [univ_inter] using h 0 T (mem_univ _) (mem_univ _)

/-- A Banach-valued almost-surely continuous native local martingale of locally bounded variation
starting at zero almost surely is indistinguishable from zero. -/
theorem indist_zero_of_locallyBoundedVariationOn
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P) (hc : ∀ᵐ ω ∂P, Continuous (M · ω))
    (hbv : ∀ᵐ ω ∂P, LocallyBoundedVariationOn (M · ω) univ) (h0 : M 0 =ᵐ[P] 0) :
    M ≡ᵐ[P] 0 := by
  filter_upwards [hM.indist_const_of_locallyBoundedVariationOn hc hbv, h0] with _ hω h0ω t
  simpa [h0ω] using hω t

/-- **Uniqueness of continuous finite-variation compensators.** If `A` and `A'` are strongly
progressive, almost-surely continuous, locally bounded-variation processes agreeing almost surely at
time `0`, such that `X - A` and `X - A'` are native local martingales for an almost-surely
continuous process `X`, then `A` and `A'` are indistinguishable. -/
theorem indist_sub_right_of_locallyBoundedVariationOn {X A A' : ℝ≥0 → Ω → E}
    (hXA : Locally (fun Y ↦ Martingale Y ℱ P) ℱ (X - A) P)
    (hXA' : Locally (fun Y ↦ Martingale Y ℱ P) ℱ (X - A') P)
    (hAprog : IsStronglyProgressive ℱ A) (hA'prog : IsStronglyProgressive ℱ A')
    (hcX : ∀ᵐ ω ∂P, Continuous (X · ω))
    (hcA : ∀ᵐ ω ∂P, Continuous (A · ω)) (hcA' : ∀ᵐ ω ∂P, Continuous (A' · ω))
    (hbvA : ∀ᵐ ω ∂P, LocallyBoundedVariationOn (A · ω) univ)
    (hbvA' : ∀ᵐ ω ∂P, LocallyBoundedVariationOn (A' · ω) univ)
    (h0 : A 0 =ᵐ[P] A' 0) : A ≡ᵐ[P] A' := by
  have hdiff_loc : Locally (fun U ↦ Martingale U ℱ P) ℱ (A' - A) P :=
    (hA'prog.sub hAprog).locally_martingale_of_indist_sub hXA hXA'
      ((hcX.and hcA).mono fun _ h ↦ h.1.sub h.2) ((hcX.and hcA').mono fun _ h ↦ h.1.sub h.2)
      (.of_forall fun _ _ ↦ by dsimp only [Pi.sub_apply]; abel)
  exact (hdiff_loc.indist_zero_of_locallyBoundedVariationOn
    ((hcA'.and hcA).mono fun _ h ↦ h.1.sub h.2) ((hbvA'.and hbvA).mono fun _ h ↦ h.1.sub h.2)
    (h0.mono fun _ hω ↦ by simp [hω])).mono fun _ hω t ↦ (sub_eq_zero.1 (hω t)).symm

end BanachSpace

section RealMonotone

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {ℱ : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

/-- An almost-surely continuous real native local martingale with almost-surely monotone paths is
indistinguishable from its initial value. -/
theorem indist_const_of_ae_monotone (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hc : ∀ᵐ ω ∂P, Continuous (M · ω)) (hmono : ∀ᵐ ω ∂P, Monotone (M · ω)) :
    M ≡ᵐ[P] fun _ ↦ M 0 :=
  hM.indist_const_of_locallyBoundedVariationOn hc
    (hmono.mono fun _ h ↦ (h.monotoneOn univ).locallyBoundedVariationOn)

/-- An almost-surely continuous real native local martingale with almost-surely antitone paths is
indistinguishable from its initial value. -/
theorem indist_const_of_ae_antitone (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hc : ∀ᵐ ω ∂P, Continuous (M · ω)) (hanti : ∀ᵐ ω ∂P, Antitone (M · ω)) :
    M ≡ᵐ[P] fun _ ↦ M 0 := by
  filter_upwards [hM.martingale_neg.indist_const_of_ae_monotone
    (hc.mono fun _ h ↦ h.neg) (hanti.mono fun _ h ↦ h.neg)] with _ hω t using neg_inj.1 (hω t)

end RealMonotone

end ProbabilityTheory.Locally

namespace MeasureTheory.Martingale

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → E}

/-- Under a finite measure, any almost-surely continuous Banach-valued martingale on `ℝ≥0` whose
paths have bounded variation on every compact interval `[0, T]` is indistinguishable from its
initial value. -/
theorem indist_const_of_boundedVariationOn (hM : Martingale M ℱ P)
    (hc : ∀ᵐ ω ∂P, Continuous (M · ω))
    (hbv : ∀ T : ℝ≥0, ∀ᵐ ω ∂P, BoundedVariationOn (M · ω) (Icc 0 T)) : M ≡ᵐ[P] fun _ ↦ M 0 :=
  (Locally.of_prop hM).indist_const_of_boundedVariationOn hc hbv

/-- A Banach-valued almost-surely continuous martingale of locally bounded variation starting at
zero almost surely is indistinguishable from zero. -/
theorem indist_zero_of_locallyBoundedVariationOn (hM : Martingale M ℱ P)
    (hc : ∀ᵐ ω ∂P, Continuous (M · ω)) (hbv : ∀ᵐ ω ∂P, LocallyBoundedVariationOn (M · ω) univ)
    (h0 : M 0 =ᵐ[P] 0) : M ≡ᵐ[P] 0 :=
  (Locally.of_prop hM).indist_zero_of_locallyBoundedVariationOn hc hbv h0

end MeasureTheory.Martingale
