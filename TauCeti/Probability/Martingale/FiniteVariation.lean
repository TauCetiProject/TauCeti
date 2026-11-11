/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.QuadraticSums
public import Mathlib.Probability.Process.Indistinguishable
public import TauCeti.Analysis.BoundedVariation.QuadraticSums
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.MeasureTheory.Function.DeLaValleePoussin
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Bounded continuous martingales of finite variation

A continuous real martingale with finite-variation paths is constant if its values have a
deterministic bound on each finite horizon. No moment assumption on the random total
variation is imposed. This is the bounded-stage rigidity argument used in uniqueness of
continuous quadratic variation; it does not assert a localization theorem for arbitrary
local martingales.

Quadratic sums vanish pathwise by continuity and finite variation. Their partition-independent
second-moment bound gives uniform integrability, so their expectations vanish as well. The
discrete martingale isometry then forces every increment to vanish. Continuity upgrades
fixed-time equality to indistinguishability on the original filtration.

## References

* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Chapter IV, §1.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set Finset
open scoped Topology NNReal ENNReal

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {ℱ : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

/-- At a finite horizon a bounded continuous finite-variation martingale equals its initial
value almost surely. The variation itself need not be integrable. -/
theorem ae_eq_initial_of_boundedVariationOn_of_bound (hM : Martingale M ℱ P) (T : ℝ≥0)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (M · ω) (Icc 0 T))
    (hv : ∀ᵐ ω ∂P, BoundedVariationOn (M · ω) (Icc 0 T))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, |M t ω| ≤ C) :
    M T =ᵐ[P] M 0 := by
  -- Use equal grids, including the zero-horizon case. Only these deterministic grids
  -- are selected here; the pathwise variation estimate itself allows arbitrary grids.
  let u (k i : ℕ) : ℝ≥0 := i * T / (k + 1 : ℕ)
  have hu (k : ℕ) : Monotone (u k) := by
    intro i j hij
    dsimp [u]
    gcongr
  have hu0 (k : ℕ) : u k 0 = 0 := by simp [u]
  have huT (k : ℕ) : u k (k + 1) = T := by
    dsimp [u]
    field_simp
  have humem (k i : ℕ) (hi : i ≤ k + 1) : u k i ∈ Icc 0 T :=
    ⟨by positivity, (hu k hi).trans_eq (huT k)⟩
  have hmesh (k i : ℕ) (_hi : i < k + 1) :
      dist (u k (i + 1)) (u k i) ≤ (T : ℝ) / (k + 1 : ℕ) := by
    rw [NNReal.dist_eq]
    simp only [u, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast]
    push_cast
    have he : (i + 1 : ℝ) * T / (k + 1) - i * T / (k + 1) = T / (k + 1) := by ring
    rw [he, abs_of_nonneg (by positivity)]
  have hlim : Tendsto (fun k : ℕ ↦ (T : ℝ) / (k + 1 : ℕ)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  let Q (k : ℕ) (ω : Ω) := ∑ i ∈ range (k + 1),
    (M (u k (i + 1)) ω - M (u k i) ω) ^ 2
  have hm (k : ℕ) : AEStronglyMeasurable (Q k) P := by
    exact Finset.aestronglyMeasurable_fun_sum (range (k + 1)) fun i _ ↦
      ((((hM.stronglyMeasurable (u k (i + 1))).mono (ℱ.le _)).sub
        ((hM.stronglyMeasurable (u k i)).mono (ℱ.le _))).pow 2).aestronglyMeasurable
  -- Continuous finite-variation paths have vanishing quadratic sums, without a
  -- dominating integrable variation bound.
  have hQlim : ∀ᵐ ω ∂P, Tendsto (fun k ↦ Q k ω) atTop (𝓝 0) := by
    filter_upwards [hc, hv] with ω hc hv
    have huc := isCompact_Icc.uniformContinuousOn_of_continuous hc
    have h := huc.tendsto_sum_sub_mul_sub_of_boundedVariationOn
      hv (fun k ↦ (hu k).monotoneOn _) humem hmesh hlim
    simpa only [Q, pow_two] using h
  have hbound (k : ℕ) : ∫ ω, Q k ω ^ 2 ∂P ≤ 40 * C ^ 4 * P.real univ :=
    hM.integral_sq_sum_sq_sub_le ((hu k).monotoneOn _) hC
      (hb.mono fun ω hω i hi ↦ hω _ (humem k i hi))
  have hp (p : ℝ≥0∞) (t : ℝ≥0) (ht : t ∈ Icc 0 T) : MemLp (M t) p P :=
    MemLp.of_bound ((hM.stronglyMeasurable t).mono (ℱ.le t)).aestronglyMeasurable C
      (hb.mono fun ω hω ↦ by simpa only [Real.norm_eq_abs] using hω t ht)
  have hQ₂ (k : ℕ) : MemLp (Q k) 2 P := by
    let : ENNReal.HolderTriple 4 4 2 := .of_toReal (by
      norm_num [Real.holderTriple_iff])
    apply memLp_finsetSum _
    intro i hi
    have hd := (hp 4 _ (humem k (i + 1) (mem_range.mp hi))).sub
      (hp 4 _ (humem k i (mem_range.mp hi).le))
    simpa only [pow_two, Pi.sub_def] using hd.fun_mul hd
  -- The discrete fourth-moment bound replaces domination by the random variation.
  -- Apply the existing de la Vallée Poussin criterion and Vitali convergence.
  have hUI : UnifIntegrable Q 1 P := by
    apply TauCeti.unifIntegrable_of_lintegral_ofReal_le
      (Φ := fun x : ℝ ↦ x ^ 2) (C := ENNReal.ofReal (40 * C ^ 4 * P.real univ))
      (by
        have he : (fun x : ℝ ↦ x ^ 2 / x) =ᶠ[atTop] fun x ↦ x := by
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
          field_simp
        exact tendsto_id.congr' he.symm)
      hm ENNReal.ofReal_ne_top
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal
      (by simpa only [Real.norm_eq_abs, sq_abs] using (hQ₂ k).integrable_sq)
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)]
    simpa only [Real.norm_eq_abs, sq_abs] using ENNReal.ofReal_le_ofReal (hbound k)
  have hL1 := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hm
    (MemLp.zero : MemLp (0 : Ω → ℝ) 1 P) hUI hQlim
  have hmean : Tendsto (fun k ↦ ∫ ω, Q k ω ∂P) atTop (𝓝 0) := by
    have h := tendsto_integral_of_L1 (0 : Ω → ℝ) aestronglyMeasurable_zero
      (Eventually.of_forall fun k ↦ (hQ₂ k).integrable (by norm_num))
      (by simpa only [sub_zero, Pi.zero_apply, eLpNorm_one_eq_lintegral_enorm (hm _)] using hL1)
    simpa only [Pi.zero_apply, integral_zero] using h
  -- Isometry makes every quadratic-sum expectation the same terminal second moment.
  have heq (k : ℕ) : ∫ ω, Q k ω ∂P = ∫ ω, (M T ω - M 0 ω) ^ 2 ∂P := by
    simpa only [Q, hu0, huT] using
      hM.integral_sum_sq_sub ((hu k).monotoneOn _) (fun i hi ↦ hp 2 _ (humem k i hi))
  have hzero : ∫ ω, (M T ω - M 0 ω) ^ 2 ∂P = 0 :=
    tendsto_nhds_unique tendsto_const_nhds (hmean.congr (fun k ↦ heq k))
  have hz := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun ω ↦ sq_nonneg (M T ω - M 0 ω))
    (by simpa only [Pi.sub_def] using
      ((hp 2 T ⟨by positivity, le_rfl⟩).sub
        (hp 2 0 ⟨le_rfl, by positivity⟩)).integrable_sq)).1 hzero
  filter_upwards [hz] with ω hω
  exact sub_eq_zero.mp (by simpa only [Pi.zero_apply, sq_eq_zero_iff] using hω)

/-- A continuous martingale with locally finite variation and deterministic bounds on
finite horizons is indistinguishable from its initial value. Neither usual conditions nor
moments of the path variation are required. -/
theorem indist_initial_of_locally_boundedVariation_of_bound (hM : Martingale M ℱ P)
    (hc : ∀ᵐ ω ∂P, Continuous (M · ω))
    (hv : ∀ T : ℝ≥0, ∀ᵐ ω ∂P, BoundedVariationOn (M · ω) (Icc 0 T))
    (hb : ∀ T : ℝ≥0, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, |M t ω| ≤ C) :
    M ≡ᵐ[P] (fun _ ↦ M 0) := by
  have heq (t : ℝ≥0) : M t =ᵐ[P] M 0 := by
    obtain ⟨C, hC, hb⟩ := hb t
    exact hM.ae_eq_initial_of_boundedVariationOn_of_bound t
      (hc.mono fun _ h ↦ h.continuousOn) (hv t) hC hb
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq ℝ≥0
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, M (u n) ω = M 0 ω := ae_all_iff.2 fun n ↦ heq (u n)
  filter_upwards [hc, hall] with ω hc hω t
  exact hu.induction_on t (isClosed_eq hc continuous_const) hω

end MeasureTheory.Martingale
