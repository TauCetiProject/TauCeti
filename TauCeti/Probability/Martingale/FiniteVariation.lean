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
import TauCeti.Topology.Instances.NNReal

/-!
# Bounded continuous martingales of finite variation

A continuous real martingale with finite-variation paths is constant if its terminal values
have deterministic bounds on each finite horizon. No moment assumption on the random total
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

/-- A continuous finite-variation martingale on a compact interval with a deterministically
bounded terminal value has equal endpoint values almost surely. The variation itself need
not be integrable. -/
theorem ae_eq_of_boundedVariationOn_of_bound (hM : Martingale M ℱ P) {S T : ℝ≥0}
    (hST : S ≤ T) (hc : ∀ᵐ ω ∂P, ContinuousOn (M · ω) (Icc S T))
    (hv : ∀ᵐ ω ∂P, BoundedVariationOn (M · ω) (Icc S T))
    {C : ℝ} (hb : ∀ᵐ ω ∂P, |M T ω| ≤ C) : M T =ᵐ[P] M S := by
  -- Equal grids also cover degenerate intervals; the pathwise estimate allows arbitrary grids.
  choose u hu huS huT hmesh using fun k ↦ S.exists_monotone_grid T hST (k + 1) (by omega)
  have humem (k i : ℕ) (hi : i ≤ k + 1) : u k i ∈ Icc S T :=
    ⟨(huS k).symm.trans_le (hu k (Nat.zero_le i)), (hu k hi).trans_eq (huT k)⟩
  have hlim : Tendsto (fun k : ℕ ↦ ((T - S : ℝ≥0) : ℝ) / (k + 1 : ℕ)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  let Q (k : ℕ) (ω : Ω) := ∑ i ∈ range (k + 1),
    (M (u k (i + 1)) ω - M (u k i) ω) ^ 2
  -- Continuous finite-variation paths have vanishing quadratic sums, without a
  -- dominating integrable variation bound.
  have hQlim : ∀ᵐ ω ∂P, Tendsto (fun k ↦ Q k ω) atTop (𝓝 0) := by
    filter_upwards [hc, hv] with ω hc hv
    have huc := isCompact_Icc.uniformContinuousOn_of_continuous hc
    have h := huc.tendsto_sum_sub_mul_sub_of_boundedVariationOn
      hv (fun k ↦ (hu k).monotoneOn _) humem (fun k i _ ↦ hmesh k i) hlim
    simpa only [Q, pow_two] using h
  have hbound (k : ℕ) : ∫ ω, Q k ω ^ 2 ∂P ≤ 40 * C ^ 4 * P.real univ :=
    hM.integral_sq_sum_sq_sub_le ((hu k).monotoneOn _) (by simpa only [huT] using hb)
  have hp (p : ℝ≥0∞) (t : ℝ≥0) (ht : t ∈ Icc S T) : MemLp (M t) p P :=
    MemLp.of_bound ((hM.stronglyMeasurable t).mono (ℱ.le t)).aestronglyMeasurable C
      (hM.ae_norm_le_of_le ht.2 (by simpa only [Real.norm_eq_abs] using hb))
  have hQ₂ (k : ℕ) : MemLp (Q k) 2 P := by
    let : ENNReal.HolderTriple 4 4 2 := .of_toReal (by
      norm_num [Real.holderTriple_iff])
    apply memLp_finsetSum _
    intro i hi
    have hd := (hp 4 _ (humem k (i + 1) (mem_range.mp hi))).sub
      (hp 4 _ (humem k i (mem_range.mp hi).le))
    simpa only [pow_two, Pi.sub_def] using hd.fun_mul hd
  -- The moment bound replaces domination by the random variation.
  have hmean := TauCeti.tendsto_integral_zero_of_integral_sq_le hQ₂ hbound hQlim
  -- Isometry makes every quadratic-sum expectation the same terminal second moment.
  have heq (k : ℕ) : ∫ ω, Q k ω ∂P = ∫ ω, (M T ω - M S ω) ^ 2 ∂P := by
    simpa only [Q, huS, huT] using
      hM.integral_sum_sq_sub ((hu k).monotoneOn _) (hp 2 _ (humem k _ le_rfl))
  have hzero : ∫ ω, (M T ω - M S ω) ^ 2 ∂P = 0 :=
    tendsto_nhds_unique tendsto_const_nhds (hmean.congr (fun k ↦ heq k))
  have hz := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun ω ↦ sq_nonneg (M T ω - M S ω))
    (by simpa only [Pi.sub_def] using
      ((hp 2 T ⟨hST, le_rfl⟩).sub (hp 2 S ⟨le_rfl, hST⟩)).integrable_sq)).1 hzero
  filter_upwards [hz] with ω hω
  exact sub_eq_zero.mp (by simpa only [Pi.zero_apply, sq_eq_zero_iff] using hω)

/-- A continuous martingale with locally finite variation and deterministic bounds on
its value at each finite horizon is indistinguishable from its initial value. Neither usual
conditions nor moments of the path variation are required. -/
theorem indist_initial_of_boundedVariationOn_of_bound (hM : Martingale M ℱ P)
    (hc : ∀ᵐ ω ∂P, Continuous (M · ω))
    (hv : ∀ T : ℝ≥0, ∀ᵐ ω ∂P, BoundedVariationOn (M · ω) (Icc 0 T))
    (hb : ∀ T : ℝ≥0, ∃ C : ℝ, ∀ᵐ ω ∂P, |M T ω| ≤ C) :
    M ≡ᵐ[P] (fun _ ↦ M 0) := by
  have heq (t : ℝ≥0) : M t =ᵐ[P] M 0 := by
    obtain ⟨C, hb⟩ := hb t
    exact hM.ae_eq_of_boundedVariationOn_of_bound (S := 0) (T := t) (by positivity)
      (hc.mono fun _ h ↦ h.continuousOn) (hv t) hb
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq ℝ≥0
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, M (u n) ω = M 0 ω := ae_all_iff.2 fun n ↦ heq (u n)
  filter_upwards [hc, hall] with ω hc hω t
  exact hu.induction_on t (isClosed_eq hc continuous_const) hω

end MeasureTheory.Martingale
