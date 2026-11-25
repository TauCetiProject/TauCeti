/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Germ.HolomorphicRestrictions.Basic
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.PSeries

/-!
# Holomorphic restrictions to the closed unit disc do not form a closed algebra

Let `D` be the closed unit disc. The power series `F(z) = ∑ zⁿ / (n + 1)²` converges uniformly on
`D` by comparison with `∑ 1 / (n + 1)²`, so its restriction to `D` is a uniform limit of
polynomials, all of which lie in `O(D) = holomorphicRestrictions D`. But `F` is not the
restriction of a function holomorphic near `D`: such a function would be holomorphic on a disc of
radius `R > 1`, and its Taylor series at `0`, which is the series of `F`, would have radius of
convergence at least `R`, while the ratio test gives the radius `1`. Hence `O(D)` is not closed in
`C(D, ℂ)` (`not_isClosed_holomorphicRestrictions_closedBall`). The function `F` is continuous on
`D` and holomorphic on its interior, so it also separates `O(D)` from the functions that are merely
holomorphic on the interior of `D`
(`exists_mem_holomorphicFunctions_interior_notMem_holomorphicRestrictions_closedBall`).

Together with `TauCeti.not_isOpen_holomorphicRestrictions` this shows that `O(K)` need be neither
open nor closed in `C(K, ℂ)` for compact `K`.

## Main results

* `TauCeti.not_isClosed_holomorphicRestrictions_closedBall`: `O(D)` is not closed in `C(D, ℂ)`.
* `TauCeti.exists_mem_holomorphicFunctions_interior_notMem_holomorphicRestrictions_closedBall`:
  a continuous function on `D`, holomorphic on the interior of `D`, need not lie in `O(D)`.
-/

public noncomputable section

open Filter Set Topology TopologicalSpace Metric FormalMultilinearSeries

namespace TauCeti

/-- The coefficients `1 / (n + 1)²` of the example series. -/
private def invSqCoeff (n : ℕ) : ℂ := (((n + 1 : ℕ) : ℂ) ^ 2)⁻¹

private theorem norm_invSqCoeff (n : ℕ) : ‖invSqCoeff n‖ = (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
  simp only [invSqCoeff, norm_inv, norm_pow, Complex.norm_natCast]

private theorem summable_norm_invSqCoeff : Summable fun n ↦ ‖invSqCoeff n‖ := by
  simp_rw [norm_invSqCoeff]
  exact (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr one_lt_two)

/-- The ratio test: the series `∑ zⁿ / (n + 1)²` has radius of convergence `1`. -/
private theorem radius_ofScalars_invSqCoeff : (ofScalars ℂ invSqCoeff).radius = 1 := by
  have hlim : Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) + 1)) ^ 2) atTop (𝓝 1) := by
    simpa using ((tendsto_natCast_div_add_atTop (1 : ℝ)).comp (tendsto_add_atTop_nat 1)).pow 2
  have hc : Tendsto (fun n ↦ ‖invSqCoeff n.succ‖ / ‖invSqCoeff n‖) atTop
      (𝓝 ((1 : NNReal) : ℝ)) := by
    refine hlim.congr fun n ↦ ?_
    rw [norm_invSqCoeff, norm_invSqCoeff, div_pow, inv_div_inv]
    push_cast
    ring
  simpa using ofScalars_radius_eq_inv_of_tendsto ℂ invSqCoeff one_ne_zero hc

/-- The series `∑ zⁿ / (n + 1)²` represents its sum on the open unit disc. -/
private theorem hasFPowerSeriesOnBall_invSqCoeff :
    HasFPowerSeriesOnBall (ofScalarsSum invSqCoeff) (ofScalars ℂ invSqCoeff) 0 1 := by
  have h := (ofScalars ℂ invSqCoeff).hasFPowerSeriesOnBall (by simp [radius_ofScalars_invSqCoeff])
  rwa [radius_ofScalars_invSqCoeff] at h

/-- The partial sums of `∑ zⁿ / (n + 1)²` converge uniformly on the closed unit disc. -/
private theorem tendstoUniformlyOn_invSqCoeff :
    TendstoUniformlyOn (fun N z ↦ ∑ n ∈ Finset.range N, invSqCoeff n • z ^ n)
      (ofScalarsSum invSqCoeff) atTop (closedBall (0 : ℂ) 1) := by
  rw [ofScalarsSum_eq_tsum]
  refine tendstoUniformlyOn_tsum_nat summable_norm_invSqCoeff fun n z hz ↦ ?_
  rw [norm_smul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (by simpa using hz))

/-- The sum of `∑ zⁿ / (n + 1)²` is holomorphic on the open unit disc. -/
private theorem differentiableOn_ofScalarsSum_invSqCoeff :
    DifferentiableOn ℂ (ofScalarsSum invSqCoeff) (ball (0 : ℂ) 1) := by
  intro z hz
  refine (hasFPowerSeriesOnBall_invSqCoeff.analyticAt_of_mem ?_).differentiableAt
    |>.differentiableWithinAt
  rwa [← ENNReal.ofReal_one, Metric.eball_ofReal]

/-- The sum of `∑ zⁿ / (n + 1)²` is not the restriction to the closed unit disc of a function
holomorphic on an open set containing it. -/
private theorem not_exists_differentiableOn_eq_ofScalarsSum_invSqCoeff :
    ¬∃ (U : Set ℂ) (g : ℂ → ℂ), IsOpen U ∧ closedBall (0 : ℂ) 1 ⊆ U ∧
      DifferentiableOn ℂ g U ∧ ∀ z ∈ closedBall (0 : ℂ) 1, g z = ofScalarsSum invSqCoeff z := by
  rintro ⟨U, g, hU, hDU, hg, hgF⟩
  -- The function `g` is holomorphic on a closed disc of radius `R = δ + 1 > 1`.
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_cthickening_subset_open hU hDU
  rw [cthickening_closedBall hδ.le zero_le_one] at hδU
  set R : NNReal := (δ + 1).toNNReal
  have hR : (R : ℝ) = δ + 1 := Real.coe_toNNReal _ (by positivity)
  rw [← hR] at hδU
  have hq := (hg.mono hδU).hasFPowerSeriesOnBall (R := R)
    (by rw [← NNReal.coe_pos, hR]; positivity)
  -- Near `0` the function `g` is the sum of the example series, so it has that power series.
  have hp : HasFPowerSeriesAt g (ofScalars ℂ invSqCoeff) 0 := by
    refine hasFPowerSeriesOnBall_invSqCoeff.hasFPowerSeriesAt.congr ?_
    filter_upwards [closedBall_mem_nhds (0 : ℂ) one_pos] with z hz
    exact (hgF z hz).symm
  have hr := hq.r_le
  rw [← hp.eq_formalMultilinearSeries hq.hasFPowerSeriesAt, radius_ofScalars_invSqCoeff] at hr
  have : (R : ℝ) ≤ 1 := by exact_mod_cast hr
  linarith

/-- The polynomial partial sums of `∑ zⁿ / (n + 1)²` are entire. -/
private theorem differentiable_partialSum_invSqCoeff (N : ℕ) :
    Differentiable ℂ fun z : ℂ ↦ ∑ n ∈ Finset.range N, invSqCoeff n • z ^ n := by
  fun_prop

/-- The restriction of `∑ zⁿ / (n + 1)²` to the closed unit disc. -/
private def invSqRestrict : C(closedBall (0 : ℂ) 1, ℂ) :=
  ⟨(closedBall (0 : ℂ) 1).domRestrict (ofScalarsSum invSqCoeff),
    (tendstoUniformlyOn_invSqCoeff.continuousOn (Frequently.of_forall fun N ↦
      (differentiable_partialSum_invSqCoeff N).continuous.continuousOn)).domRestrict⟩

@[simp]
private theorem invSqRestrict_apply (z : closedBall (0 : ℂ) 1) :
    invSqRestrict z = ofScalarsSum invSqCoeff (z : ℂ) :=
  rfl

private theorem invSqRestrict_notMem :
    invSqRestrict ∉ holomorphicRestrictions (closedBall (0 : ℂ) 1) := fun h ↦ by
  obtain ⟨U, g, hU, hDU, hg, hgΦ⟩ := mem_holomorphicRestrictions_iff_exists_open.mp h
  exact not_exists_differentiableOn_eq_ofScalarsSum_invSqCoeff
    ⟨U, g, hU, hDU, hg, fun z hz ↦ (hgΦ ⟨z, hz⟩).trans (invSqRestrict_apply _)⟩

/-- The algebra `O(D)` of restrictions to the closed unit disc `D` of functions holomorphic near
`D` is not closed in `C(D, ℂ)`. -/
theorem not_isClosed_holomorphicRestrictions_closedBall :
    ¬IsClosed (holomorphicRestrictions (closedBall (0 : ℂ) 1) :
      Set C(closedBall (0 : ℂ) 1, ℂ)) := by
  set D := closedBall (0 : ℂ) 1
  have : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  let S (N : ℕ) : C(D, ℂ) :=
    ⟨D.domRestrict fun z ↦ ∑ n ∈ Finset.range N, invSqCoeff n • z ^ n,
      (differentiable_partialSum_invSqCoeff N).continuous.continuousOn.domRestrict⟩
  refine fun hclosed ↦ invSqRestrict_notMem <|
    hclosed.mem_of_tendsto (f := S) (b := atTop) ?_ (Eventually.of_forall fun N ↦ ?_)
  · rw [ContinuousMap.tendsto_iff_tendstoUniformly,
      show ⇑invSqRestrict = ofScalarsSum invSqCoeff ∘ Subtype.val from funext invSqRestrict_apply]
    exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp tendstoUniformlyOn_invSqCoeff
  · exact mem_holomorphicRestrictions_iff_exists_open.mpr ⟨univ, _, isOpen_univ, subset_univ _,
      (differentiable_partialSum_invSqCoeff N).differentiableOn, fun _ ↦ rfl⟩

/-- A continuous function on the closed unit disc `D` that is holomorphic on the interior of `D`
need not lie in `O(D)`. -/
theorem exists_mem_holomorphicFunctions_interior_notMem_holomorphicRestrictions_closedBall :
    ∃ φ : C(closedBall (0 : ℂ) 1, ℂ),
      φ.comp (ContinuousMap.inclusion interior_subset) ∈
          holomorphicFunctions (Opens.interior (closedBall (0 : ℂ) 1)) ∧
        φ ∉ holomorphicRestrictions (closedBall (0 : ℂ) 1) := by
  refine ⟨invSqRestrict,
    (mem_holomorphicFunctions_iff_of_eqOn (g := ofScalarsSum invSqCoeff) fun z ↦
      (invSqRestrict_apply ⟨z, interior_subset z.property⟩).symm).mpr ?_,
    invSqRestrict_notMem⟩
  rw [Opens.coe_interior, interior_closedBall _ one_ne_zero]
  exact differentiableOn_ofScalarsSum_invSqCoeff

end TauCeti
