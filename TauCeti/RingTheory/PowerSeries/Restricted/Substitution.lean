/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Restricted
public import Mathlib.RingTheory.PowerSeries.Substitution
import TauCeti.RingTheory.PowerSeries.Restricted
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Formal substitution of restricted power series

Over an ultrametric commutative seminormed ring `R`, substituting `f ∈ R⟦X⟧` with zero constant
term and `‖coeff k f‖ ≤ 1` into `g ∈ R⟦X⟧` preserves uniform coefficient bounds
(`PowerSeries.norm_coeff_subst_le`). Over a normed ring, if `g` and `f` are restricted at radius
`1`, then so is `g.subst f` (`PowerSeries.IsRestricted.subst_one`). Neither result requires
`NormOneClass R` or completeness.

## Main results

* `PowerSeries.norm_coeff_subst_le`: uniform coefficient bound under formal substitution.
* `PowerSeries.IsRestricted.subst_one`: substitution preserves restrictedness at radius `1`.
-/

public section

open Filter Topology
open scoped PowerSeries

namespace PowerSeries

/-- Substituting a unit-ball series `f` with zero constant term into a series `g` with coefficients
bounded by `r` preserves the uniform bound `r` (without needing `NormOneClass R`). -/
theorem norm_coeff_subst_le {R : Type*} [SeminormedCommRing R] [IsUltrametricDist R] {f g : R⟦X⟧}
    {r : ℝ} (hgn : ∀ k, ‖coeff k g‖ ≤ r) (hfn : ∀ k, ‖coeff k f‖ ≤ 1) (hf0 : constantCoeff f = 0)
    (k : ℕ) : ‖coeff k (g.subst f)‖ ≤ r := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (hgn 0)
  rw [coeff_subst_eq_sum_range g hf0 k]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr0 fun m _ ↦ ?_
  rcases eq_or_ne m 0 with rfl | hm
  · rcases eq_or_ne k 0 with rfl | hk
    · simpa using hgn 0
    · simp [coeff_one, hk, hr0]
  · rw [smul_eq_mul]
    exact (norm_mul_le _ _).trans <|
      (mul_le_of_le_one_right (norm_nonneg _) (norm_coeff_pow_le_one hfn hm k)).trans (hgn m)

/-- Substituting a restricted unit-ball series `f` with zero constant term into a series `g`
restricted at radius `1` yields a series restricted at radius `1`. -/
theorem IsRestricted.subst_one {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {f g : R⟦X⟧}
    (hg : g.IsRestricted 1) (hf : f.IsRestricted 1) (hfn : ∀ k, ‖coeff k f‖ ≤ 1)
    (hf0 : constantCoeff f = 0) : PowerSeries.IsRestricted 1 (g.subst f) := by
  rw [← tendsto_coeff_atTop_iff_isRestricted_one, NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨M, hM⟩ := eventually_atTop.mp <|
    NormedAddGroup.tendsto_nhds_zero.mp
      (tendsto_coeff_atTop_iff_isRestricted_one.mpr hg) (ε / 2) (half_pos hε)
  have hhead : ∀ m ∈ Finset.range (M + 1),
      ∀ᶠ k in atTop, ‖coeff m g * coeff k (f ^ m)‖ < ε / 2 := fun m _ ↦
    NormedAddGroup.tendsto_nhds_zero.mp
      (by simpa only [mul_zero] using
        (tendsto_coeff_atTop_iff_isRestricted_one.mpr (hf.pow m)).const_mul (coeff m g))
      (ε / 2) (half_pos hε)
  obtain ⟨K, hK⟩ := eventually_atTop.mp ((Finset.range (M + 1)).eventually_all.mpr hhead)
  refine eventually_atTop.mpr ⟨K, fun k hk ↦ ?_⟩
  rw [coeff_subst_eq_sum_range g hf0 k]
  refine (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (half_pos hε).le
    fun m _ ↦ ?_).trans_lt (half_lt_self hε)
  rw [smul_eq_mul]
  rcases lt_or_ge m (M + 1) with hm | hm
  · exact (hK k hk m (Finset.mem_range.mpr hm)).le
  · exact (norm_mul_le _ _).trans <| (mul_le_of_le_one_right (norm_nonneg _)
      (norm_coeff_pow_le_one hfn (by omega) k)).trans (hM m (by omega)).le

end PowerSeries
