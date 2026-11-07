/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Theta.Gaussian
public import TauCeti.NumberTheory.LFunctions.Theta.Surface.Coordinates
public import TauCeti.Analysis.SpecialFunctions.Exp.StretchedDecay

/-!
# Uniform decay of archimedean theta kernels

The theta kernel minus its constant term decays exponentially as all archimedean parameters
increase. The estimate is uniform when the surface parameter ranges over a bounded subset of
the norm-one surface. In the radial variable `u` used for the Mellin transform, the decay is
`O(exp (-c u^(1/[K:ℚ])))`, hence faster than every power. This is the decay estimate needed to
integrate the kernel over a bounded unit fundamental domain and apply the Mellin principle.

Only discreteness of the lattice is needed, not full rank or stability under units. The
positive lower bound for the Euclidean length of a nonzero lattice vector lets us split off
an exponentially decaying factor; the remaining Gaussian is summable.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, especially (5.8).
-/

public section

noncomputable section

open Complex Filter NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  TauCeti.NumberField.mixedEmbedding
open scoped Topology Real

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-- A Gaussian at parameters at least `t`, `t ≥ 1`, is bounded by a fixed summable Gaussian
times an exponentially decreasing factor, provided the vector has squared length at least `δ`. -/
private theorem norm_archGaussian_le_exp_mul {x : mixedSpace K} {δ t : ℝ}
    (hδ : δ ≤ mixedInner K x x) (ht : 1 ≤ t) {y : realSpace K} (hy : ∀ w, t ≤ y w) :
    ‖archGaussian y x‖ ≤ Real.exp (-(Real.pi * δ / 2) * t) *
      ‖archGaussian (fun _ ↦ (1 / 2 : ℝ)) x‖ := by
  classical
  have hQ : 0 ≤ mixedInner K x x := by
    rw [mixedInner_self_eq_sum]
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hsum : t * mixedInner K x x ≤ ∑ w, y w * normAtPlace w x ^ 2 := by
    rw [mixedInner_self_eq_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ ↦ mul_le_mul_of_nonneg_right (hy w) (sq_nonneg _)
  have hsplit : δ / 2 * t + 1 / 2 * mixedInner K x x ≤ t * mixedInner K x x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) hQ,
      mul_nonneg (by linarith : 0 ≤ t) (sub_nonneg.mpr hδ)]
  simp only [archGaussian_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [← Finset.mul_sum, ← mixedInner_self_eq_sum]
  nlinarith [Real.pi_pos]

/-- The theta kernel minus its constant term `1` is bounded by `C * exp (-c * t)` whenever
every archimedean parameter is at least `t ≥ 1`. The constants depend only on the discrete
lattice. -/
theorem exists_norm_latticeTheta_sub_one_le (L : Submodule ℤ (mixedSpace K))
    [DiscreteTopology L] :
    ∃ c > 0, ∃ C ≥ 0, ∀ t : ℝ, 1 ≤ t → ∀ y : realSpace K, (∀ w, t ≤ y w) →
      ‖latticeTheta L y - 1‖ ≤ C * Real.exp (-c * t) := by
  classical
  obtain ⟨δ, hδ, hL⟩ := exists_pos_le_mixedInner L
  let a : {x : L // x ≠ 0} → ℝ := fun x ↦
    ‖archGaussian (fun _ ↦ (1 / 2 : ℝ)) ((x : L) : mixedSpace K)‖
  have ha : Summable a :=
    (summable_archGaussian L (fun _ ↦ (1 / 2 : ℝ)) (fun _ ↦ by norm_num)).norm.subtype _
  refine ⟨Real.pi * δ / 2, by positivity, ∑' x, a x,
    tsum_nonneg (fun _ ↦ norm_nonneg _), fun t ht y hy ↦ ?_⟩
  rw [latticeTheta_eq_one_add L y (fun w ↦ lt_of_lt_of_le zero_lt_one (ht.trans (hy w))),
    add_sub_cancel_left]
  calc
    ‖∑' x : {x : L // x ≠ 0}, archGaussian y (x : L)‖
        ≤ ∑' x, Real.exp (-(Real.pi * δ / 2) * t) * a x :=
      tsum_of_norm_bounded (ha.mul_left _).hasSum fun x ↦
        norm_archGaussian_le_exp_mul (hL x x.2) ht hy
    _ = (∑' x, a x) * Real.exp (-(Real.pi * δ / 2) * t) := by
      rw [tsum_mul_left, mul_comm]

/-- Uniform stretched-exponential decay of the theta kernel minus its constant term `1` along
the radial decomposition of any bounded subset of the norm-one surface. No fundamental-domain
or unit-invariance hypothesis is needed. -/
theorem exists_norm_latticeTheta_surfaceScale_sub_one_le
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] {D : Set (realSpace K)}
    (hD : Bornology.IsBounded D) (hS : D ⊆ normOneSurface K) :
    ∃ c > 0, ∃ C ≥ 0, ∀ᶠ u : ℝ in atTop, ∀ x ∈ D,
      ‖latticeTheta L (surfaceScale x u) - 1‖ ≤
        C * Real.exp (-c * u ^ (Module.finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨b, hb, hbx⟩ := exists_pos_le_of_isBounded_normOneSurface hD hS
  obtain ⟨c, hc, C, hC, htheta⟩ := exists_norm_latticeTheta_sub_one_le L
  have hn : 0 < (Module.finrank ℚ K : ℝ)⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K)))
  have hu : Tendsto (fun u : ℝ ↦ b * u ^ (Module.finrank ℚ K : ℝ)⁻¹) atTop atTop :=
    (tendsto_rpow_atTop hn).const_mul_atTop hb
  refine ⟨c * b, mul_pos hc hb, C, hC, ?_⟩
  filter_upwards [hu.eventually_ge_atTop 1, eventually_ge_atTop (0 : ℝ)] with u hu hu0 x hx
  have h := htheta (b * u ^ (Module.finrank ℚ K : ℝ)⁻¹) hu (surfaceScale x u) fun w ↦ by
    rw [surfaceScale_apply]
    simpa only [one_div] using
      mul_le_mul_of_nonneg_right (hbx x hx w)
        (Real.rpow_nonneg hu0 (Module.finrank ℚ K : ℝ)⁻¹)
  simpa only [neg_mul, mul_assoc] using h

/-- If `x u` eventually lies in a fixed bounded subset of the norm-one surface, then
`latticeTheta L (surfaceScale (x u) u) - 1` is `O(u^r)` for every real `r` as `u → ∞`.
This supplies rapid decay for the weak Mellin functional equation. -/
theorem isBigO_latticeTheta_surfaceScale_sub_one_rpow
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] {D : Set (realSpace K)}
    (hD : Bornology.IsBounded D) (hS : D ⊆ normOneSurface K)
    {x : ℝ → realSpace K} (hx : ∀ᶠ u in atTop, x u ∈ D) (r : ℝ) :
    (fun u ↦ latticeTheta L (surfaceScale (x u) u) - 1) =O[atTop] (fun u ↦ u ^ r) := by
  obtain ⟨c, hc, C, _, h⟩ := exists_norm_latticeTheta_surfaceScale_sub_one_le L hD hS
  apply TauCeti.isBigO_rpow_of_isBigO_exp_neg hc
    (inv_pos.mpr (Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K))))
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [h, hx] with u hu hxu
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hu (x u) hxu

end TauCeti.LFunctions
