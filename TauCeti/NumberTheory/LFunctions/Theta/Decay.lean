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

/-- The theta kernel minus its constant term `1` is bounded by `C * exp (-c * t)` whenever
every archimedean parameter is at least `t ≥ 1`. The constants depend only on the discrete
lattice. -/
theorem exists_norm_latticeTheta_sub_one_le (L : Submodule ℤ (mixedSpace K))
    [DiscreteTopology L] :
    ∃ c > 0, ∃ C ≥ 0, ∀ t : ℝ, 1 ≤ t → ∀ y : realSpace K, (∀ w, t ≤ y w) →
      ‖latticeTheta L y - 1‖ ≤ C * Real.exp (-c * t) := by
  classical
  obtain ⟨δ, hδ, hL⟩ := exists_pos_le_mixedInner L
  obtain ⟨c, hc, C, hC, h⟩ := exists_norm_tsum_mul_archGaussian_le
    (fun _ : {x : L // x ≠ 0} ↦ (1 : ℂ)) (fun x ↦ (x.val : mixedSpace K)) hδ
    (fun x ↦ hL x x.property)
    (by simpa only [one_mul, Function.comp_def] using
      (summable_archGaussian L (fun _ ↦ 1 / 2) fun _ ↦ by norm_num).norm.subtype _)
  refine ⟨c, hc, C, hC, fun t ht y hy ↦ ?_⟩
  rw [latticeTheta_eq_one_add L y (fun w ↦ lt_of_lt_of_le zero_lt_one (ht.trans (hy w))),
    add_sub_cancel_left]
  simpa using h t ht y hy

/-- Uniform stretched-exponential decay of the theta kernel minus its constant term `1` along
the radial decomposition of any bounded subset of the norm-one surface. No fundamental-domain
or unit-invariance hypothesis is needed. -/
theorem exists_norm_latticeTheta_surfaceScale_sub_one_le
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] {D : Set (realSpace K)}
    (hD : Bornology.IsBounded D) (hS : D ⊆ normOneSurface K) :
    ∃ c > 0, ∃ C ≥ 0, ∀ᶠ u : ℝ in atTop, ∀ x ∈ D,
      ‖latticeTheta L (surfaceScale x u) - 1‖ ≤
        C * Real.exp (-c * u ^ (Module.finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨c, hc, C, hC, h⟩ := exists_norm_latticeTheta_sub_one_le L
  exact exists_norm_surfaceScale_le_of_forall_le hc hC h hD hS

/-- If `x u` eventually lies in a fixed bounded subset of the norm-one surface, then
`latticeTheta L (surfaceScale (x u) u) - 1` is `O(u^r)` for every real `r` as `u → ∞`.
This supplies rapid decay for the weak Mellin functional equation. -/
theorem isBigO_latticeTheta_surfaceScale_sub_one_rpow
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] {D : Set (realSpace K)}
    (hD : Bornology.IsBounded D) (hS : D ⊆ normOneSurface K)
    {x : ℝ → realSpace K} (hx : ∀ᶠ u in atTop, x u ∈ D) (r : ℝ) :
    (fun u ↦ latticeTheta L (surfaceScale (x u) u) - 1) =O[atTop] (fun u ↦ u ^ r) := by
  obtain ⟨c, hc, C, hC, h⟩ := exists_norm_latticeTheta_surfaceScale_sub_one_le L hD hS
  refine TauCeti.isBigO_rpow_of_eventually_norm_le_exp_neg
    (inv_pos.mpr (Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K))))
    ⟨c, hc, C, hC, ?_⟩ r
  filter_upwards [h, hx] with u hu hxu
  exact hu (x u) hxu

end TauCeti.LFunctions
