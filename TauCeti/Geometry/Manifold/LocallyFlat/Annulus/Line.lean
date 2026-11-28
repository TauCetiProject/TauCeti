/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Annulus.Basic
import TauCeti.AlgebraicTopology.Sphere.Zero

/-!
# The zero-dimensional annulus theorem (on a line)

This file proves the `n = 0` (`ℝ¹`) case of the annulus conjecture without any local flatness
hypothesis, in any one-dimensional real normed space. Every pair of distinct points is a round
sphere (`TauCeti.exists_range_eq_sphere_of_finrank_eq_one`), so any two maps of the unit sphere
`{±u}` with the inner one injective and nested images cobound an annulus
(`TauCeti.coboundAnnulus_of_finrank_eq_one`), a pair of closed intervals, giving
`TauCeti.annulusConjecture_zero`.

## Main results

* `TauCeti.coboundAnnulus_of_finrank_eq_one`: on a line, two nested pairs of points cobound an
  annulus.
* `TauCeti.annulusConjecture_zero`: the annulus conjecture holds for `n = 0`.
-/

public section

noncomputable section

namespace TauCeti

open Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The annulus theorem on a line:** in a one-dimensional real normed space, two maps `f` and `g`
of the unit sphere `{±u}`, with `g` injective and the image of `g` in the open region bounded by the
image of `f`, cobound an annulus. The two pairs of points are the endpoints of nested intervals,
and the annulus is the pair of closed intervals between them. Injectivity of `f` is not assumed: a
map with a single value bounds no region. -/
theorem coboundAnnulus_of_finrank_eq_one (hE : Module.finrank ℝ E = 1) {f g : sphere (0 : E) 1 → E}
    (hg : Function.Injective g) (hfg : range g ⊆ filledHull (range f) \ range f) :
    CoboundAnnulus f g := by
  obtain ⟨c₁, R, hR, -, hfR⟩ := exists_range_eq_sphere_of_finrank_eq_one hE f
  obtain ⟨c₂, r, -, hr, hgr⟩ := exists_range_eq_sphere_of_finrank_eq_one hE g
  have hr := hr hg
  refine coboundAnnulus_of_range_eq_sphere hfR hgr hr ?_
  rw [hfR, hgr, filledHull_sphere _ hR] at hfg
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  obtain ⟨u, hu⟩ : (sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.2 zero_le_one
  have hu1 : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by positivity)
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one hE hu0 (c₂ - c₁)
  -- Both points `c₂ ± r • u` of the inner sphere lie strictly inside the outer sphere.
  have hlt : ∀ t : ℝ, |t| = r → |a + t| < R := fun t ht => by
    have hm : c₂ + t • u ∈ sphere c₂ r := by
      rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hu1,
        mul_one, ht]
    obtain ⟨h₁, h₂⟩ := hfg hm
    rw [mem_closedBall, dist_eq_norm] at h₁
    rw [mem_sphere, dist_eq_norm] at h₂
    have hnorm : ‖c₂ + t • u - c₁‖ = |a + t| := by
      rw [show c₂ + t • u - c₁ = (c₂ - c₁) + t • u by abel, ← ha, ← add_smul,
        norm_smul, Real.norm_eq_abs, hu1, mul_one]
    rw [← hnorm]
    exact lt_of_le_of_ne h₁ h₂
  have hpos := hlt r (abs_of_pos hr)
  have hneg := hlt (-r) (by rw [abs_neg, abs_of_pos hr])
  rw [dist_eq_norm, ← ha, norm_smul, Real.norm_eq_abs, hu1, mul_one]
  rcases le_total a 0 with h | h
  · rw [abs_of_nonpos h]
    linarith [(abs_lt.1 hneg).1]
  · rw [abs_of_nonneg h]
    linarith [(abs_lt.1 hpos).2]

/-- **The annulus theorem for `0`-spheres:** two nested pairs of points on the real line cobound
an annulus, a pair of closed intervals. Local flatness enters only through the injectivity of the
inner pair. -/
theorem annulusConjecture_zero : AnnulusConjecture 0 := by
  rw [annulusConjecture_iff]
  exact fun _ _ _ hg hfg =>
    coboundAnnulus_of_finrank_eq_one (finrank_euclideanSpace_fin (𝕜 := ℝ)) hg.injective hfg

end TauCeti
