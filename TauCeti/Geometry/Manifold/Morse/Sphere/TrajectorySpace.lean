/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Hemisphere
public import TauCeti.Geometry.Manifold.Morse.Sphere.PseudoGradient
public import TauCeti.Geometry.Manifold.Morse.Stable.Broken.TrajectorySpace

/-!
# The trajectory space of the height function on the sphere

Let `v` be a unit vector in an `(n + 1)`-dimensional real inner product space `E` and `X` any
pseudo-gradient adapted to the height function `sphereHeight v` on the unit sphere `Sⁿ`. Its only
critical points are the north pole `v` and the south pole `-v`, of heights `1` and `-1`. Record the
broken trajectories from `v` to `-v` on the levels of a family `c`
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpace`). This file identifies this
compactified space of trajectories, for every choice of `X` and of the levels.

* No critical value lies strictly between `-1` and `1`, so every broken trajectory from `v` to `-v`
  is unbroken, and the trajectory space has empty boundary
  (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceBoundary_sphereHeight`).
* Every point of height `a ∈ (-1, 1)` flows out of the north pole and into the south pole
  (`IsAdaptedPseudoGradient.unstableSet_inter_stableSet_inter_setOf_sphereHeight_eq` in
  `TauCeti`), so a trajectory is determined by its point on the parallel `{h = a}`.
* The parallel `{h = a}` is a copy of the unit sphere of `(ℝ ∙ v)ᗮ`, through the latitude map
  `u ↦ √(1 - a²) • u + a • v` (`TauCeti.latitudeHomeomorphParallel`).

Hence the trajectory space from the north pole to the south pole is homeomorphic to the unit sphere
`Sⁿ⁻¹` of `(ℝ ∙ v)ᗮ`
(`IsAdaptedPseudoGradient.exists_homeomorph_morseBrokenTrajectorySpace_sphereHeight` in
`TauCeti`), a closed manifold of dimension `ind v - ind (-v) - 1 = n - 1`: a trajectory is the
meridian through a point of the equator. On the circle `S¹` it is two points, the two
half-circles; on `S²` it is a circle. This is the trajectory-space input of the DG Morse complex
of the height function, whose Barraud–Cornea cocycle evaluates chains on this space into the Moore
loops of `Sⁿ`.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceBoundary_sphereHeight`: the trajectory
  space from the north pole to the south pole has empty boundary.
* `TauCeti.IsAdaptedPseudoGradient.exists_homeomorph_morseBrokenTrajectorySpace_sphereHeight`: it is
  homeomorphic to the unit sphere of `(ℝ ∙ v)ᗮ`, through the point of each trajectory on a level.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (spaces of broken trajectories).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 5 (the compactified spaces
  of trajectories and their representing chain systems).
-/

public section

open Metric Module Set
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] {v : sphere (0 : E) 1}
  {X : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
  (hX : IsAdaptedPseudoGradient (sphereHeight v) X) {ι : Type*} (c : ι → ℝ)

/-- **Every point off the poles lies on a trajectory from the north pole to the south pole.** For
`a ∈ (-1, 1)`, the level slice `W^u(v) ∩ W^s(-v) ∩ {h = a}` is the whole parallel `{h = a}`. -/
theorem unstableSet_inter_stableSet_inter_setOf_sphereHeight_eq {a : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1) :
    hX.flow.unstableSet v ∩ hX.flow.stableSet (-v) ∩ {x | sphereHeight v x = a} =
      {x | sphereHeight v x = a} := by
  refine inter_eq_right.2 fun x (hx : sphereHeight v x = a) ↦ ?_
  obtain ⟨hxv, hxnv⟩ := sphereHeight_mem_Ioo_iff.1 (hx ▸ ha)
  rw [unstableSet_sphereHeight_self, stableSet_sphereHeight_neg]
  exact ⟨hxnv, hxv⟩

omit [FiniteDimensional ℝ E] in
/-- The heights of the critical points of the height function are not strictly between the heights
of the south and north poles. -/
private theorem sphereHeight_notMem_Ioo_of_mfderiv_eq_zero {x : sphere (0 : E) 1}
    (hx : mfderiv (𝓡 n) 𝓘(ℝ) (sphereHeight v) x = 0) :
    sphereHeight v x ∉ Ioo (sphereHeight v (-v)) (sphereHeight v v) := by
  rw [sphereHeight_neg_self, sphereHeight_self, sphereHeight_mem_Ioo_iff, not_and_or, not_not,
    not_not]
  exact (mfderiv_sphereHeight_eq_zero_iff v x).1 hx

/-- **The trajectory space from the north pole to the south pole has empty boundary.** No critical
value of the height function lies strictly between `-1` and `1`, so every broken trajectory from
`v` to `-v` is unbroken. -/
theorem morseBrokenTrajectorySpaceBoundary_sphereHeight :
    hX.morseBrokenTrajectorySpaceBoundary c v (-v) = ∅ :=
  hX.morseBrokenTrajectorySpaceBoundary_eq_empty_of_forall_notMem
    ((mfderiv_sphereHeight_eq_zero_iff v v).2 (Or.inl rfl))
    ((mfderiv_sphereHeight_eq_zero_iff v (-v)).2 (Or.inr rfl))
    fun _ ↦ sphereHeight_notMem_Ioo_of_mfderiv_eq_zero

/-- **The trajectory space of the height function is a sphere.** For every adapted pseudo-gradient
`X` and every level `c i₀` of the family strictly between the heights `-1` and `1` of the poles,
the space of broken trajectories from the north pole `v` to the south pole `-v` is homeomorphic to
the unit sphere of `(ℝ ∙ v)ᗮ`, a sphere of dimension `n - 1`: a broken trajectory corresponds to
the point `u` of the equator such that it crosses the level `c i₀` at the latitude
`√(1 - (c i₀)²) • u + c i₀ • v`. -/
theorem exists_homeomorph_morseBrokenTrajectorySpace_sphereHeight
    (i₀ : c ⁻¹' Ioo (sphereHeight v (-v)) (sphereHeight v v)) :
    ∃ Φ : hX.morseBrokenTrajectorySpace c v (-v) ≃ₜ sphere (0 : (ℝ ∙ (v : E))ᗮ) 1,
      ∀ w, latitude v (Φ w) (c i₀) =
        (w : c ⁻¹' Ioo (sphereHeight v (-v)) (sphereHeight v v) → sphere (0 : E) 1) i₀ := by
  have ha : c i₀ ∈ Ioo (-1 : ℝ) 1 := by
    have h : c i₀ ∈ Ioo (sphereHeight v (-v)) (sphereHeight v v) := i₀.property
    exact ⟨by linarith [h.1, sphereHeight_neg_self v], by linarith [h.2, sphereHeight_self v]⟩
  obtain ⟨Φ, hΦ⟩ := hX.exists_homeomorph_morseBrokenTrajectorySpace_of_forall_notMem
    ((mfderiv_sphereHeight_eq_zero_iff v v).2 (Or.inl rfl))
    ((mfderiv_sphereHeight_eq_zero_iff v (-v)).2 (Or.inr rfl)) (ne_neg_of_mem_unit_sphere ℝ v)
    (fun _ ↦ sphereHeight_notMem_Ioo_of_mfderiv_eq_zero) i₀
  -- The level slice is the parallel `{⟪x, v⟫ = c i₀}`, a copy of the unit sphere of `(ℝ ∙ v)ᗮ`.
  have hslice : hX.flow.unstableSet v ∩ hX.flow.stableSet (-v) ∩ {x | sphereHeight v x = c i₀} =
      {z : sphere (0 : E) 1 | ⟪(z : E), (v : E)⟫ = c i₀} := by
    rw [hX.unstableSet_inter_stableSet_inter_setOf_sphereHeight_eq ha]
    simp only [sphereHeight_apply]
  refine ⟨(Φ.trans (Homeomorph.setCongr hslice)).trans (latitudeHomeomorphParallel v ha).symm,
    fun w ↦ ?_⟩
  rw [Homeomorph.trans_apply, ← coe_latitudeHomeomorphParallel_apply v ha,
    Homeomorph.apply_symm_apply, Homeomorph.trans_apply]
  -- `Homeomorph.setCongr` is `Set.equivOfEq`, which keeps the underlying point.
  exact hΦ w

end IsAdaptedPseudoGradient

end TauCeti
