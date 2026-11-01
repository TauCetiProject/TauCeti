/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Basic
public import TauCeti.Geometry.Manifold.Instances.Sphere

import TauCeti.Geometry.Manifold.MFDeriv.Chart

/-!
# Solid torus neighbourhoods of knots in the three-sphere

A `C²` embedded circle in the unit three-sphere has a solid torus neighbourhood inside any
prescribed neighbourhood of its image. Stereographic projection from a point omitted by the
circle reduces the construction to the Euclidean tubular-neighbourhood theorem. The closed
solid torus is transported back by inverse stereographic projection.

Removing its open image gives a compact exterior with torus frontier. The neighbourhood carries
an explicit framing; no preferred longitude is selected. Like the Euclidean one, it is
differentiable along the core with injective derivative
(`TauCeti.exists_isSolidTorusNeighborhood_sphere_hasFDerivAt`), since inverse stereographic
projection, read in the ambient space, has injective derivative.

## References

* D. Rolfsen, *Knots and Links* (1976), Sections 2E and 9F.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed. (2013), Theorem 6.24.
-/

public section

open Function Manifold Metric Module Set Topology
open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = 3 + 1)]

/-- **Solid torus neighbourhoods of knots in `S³`, differentiable along the core.** Every `C²`
embedded circle `f` in a unit three-sphere has a solid torus neighbourhood `Φ` inside any
prescribed neighbourhood of its image which, in the coordinates `(u, t) ↦ (u, exp (t i))` of the
solid torus and read in the ambient space `E`, is the restriction of a map `g : ℂ × ℝ → E` that is
differentiable at every point `(0, t)` of the core, with injective derivative. -/
theorem exists_isSolidTorusNeighborhood_sphere_hasFDerivAt {f : Circle → sphere (0 : E) 1}
    (hf : ContMDiff (𝓡 1) (𝓡 3) 2 f)
    (himm : ∀ z, Injective (mfderiv (𝓡 1) (𝓡 3) f z)) (hinj : Injective f)
    {U : Set (sphere (0 : E) 1)} (hU : U ∈ 𝓝ˢ (range f)) :
    ∃ (Φ : SolidTorus → sphere (0 : E) 1) (g : ℂ × ℝ → E), IsSolidTorusNeighborhood f Φ ∧
      range Φ ⊆ U ∧ (∀ (u : closedBall (0 : ℂ) 1) (t : ℝ), (Φ (u, Circle.exp t) : E) = g (u, t)) ∧
      ∀ t, ∃ L : ℂ × ℝ →L[ℝ] E, HasFDerivAt g L (0, t) ∧ Injective L := by
  obtain ⟨p, hp⟩ := exists_notMem_range_circle_sphere (by omega) (hf.mdifferentiable (by decide))
  -- The extended chart gives the coordinate map and its invertible manifold derivative.
  let c := extChartAt (𝓡 3) (-p)
  have hc : c = (stereographic' 3 p).toPartialEquiv := by
    simp only [c, extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
      PartialEquiv.trans_refl, chartAt_sphere, neg_neg]
  have hsrc : ∀ z, f z ∈ c.source := by
    intro z
    rw [hc, stereographic'_source]
    exact fun h => hp ⟨z, (mem_singleton_iff.mp h)⟩
  have htgt : ∀ y, y ∈ c.target := fun y => by simp [hc]
  have hchart : ∀ z, ContMDiffAt (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 2 c (f z) :=
    fun z => contMDiffAt_extChartAt' (by simpa only [c, extChartAt_source] using hsrc z)
  have hcf : ContMDiff (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 2 (c ∘ f) :=
    fun z => (hchart z).comp z (hf z)
  have hicf : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (c ∘ f) z) := by
    intro z
    rw [mfderiv_comp z ((hchart z).mdifferentiableAt (by decide))
      (hf.mdifferentiableAt (by decide))]
    exact (isInvertible_mfderiv_extChartAt (hsrc z)).injective.comp (himm z)
  have hinjcf : Injective (c ∘ f) := fun z w h =>
    hinj (c.injOn (hsrc z) (hsrc w) h)
  have he : IsOpenEmbedding c.symm := by
    rw [hc]
    exact (stereographic' 3 p).symm.isOpenEmbedding (by simp)
  have hpre : c.symm ⁻¹' U ∈ 𝓝ˢ (range (c ∘ f)) := by
    apply nhdsSet_mono ?_ (he.continuous.preimage_mem_nhdsSet hU)
    rintro _ ⟨z, rfl⟩
    exact ⟨z, (c.left_inv (hsrc z)).symm⟩
  obtain ⟨Ψ, g, hΨ, hΨU, hΨg, hg⟩ :=
    exists_isSolidTorusNeighborhood_hasFDerivAt hcf hicf hinjcf hpre
  have hback : c.symm ∘ (c ∘ f) = f := funext fun z => c.left_inv (hsrc z)
  refine ⟨c.symm ∘ Ψ, fun v => (c.symm (g v) : E), hback ▸ hΨ.comp he, ?_,
    fun u t => by rw [comp_apply, hΨg], fun t => ?_⟩
  · rintro _ ⟨q, rfl⟩
    exact hΨU (mem_range_self q)
  · -- The inverse chart, read in `E`, has injective derivative, since the inclusion of the sphere
    -- does.
    obtain ⟨L, hL, hLinj⟩ := hg t
    set y := g (0, t)
    have hcs : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, E)
        (((↑) : sphere (0 : E) 1 → E) ∘ c.symm) y :=
      ((contMDiff_coe_sphere (m := 1) (n := 3)).mdifferentiableAt one_ne_zero).comp y
        ((mdifferentiableWithinAt_extChartAt_symm (htgt y)).mdifferentiableAt
          (by simp [Filter.univ_mem]))
    have hd : DifferentiableAt ℝ (((↑) : sphere (0 : E) 1 → E) ∘ c.symm) y :=
      mdifferentiableAt_iff_differentiableAt.1 hcs
    have hy : c.symm y ∈ (extChartAt (𝓡 3) (-p)).source := c.map_target (htgt y)
    have hinc : Injective (mfderiv (𝓡 3) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) (c.symm y)) := by
      have h := injective_mvfderiv_subtypeVal_sphere (n := 3) (c.symm y)
      unfold mvfderiv at h
      rw [ContinuousLinearMap.coe_comp] at h
      exact h.of_comp
    have hDinj := fderiv_comp_extChartAt_symm_injective hy
      (by rwa [show extChartAt (𝓡 3) (-p) (c.symm y) = y from c.right_inv (htgt y)]) hinc
    rw [show extChartAt (𝓡 3) (-p) (c.symm y) = y from c.right_inv (htgt y)] at hDinj
    exact ⟨_, hd.hasFDerivAt.comp (0, t) hL, hDinj.comp hLinj⟩

/-- Every `C²` embedded circle in a unit three-sphere has a solid torus neighbourhood inside
any prescribed neighbourhood of its image. -/
theorem exists_isSolidTorusNeighborhood_sphere {f : Circle → sphere (0 : E) 1}
    (hf : ContMDiff (𝓡 1) (𝓡 3) 2 f)
    (himm : ∀ z, Injective (mfderiv (𝓡 1) (𝓡 3) f z)) (hinj : Injective f)
    {U : Set (sphere (0 : E) 1)} (hU : U ∈ 𝓝ˢ (range f)) :
    ∃ Φ : SolidTorus → sphere (0 : E) 1, IsSolidTorusNeighborhood f Φ ∧ range Φ ⊆ U :=
  let ⟨Φ, _, hΦ, hΦU, _⟩ := exists_isSolidTorusNeighborhood_sphere_hasFDerivAt hf himm hinj hU
  ⟨Φ, hΦ, hΦU⟩

end TauCeti
