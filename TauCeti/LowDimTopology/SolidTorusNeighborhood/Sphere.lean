/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Basic
public import TauCeti.Geometry.Manifold.Instances.Sphere

/-!
# Solid torus neighbourhoods of knots in the three-sphere

A `C²` embedded circle in the unit three-sphere has a solid torus neighbourhood inside any
prescribed neighbourhood of its image. Stereographic projection from a point omitted by the
circle reduces the construction to the Euclidean tubular-neighbourhood theorem. The closed
solid torus is transported back by inverse stereographic projection.

Removing its open image gives a compact exterior with torus frontier. The neighbourhood carries
an explicit framing; no preferred longitude is selected. It is differentiable at the point `(0, 1)`
of its core with injective derivative: so is the Euclidean neighbourhood, and inverse stereographic
projection is an immersion (`TauCeti.injective_fderiv_coe_comp_stereographic'_symm`). This
derivative is what reads the orientation of the neighbourhood at its core.

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

/-- Every `C²` embedded circle in a unit three-sphere has a solid torus neighbourhood `Φ` inside
any prescribed neighbourhood of its image. Moreover `Φ` is differentiable at the point `(0, 1)` of
its core, with injective derivative: its reading `(u, t) ↦ Φ (u, exp (t i))` in `E`
(`TauCeti.SolidTorus.coreReading`) has an injective derivative at the origin. -/
theorem exists_isSolidTorusNeighborhood_sphere {f : Circle → sphere (0 : E) 1}
    (hf : ContMDiff (𝓡 1) (𝓡 3) 2 f)
    (himm : ∀ z, Injective (mfderiv (𝓡 1) (𝓡 3) f z)) (hinj : Injective f)
    {U : Set (sphere (0 : E) 1)} (hU : U ∈ 𝓝ˢ (range f)) :
    ∃ Φ : SolidTorus → sphere (0 : E) 1, IsSolidTorusNeighborhood f Φ ∧ range Φ ⊆ U ∧
      ∃ L : ℂ × ℝ →L[ℝ] E,
        HasFDerivAt (SolidTorus.coreReading (Subtype.val ∘ Φ)) L 0 ∧ Injective L := by
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
  obtain ⟨Ψ, hΨ, hΨU, L, hL, hLinj⟩ := exists_isSolidTorusNeighborhood hcf hicf hinjcf hpre
  have hback : c.symm ∘ (c ∘ f) = f := funext fun z => c.left_inv (hsrc z)
  -- Read in `E`, the inverse chart is inverse stereographic projection, an immersion.
  set S : EuclideanSpace ℝ (Fin 3) → E := ((↑) : sphere (0 : E) 1 → E) ∘ (stereographic' 3 p).symm
  have hS : HasFDerivAt S (fderiv ℝ S (SolidTorus.coreReading Ψ 0)) (SolidTorus.coreReading Ψ 0) :=
    ((contDiff_coe_comp_stereographic'_symm p (k := 1)).differentiable one_ne_zero _).hasFDerivAt
  refine ⟨c.symm ∘ Ψ, hback ▸ hΨ.comp he, ?_, _, (hS.comp 0 hL).congr_of_eventuallyEq ?_,
    (injective_fderiv_coe_comp_stereographic'_symm p _).comp hLinj⟩
  · rintro _ ⟨q, rfl⟩
    exact hΨU (mem_range_self q)
  · filter_upwards [SolidTorus.eventually_coreReading_eq (Subtype.val ∘ c.symm ∘ Ψ),
      SolidTorus.eventually_coreReading_eq Ψ] with v ⟨hv, heq⟩ ⟨hv', heq'⟩
    rw [heq, comp_apply (f := S), heq']
    simp only [S, comp_apply, hc, OpenPartialHomeomorph.coe_toPartialEquiv_symm]

end TauCeti
