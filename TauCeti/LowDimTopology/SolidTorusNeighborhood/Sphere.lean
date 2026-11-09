/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Basic
public import TauCeti.Geometry.Manifold.Instances.Sphere
import TauCeti.Analysis.Calculus.FDeriv.Norm

/-!
# Solid torus neighbourhoods of knots in the three-sphere

A `C²` embedded circle in the unit three-sphere has a solid torus neighbourhood inside any
prescribed neighbourhood of its image. Stereographic projection from a point omitted by the
circle reduces the construction to the Euclidean tubular-neighbourhood theorem. The closed
solid torus is transported back by inverse stereographic projection.

Removing its open image gives a compact exterior with torus frontier. The neighbourhood carries
an explicit framing; no preferred longitude is selected.

Read in the ambient space at its core point (`TauCeti.SolidTorus.coreReading`), the neighbourhood
is differentiable with injective derivative, valued in the tangent space of the sphere: the
Euclidean neighbourhood is, and the inverse stereographic projection is smooth with injective
derivative. This is the input for choosing the neighbourhood to preserve orientation.

## Main results

* `TauCeti.exists_isSolidTorusNeighborhood_sphere_hasFDerivAt_coreReading`: a `C²` embedded circle
  in `S³` has solid torus neighbourhoods, inside any neighbourhood of its image, with an injective
  derivative at the core point.
* `TauCeti.exists_isSolidTorusNeighborhood_sphere`: the same without the derivative.

## References

* D. Rolfsen, *Knots and Links* (1976), Sections 2E and 9F.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed. (2013), Theorem 6.24.
-/

public section

open Function Manifold Metric Module Set Topology
open scoped Manifold RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = 3 + 1)]

/-- If the reading of `Ψ : D² × S¹ → ℝ³` at its core point (`TauCeti.SolidTorus.coreReading`) has
an injective derivative at the origin, then so has the reading in `E` of its image under an inverse
stereographic chart, and that derivative is valued in the tangent space of the sphere at the core
point. -/
private theorem exists_hasFDerivAt_coreReading_stereographic'_symm_comp (p : sphere (0 : E) 1)
    {Ψ : SolidTorus → EuclideanSpace ℝ (Fin 3)} {LΨ : ℂ × ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    (hLΨ : HasFDerivAt (SolidTorus.coreReading Ψ) LΨ 0) (hinj : Injective LΨ) :
    ∃ L : ℂ × ℝ →L[ℝ] E,
      HasFDerivAt (SolidTorus.coreReading fun q ↦ ((stereographic' 3 p).symm (Ψ q) : E)) L 0 ∧
        Injective L ∧ ∀ v, ⟪((stereographic' 3 p).symm (Ψ (0, 1)) : E), L v⟫ = 0 := by
  -- Read in `E`, the inverse chart `G` is smooth with injective derivative.
  let G := ((↑) : sphere (0 : E) 1 → E) ∘ (stereographic' 3 p).symm
  have hG : HasFDerivAt G (fderiv ℝ G (Ψ (0, 1))) (SolidTorus.coreReading Ψ 0) := by
    rw [SolidTorus.coreReading_zero]
    exact ((contDiff_coe_comp_stereographic'_symm p (k := 1)).differentiable one_ne_zero
      _).hasFDerivAt
  refine ⟨(fderiv ℝ G (Ψ (0, 1))).comp LΨ, (hG.comp 0 hLΨ).congr_of_eventuallyEq
    (SolidTorus.coreReading_comp_eventuallyEq G Ψ),
    (injective_fderiv_coe_comp_stereographic'_symm p _).comp hinj, fun v ↦ ?_⟩
  -- `G` takes values in the unit sphere, so its derivative is orthogonal to its value.
  exact inner_fderiv_eq_zero_of_eventually_norm_eq (ψ := G) (w := Ψ (0, 1))
    (.of_forall fun y ↦ by simp [G, norm_eq_of_mem_sphere]) (LΨ v)

/-- **Solid torus neighbourhoods of knots in the three-sphere, with their derivative at the core.**
Every `C²` embedded circle `f` in a unit three-sphere has a solid torus neighbourhood `Φ` inside
any prescribed neighbourhood of its image, whose reading `(u, t) ↦ Φ (u, exp (t i))` at the core
point `(0, 1)` (`TauCeti.SolidTorus.coreReading`), taken in the ambient space, is differentiable at
the origin with injective derivative valued in the tangent space `(ℝ ∙ Φ (0, 1))ᗮ` of the
sphere. -/
theorem exists_isSolidTorusNeighborhood_sphere_hasFDerivAt_coreReading
    {f : Circle → sphere (0 : E) 1} (hf : ContMDiff (𝓡 1) (𝓡 3) 2 f)
    (himm : ∀ z, Injective (mfderiv (𝓡 1) (𝓡 3) f z)) (hinj : Injective f)
    {U : Set (sphere (0 : E) 1)} (hU : U ∈ 𝓝ˢ (range f)) :
    ∃ Φ : SolidTorus → sphere (0 : E) 1, IsSolidTorusNeighborhood f Φ ∧ range Φ ⊆ U ∧
      ∃ L : ℂ × ℝ →L[ℝ] E, HasFDerivAt (SolidTorus.coreReading fun q ↦ (Φ q : E)) L 0 ∧
        Injective L ∧ ∀ v, ⟪(Φ (0, 1) : E), L v⟫ = 0 := by
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
  obtain ⟨Ψ, hΨ, hΨU, LΨ, hLΨ, hLΨinj⟩ :=
    exists_isSolidTorusNeighborhood_hasFDerivAt_coreReading hcf hicf hinjcf hpre
  have hback : c.symm ∘ (c ∘ f) = f := funext fun z => c.left_inv (hsrc z)
  refine ⟨c.symm ∘ Ψ, hback ▸ hΨ.comp he, ?_, ?_⟩
  · rintro _ ⟨q, rfl⟩
    exact hΨU (mem_range_self q)
  have hcΨ : ∀ q, ((c.symm ∘ Ψ) q : E) = ((stereographic' 3 p).symm (Ψ q) : E) := by
    simp [hc]
  obtain ⟨L, hL, hLinj, horth⟩ :=
    exists_hasFDerivAt_coreReading_stereographic'_symm_comp p hLΨ hLΨinj
  refine ⟨L, by simpa only [hcΨ] using hL, hLinj, fun v ↦ ?_⟩
  rw [hcΨ]
  exact horth v

/-- Every `C²` embedded circle in a unit three-sphere has a solid torus neighbourhood inside
any prescribed neighbourhood of its image. -/
theorem exists_isSolidTorusNeighborhood_sphere {f : Circle → sphere (0 : E) 1}
    (hf : ContMDiff (𝓡 1) (𝓡 3) 2 f)
    (himm : ∀ z, Injective (mfderiv (𝓡 1) (𝓡 3) f z)) (hinj : Injective f)
    {U : Set (sphere (0 : E) 1)} (hU : U ∈ 𝓝ˢ (range f)) :
    ∃ Φ : SolidTorus → sphere (0 : E) 1, IsSolidTorusNeighborhood f Φ ∧ range Φ ⊆ U :=
  let ⟨Φ, hΦ, hΦU, _⟩ :=
    exists_isSolidTorusNeighborhood_sphere_hasFDerivAt_coreReading hf himm hinj hU
  ⟨Φ, hΦ, hΦU⟩

end TauCeti
