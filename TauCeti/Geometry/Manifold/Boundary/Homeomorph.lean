/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Invariance

/-!
# Invariance of interior and boundary under homeomorphisms

By topological invariance of interior and boundary points under partial homeomorphisms
(`OpenPartialHomeomorph.isInteriorPoint_iff` and `OpenPartialHomeomorph.isBoundaryPoint_iff`),
any global homeomorphism `e : M ≃ₜ N` between charted spaces modelled with corners on
normed spaces of the same finite dimension preserves the manifold interior, preserves the
manifold boundary, and restricts to homeomorphisms between their interiors and between their
boundaries.

## Main declarations

* `Homeomorph.isInteriorPoint_iff` and `Homeomorph.isBoundaryPoint_iff`: pointwise
  preservation of interior and boundary points.
* `Homeomorph.preimage_manifoldInterior`, `Homeomorph.image_manifoldInterior`,
  `Homeomorph.preimage_boundary`, and `Homeomorph.image_boundary`: set-level invariance of the
  interior and boundary.
* `Homeomorph.boundarylessManifold` and `Homeomorph.boundarylessManifold_iff`: being a
  boundaryless manifold is invariant under homeomorphism.
* `Homeomorph.manifoldInteriorHomeomorph` and `Homeomorph.boundaryHomeomorph`: the restricted
  homeomorphisms between the interiors and between the boundaries.
-/

public section

open Module Set

open scoped Manifold

namespace Homeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E H E' H' : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') {M N : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E']

/-- **Topological invariance of interior points under homeomorphisms.** A homeomorphism between
charted spaces modelled with corners on finite-dimensional normed spaces of the same dimension
preserves interior points. -/
theorem isInteriorPoint_iff (e : M ≃ₜ N) (hEE' : finrank 𝕜 E = finrank 𝕜 E') (x : M) :
    I.IsInteriorPoint x ↔ I'.IsInteriorPoint (e x) :=
  e.toOpenPartialHomeomorph.isInteriorPoint_iff I I' hEE' (mem_univ x)

/-- **Topological invariance of boundary points under homeomorphisms.** A homeomorphism between
charted spaces modelled with corners on finite-dimensional normed spaces of the same dimension
preserves boundary points. -/
theorem isBoundaryPoint_iff (e : M ≃ₜ N) (hEE' : finrank 𝕜 E = finrank 𝕜 E') (x : M) :
    I.IsBoundaryPoint x ↔ I'.IsBoundaryPoint (e x) :=
  e.toOpenPartialHomeomorph.isBoundaryPoint_iff I I' hEE' (mem_univ x)

/-- The preimage of the manifold interior under a homeomorphism is the manifold interior of the
domain. -/
theorem preimage_manifoldInterior (e : M ≃ₜ N) (hEE' : finrank 𝕜 E = finrank 𝕜 E') :
    e ⁻¹' I'.interior N = I.interior M := by
  ext x
  exact (e.isInteriorPoint_iff I I' hEE' x).symm

/-- The image of the manifold interior under a homeomorphism is the manifold interior of the
codomain. -/
theorem image_manifoldInterior (e : M ≃ₜ N) (hEE' : finrank 𝕜 E = finrank 𝕜 E') :
    e '' I.interior M = I'.interior N :=
  (e.eq_preimage_iff_image_eq _ _).1 (e.preimage_manifoldInterior I I' hEE').symm

/-- The preimage of the manifold boundary under a homeomorphism is the manifold boundary of the
domain. -/
theorem preimage_boundary (e : M ≃ₜ N) (hEE' : finrank 𝕜 E = finrank 𝕜 E') :
    e ⁻¹' I'.boundary N = I.boundary M := by
  ext x
  exact (e.isBoundaryPoint_iff I I' hEE' x).symm

/-- The image of the manifold boundary under a homeomorphism is the manifold boundary of the
codomain. -/
theorem image_boundary (e : M ≃ₜ N) (hEE' : finrank 𝕜 E = finrank 𝕜 E') :
    e '' I.boundary M = I'.boundary N :=
  (e.eq_preimage_iff_image_eq _ _).1 (e.preimage_boundary I I' hEE').symm

/-- A homeomorphism maps the manifold boundary of its domain into the manifold boundary of its
codomain. -/
theorem mapsTo_boundary (e : M ≃ₜ N) (hEE' : finrank 𝕜 E = finrank 𝕜 E') :
    MapsTo e (I.boundary M) (I'.boundary N) := by
  rw [← e.image_boundary I I' hEE']
  exact mapsTo_image e (I.boundary M)

/-- A homeomorphism between charted spaces modelled on spaces of the same finite dimension has
empty boundary in the domain if and only if it has empty boundary in the codomain. -/
theorem boundary_eq_empty_iff (e : M ≃ₜ N) (hEE' : finrank 𝕜 E = finrank 𝕜 E') :
    I.boundary M = ∅ ↔ I'.boundary N = ∅ := by
  rw [← e.image_boundary I I' hEE', image_eq_empty]

/-- If the domain of a homeomorphism is boundaryless, so is its codomain. -/
theorem boundarylessManifold (e : M ≃ₜ N) (hEE' : finrank 𝕜 E = finrank 𝕜 E')
    [BoundarylessManifold I M] : BoundarylessManifold I' N := by
  rw [← ModelWithCorners.Boundaryless.iff_boundary_eq_empty,
    ← e.boundary_eq_empty_iff I I' hEE', ModelWithCorners.Boundaryless.boundary_eq_empty]

/-- Being a boundaryless manifold is invariant under homeomorphism (over finite-dimensional
models of the same dimension). -/
theorem boundarylessManifold_iff (e : M ≃ₜ N) (hEE' : finrank 𝕜 E = finrank 𝕜 E') :
    BoundarylessManifold I M ↔ BoundarylessManifold I' N :=
  ⟨fun _ => e.boundarylessManifold I I' hEE',
    fun _ => e.symm.boundarylessManifold I' I hEE'.symm⟩

/-- The restriction of a homeomorphism to the manifold interiors of its domain and codomain. -/
@[expose] def manifoldInteriorHomeomorph (e : M ≃ₜ N)
    (hEE' : finrank 𝕜 E = finrank 𝕜 E') :
    I.interior M ≃ₜ I'.interior N :=
  e.subtype (e.isInteriorPoint_iff I I' hEE')

/-- The underlying map of `Homeomorph.manifoldInteriorHomeomorph` agrees with `e`. -/
@[simp]
theorem coe_manifoldInteriorHomeomorph_apply (e : M ≃ₜ N)
    (hEE' : finrank 𝕜 E = finrank 𝕜 E')
    (x : I.interior M) : (e.manifoldInteriorHomeomorph I I' hEE' x : N) = e x :=
  rfl

/-- The inverse of `Homeomorph.manifoldInteriorHomeomorph` agrees with `e.symm`. -/
@[simp]
theorem coe_manifoldInteriorHomeomorph_symm_apply (e : M ≃ₜ N)
    (hEE' : finrank 𝕜 E = finrank 𝕜 E')
    (y : I'.interior N) : ((e.manifoldInteriorHomeomorph I I' hEE').symm y : M) = e.symm y :=
  rfl

/-- The restriction of a homeomorphism to the manifold boundaries of its domain and codomain. -/
@[expose] def boundaryHomeomorph (e : M ≃ₜ N) (hEE' : finrank 𝕜 E = finrank 𝕜 E') :
    I.boundary M ≃ₜ I'.boundary N :=
  e.subtype (e.isBoundaryPoint_iff I I' hEE')

/-- The underlying map of `Homeomorph.boundaryHomeomorph` agrees with `e`. -/
@[simp]
theorem coe_boundaryHomeomorph_apply (e : M ≃ₜ N) (hEE' : finrank 𝕜 E = finrank 𝕜 E')
    (x : I.boundary M) : (e.boundaryHomeomorph I I' hEE' x : N) = e x :=
  rfl

/-- The inverse of `Homeomorph.boundaryHomeomorph` agrees with `e.symm`. -/
@[simp]
theorem coe_boundaryHomeomorph_symm_apply (e : M ≃ₜ N) (hEE' : finrank 𝕜 E = finrank 𝕜 E')
    (y : I'.boundary N) : ((e.boundaryHomeomorph I I' hEE').symm y : M) = e.symm y :=
  rfl

end Homeomorph
