/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import TauCeti.Topology.JacobsonSpace

/-!
# Closed points in the image of a finite-type morphism

A morphism locally of finite type into a Jacobson scheme maps closed points to closed
points. Conversely, every closed point in its image lifts to a closed point of the source:
the nonempty closed fiber contains a closed point in the Jacobson source. Thus its image
on closed points is exactly the closed-point part of its full topological image.

The file also records the affine charts of a morphism `X ⟶ Spec A` locally of finite type:
every point lies in an affine open `Spec R ⟶ X` with `R` of finite type over `A`
(`Scheme.Hom.exists_isOpenImmersion_finiteType`), and the sections over every affine open are of
finite type over `A` (`Scheme.Hom.finiteType_ΓSpecIso_inv_comp_appLE`). For a quasi-compact
source, `Scheme.Hom.exists_finite_affine_charts` gives a finite family of such charts.

This complements Mathlib's `Scheme.Hom.closedPoints_subset_preimage_closedPoints` with the
lifting direction, needed to compare rational and topological orbit images.

## References

* The Stacks Project, Tag 01TB, morphisms locally of finite type into Jacobson schemes.
-/

public section

open CategoryTheory Topology

namespace AlgebraicGeometry.Scheme.Hom

universe u

section Chart

variable {X : Scheme.{u}} {A : CommRingCat.{u}} (f : X ⟶ Spec A) [LocallyOfFiniteType f]

/-- Every point of the source of a morphism `f : X ⟶ Spec A` locally of finite type lies in the
image of an affine open immersion `g : Spec R ⟶ X` such that `g ≫ f` is induced by a ring map
`A ⟶ R` of finite type. -/
theorem exists_isOpenImmersion_finiteType (x : X) :
    ∃ (R : CommRingCat.{u}) (g : Spec R ⟶ X) (_ : IsOpenImmersion g) (y : Spec R)
      (φ : A ⟶ R) (_ : Spec.map φ = g ≫ f), g y = x ∧ φ.hom.FiniteType := by
  obtain ⟨R, g, _, ⟨y, rfl⟩, -⟩ :=
    X.exists_affine_mem_range_and_range_subset (x := x) (U := ⊤) (by simp)
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = g ≫ f := ⟨_, Spec.map_preimage _⟩
  exact ⟨R, g, inferInstance, y, φ, hφ, rfl,
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)⟩

/-- On an affine open `U` of the source of a morphism `f : X ⟶ Spec A` locally of finite type,
the ring map `A ⟶ Γ(X, U)` induced by `f` is of finite type. -/
theorem finiteType_ΓSpecIso_inv_comp_appLE {U : X.Opens} (hU : IsAffineOpen U) :
    ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top).hom.FiniteType :=
  (f.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
    (.of_surjective _ (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv.surjective)

/-- A quasi-compact scheme locally of finite type over `K` is covered by finitely many open
charts `Spec (A i)`, each `A i` a finitely generated `K`-algebra compatibly with the structure
morphism. -/
theorem exists_finite_affine_charts {K : Type u} [CommRing K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [QuasiCompact f] [LocallyOfFiniteType f] :
    ∃ (ι : Type u) (_ : Finite ι) (A : ι → Type u) (_ : ∀ i, CommRing (A i))
      (_ : ∀ i, Algebra K (A i)) (_ : ∀ i, Algebra.FiniteType K (A i))
      (φ : ∀ i, Spec (.of (A i)) ⟶ X), (∀ i, IsOpenImmersion (φ i)) ∧
        (∀ i, φ i ≫ f = Spec.algebraMap K (A i)) ∧ ∀ x, ∃ i y, φ i y = x := by
  have := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := X.affineCover.finiteSubcover
  have (i : 𝒰.I₀) : IsAffine (𝒰.X i) :=
    (OpenCover.finiteSubcover_X X.affineCover i).symm ▸ inferInstance
  let φ (i : 𝒰.I₀) : Spec Γ(𝒰.X i, ⊤) ⟶ X := (𝒰.X i).isoSpec.inv ≫ 𝒰.f i
  let _ (i : 𝒰.I₀) : Algebra K Γ(𝒰.X i, ⊤) := (Spec.preimage (φ i ≫ f)).hom.toAlgebra
  have hφ (i : 𝒰.I₀) : φ i ≫ f = Spec.algebraMap K Γ(𝒰.X i, ⊤) := (Spec.map_preimage _).symm
  refine ⟨𝒰.I₀, inferInstance, fun i ↦ Γ(𝒰.X i, ⊤), inferInstance, inferInstance,
    fun i ↦ ?_, φ, fun i ↦ inferInstance, hφ, fun x ↦ ?_⟩
  · have : LocallyOfFiniteType (Spec.algebraMap K Γ(𝒰.X i, ⊤)) := hφ i ▸ inferInstance
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at this
    exact RingHom.finiteType_algebraMap.mp this
  · obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    exact ⟨i, (𝒰.X i).isoSpec.hom y, by simp [φ, hy]⟩

end Chart

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [JacobsonSpace Y]

/-- The image on closed points is exactly the intersection of the full image with the
closed points of the target. -/
theorem image_closedPoints_eq_range_inter_closedPoints :
    f '' closedPoints X = Set.range f ∩ closedPoints Y := by
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, f.closedPoints_subset_preimage_closedPoints hx⟩
  · rintro ⟨hyf, hy⟩
    obtain ⟨x, hx, rfl⟩ := f.continuous.exists_isClosed_singleton_of_mem_range
      (IsClosed.isLocallyClosed hy) hyf
    exact ⟨x, hx, rfl⟩

end AlgebraicGeometry.Scheme.Hom
