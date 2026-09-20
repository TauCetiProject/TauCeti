/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import TauCeti.Algebra.MonoidAlgebra.Localization
public import TauCeti.Geometry.Toric.Algebraic.AffineScheme
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Face

/-!
# Face localizations of affine toric schemes

A character `m` in the dual semigroup of a cone `σ` is nonnegative on `σ`, so it cuts out the face
`σ ⊓ ker m` of `σ` (`PointedCone.isFaceOf_inf_ker`). The inclusion of that face into `σ` induces
the restriction map from the coordinate ring of `σ` to the coordinate ring of the face. When `σ`
is finitely generated, this map is the localization away from the monomial of `m`: the dual
semigroup of the face is obtained from that of `σ` by adjoining `-m`
(`TauCeti.Toric.dualSemigroup_inf_ker_eq_sup`). On spectra, the affine toric scheme of the face is
therefore the basic open subscheme of the affine toric scheme of `σ` where the monomial of `m`
does not vanish, and the induced morphism is an open immersion.

Every face of a regular cone is cut out by such a character
(`TauCeti.Toric.IsRegularCone.exists_mem_dualSemigroup_inf_ker_eq`), so for a regular cone the
inclusion of an arbitrary face induces a localization at a single monomial and an open immersion
of affine toric schemes.

These open immersions are the maps along which the affine toric schemes of a fan are glued.
The canonical face maps introduced here satisfy identity and composition laws, so successive
face restrictions give the same morphism as the composite face inclusion. This is the
functoriality needed for the overlap and cocycle maps in fan gluing.

## Main declarations

* `TauCeti.Toric.isLocalization_away_affineCoordinateRingMap_inf_ker`: the coordinate ring of the
  face `σ ⊓ ker m` is the localization of the coordinate ring of `σ` away from the monomial of
  `m`.
* `TauCeti.Toric.isOpenImmersion_affineToricSchemeMap_inf_ker`: the affine toric scheme of the
  face is an open subscheme of the affine toric scheme of `σ`.
* `TauCeti.Toric.faceAffineCoordinateRingMap` and
  `TauCeti.Toric.faceAffineToricSchemeMap`: the canonical restriction map and affine-scheme
  morphism attached to a face inclusion, with identity and composition laws.
* `TauCeti.Toric.IsRegularCone.exists_isLocalization_away_faceAffineCoordinateRingMap` and
  `TauCeti.Toric.IsRegularCone.isOpenImmersion_faceAffineToricSchemeMap`: for a face `τ` of a
  regular cone `σ`, the coordinate ring of `τ` is the localization of that of `σ` away from a
  single monomial, and the affine toric scheme of `τ` is an open subscheme of that of `σ`.
* `TauCeti.Toric.range_faceAffineToricSchemeMap` and
  `TauCeti.Toric.IsRegularCone.range_faceAffineToricSchemeMap_inf`: the image of the affine
  toric scheme of a face is a basic open set, and for faces of a regular cone the image of an
  intersection of faces is the intersection of their images.
* `TauCeti.Toric.Fan.affineToricChart`, `TauCeti.Toric.Fan.affineToricOverlap`,
  `TauCeti.Toric.Fan.affineToricOverlapLeft` and `TauCeti.Toric.Fan.affineToricOverlapRight`: the
  affine toric charts of a fan and the two maps from their pairwise overlap; these maps are open
  immersions when their target cones are regular.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.3.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §1.3.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative

namespace TauCeti.Toric

universe u

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {σ : PointedCone ℝ V}

/-! ### Canonical maps attached to face inclusions -/

variable {τ υ : PointedCone ℝ V}

/-- A face inclusion `τ ≼ σ` induces the restriction map from the coordinate ring of `σ`
to the coordinate ring of `τ`. -/
noncomputable def faceAffineCoordinateRingMap (hi : IsIntegralLattice i)
    (hτσ : τ.IsFaceOf σ) : affineCoordinateRing hi σ →ₐ[ℂ] affineCoordinateRing hi τ :=
  affineCoordinateRingMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
    fun _ hx ↦ hτσ.le hx

/-- Restriction along a face inclusion sends a monomial to the same integral character, regarded
as an element of the larger dual semigroup of the face. -/
@[simp]
theorem faceAffineCoordinateRingMap_single (hi : IsIntegralLattice i)
    (hτσ : τ.IsFaceOf σ) (m : dualSemigroup hi σ) (z : ℂ) :
    faceAffineCoordinateRingMap hi hτσ (MonoidAlgebra.single (ofAdd m) z) =
      MonoidAlgebra.single (ofAdd ⟨m, dualSemigroup_anti hi hτσ.le m.2⟩) z := by
  rw [faceAffineCoordinateRingMap]
  convert affineCoordinateRingMap_single hi hi (AddMonoidHom.id N) LinearMap.id
    (fun _ ↦ rfl) (fun _ hx ↦ hτσ.le hx) m z using 1
  apply congrArg (fun u ↦ MonoidAlgebra.single (ofAdd u) z)
  apply Subtype.ext
  exact (coe_dualSemigroupMap_id hi (fun _ hx ↦ hτσ.le hx) m).symm

/-- Restriction to a cone viewed as its own face is the identity map of its coordinate ring. -/
@[simp]
theorem faceAffineCoordinateRingMap_id (hi : IsIntegralLattice i) :
    faceAffineCoordinateRingMap hi (PointedCone.IsFaceOf.refl σ) =
      AlgHom.id ℂ (affineCoordinateRing hi σ) :=
  affineCoordinateRingMap_id hi σ

/-- Restriction through two successive face inclusions is restriction along their composite. -/
@[simp]
theorem faceAffineCoordinateRingMap_comp (hi : IsIntegralLattice i)
    (hυτ : υ.IsFaceOf τ) (hτσ : τ.IsFaceOf σ) :
    (faceAffineCoordinateRingMap hi hυτ).comp (faceAffineCoordinateRingMap hi hτσ) =
      faceAffineCoordinateRingMap hi (hυτ.trans hτσ) := by
  simpa [faceAffineCoordinateRingMap] using
    affineCoordinateRingMap_comp hi hi hi (AddMonoidHom.id N) (AddMonoidHom.id N)
      LinearMap.id LinearMap.id (fun _ ↦ rfl) (fun _ ↦ rfl)
      (fun _ hx ↦ hυτ.le hx) (fun _ hx ↦ hτσ.le hx)

/-- The canonical morphism from the affine toric scheme of a face to that of its ambient cone. -/
noncomputable def faceAffineToricSchemeMap (hi : IsIntegralLattice i)
    (hτσ : τ.IsFaceOf σ) : affineToricScheme hi τ ⟶ affineToricScheme hi σ :=
  affineToricSchemeMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
    (fun _ hx ↦ hτσ.le hx)

/-- The face morphism is the affine toric morphism for the identity lattice map. -/
theorem faceAffineToricSchemeMap_eq_affineToricSchemeMap (hi : IsIntegralLattice i)
    (hτσ : τ.IsFaceOf σ) :
    faceAffineToricSchemeMap hi hτσ =
      affineToricSchemeMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
        (by
          intro x hx
          exact hτσ.le hx) :=
  by
    rw [faceAffineToricSchemeMap]

/-- The morphism attached to a face inclusion is the spectrum of its coordinate-ring
restriction. -/
theorem faceAffineToricSchemeMap_def (hi : IsIntegralLattice i) (hτσ : τ.IsFaceOf σ) :
    faceAffineToricSchemeMap hi hτσ =
      Spec.map (CommRingCat.ofHom (faceAffineCoordinateRingMap hi hτσ).toRingHom) :=
  by
    rw [faceAffineToricSchemeMap, faceAffineCoordinateRingMap]
    exact affineToricSchemeMap_def hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
      (fun _ hx ↦ hτσ.le hx)

/-- The morphism of a cone viewed as its own face is the identity morphism. -/
@[simp]
theorem faceAffineToricSchemeMap_id (hi : IsIntegralLattice i) :
    faceAffineToricSchemeMap hi (PointedCone.IsFaceOf.refl σ) =
      𝟙 (affineToricScheme hi σ) := by
  rw [faceAffineToricSchemeMap_def, faceAffineCoordinateRingMap_id]
  exact Spec.map_id _

/-- The morphism of a composite face inclusion is the composite of the face morphisms. -/
@[simp]
theorem faceAffineToricSchemeMap_comp (hi : IsIntegralLattice i)
    (hυτ : υ.IsFaceOf τ) (hτσ : τ.IsFaceOf σ) :
    faceAffineToricSchemeMap hi hυτ ≫ faceAffineToricSchemeMap hi hτσ =
      faceAffineToricSchemeMap hi (hυτ.trans hτσ) := by
  simpa [faceAffineToricSchemeMap] using
    affineToricSchemeMap_comp hi hi hi (AddMonoidHom.id N) (AddMonoidHom.id N)
      LinearMap.id LinearMap.id (fun _ ↦ rfl) (fun _ ↦ rfl)
      (fun _ hx ↦ hυτ.le hx) (fun _ hx ↦ hτσ.le hx)

/-! ### Localizations and open immersions -/

/-- For a character `m` in the dual semigroup of a finitely generated cone `σ`, the restriction
map from the coordinate ring of `σ` to that of the face `σ ⊓ ker m` is the localization away from
the monomial of `m`. -/
theorem isLocalization_away_affineCoordinateRingMap_inf_ker (hi : IsIntegralLattice i)
    (hσ : σ.FG) (m : dualSemigroup hi σ) :
    letI := (affineCoordinateRingMap
      (σ := σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))) (τ := σ) hi hi
      (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl) (fun _ hx ↦ hx.1)).toRingHom.toAlgebra
    IsLocalization.Away (MonoidAlgebra.single (ofAdd m) (1 : ℂ))
      (affineCoordinateRing hi
        (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) := by
  set F := σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))
  have hmaps : Set.MapsTo (LinearMap.id : V →ₗ[ℝ] V) F σ := fun _ hx ↦ hx.1
  set f := AddMonoidHom.toMultiplicative
    (dualSemigroupMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl) hmaps)
  have hf : ∀ u, ((toAdd (f u) : dualSemigroup hi F) : N →+ ℤ) = toAdd u := fun u ↦
    coe_dualSemigroupMap_id hi hmaps _
  have hring : (affineCoordinateRingMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
      hmaps).toRingHom = MonoidAlgebra.mapDomainRingHom ℂ f := by
    have halg : affineCoordinateRingMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
        hmaps = MonoidAlgebra.mapDomainAlgHom ℂ ℂ f := by
      refine MonoidAlgebra.algHom_ext (fun u ↦ ?_) (Subsingleton.elim _ _)
      obtain ⟨u, rfl⟩ := ofAdd.surjective u
      simp [f]
    rw [halg]
    ext <;> simp
  rw [hring]
  refine MonoidAlgebra.isLocalization_away_mapDomainRingHom ℂ f ?_ (ofAdd m) ?_ ?_
  · intro u v huv
    apply toAdd.injective
    apply Subtype.ext
    rw [← hf, ← hf, huv]
  · -- The image of `m` is invertible because `-m` lies in the dual semigroup of the face.
    refine IsUnit.of_mul_eq_one (ofAdd ⟨-(m : N →+ ℤ), neg_mem_dualSemigroup_inf_ker hi σ m⟩) ?_
    apply toAdd.injective
    apply Subtype.ext
    simp [hf]
  · intro y
    obtain ⟨n, hn⟩ := exists_add_nsmul_mem_dualSemigroup hi hσ m.2 (toAdd y).2
    refine ⟨n, ofAdd ⟨_, hn⟩, ?_⟩
    apply toAdd.injective
    apply Subtype.ext
    simp [hf]

/-- For a character `m` in the dual semigroup of a finitely generated cone `σ`, the morphism from
the affine toric scheme of the face `σ ⊓ ker m` to that of `σ` is an open immersion. -/
theorem isOpenImmersion_affineToricSchemeMap_inf_ker {N : Type u} [AddCommGroup N]
    {i : N →+ V} (hi : IsIntegralLattice i) (hσ : σ.FG) (m : dualSemigroup hi σ) :
    IsOpenImmersion (affineToricSchemeMap
      (σ := σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))) (τ := σ)
      hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl) (fun _ hx ↦ hx.1)) := by
  let := (affineCoordinateRingMap
    (σ := σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))) (τ := σ)
    hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl) (fun _ hx ↦ hx.1)).toRingHom.toAlgebra
  have := isLocalization_away_affineCoordinateRingMap_inf_ker hi hσ m
  have h := IsOpenImmersion.of_isLocalization
    (S := affineCoordinateRing hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))))
    (MonoidAlgebra.single (ofAdd m) (1 : ℂ))
  rw [RingHom.algebraMap_toAlgebra] at h
  convert h using 1
  exact affineToricSchemeMap_def ..

private theorem range_faceAffineToricSchemeMap_of_eq (hi : IsIntegralLattice i) (hσ : σ.FG)
    (hτσ : τ.IsFaceOf σ) (m : dualSemigroup hi σ)
    (hm : σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)) = τ) :
    Set.range (faceAffineToricSchemeMap hi hτσ) =
      (PrimeSpectrum.basicOpen (MonoidAlgebra.single (ofAdd m) (1 : ℂ)) :
        Set (PrimeSpectrum (affineCoordinateRing hi σ))) := by
  subst hm
  let := (faceAffineCoordinateRingMap hi hτσ).toRingHom.toAlgebra
  have : IsLocalization.Away (MonoidAlgebra.single (ofAdd m) (1 : ℂ))
      (affineCoordinateRing hi
        (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) :=
    isLocalization_away_affineCoordinateRingMap_inf_ker hi hσ m
  rw [faceAffineToricSchemeMap_def]
  exact PrimeSpectrum.localization_away_comap_range _ _

/-- For a character `m` in the dual semigroup of a finitely generated cone `σ`, the image of the
affine toric scheme of the face `σ ⊓ ker m` in that of `σ` is the basic open set where the
monomial of `m` does not vanish. -/
theorem range_faceAffineToricSchemeMap (hi : IsIntegralLattice i) (hσ : σ.FG)
    (m : dualSemigroup hi σ) :
    Set.range (faceAffineToricSchemeMap hi
      (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2))) =
      (PrimeSpectrum.basicOpen (MonoidAlgebra.single (ofAdd m) (1 : ℂ)) :
        Set (PrimeSpectrum (affineCoordinateRing hi σ))) :=
  range_faceAffineToricSchemeMap_of_eq hi hσ _ m rfl

namespace IsRegularCone

variable {τ : PointedCone ℝ V}

/-- For a face `τ` of a regular cone `σ`, the restriction map from the coordinate ring of `σ` to
that of `τ` is the localization away from the monomial of a character in the dual semigroup
of `σ`. -/
theorem exists_isLocalization_away_faceAffineCoordinateRingMap (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) (hτ : τ.IsFaceOf σ) :
    ∃ m : dualSemigroup hi σ,
      letI := (faceAffineCoordinateRingMap hi hτ).toRingHom.toAlgebra
      IsLocalization.Away (MonoidAlgebra.single (ofAdd m) (1 : ℂ))
        (affineCoordinateRing hi τ) := by
  obtain ⟨m, hm, rfl⟩ := hσ.exists_mem_dualSemigroup_inf_ker_eq hi hτ
  have hh : hτ = PointedCone.isFaceOf_inf_ker
      ((mem_dualSemigroup hi m).1 hm) := Subsingleton.elim _ _
  subst hτ
  refine ⟨⟨m, hm⟩, ?_⟩
  rw [faceAffineCoordinateRingMap]
  exact isLocalization_away_affineCoordinateRingMap_inf_ker hi hσ.fg ⟨m, hm⟩

/-- For a face `τ` of a regular cone `σ`, the morphism from the affine toric scheme of `τ` to that
of `σ` is an open immersion. -/
theorem isOpenImmersion_faceAffineToricSchemeMap {N : Type u} [AddCommGroup N] {i : N →+ V}
    (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ) (hτ : τ.IsFaceOf σ) :
    IsOpenImmersion (faceAffineToricSchemeMap hi hτ) := by
  obtain ⟨m, hm, rfl⟩ := hσ.exists_mem_dualSemigroup_inf_ker_eq hi hτ
  have hh : hτ = PointedCone.isFaceOf_inf_ker
      ((mem_dualSemigroup hi m).1 hm) := Subsingleton.elim _ _
  subst hτ
  rw [faceAffineToricSchemeMap_def, faceAffineCoordinateRingMap]
  convert isOpenImmersion_affineToricSchemeMap_inf_ker hi hσ.fg ⟨m, hm⟩ using 1
  exact (affineToricSchemeMap_def ..).symm

/-- For two faces `τ` and `υ` of a regular cone `σ`, the image of the affine toric scheme of
`τ ⊓ υ` in that of `σ` is the intersection of the images of the affine toric schemes of `τ` and
of `υ`. -/
theorem range_faceAffineToricSchemeMap_inf (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) {υ : PointedCone ℝ V} (hτ : τ.IsFaceOf σ) (hυ : υ.IsFaceOf σ) :
    Set.range (faceAffineToricSchemeMap hi (hτ.inf_left hυ)) =
      Set.range (faceAffineToricSchemeMap hi hτ) ∩ Set.range (faceAffineToricSchemeMap hi hυ) := by
  obtain ⟨m₁, hm₁, h₁⟩ := hσ.exists_mem_dualSemigroup_inf_ker_eq hi hτ
  obtain ⟨m₂, hm₂, h₂⟩ := hσ.exists_mem_dualSemigroup_inf_ker_eq hi hυ
  have hmul : MonoidAlgebra.single (ofAdd (⟨m₁, hm₁⟩ + ⟨m₂, hm₂⟩ : dualSemigroup hi σ)) (1 : ℂ) =
      MonoidAlgebra.single (ofAdd ⟨m₁, hm₁⟩) 1 * MonoidAlgebra.single (ofAdd ⟨m₂, hm₂⟩) 1 := by
    rw [MonoidAlgebra.single_mul_single, ofAdd_add, mul_one]
  rw [range_faceAffineToricSchemeMap_of_eq hi hσ.fg hτ ⟨m₁, hm₁⟩ h₁,
    range_faceAffineToricSchemeMap_of_eq hi hσ.fg hυ ⟨m₂, hm₂⟩ h₂,
    range_faceAffineToricSchemeMap_of_eq hi hσ.fg _ (⟨m₁, hm₁⟩ + ⟨m₂, hm₂⟩)
      (by rw [AddSubmonoid.coe_add, map_add, PointedCone.inf_ker_add
        ((mem_dualSemigroup hi m₁).1 hm₁) ((mem_dualSemigroup hi m₂).1 hm₂), h₁, h₂]),
    hmul, PrimeSpectrum.basicOpen_mul]
  exact TopologicalSpace.Opens.coe_inf ..

end IsRegularCone

/-! ### Pairwise overlaps in a regular fan -/

namespace Fan

variable (Φ : Fan i)

/-- The affine toric chart indexed by a cone of a fan. -/
noncomputable abbrev affineToricChart (σ : Φ.cones) : Scheme :=
  affineToricScheme Φ.lattice σ

/-- The affine toric scheme of the intersection of two cones is their pairwise overlap chart. -/
noncomputable abbrev affineToricOverlap (σ τ : Φ.cones) : Scheme :=
  affineToricScheme Φ.lattice (σ.1 ⊓ τ.1)

/-- The canonical map from a pairwise overlap into its left affine chart. -/
noncomputable def affineToricOverlapLeft (σ τ : Φ.cones) :
    Φ.affineToricOverlap σ τ ⟶ Φ.affineToricChart σ :=
  faceAffineToricSchemeMap Φ.lattice
    (Φ.inf_isFaceOf_left σ.property τ.property)

/-- The canonical map from a pairwise overlap into its right affine chart. -/
noncomputable def affineToricOverlapRight (σ τ : Φ.cones) :
    Φ.affineToricOverlap σ τ ⟶ Φ.affineToricChart τ :=
  faceAffineToricSchemeMap Φ.lattice
    (Φ.inf_isFaceOf_right σ.property τ.property)

/-- The left overlap leg is the face map of the inclusion `σ ⊓ τ ≼ σ`. -/
@[simp]
theorem affineToricOverlapLeft_def (σ τ : Φ.cones) :
    Φ.affineToricOverlapLeft σ τ =
      faceAffineToricSchemeMap Φ.lattice (Φ.inf_isFaceOf_left σ.property τ.property) := by
  rw [affineToricOverlapLeft]

/-- The right overlap leg is the face map of the inclusion `σ ⊓ τ ≼ τ`. -/
@[simp]
theorem affineToricOverlapRight_def (σ τ : Φ.cones) :
    Φ.affineToricOverlapRight σ τ =
      faceAffineToricSchemeMap Φ.lattice (Φ.inf_isFaceOf_right σ.property τ.property) := by
  rw [affineToricOverlapRight]

/-- If the left target cone is regular, the map from a pairwise overlap into its left chart is an
open immersion. -/
theorem isOpenImmersion_affineToricOverlapLeft (σ τ : Φ.cones)
    (hσ : IsRegularCone i σ.1) :
    IsOpenImmersion (Φ.affineToricOverlapLeft σ τ) :=
  hσ.isOpenImmersion_faceAffineToricSchemeMap Φ.lattice
    (Φ.inf_isFaceOf_left σ.property τ.property)

/-- If the right target cone is regular, the map from a pairwise overlap into its right chart is an
open immersion. -/
theorem isOpenImmersion_affineToricOverlapRight (σ τ : Φ.cones)
    (hτ : IsRegularCone i τ.1) :
    IsOpenImmersion (Φ.affineToricOverlapRight σ τ) :=
  hτ.isOpenImmersion_faceAffineToricSchemeMap Φ.lattice
    (Φ.inf_isFaceOf_right σ.property τ.property)

end Fan

end TauCeti.Toric
