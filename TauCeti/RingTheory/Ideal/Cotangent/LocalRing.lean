/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent
public import TauCeti.RingTheory.LocalRing.ResidueField.Map
import TauCeti.LinearAlgebra.Basis.Semilinear

/-!
# Cotangent spaces of local rings under local homomorphisms

A local ring homomorphism `f : R →+* S` induces a semilinear map between cotangent spaces
`IsLocalRing.cotangentSpaceMap f : CotangentSpace R →ₛₗ[ResidueField.map f] CotangentSpace S`
over the induced map of residue fields (`IsLocalRing.mapCotangent_residue_smul`). In particular, a
ring isomorphism `σ : R ≃+* S` between local rings induces a semilinear equivalence
`IsLocalRing.cotangentSpaceEquiv σ : CotangentSpace R ≃ₛₗ[ResidueField.mapEquiv σ] CotangentSpace S`
between their cotangent spaces over the induced isomorphism of residue fields, and hence preserves
the residue-field dimension of the cotangent space.

## Main declarations

* `IsLocalRing.mapCotangent_residue_smul`: `Ideal.mapCotangent` is compatible with scalar
  multiplication by `IsLocalRing.residue`.
* `IsLocalRing.cotangentSpaceMap`: a local ring homomorphism induces a semilinear map between
  cotangent spaces over `IsLocalRing.ResidueField.map`, respecting identity and composition.
* `IsLocalRing.cotangentSpaceEquiv`: a ring isomorphism between local rings induces a semilinear
  equivalence between their cotangent spaces over `IsLocalRing.ResidueField.mapEquiv`, respecting
  identity, composition, and inversion.
* `IsLocalRing.finrank_cotangentSpace_eq_of_ringEquiv`: a ring isomorphism between local rings
  preserves the dimension of the cotangent space over the residue field.
-/

public section

namespace IsLocalRing

/-- The cotangent map induced by a local ring homomorphism is compatible with scalar
multiplication by residues. -/
@[simp]
theorem mapCotangent_residue_smul {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S)
    (h : maximalIdeal R ≤ (maximalIdeal S).comap f.toIntAlgHom)
    (r : R) (v : CotangentSpace R) :
    Ideal.mapCotangent (maximalIdeal R) (maximalIdeal S) f.toIntAlgHom h (residue R r • v) =
      residue S (f r) •
        Ideal.mapCotangent (maximalIdeal R) (maximalIdeal S) f.toIntAlgHom h v := by
  obtain ⟨m, rfl⟩ := Ideal.toCotangent_surjective _ v
  simp only [← ResidueField.algebraMap_eq, IsScalarTower.algebraMap_smul, ← map_smul,
    Ideal.mapCotangent_toCotangent]
  exact congrArg (Ideal.toCotangent _) (Subtype.ext (map_mul f r m))

/-- A local ring homomorphism between local rings induces a semilinear map between their
cotangent spaces over `ResidueField.map f`. -/
def cotangentSpaceMap {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) [IsLocalHom f] :
    CotangentSpace R →ₛₗ[ResidueField.map f] CotangentSpace S where
  toFun := Ideal.mapCotangent (maximalIdeal R) (maximalIdeal S) f.toIntAlgHom
    (maximalIdeal_comap f).symm.le
  map_add' := map_add _
  map_smul' r v := by
    obtain ⟨r, rfl⟩ := residue_surjective r
    exact mapCotangent_residue_smul f _ r v

/-- On `Ideal.toCotangent` representatives, `cotangentSpaceMap` acts by applying `f`. -/
@[simp]
theorem cotangentSpaceMap_toCotangent {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) [IsLocalHom f] (x : maximalIdeal R) :
    cotangentSpaceMap f (Ideal.toCotangent (maximalIdeal R) x) =
      Ideal.toCotangent (maximalIdeal S) ⟨f x, map_nonunit f x x.property⟩ :=
  Ideal.mapCotangent_toCotangent (maximalIdeal R) (maximalIdeal S) f.toIntAlgHom _ x

/-- The cotangent map induced by the identity ring homomorphism is `LinearMap.id'`. -/
theorem cotangentSpaceMap_id {R : Type*} [CommRing R] [IsLocalRing R] :
    cotangentSpaceMap (RingHom.id R) =
      (LinearMap.id' : CotangentSpace R →ₛₗ[ResidueField.map (RingHom.id R)] CotangentSpace R) := by
  ext v
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ v
  rfl

/-- Applying `cotangentSpaceMap` to the identity ring homomorphism is the identity on the
cotangent space. -/
@[simp]
theorem cotangentSpaceMap_id_apply {R : Type*} [CommRing R] [IsLocalRing R]
    (v : CotangentSpace R) :
    cotangentSpaceMap (RingHom.id R) v = v := by
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ v
  rfl

/-- `cotangentSpaceMap` respects composition of local ring homomorphisms. -/
theorem cotangentSpaceMap_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing T] (g : S →+* T) (f : R →+* S)
    [IsLocalHom g] [IsLocalHom f] :
    cotangentSpaceMap (g.comp f) = (cotangentSpaceMap g).comp (cotangentSpaceMap f) := by
  ext v
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ v
  simp

/-- Pointwise, `cotangentSpaceMap` respects composition of local ring homomorphisms. -/
@[simp]
theorem cotangentSpaceMap_comp_apply {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing T] (g : S →+* T) (f : R →+* S)
    [IsLocalHom g] [IsLocalHom f] (v : CotangentSpace R) :
    cotangentSpaceMap (g.comp f) v = cotangentSpaceMap g (cotangentSpaceMap f v) :=
  DFunLike.congr_fun (cotangentSpaceMap_comp g f) v

/-- A ring isomorphism between local rings induces a semilinear equivalence between their
cotangent spaces over `ResidueField.mapEquiv σ`. -/
def cotangentSpaceEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (σ : R ≃+* S) :
    CotangentSpace R ≃ₛₗ[(ResidueField.mapEquiv σ : ResidueField R →+* ResidueField S)]
      CotangentSpace S where
  __ := cotangentSpaceMap (σ : R →+* S)
  invFun := cotangentSpaceMap (σ.symm : S →+* R)
  left_inv v := by
    obtain ⟨s, rfl⟩ := Ideal.toCotangent_surjective _ v
    simp
  right_inv w := by
    obtain ⟨s, rfl⟩ := Ideal.toCotangent_surjective _ w
    simp

/-- The underlying semilinear map of `cotangentSpaceEquiv σ` is `cotangentSpaceMap σ`. -/
@[simp]
theorem cotangentSpaceEquiv_toLinearMap {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (σ : R ≃+* S) :
    (cotangentSpaceEquiv σ).toLinearMap = cotangentSpaceMap (σ : R →+* S) := by
  ext v
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ v
  rfl

/-- On `Ideal.toCotangent` representatives, `cotangentSpaceEquiv` acts by applying `σ`. -/
@[simp]
theorem cotangentSpaceEquiv_toCotangent {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (σ : R ≃+* S) (x : maximalIdeal R) :
    cotangentSpaceEquiv σ (Ideal.toCotangent (maximalIdeal R) x) =
      Ideal.toCotangent (maximalIdeal S) ⟨σ x, map_nonunit (σ : R →+* S) x x.property⟩ :=
  cotangentSpaceMap_toCotangent (σ : R →+* S) x

/-- On `Ideal.toCotangent` representatives, `(cotangentSpaceEquiv σ).symm` acts by applying
`σ.symm`. -/
@[simp]
theorem cotangentSpaceEquiv_symm_toCotangent {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (σ : R ≃+* S) (y : maximalIdeal S) :
    (cotangentSpaceEquiv σ).symm (Ideal.toCotangent (maximalIdeal S) y) =
      Ideal.toCotangent (maximalIdeal R)
        ⟨σ.symm y, map_nonunit (σ.symm : S →+* R) y y.property⟩ :=
  cotangentSpaceMap_toCotangent (σ.symm : S →+* R) y

/-- The inverse of `cotangentSpaceEquiv σ` is `cotangentSpaceEquiv σ.symm`. -/
theorem cotangentSpaceEquiv_symm {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (σ : R ≃+* S) :
    (cotangentSpaceEquiv σ).symm = cotangentSpaceEquiv σ.symm := by
  ext v
  obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective _ v
  exact (cotangentSpaceEquiv_symm_toCotangent σ y).trans
    (cotangentSpaceEquiv_toCotangent σ.symm y).symm

/-- `cotangentSpaceEquiv (RingEquiv.refl R)` is the identity semilinear equivalence over
`ResidueField.mapEquiv (RingEquiv.refl R)`. -/
theorem cotangentSpaceEquiv_refl {R : Type*} [CommRing R] [IsLocalRing R] :
    cotangentSpaceEquiv (RingEquiv.refl R) =
      LinearEquiv.ofLinearMap
        (LinearMap.id' : CotangentSpace R →ₛₗ[(ResidueField.mapEquiv (RingEquiv.refl R) :
          ResidueField R →+* ResidueField R)] CotangentSpace R)
        (LinearMap.id' : CotangentSpace R →ₛₗ[(ResidueField.mapEquiv (RingEquiv.refl R).symm :
          ResidueField R →+* ResidueField R)] CotangentSpace R)
        (by ext v; rfl) (by ext v; rfl) := by
  ext v
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ v
  rfl

/-- As a semilinear map, `cotangentSpaceEquiv (RingEquiv.refl R)` is `LinearMap.id'`. -/
theorem cotangentSpaceEquiv_refl_toLinearMap {R : Type*} [CommRing R] [IsLocalRing R] :
    (cotangentSpaceEquiv (RingEquiv.refl R)).toLinearMap = LinearMap.id' := by
  rw [cotangentSpaceEquiv_refl, LinearEquiv.toLinearMap_ofLinearMap]

/-- Applying `cotangentSpaceEquiv` to the identity ring equivalence is the identity on the
cotangent space. -/
@[simp]
theorem cotangentSpaceEquiv_refl_apply {R : Type*} [CommRing R] [IsLocalRing R]
    (v : CotangentSpace R) :
    cotangentSpaceEquiv (RingEquiv.refl R) v = v := by
  rw [cotangentSpaceEquiv_refl, LinearEquiv.coe_ofLinearMap, LinearMap.id'_apply]

/-- `cotangentSpaceEquiv` respects composition of ring equivalences. -/
theorem cotangentSpaceEquiv_trans {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing T] (σ : R ≃+* S) (τ : S ≃+* T) :
    cotangentSpaceEquiv (σ.trans τ) =
      (cotangentSpaceEquiv σ).trans (cotangentSpaceEquiv τ) := by
  ext v
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ v
  rfl

/-- Pointwise, `cotangentSpaceEquiv` respects composition of ring equivalences. -/
@[simp]
theorem cotangentSpaceEquiv_trans_apply {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing T] (σ : R ≃+* S) (τ : S ≃+* T)
    (v : CotangentSpace R) :
    cotangentSpaceEquiv (σ.trans τ) v = cotangentSpaceEquiv τ (cotangentSpaceEquiv σ v) := by
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ v
  simp

/-- A ring isomorphism between local rings preserves the dimension of the cotangent space over the
residue field. -/
theorem finrank_cotangentSpace_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (σ : R ≃+* S) :
    Module.finrank (ResidueField R) (CotangentSpace R) =
      Module.finrank (ResidueField S) (CotangentSpace S) :=
  (cotangentSpaceEquiv σ).finrank_eqₛₗ

end IsLocalRing
