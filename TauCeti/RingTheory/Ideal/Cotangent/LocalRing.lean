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
# Cotangent spaces of local rings under ring equivalences

A local ring homomorphism induces a map between cotangent spaces compatible with the induced
scalar action on residue fields (`IsLocalRing.mapCotangent_residue_smul`). In particular, a ring
isomorphism `σ : R ≃+* S` between local rings induces a semilinear equivalence
`IsLocalRing.cotangentSpaceEquiv σ : CotangentSpace R ≃ₛₗ[ResidueField.mapEquiv σ] CotangentSpace S`
between their cotangent spaces over the induced isomorphism of residue fields, and hence preserves
the residue-field dimension of the cotangent space.

## Main declarations

* `IsLocalRing.mapCotangent_residue_smul`: `Ideal.mapCotangent` is compatible with scalar
  multiplication by `IsLocalRing.residue`.
* `IsLocalRing.cotangentSpaceEquiv`: a ring isomorphism between local rings induces a semilinear
  equivalence between their cotangent spaces over the induced isomorphism of residue fields.
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

/-- A ring isomorphism between local rings induces a semilinear equivalence between their
cotangent spaces over `ResidueField.mapEquiv σ`. -/
def cotangentSpaceEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (σ : R ≃+* S) :
    CotangentSpace R ≃ₛₗ[(ResidueField.mapEquiv σ : ResidueField R →+* ResidueField S)]
      CotangentSpace S where
  toFun := Ideal.mapCotangent (maximalIdeal R) (maximalIdeal S) σ.toRingHom.toIntAlgHom
    (maximalIdeal_comap (σ : R →+* S)).symm.le
  invFun := Ideal.mapCotangent (maximalIdeal S) (maximalIdeal R) σ.symm.toRingHom.toIntAlgHom
    (maximalIdeal_comap (σ.symm : S →+* R)).symm.le
  left_inv v := by
    obtain ⟨s, rfl⟩ := Ideal.toCotangent_surjective _ v
    simp
  right_inv w := by
    obtain ⟨s, rfl⟩ := Ideal.toCotangent_surjective _ w
    simp
  map_add' := map_add _
  map_smul' r m := by
    obtain ⟨r, rfl⟩ := residue_surjective r
    simp

/-- On `Ideal.toCotangent` representatives, `cotangentSpaceEquiv` acts by applying `σ`. -/
@[simp]
theorem cotangentSpaceEquiv_toCotangent {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (σ : R ≃+* S) (x : maximalIdeal R) :
    cotangentSpaceEquiv σ (Ideal.toCotangent (maximalIdeal R) x) =
      Ideal.toCotangent (maximalIdeal S) ⟨σ x, map_nonunit (σ : R →+* S) x x.property⟩ :=
  Ideal.mapCotangent_toCotangent (maximalIdeal R) (maximalIdeal S) σ.toRingHom.toIntAlgHom _ x

/-- On `Ideal.toCotangent` representatives, `(cotangentSpaceEquiv σ).symm` acts by applying
`σ.symm`. -/
@[simp]
theorem cotangentSpaceEquiv_symm_toCotangent {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (σ : R ≃+* S) (y : maximalIdeal S) :
    (cotangentSpaceEquiv σ).symm (Ideal.toCotangent (maximalIdeal S) y) =
      Ideal.toCotangent (maximalIdeal R)
        ⟨σ.symm y, map_nonunit (σ.symm : S →+* R) y y.property⟩ :=
  Ideal.mapCotangent_toCotangent (maximalIdeal S) (maximalIdeal R) σ.symm.toRingHom.toIntAlgHom _ y

/-- Applying `cotangentSpaceEquiv` to the identity ring equivalence is the identity on the
cotangent space. -/
@[simp]
theorem cotangentSpaceEquiv_refl {R : Type*} [CommRing R] [IsLocalRing R]
    (v : CotangentSpace R) :
    cotangentSpaceEquiv (RingEquiv.refl R) v = v := by
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ v
  rw [cotangentSpaceEquiv_toCotangent]
  simp

/-- `cotangentSpaceEquiv` respects composition of ring equivalences. -/
@[simp]
theorem cotangentSpaceEquiv_trans {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing T] (σ : R ≃+* S) (τ : S ≃+* T)
    (v : CotangentSpace R) :
    cotangentSpaceEquiv (σ.trans τ) v = cotangentSpaceEquiv τ (cotangentSpaceEquiv σ v) := by
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ v
  simp

/-- Applying `cotangentSpaceEquiv` to `σ.symm` agrees with `(cotangentSpaceEquiv σ).symm`. -/
@[simp]
theorem cotangentSpaceEquiv_symm {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (σ : R ≃+* S) (v : CotangentSpace S) :
    cotangentSpaceEquiv σ.symm v = (cotangentSpaceEquiv σ).symm v := by
  obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective _ v
  rw [cotangentSpaceEquiv_toCotangent, cotangentSpaceEquiv_symm_toCotangent]

/-- A ring isomorphism between local rings preserves the dimension of the cotangent space over the
residue field. -/
theorem finrank_cotangentSpace_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (σ : R ≃+* S) :
    Module.finrank (ResidueField R) (CotangentSpace R) =
      Module.finrank (ResidueField S) (CotangentSpace S) :=
  (cotangentSpaceEquiv σ).finrank_eqₛₗ

end IsLocalRing
