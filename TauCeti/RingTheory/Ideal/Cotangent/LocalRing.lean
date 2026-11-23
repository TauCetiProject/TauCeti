/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Cotangent spaces of local rings under ring equivalences

A ring isomorphism `σ : R ≃+* S` between local rings induces a semilinear equivalence
`IsLocalRing.cotangentSpaceEquiv σ : CotangentSpace R ≃ₛₗ[ResidueField.mapEquiv σ] CotangentSpace S`
between their cotangent spaces over the induced isomorphism of residue fields, and hence preserves
the residue-field dimension of the cotangent space.

## Main declarations

* `IsLocalRing.cotangentSpaceEquiv`: a ring isomorphism between local rings induces a semilinear
  equivalence between their cotangent spaces over the induced isomorphism of residue fields.
* `IsLocalRing.finrank_cotangentSpace_eq_of_ringEquiv`: a ring isomorphism between local rings
  preserves the dimension of the cotangent space over the residue field.
-/

public section

namespace IsLocalRing

/-- `ResidueField.mapEquiv σ` and `ResidueField.mapEquiv σ.symm` form an inverse pair of ring
homomorphisms, allowing semilinear equivalences over `ResidueField.mapEquiv σ`. -/
instance ResidueField.ringHomInvPair_mapEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (σ : R ≃+* S) :
    RingHomInvPair (ResidueField.mapEquiv σ : ResidueField R →+* ResidueField S)
      (ResidueField.mapEquiv σ.symm : ResidueField S →+* ResidueField R) :=
  .of_ringEquiv (ResidueField.mapEquiv σ)

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
    obtain ⟨m, rfl⟩ := Ideal.toCotangent_surjective _ m
    change Ideal.mapCotangent _ _ _ _ (residue R r • Ideal.toCotangent _ m) =
      (ResidueField.mapEquiv σ : ResidueField R →+* ResidueField S) (residue R r) •
        Ideal.mapCotangent _ _ _ _ (Ideal.toCotangent _ m)
    rw [← ResidueField.algebraMap_eq, IsScalarTower.algebraMap_smul,
      RingHom.coe_coe, ResidueField.mapEquiv_apply, ResidueField.algebraMap_eq,
      ResidueField.map_residue, ← ResidueField.algebraMap_eq,
      IsScalarTower.algebraMap_smul]
    apply congrArg (Ideal.toCotangent _)
    ext
    exact map_mul σ r m

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
      Module.finrank (ResidueField S) (CotangentSpace S) := by
  let e := cotangentSpaceEquiv σ
  simpa [Module.finrank] using congrArg Cardinal.toNat
    (lift_rank_eq_of_equiv_equiv (ResidueField.mapEquiv σ) e.toAddEquiv
      (ResidueField.mapEquiv σ).bijective e.map_smulₛₗ)

end IsLocalRing
