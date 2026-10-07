/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Basic

/-!
# Transport of places along isomorphisms

A `k`-algebra isomorphism `e : F ≃ₐ[k] F'` carries a place `P` of `F / k` to the place `P.map e`
of `F' / k` whose valuation is `v_P ∘ e⁻¹`. Normalization is preserved because `e` is bijective,
and triviality on the constants because `e` commutes with the structure maps from `k`. The
construction is the one behind the action of `Aut(F' / F)` on the places of `F' / k`
(`TauCeti.Place.instMulActionAlgEquiv`), which it extends to isomorphisms between different
fields; the two agree on automorphisms (`TauCeti.Place.smul_eq_map`).

## Main definitions

* `TauCeti.Place.map`: the place `P.map e` of `F'` obtained from a place `P` of `F` and an
  isomorphism `e : F ≃ₐ[k] F'`.
* `TauCeti.Place.mapEquiv`: the resulting bijection between the places of `F` and those of `F'`.

## Main results

* `TauCeti.Place.valuation_map_apply` and `TauCeti.Place.ord_map_apply`: `e` carries the
  valuation and the order function of `P` to those of `P.map e`.
* `TauCeti.Place.integersEquivMap` and `TauCeti.Place.residueFieldEquivMap`: `e` carries the
  valuation ring and the residue field of `P` isomorphically onto those of `P.map e`.
* `TauCeti.Place.degree_map`: transport preserves the degree of a place.
-/

public section

namespace TauCeti.Place

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']

/-- **Transport of a place along an isomorphism**: the place `P.map e` of `F' / k` whose
valuation is `v_P ∘ e⁻¹`, for a `k`-algebra isomorphism `e : F ≃ₐ[k] F'` and a place `P` of
`F / k`. -/
def map (e : F ≃ₐ[k] F') (P : Place k F) : Place k F' where
  valuation := P.valuation.comap (e.symm : F' →+* F)
  valuation_surjective := fun y ↦ by
    obtain ⟨x, hx⟩ := P.valuation_surjective y
    exact ⟨e x, by simpa using hx⟩
  isTrivialOn :=
    { eq_one := fun c hc ↦ by
        rw [Valuation.comap_apply, RingHom.coe_coe, AlgEquiv.commutes]
        exact P.isTrivialOn.eq_one c hc }

variable (e : F ≃ₐ[k] F') (P : Place k F)

/-- **The defining property of transport**: the valuation of `P.map e` is the valuation of `P`
composed with `e⁻¹`. -/
@[simp]
theorem valuation_map (x : F') : (P.map e).valuation x = P.valuation (e.symm x) := by rfl

/-- Transport moves the valuation along `e`. -/
theorem valuation_map_apply (x : F) : (P.map e).valuation (e x) = P.valuation x := by
  simp

/-- The order function of `P.map e` is the order function of `P` composed with `e⁻¹`. -/
@[simp]
theorem ord_map (x : F') : (P.map e).ord x = P.ord (e.symm x) := by
  rw [ord_def, ord_def, valuation_map]

/-- Transport moves the order function along `e`. -/
theorem ord_map_apply (x : F) : (P.map e).ord (e x) = P.ord x := by
  simp

/-- Membership in the valuation ring of `P.map e`, read off at `P`. -/
theorem mem_integers_map_iff {x : F'} : x ∈ (P.map e).integers ↔ e.symm x ∈ P.integers := by
  simp

/-- Transport along the identity is the identity. -/
@[simp]
theorem map_refl : P.map AlgEquiv.refl = P :=
  Place.ext (Valuation.ext fun _ ↦ rfl)

/-- Transport respects composition: transporting along `e` and then along `e'` is transport
along `e.trans e'`. -/
@[simp]
theorem map_map {F'' : Type*} [Field F''] [Algebra k F''] (e' : F' ≃ₐ[k] F'') :
    (P.map e).map e' = P.map (e.trans e') :=
  Place.ext (Valuation.ext fun _ ↦ rfl)

/-- Transport along `e.symm` undoes transport along `e`. -/
theorem map_symm_map : (P.map e).map e.symm = P := by
  rw [map_map, AlgEquiv.self_trans_symm, map_refl]

/-- Transport along `e` undoes transport along `e.symm`. -/
theorem map_map_symm (Q : Place k F') : (Q.map e.symm).map e = Q := by
  rw [map_map, AlgEquiv.symm_trans_self, map_refl]

/-- **Transport is a bijection** between the places of `F / k` and those of `F' / k`, with
inverse the transport along `e⁻¹`. -/
def mapEquiv : Place k F ≃ Place k F' where
  toFun := map e
  invFun := map e.symm
  left_inv := map_symm_map e
  right_inv := map_map_symm e

@[simp]
theorem mapEquiv_apply : mapEquiv e P = P.map e := by rfl

@[simp]
theorem mapEquiv_symm_apply (Q : Place k F') : (mapEquiv e).symm Q = Q.map e.symm := by rfl

/-- **Transport of the valuation ring**: `e` carries the valuation ring of `P` isomorphically
onto the valuation ring of `P.map e`. -/
def integersEquivMap : P.integers ≃+* (P.map e).integers where
  toFun x := ⟨e x, (mem_integers_map_iff e P).mpr (by simp)⟩
  invFun y := ⟨e.symm y, (mem_integers_map_iff e P).mp y.2⟩
  left_inv _ := Subtype.ext (by simp)
  right_inv _ := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

@[simp]
theorem coe_integersEquivMap (x : P.integers) :
    ((integersEquivMap e P x : (P.map e).integers) : F') = e (x : F) := by rfl

@[simp]
theorem coe_integersEquivMap_symm (y : (P.map e).integers) :
    (((integersEquivMap e P).symm y : P.integers) : F) = e.symm (y : F') := by rfl

/-- `e` carries the constants of `𝒪_P` to the constants of `𝒪_{P.map e}`. -/
@[simp]
theorem integersEquivMap_algebraMap (c : k) :
    integersEquivMap e P (algebraMap k P.integers c) = algebraMap k (P.map e).integers c :=
  Subtype.ext (by simp)

/-- **Transport of the residue field**: the `k`-algebra isomorphism `F_P ≃ F_{P.map e}` of
residue fields induced by `e`. -/
noncomputable def residueFieldEquivMap : P.ResidueField ≃ₐ[k] (P.map e).ResidueField :=
  AlgEquiv.ofRingEquiv (f := IsLocalRing.ResidueField.mapEquiv (integersEquivMap e P)) fun c ↦ by
    simp only [IsScalarTower.algebraMap_apply k P.integers P.ResidueField,
      IsScalarTower.algebraMap_apply k (P.map e).integers (P.map e).ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue, RingHom.coe_coe, integersEquivMap_algebraMap]

/-- The residue-field isomorphism of transport sends the residue of `x` at `P` to the residue
of `e x` at `P.map e`. -/
@[simp]
theorem residueFieldEquivMap_residue (x : P.integers) :
    residueFieldEquivMap e P (IsLocalRing.residue P.integers x) =
      IsLocalRing.residue (P.map e).integers (integersEquivMap e P x) := by
  simp only [residueFieldEquivMap, AlgEquiv.ofRingEquiv_apply,
    IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue, RingHom.coe_coe]

/-- **Transport preserves the degree of a place**: `e` identifies the residue fields of `P` and
`P.map e` as `k`-algebras. -/
@[simp]
theorem degree_map : (P.map e).degree = P.degree := by
  rw [degree_eq_finrank, degree_eq_finrank]
  exact (residueFieldEquivMap e P).toLinearEquiv.finrank_eq.symm

end TauCeti.Place
