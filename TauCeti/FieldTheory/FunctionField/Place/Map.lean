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
* `TauCeti.Place.degree_map`: transport preserves the degree of a place, because `e` induces a
  `k`-algebra isomorphism of residue fields.
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

@[simp]
theorem map_refl : P.map AlgEquiv.refl = P :=
  Place.ext (Valuation.ext fun _ ↦ rfl)

@[simp]
theorem map_map {F'' : Type*} [Field F''] [Algebra k F''] (e' : F' ≃ₐ[k] F'') :
    (P.map e).map e' = P.map (e.trans e') :=
  Place.ext (Valuation.ext fun _ ↦ rfl)

theorem map_symm_map : (P.map e).map e.symm = P := by
  rw [map_map, AlgEquiv.self_trans_symm, map_refl]

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

/-- The isomorphism `e⁻¹` carries the valuation ring of `P.map e` isomorphically onto the
valuation ring of `P`. -/
private def integersEquivMap : (P.map e).integers ≃+* P.integers where
  toFun x := ⟨e.symm x, (mem_integers_map_iff e P).mp x.2⟩
  invFun y := ⟨e y, (mem_integers_map_iff e P).mpr (by simp)⟩
  left_inv _ := Subtype.ext (by simp)
  right_inv _ := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

@[simp]
private theorem coe_integersEquivMap (x : (P.map e).integers) :
    ((integersEquivMap e P x : P.integers) : F) = e.symm (x : F') := rfl

/-- **Transport preserves the degree of a place**: `e⁻¹` carries the valuation ring of `P.map e`
onto that of `P` and commutes with the constants, so it identifies the two residue fields as
`k`-algebras. -/
@[simp]
theorem degree_map : (P.map e).degree = P.degree := by
  rw [degree_eq_finrank, degree_eq_finrank]
  refine Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl k)
    (IsLocalRing.ResidueField.mapEquiv (integersEquivMap e P)) (RingHom.ext fun c ↦ ?_)
  have hfix : integersEquivMap e P (algebraMap k (P.map e).integers c) =
      algebraMap k P.integers c :=
    Subtype.ext (by simp)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.refl_apply, IsLocalRing.ResidueField.mapEquiv_apply,
    IsScalarTower.algebraMap_apply k P.integers P.ResidueField,
    IsScalarTower.algebraMap_apply k (P.map e).integers (P.map e).ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ResidueField.map_residue, hfix]

end TauCeti.Place
