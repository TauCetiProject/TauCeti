/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Basic

/-!
# Transport of places under semilinear field isomorphisms

An isomorphism of fields carrying one constant field onto another transports normalized places
by composing their valuations with its inverse. The residue fields are correspondingly
isomorphic, semilinearly over the constant-field isomorphism, so residue degrees are preserved.
This permits coefficient automorphisms to act on places even when they do not fix the constants
pointwise, as in Galois actions on base-changed curves.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Section I.1.
-/

public section

namespace TauCeti.Place

variable {k k' L L' : Type*} [Field k] [Field k'] [Field L] [Field L']
  [Algebra k L] [Algebra k' L']

/-- **Transport of places under a semilinear field isomorphism.** The compatibility equation
says that `τ` carries the constants along `σ`; the transported valuation is `v ∘ τ⁻¹`. -/
noncomputable def equivOfRingEquiv (σ : k ≃+* k') (τ : L ≃+* L')
    (h : ∀ c, τ (algebraMap k L c) = algebraMap k' L' (σ c)) :
    Place k L ≃ Place k' L' where
  toFun P :=
    { valuation := P.valuation.comap τ.symm.toRingHom
      valuation_surjective := P.valuation_surjective.comp τ.symm.surjective
      isTrivialOn := ⟨fun c hc ↦ by
        have h' : τ.symm (algebraMap k' L' c) = algebraMap k L (σ.symm c) := by
          apply τ.injective
          simp [h]
        rw [Valuation.comap_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, h']
        exact P.isTrivialOn.eq_one (σ.symm c) (by simpa using hc)⟩ }
  invFun Q :=
    { valuation := Q.valuation.comap τ.toRingHom
      valuation_surjective := Q.valuation_surjective.comp τ.surjective
      isTrivialOn := ⟨fun c hc ↦ by
        rw [Valuation.comap_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, h]
        exact Q.isTrivialOn.eq_one (σ c) (by simpa using hc)⟩ }
  left_inv P := Place.ext (Valuation.ext fun z ↦ by simp)
  right_inv Q := Place.ext (Valuation.ext fun z ↦ by simp)

variable (σ : k ≃+* k') (τ : L ≃+* L')
  (h : ∀ c, τ (algebraMap k L c) = algebraMap k' L' (σ c))

/-- The defining valuation formula for transport of a place. -/
@[simp]
theorem valuation_equivOfRingEquiv (P : Place k L) (z : L') :
    (equivOfRingEquiv σ τ h P).valuation z = P.valuation (τ.symm z) := (rfl)

/-- The order at the transported place is computed by applying the inverse field isomorphism. -/
@[simp]
theorem ord_equivOfRingEquiv (P : Place k L) (z : L') :
    (equivOfRingEquiv σ τ h P).ord z = P.ord (τ.symm z) := by
  rw [ord_def, ord_def, valuation_equivOfRingEquiv]

/-- The inverse transport has valuation `v ∘ τ`. -/
@[simp]
theorem valuation_equivOfRingEquiv_symm (Q : Place k' L') (z : L) :
    ((equivOfRingEquiv σ τ h).symm Q).valuation z = Q.valuation (τ z) := (rfl)

/-- Transport restricts to an isomorphism of the valuation rings. -/
noncomputable def integersEquivOfRingEquiv (P : Place k L) :
    P.integers ≃+* (equivOfRingEquiv σ τ h P).integers where
  toFun x := ⟨τ x, by
    rw [mem_integers_iff, valuation_equivOfRingEquiv, τ.symm_apply_apply]
    exact P.mem_integers_iff.mp x.2⟩
  invFun y := ⟨τ.symm y, by
    exact P.mem_integers_iff.mpr
      ((equivOfRingEquiv σ τ h P).mem_integers_iff.mp y.2)⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (map_mul τ _ _)
  map_add' x y := Subtype.ext (map_add τ _ _)

/-- The valuation-ring isomorphism is the restriction of the field isomorphism. -/
@[simp]
theorem coe_integersEquivOfRingEquiv (P : Place k L) (x : P.integers) :
    ((integersEquivOfRingEquiv σ τ h P x : (equivOfRingEquiv σ τ h P).integers) : L') =
      τ (x : L) := (rfl)

/-- **Residue degrees are preserved by semilinear transport.** The residue-field isomorphism
carries constants by `σ`, which suffices to preserve their vector-space dimension. -/
@[simp]
theorem degree_equivOfRingEquiv (P : Place k L) :
    (equivOfRingEquiv σ τ h P).degree = P.degree := by
  rw [degree_eq_finrank, degree_eq_finrank]
  symm
  refine Algebra.finrank_eq_of_equiv_equiv σ
    (IsLocalRing.ResidueField.mapEquiv (integersEquivOfRingEquiv σ τ h P))
    (RingHom.ext fun c ↦ ?_)
  have hc : integersEquivOfRingEquiv σ τ h P (algebraMap k P.integers c) =
      algebraMap k' (equivOfRingEquiv σ τ h P).integers (σ c) :=
    Subtype.ext (by simp [h])
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    IsLocalRing.ResidueField.mapEquiv_apply,
    IsScalarTower.algebraMap_apply k P.integers P.ResidueField,
    IsScalarTower.algebraMap_apply k' (equivOfRingEquiv σ τ h P).integers
      (equivOfRingEquiv σ τ h P).ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ResidueField.map_residue, hc]

end TauCeti.Place
