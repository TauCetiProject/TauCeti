/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Normal.Basic

/-!
# Restricting automorphisms to a stable intermediate field

Let `E` be an intermediate field of `L / K` carried onto itself by every `K`-automorphism of `L`.
Restriction is then a group homomorphism `Aut(L / K) →* Aut(E / K)`, whose kernel is the subgroup
fixing `E` pointwise. This is the general form of the restriction map of Galois theory, which
needs no normality: stability under the automorphisms is assumed instead of derived.

## Main definitions

* `IntermediateField.restrictAlgEquivHom`: the restriction homomorphism
  `Aut(L / K) →* Aut(E / K)` for a stable intermediate field `E`.

## Main results

* `IntermediateField.coe_restrictAlgEquivHom_apply` and
  `IntermediateField.coe_restrictAlgEquivHom_symm_apply`: the restriction and its inverse act as
  the automorphism and its inverse do.
* `IntermediateField.ker_restrictAlgEquivHom`: its kernel is `E.fixingSubgroup`.
* `IntermediateField.natCard_fixingSubgroup_of_finrank_eq_two`: for a separable quadratic
  `L / E`, the fixing subgroup of `E` has order two.
-/

public section

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (E : IntermediateField K L)
  (hE : ∀ σ : L ≃ₐ[K] L, E.map σ.toAlgHom = E)

/-- **Restriction to a stable intermediate field**: for `E` carried onto itself by every
`K`-automorphism of `L`, the homomorphism `Aut(L / K) →* Aut(E / K)` restricting an automorphism
to `E`. -/
noncomputable def restrictAlgEquivHom : (L ≃ₐ[K] L) →* (E ≃ₐ[K] E) where
  toFun σ := (E.equivMap σ.toAlgHom).trans (equivOfEq (hE σ))
  map_one' := by
    ext y
    simp [coe_equivMap_apply, equivOfEq_apply]
  map_mul' σ τ := by
    ext y
    simp [coe_equivMap_apply, equivOfEq_apply]

/-- The restriction of `σ` to `E` acts as `σ`. -/
@[simp]
theorem coe_restrictAlgEquivHom_apply (σ : L ≃ₐ[K] L) (y : E) :
    (restrictAlgEquivHom E hE σ y : L) = σ y := by
  simp [restrictAlgEquivHom, coe_equivMap_apply,
    equivOfEq_apply]

/-- The inverse of the restriction of `σ` to `E` acts as `σ⁻¹`. -/
@[simp]
theorem coe_restrictAlgEquivHom_symm_apply (σ : L ≃ₐ[K] L) (y : E) :
    ((restrictAlgEquivHom E hE σ).symm y : L) = σ.symm y := by
  rw [← AlgEquiv.aut_inv, ← map_inv, coe_restrictAlgEquivHom_apply, AlgEquiv.aut_inv]

/-- Restriction commutes with inverses, read in `L`: `σ⁻¹` carries an element of `E` to the
image of its `σ|_E⁻¹`-preimage. -/
theorem symm_apply_algebraMap_eq_algebraMap_restrictAlgEquivHom_symm_apply (σ : L ≃ₐ[K] L)
    (y : E) : σ.symm (algebraMap E L y) = algebraMap E L ((restrictAlgEquivHom E hE σ).symm y) := by
  rw [IntermediateField.algebraMap_apply, IntermediateField.algebraMap_apply,
    coe_restrictAlgEquivHom_symm_apply]

/-- **The kernel of restriction is the fixing subgroup**: an automorphism restricts to the identity
of `E` exactly when it fixes `E` pointwise. -/
theorem ker_restrictAlgEquivHom : (restrictAlgEquivHom E hE).ker = E.fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_ker, mem_fixingSubgroup_iff]
  constructor
  · intro h y hy
    have := congrArg (fun τ : E ≃ₐ[K] E ↦ (τ ⟨y, hy⟩ : L)) h
    simpa using this
  · intro h
    ext y
    simpa using h y y.2

/-- **The fixing subgroup of a separable quadratic subextension has order two**: a separable
quadratic extension is Galois, with Galois group of order `[L : E] = 2`. -/
theorem natCard_fixingSubgroup_of_finrank_eq_two (hdeg : Module.finrank E L = 2)
    [Algebra.IsSeparable E L] : Nat.card E.fixingSubgroup = 2 := by
  have : Algebra.IsQuadraticExtension E L := ⟨hdeg⟩
  rw [Nat.card_congr (fixingSubgroupEquiv E).toEquiv, IsGalois.card_aut_eq_finrank, hdeg]

end IntermediateField
