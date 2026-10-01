/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic

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

* `IntermediateField.coe_restrictAlgEquivHom_apply`: the restriction acts as the
  automorphism does.
* `IntermediateField.ker_restrictAlgEquivHom`: its kernel is `E.fixingSubgroup`.
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

end IntermediateField
