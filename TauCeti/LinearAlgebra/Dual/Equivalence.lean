/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Algebra.Tower

/-!
# Recovering module equivalences from scalar duals

An equivalence between the left scalar duals of two reflexive right modules gives an
equivalence of the original right modules in the opposite direction. The dual actions are
specified by equivariant pairings, avoiding competing global module instances on duals.
This lets constructions involving scalar duality recover actual module isomorphism classes.
Conversely, a right-module equivalence transports the scalar duals in the opposite direction
without requiring reflexivity.

The construction uses Mathlib's `Module.evalEquiv` and `LinearEquiv.dualMap`; the
equivariant pairing interface follows `LinearEquiv.dualEndRingEquiv`.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section I.3.
-/

public section

namespace LinearEquiv

universe u v w₁ w₂ z₁ z₂

variable {k : Type u} [CommSemiring k] {A : Type v} [Semiring A] [Algebra k A]
  {N₁ : Type w₁} {N₂ : Type w₂}
  [AddCommMonoid N₁] [Module Aᵐᵒᵖ N₁] [Module k N₁] [IsScalarTower k Aᵐᵒᵖ N₁]
  [AddCommMonoid N₂] [Module Aᵐᵒᵖ N₂] [Module k N₂] [IsScalarTower k Aᵐᵒᵖ N₂]
  {Q₁ : Type z₁} {Q₂ : Type z₂}
  [AddCommMonoid Q₁] [Module A Q₁] [Module k Q₁]
  [AddCommMonoid Q₂] [Module A Q₂] [Module k Q₂]

/-- A right-module equivalence transports equivariantly identified scalar duals in the
reverse direction. No reflexivity assumption is required. -/
noncomputable def toEquivariantDual (e₁ : Q₁ ≃ₗ[k] Module.Dual k N₁)
    (e₂ : Q₂ ≃ₗ[k] Module.Dual k N₂)
    (h₁ : ∀ (a : A) (q : Q₁) (x : N₁), e₁ (a • q) x = e₁ q (MulOpposite.op a • x))
    (h₂ : ∀ (a : A) (q : Q₂) (x : N₂), e₂ (a • q) x = e₂ q (MulOpposite.op a • x))
    (f : N₂ ≃ₗ[Aᵐᵒᵖ] N₁) : Q₁ ≃ₗ[A] Q₂ := by
  let t := e₁.trans ((f.restrictScalars k).dualMap.trans e₂.symm)
  have ht (q : Q₁) (x : N₂) : e₂ (t q) x = e₁ q (f x) := by
    simp [t, LinearEquiv.dualMap_apply]
  refine { t with map_smul' := fun a q ↦ e₂.injective ?_ }
  ext x
  calc
    e₂ (t (a • q)) x = e₁ (a • q) (f x) := ht _ _
    _ = e₁ q (f (MulOpposite.op a • x)) := by rw [h₁, f.map_smul]
    _ = e₂ (a • t q) x := by rw [h₂, ht]

/-- Transport across equivariant scalar duals is precomposition by the original equivalence. -/
@[simp]
theorem toEquivariantDual_apply_apply (e₁ : Q₁ ≃ₗ[k] Module.Dual k N₁)
    (e₂ : Q₂ ≃ₗ[k] Module.Dual k N₂)
    (h₁ : ∀ (a : A) (q : Q₁) (x : N₁), e₁ (a • q) x = e₁ q (MulOpposite.op a • x))
    (h₂ : ∀ (a : A) (q : Q₂) (x : N₂), e₂ (a • q) x = e₂ q (MulOpposite.op a • x))
    (f : N₂ ≃ₗ[Aᵐᵒᵖ] N₁) (q : Q₁) (x : N₂) :
    e₂ (e₁.toEquivariantDual e₂ h₁ h₂ f q) x = e₁ q (f x) := by
  simp [toEquivariantDual, LinearEquiv.dualMap_apply]

variable [Module.IsReflexive k N₁] [Module.IsReflexive k N₂]

/-- An equivalence of equivariantly identified scalar duals recovers a right-module
equivalence in the reverse direction, provided both original modules are reflexive. -/
noncomputable def ofEquivariantDual (e₁ : Q₁ ≃ₗ[k] Module.Dual k N₁)
    (e₂ : Q₂ ≃ₗ[k] Module.Dual k N₂)
    (h₁ : ∀ (a : A) (q : Q₁) (x : N₁), e₁ (a • q) x = e₁ q (MulOpposite.op a • x))
    (h₂ : ∀ (a : A) (q : Q₂) (x : N₂), e₂ (a • q) x = e₂ q (MulOpposite.op a • x))
    (f : Q₁ ≃ₗ[A] Q₂) : N₂ ≃ₗ[Aᵐᵒᵖ] N₁ := by
  let : IsScalarTower k A Q₁ := IsScalarTower.of_algebraMap_smul fun c q ↦ by
    apply e₁.injective
    ext x
    simp [h₁, ← MulOpposite.algebraMap_apply]
  let : IsScalarTower k A Q₂ := IsScalarTower.of_algebraMap_smul fun c q ↦ by
    apply e₂.injective
    ext x
    simp [h₂, ← MulOpposite.algebraMap_apply]
  let d := e₁.symm.trans ((f.restrictScalars k).trans e₂)
  let t := (Module.evalEquiv k N₂).trans (d.dualMap.trans (Module.evalEquiv k N₁).symm)
  have ht (q : Q₁) (x : N₂) : e₁ q (t x) = e₂ (f q) x := by simp [t, d]
  exact
    { t with
      map_smul' := fun a x ↦ by
        apply (Module.bijective_dual_eval k N₁).injective
        ext φ
        obtain ⟨q, rfl⟩ := e₁.surjective φ
        calc
          e₁ q (t (a • x)) = e₂ (f q) (a • x) := ht q _
          _ = e₂ (a.unop • f q) x := (h₂ a.unop (f q) x).symm
          _ = e₂ (f (a.unop • q)) x := by rw [f.map_smul]
          _ = e₁ (a.unop • q) (t x) := (ht _ _).symm
          _ = e₁ q (a • t x) := by simp [h₁] }

/-- The recovered equivalence moves the given equivalence across the evaluation pairing. -/
@[simp]
theorem ofEquivariantDual_apply_apply (e₁ : Q₁ ≃ₗ[k] Module.Dual k N₁)
    (e₂ : Q₂ ≃ₗ[k] Module.Dual k N₂)
    (h₁ : ∀ (a : A) (q : Q₁) (x : N₁), e₁ (a • q) x = e₁ q (MulOpposite.op a • x))
    (h₂ : ∀ (a : A) (q : Q₂) (x : N₂), e₂ (a • q) x = e₂ q (MulOpposite.op a • x))
    (f : Q₁ ≃ₗ[A] Q₂) (q : Q₁) (x : N₂) :
    e₁ q (e₁.ofEquivariantDual e₂ h₁ h₂ f x) = e₂ (f q) x := by
  simp [ofEquivariantDual]

end LinearEquiv
