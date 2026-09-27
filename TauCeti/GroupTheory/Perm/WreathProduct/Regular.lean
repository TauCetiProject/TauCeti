/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.WreathProduct.Basic
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.GroupTheory.Perm.Subgroup

/-!
# Regular wreath products as permutation wreath products

Mathlib's regular wreath product `D ≀ᵣ Q` uses the left regular action of `Q` on itself.
The permutation wreath product with top group the image of that action has the same
coordinates and multiplication. The isomorphism here identifies their base coordinates
and sends the top coordinate through the regular representation.

## Main results

* `TauCeti.regularWreathProductEquiv`: the canonical group isomorphism from Mathlib's
  regular wreath product to the permutation-subgroup wreath product.

The coordinate convention follows `Mathlib.GroupTheory.RegularWreathProduct`.
-/

public section

namespace TauCeti

universe u v

variable (D : Type u) (Q : Type v) [Group D] [Group Q]

/-- The regular representation acts by left multiplication. -/
@[simp]
theorem regularPerm_apply (q x : Q) :
    ((Equiv.Perm.subgroupOfMulAction Q Q q : (MulAction.toPermHom Q Q).range) :
      Equiv.Perm Q) x = q * x :=
  by
    -- Both coercions in the image-restricted representation preserve its underlying action.
    change q • x = q * x
    exact smul_eq_mul q x

/-- Mathlib's regular wreath product is the permutation wreath product whose top group
is the left regular image of `Q`. The isomorphism preserves each base coordinate. -/
noncomputable def regularWreathProductEquiv :
    D ≀ᵣ Q ≃* PermSubgroupWreathProduct D Q (MulAction.toPermHom Q Q).range where
  toFun w := ⟨w.left, Equiv.Perm.subgroupOfMulAction Q Q w.right⟩
  invFun w := ⟨w.left, (Equiv.Perm.subgroupOfMulAction Q Q).symm w.right⟩
  left_inv w := by cases w; simp
  right_inv w := by cases w; simp
  map_mul' a b := by
    apply SemidirectProduct.ext
    · funext x
      simp only [PermSubgroupWreathProduct.mul_left, RegularWreathProduct.mul_left,
        Pi.mul_apply]
      have h := regularPerm_apply Q a.right⁻¹ x
      rw [map_inv] at h
      -- The inverse permutation acts through the inverse equivalence.
      change a.left x * b.left (a.right⁻¹ * x) =
        a.left x * b.left
          (((Equiv.Perm.subgroupOfMulAction Q Q a.right : Equiv.Perm Q)⁻¹) x)
      exact congrArg (fun y => a.left x * b.left y) h.symm
    · exact (Equiv.Perm.subgroupOfMulAction Q Q).map_mul a.right b.right

/-- The comparison preserves the base function pointwise. -/
@[simp]
theorem regularWreathProductEquiv_left (w : D ≀ᵣ Q) (x : Q) :
    (regularWreathProductEquiv D Q w).left x = w.left x :=
  by simp [regularWreathProductEquiv]

/-- The comparison sends the top coordinate through the left regular representation. -/
@[simp]
theorem regularWreathProductEquiv_right (w : D ≀ᵣ Q) :
    (regularWreathProductEquiv D Q w).right =
      Equiv.Perm.subgroupOfMulAction Q Q w.right :=
  by simp [regularWreathProductEquiv]

/-- The base-group inclusion corresponds to the semidirect-product base inclusion. -/
@[simp]
theorem regularWreathProductEquiv_base (d : Q → D) :
    regularWreathProductEquiv D Q ⟨d, 1⟩ = SemidirectProduct.inl d := by
  ext <;> simp [regularWreathProductEquiv]

/-- Mathlib's top-group inclusion corresponds to the semidirect-product top inclusion. -/
@[simp]
theorem regularWreathProductEquiv_inl (q : Q) :
    regularWreathProductEquiv D Q (RegularWreathProduct.inl q) =
      SemidirectProduct.inr (Equiv.Perm.subgroupOfMulAction Q Q q) := by
  ext <;> simp [regularWreathProductEquiv]

end TauCeti
