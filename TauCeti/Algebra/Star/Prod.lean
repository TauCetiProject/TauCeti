/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Prod
public import Mathlib.Algebra.Star.StarAlgHom

/-!
# Star algebra equivalences of products

The coordinate swap is a star algebra equivalence between the two orders of a product,
lifting `Equiv.prodComm` with only the operations preserved by a star algebra equivalence.
-/

public section

namespace StarAlgEquiv

variable (R : Type*) {A B : Type*} [Add A] [Mul A] [Star A] [SMul R A]
  [Add B] [Mul B] [Star B] [SMul R B]

/-- Swapping the coordinates of a product preserves addition, multiplication, star, and the
scalar action. -/
protected def prodComm : A × B ≃⋆ₐ[R] B × A :=
  let e := Equiv.prodComm A B
  have he : ⇑e = Prod.swap := Equiv.coe_prodComm A B
  { e with
    map_add' := fun x y ↦ show e (x + y) = e x + e y by rw [he]; rfl
    map_mul' := fun x y ↦ show e (x * y) = e x * e y by rw [he]; rfl
    map_star' := fun x ↦ show e (star x) = star (e x) by rw [he]; rfl
    map_smul' := fun r x ↦ show e (r • x) = r • e x by rw [he]; rfl }

@[simp]
theorem prodComm_apply (x : A × B) :
    (StarAlgEquiv.prodComm R : A × B ≃⋆ₐ[R] B × A) x = x.swap :=
  congrFun (Equiv.coe_prodComm A B) x

end StarAlgEquiv
