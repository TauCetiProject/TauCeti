/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import TauCeti.RingTheory.Idempotents.Corner.Basic

/-!
# Corners in the opposite ring

For an idempotent `e` of an `R`-algebra `A`, `op e` is an idempotent of `Aᵐᵒᵖ`, and the corner of
`Aᵐᵒᵖ` at `op e` is the opposite of the corner of `A` at `e`.

## Main definitions

* `IsIdempotentElem.cornerOpAlgEquiv`: the corner of `Aᵐᵒᵖ` at `op e` is `(eAe)ᵐᵒᵖ`, as
  `R`-algebras.
-/

public section

universe u v

open MulOpposite

namespace IsIdempotentElem

variable (R : Type v) [CommSemiring R] {A : Type u} [Semiring A] [Algebra R A] {e : A}

/-- **The corner of the opposite ring.** For an idempotent `e` of an `R`-algebra `A`, the corner of
`Aᵐᵒᵖ` at `op e` is the opposite of the corner of `A` at `e`, by `c ↦ op (unop c)`. -/
def cornerOpAlgEquiv (he : IsIdempotentElem e) (he' : IsIdempotentElem (op e)) :
    he'.Corner ≃ₐ[R] he.Cornerᵐᵒᵖ where
  toFun c := op ⟨unop c.val, (Subsemigroup.mem_corner_iff he).2
    ⟨congrArg unop (he'.corner_val_mul c), congrArg unop (he'.mul_corner_val c)⟩⟩
  invFun c := ⟨op (unop c).val, (Subsemigroup.mem_corner_iff he').2
    ⟨congrArg op (he.corner_val_mul (unop c)), congrArg op (he.mul_corner_val (unop c))⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- `IsIdempotentElem.cornerOpAlgEquiv` keeps the underlying element. -/
@[simp]
theorem val_unop_cornerOpAlgEquiv_apply (he : IsIdempotentElem e) (he' : IsIdempotentElem (op e))
    (c : he'.Corner) : (unop (cornerOpAlgEquiv R he he' c)).val = unop c.val :=
  (rfl)

/-- The inverse of `IsIdempotentElem.cornerOpAlgEquiv` keeps the underlying element. -/
@[simp]
theorem val_cornerOpAlgEquiv_symm_apply (he : IsIdempotentElem e) (he' : IsIdempotentElem (op e))
    (c : he.Cornerᵐᵒᵖ) : ((cornerOpAlgEquiv R he he').symm c).val = op (unop c).val :=
  (rfl)

end IsIdempotentElem
