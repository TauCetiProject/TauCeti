/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.GroupLike

/-!
# Transport of group-like elements along coalgebra equivalences

A coalgebra equivalence preserves the group-like equations in both directions and therefore
induces an equivalence of group-like elements.

## Main declarations

* `CoalgEquiv.mapGroupLike`: the equivalence of group-like elements induced by a coalgebra
  equivalence, compatible with `CoalgEquiv.refl`, `CoalgEquiv.trans` and `CoalgEquiv.symm`.
-/

public section

namespace CoalgEquiv

variable {R A B C : Type*} [CommSemiring R]
variable [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [Module R A] [Module R B]
  [Module R C] [Coalgebra R A] [Coalgebra R B] [Coalgebra R C]

/-- A coalgebra equivalence induces an equivalence of group-like elements. -/
def mapGroupLike (e : A ≃ₗc[R] B) : GroupLike R A ≃ GroupLike R B where
  toFun x := ⟨e x.val, x.isGroupLikeElem_val.map e⟩
  invFun x := ⟨e.symm x.val, x.isGroupLikeElem_val.map e.symm⟩
  left_inv x := GroupLike.val_injective (e.symm_apply_apply x.val)
  right_inv x := GroupLike.val_injective (e.apply_symm_apply x.val)

/-- The value of the transported group-like element is the image under the coalgebra
equivalence. -/
@[simp]
theorem val_mapGroupLike (e : A ≃ₗc[R] B) (x : GroupLike R A) :
    (e.mapGroupLike x).val = e x.val :=
  (rfl)

/-- Transport along the identity coalgebra equivalence is the identity equivalence. -/
@[simp]
theorem mapGroupLike_refl : (CoalgEquiv.refl R A).mapGroupLike = Equiv.refl _ :=
  (rfl)

/-- Transport along a composite coalgebra equivalence is the composite transport. -/
@[simp]
theorem mapGroupLike_trans (e : A ≃ₗc[R] B) (f : B ≃ₗc[R] C) :
    (e.trans f).mapGroupLike = e.mapGroupLike.trans f.mapGroupLike :=
  (rfl)

/-- Inverting transport is transport along the inverse coalgebra equivalence. -/
@[simp]
theorem mapGroupLike_symm (e : A ≃ₗc[R] B) : e.mapGroupLike.symm = e.symm.mapGroupLike :=
  (rfl)

end CoalgEquiv
