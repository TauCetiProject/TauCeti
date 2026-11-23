/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.RingTheory.Flat.Basic

/-!
# Transport of group-like elements along coalgebra morphisms

A coalgebra equivalence preserves the group-like equations in both directions and therefore
induces an equivalence of group-like elements. An injective morphism of flat coalgebras still
reflects them, because its tensor square is injective.

## Main declarations

* `CoalgEquiv.mapGroupLike`: the equivalence of group-like elements induced by a coalgebra
  equivalence, compatible with `CoalgEquiv.refl`, `CoalgEquiv.trans` and `CoalgEquiv.symm`.
* `TauCeti.isGroupLikeElem_map_iff_of_injective`: an injective morphism of flat coalgebras reflects
  group-like elements.
-/

public section

namespace TauCeti

section Injective

variable {R A B F : Type*} [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [Module R A]
  [Module R B] [Coalgebra R A] [Coalgebra R B] [Module.Flat R A] [Module.Flat R B]
  [FunLike F A B] [CoalgHomClass F R A B]

/-- An injective morphism of flat coalgebras reflects group-like elements: an element is
group-like as soon as its image is. Over a field every coalgebra is flat. -/
theorem isGroupLikeElem_map_iff_of_injective (f : F) (hf : Function.Injective f) {a : A} :
    IsGroupLikeElem R (f a) ↔ IsGroupLikeElem R a := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, .map f⟩
  · rw [← CoalgHomClass.counit_comp_apply f a, h.counit_eq_one]
  · apply TensorProduct.map_injective_of_flat_flat (f : A →ₗ[R] B) (f : A →ₗ[R] B) hf hf
    rw [CoalgHomClass.map_comp_comul_apply, TensorProduct.map_tmul]
    exact h.comul_eq_tmul_self

end Injective

end TauCeti

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
