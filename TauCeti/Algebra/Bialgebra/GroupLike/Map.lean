/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Equiv
public import Mathlib.RingTheory.Bialgebra.GroupLike
public import TauCeti.Algebra.Coalgebra.GroupLike.Map

/-!
# Functoriality of group-like elements

A bialgebra morphism sends group-like elements to group-like elements and respects their
multiplication. This file bundles that operation as a monoid homomorphism and records that a
bialgebra equivalence induces a multiplicative equivalence of group-like elements.

## Main declarations

* `BialgHom.mapGroupLike`: the monoid homomorphism of group-like elements induced by a bialgebra
  morphism, compatible with `BialgHom.id` and `BialgHom.comp`.
* `BialgEquiv.mapGroupLike`: the multiplicative equivalence of group-like elements induced by a
  bialgebra equivalence, upgrading `CoalgEquiv.mapGroupLike` and compatible with
  `BialgEquiv.refl`, `BialgEquiv.trans` and `BialgEquiv.symm`.
-/

public section

variable {R A B C : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
  [Bialgebra R A] [Bialgebra R B] [Bialgebra R C]

namespace BialgHom

/-- A bialgebra morphism induces a monoid homomorphism on group-like elements. -/
def mapGroupLike (f : A →ₐc[R] B) : GroupLike R A →* GroupLike R B where
  toFun x := ⟨f x.val, x.isGroupLikeElem_val.map f⟩
  map_one' := GroupLike.val_injective (map_one f)
  map_mul' x y := GroupLike.val_injective (map_mul f x.val y.val)

/-- The underlying value of the image of a group-like element is its image under the bialgebra
morphism. -/
@[simp]
theorem val_mapGroupLike (f : A →ₐc[R] B) (x : GroupLike R A) :
    (f.mapGroupLike x).val = f x.val :=
  (rfl)

/-- Mapping group-like elements respects identity bialgebra morphisms. -/
@[simp]
theorem mapGroupLike_id : (BialgHom.id R A).mapGroupLike = MonoidHom.id _ :=
  (rfl)

/-- Mapping group-like elements respects composition of bialgebra morphisms. -/
@[simp]
theorem mapGroupLike_comp (g : B →ₐc[R] C) (f : A →ₐc[R] B) :
    (g.comp f).mapGroupLike = g.mapGroupLike.comp f.mapGroupLike :=
  (rfl)

end BialgHom

namespace BialgEquiv

/-- A bialgebra equivalence induces a multiplicative equivalence of group-like elements: the
coalgebra transport `CoalgEquiv.mapGroupLike` is multiplicative. -/
def mapGroupLike (e : A ≃ₐc[R] B) : GroupLike R A ≃* GroupLike R B :=
  MulEquiv.mk' e.toCoalgEquiv.mapGroupLike fun x y ↦ GroupLike.val_injective <| by
    simp only [CoalgEquiv.val_mapGroupLike, GroupLike.val_mul]
    exact map_mul e x.val y.val

/-- The underlying value of the image of a group-like element is its image under the bialgebra
equivalence. -/
@[simp]
theorem val_mapGroupLike (e : A ≃ₐc[R] B) (x : GroupLike R A) :
    (e.mapGroupLike x).val = e x.val :=
  e.toCoalgEquiv.val_mapGroupLike x

/-- Mapping group-like elements along the identity equivalence is the identity equivalence. -/
@[simp]
theorem mapGroupLike_refl : (BialgEquiv.refl R A).mapGroupLike = MulEquiv.refl _ :=
  MulEquiv.toEquiv_injective CoalgEquiv.mapGroupLike_refl

/-- Mapping group-like elements along a composite equivalence is the composite of the maps. -/
@[simp]
theorem mapGroupLike_trans (e : A ≃ₐc[R] B) (f : B ≃ₐc[R] C) :
    (e.trans f).mapGroupLike = e.mapGroupLike.trans f.mapGroupLike :=
  MulEquiv.toEquiv_injective (e.toCoalgEquiv.mapGroupLike_trans f.toCoalgEquiv)

/-- The inverse of the induced equivalence is induced by the inverse equivalence. -/
@[simp]
theorem mapGroupLike_symm (e : A ≃ₐc[R] B) : e.mapGroupLike.symm = e.symm.mapGroupLike :=
  MulEquiv.toEquiv_injective e.toCoalgEquiv.mapGroupLike_symm

end BialgEquiv
