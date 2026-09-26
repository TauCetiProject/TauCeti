/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.TypeTags
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.GroupTheory.GroupAction.Hom

/-!
# A distributive action on the additive type tag

`Mathlib/Algebra/Group/Action/TypeTags.lean` transports an action along the type tags on the
*acting* monoid: `Additive.addAction` turns a `MulAction α β` into an `AddAction (Additive α) β`.
This file is the missing counterpart on the side that is acted **on**: a monoid `M` acting on a
monoid `A` by monoid endomorphisms acts distributively on `Additive A`, because `g • 1 = 1` and
`g • (a * b) = g • a * g • b` are literally `g • 0 = 0` and `g • (x + y) = g • x + g • y` read in
additive notation.

Mathlib records the same transport only as a representation,
`Representation.ofMulDistribMulAction : Representation ℤ M (Additive G)` for a commutative `G`,
which is not usable where a bare `DistribMulAction M (Additive A)` instance is what typeclass
search must find. Multiplicative coefficient modules — the units of a field, the roots of unity —
reach the additive world of cohomology through exactly this instance, and their equivariant
homomorphisms through `MulDistribMulActionHom.toAdditive`, which reads an `M`-equivariant monoid
homomorphism `A →*[M] B` as an `M`-equivariant additive homomorphism `Additive A →+[M] Additive B`.

The inverse transport `Multiplicative.mulDistribMulAction` reads a distributive action on an
additive monoid `A` as an action by monoid endomorphisms on `Multiplicative A`. It is what lets an
additive coefficient module enter a construction stated for multiplicative ones, such as the
twisted product of a factor set.
-/

public section

namespace Additive

variable {M A : Type*} [Monoid M] [Monoid A] [MulDistribMulAction M A]

/-- A monoid acting on a monoid by monoid endomorphisms acts distributively on the additive type
tag: `smul_one` becomes `smul_zero` and `smul_mul'` becomes `smul_add`. -/
instance distribMulAction : DistribMulAction M (Additive A) where
  smul g x := ofMul (g • x.toMul)
  one_smul x := congrArg ofMul (one_smul M x.toMul)
  mul_smul g h x := congrArg ofMul (mul_smul g h x.toMul)
  smul_zero g := congrArg ofMul (smul_one g)
  smul_add g x y := congrArg ofMul (smul_mul' g x.toMul y.toMul)

@[simp]
theorem ofMul_smul (g : M) (a : A) : ofMul (g • a) = g • ofMul a :=
  rfl

@[simp]
theorem toMul_smul (g : M) (x : Additive A) : (g • x).toMul = g • x.toMul :=
  rfl

open scoped Pointwise in
/-- The additive tags of the orbit of a set under a set of monoid elements are the orbit of the
additive tags. -/
theorem ofMul_image_smul (s : Set M) (t : Set A) : ofMul '' (s • t) = s • (ofMul '' t) :=
  Set.image_image2_distrib_right fun _ _ ↦ rfl

end Additive

namespace Multiplicative

variable {M A : Type*} [Monoid M] [AddMonoid A] [DistribMulAction M A]

/-- A monoid acting distributively on an additive monoid acts by monoid endomorphisms on the
multiplicative type tag: `smul_zero` becomes `smul_one` and `smul_add` becomes `smul_mul`. -/
instance mulDistribMulAction : MulDistribMulAction M (Multiplicative A) where
  smul g x := ofAdd (g • x.toAdd)
  one_smul x := congrArg ofAdd (one_smul M x.toAdd)
  mul_smul g h x := congrArg ofAdd (mul_smul g h x.toAdd)
  smul_one g := congrArg ofAdd (smul_zero g)
  smul_mul g x y := congrArg ofAdd (smul_add g x.toAdd y.toAdd)

@[simp]
theorem ofAdd_smul (g : M) (a : A) : ofAdd (g • a) = g • ofAdd a :=
  rfl

@[simp]
theorem toAdd_smul (g : M) (x : Multiplicative A) : (g • x).toAdd = g • x.toAdd :=
  rfl

end Multiplicative

namespace MulDistribMulActionHom

variable {M A B : Type*} [Monoid M] [Monoid A] [Monoid B] [MulDistribMulAction M A]
  [MulDistribMulAction M B]

/-- An `M`-equivariant monoid homomorphism, read on the additive type tags as an `M`-equivariant
additive homomorphism for the distributive actions `Additive.distribMulAction`. -/
def toAdditive (f : A →*[M] B) : Additive A →+[M] Additive B where
  toFun x := Additive.ofMul (f x.toMul)
  map_smul' g x := congrArg Additive.ofMul (f.map_smul g x.toMul)
  map_zero' := congrArg Additive.ofMul (map_one f)
  map_add' x y := congrArg Additive.ofMul (map_mul f x.toMul y.toMul)

@[simp]
theorem toAdditive_apply (f : A →*[M] B) (x : Additive A) :
    f.toAdditive x = Additive.ofMul (f x.toMul) :=
  (rfl)

end MulDistribMulActionHom
