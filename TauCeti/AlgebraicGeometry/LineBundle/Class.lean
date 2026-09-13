/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.TensorProduct
public import TauCeti.CategoryTheory.Skeletal

/-!
# Isomorphism classes of line bundles

The Picard group of a scheme consists of line bundles up to isomorphism, with tensor product as
its operation. This file constructs the underlying type of isomorphism classes and descends the
tensor product and the trivial line bundle to it. Tensor symmetry and the unit isomorphisms give
the corresponding laws on classes, while the tensor associator gives associativity.

Inverses are deliberately not asserted here: they require the dual of an invertible sheaf. Once
those are available, the operations defined here are the operations of the Picard group.

## Main declarations

* `LineBundleClass X` is the type of line bundles on `X` up to isomorphism;
* `LineBundleClass.mk` sends a line bundle to its isomorphism class;
* `LineBundleClass.mk_eq_mk_iff` characterizes equality by an isomorphism of the underlying
  sheaves;
* multiplication is induced by `InvertibleSheaf.tensorProduct`, and `1` is the class of the
  trivial line bundle;
* tensor product makes `LineBundleClass X` a commutative monoid.

The construction uses Mathlib's `CategoryTheory.Skeleton`, its standard implementation of the
isomorphism classes of objects of a category.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

/-- The type of isomorphism classes of line bundles on a scheme. -/
def LineBundleClass (X : Scheme.{u}) : Type _ :=
  Skeleton (InvertibleSheaf X)

namespace LineBundleClass

variable {X : Scheme.{u}}

/-- The isomorphism class of a line bundle. -/
def mk (L : InvertibleSheaf X) : LineBundleClass X :=
  toSkeleton L

/-- Two line bundles have the same class exactly when their underlying sheaves are isomorphic. -/
@[simp]
lemma mk_eq_mk_iff {L K : InvertibleSheaf X} :
    mk L = mk K ↔ Nonempty (L.obj ≅ K.obj) := by
  exact (ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso
    (SheafOfModules.isInvertible X) L.property K.property)

/-- Tensor product of line bundles descends to their isomorphism classes. -/
noncomputable def tensorProduct (a b : LineBundleClass X) : LineBundleClass X :=
  Quotient.map₂ InvertibleSheaf.tensorProduct
    (fun _ _ hL _ _ hK ↦ InvertibleSheaf.isIsomorphic_tensorProduct hL hK) a b

noncomputable instance : Mul (LineBundleClass X) where
  mul := tensorProduct

/-- The class of a tensor product is the product of the two classes. -/
@[simp]
lemma mk_tensorProduct (L K : InvertibleSheaf X) :
    mk (InvertibleSheaf.tensorProduct L K) = mk L * mk K :=
  (rfl)

/-- The tensor product of line-bundle classes is commutative. -/
lemma mul_comm (a b : LineBundleClass X) : a * b = b * a := by
  induction a using Quotient.inductionOn with
  | _ L =>
    induction b using Quotient.inductionOn with
    | _ K => exact congr_toSkeleton_of_iso (InvertibleSheaf.tensorProductComm L K)

/-- The tensor product of line-bundle classes is associative. -/
lemma mul_assoc (a b c : LineBundleClass X) : a * b * c = a * (b * c) := by
  induction a using Quotient.inductionOn with
  | _ L =>
    induction b using Quotient.inductionOn with
    | _ K =>
      induction c using Quotient.inductionOn with
      | _ M => exact congr_toSkeleton_of_iso (InvertibleSheaf.tensorProductAssoc L K M)

/-- The unit for tensor product is the class of the trivial line bundle. -/
noncomputable instance : One (LineBundleClass X) where
  one := mk (InvertibleSheaf.trivial X)

/-- The class of the trivial line bundle is the tensor unit. -/
@[simp]
lemma mk_trivial : mk (InvertibleSheaf.trivial X) = (1 : LineBundleClass X) :=
  rfl

/-- The trivial line bundle is a left unit on isomorphism classes. -/
@[simp high]
lemma one_mul (a : LineBundleClass X) : 1 * a = a := by
  induction a using Quotient.inductionOn with
  | _ L => exact congr_toSkeleton_of_iso (InvertibleSheaf.tensorTrivialLeftIso L)

/-- The trivial line bundle is a right unit on isomorphism classes. -/
@[simp high]
lemma mul_one (a : LineBundleClass X) : a * 1 = a := by
  induction a using Quotient.inductionOn with
  | _ L => exact congr_toSkeleton_of_iso (InvertibleSheaf.tensorTrivialRightIso L)

/-- Tensor product makes line-bundle classes a commutative monoid. -/
noncomputable instance : CommMonoid (LineBundleClass X) where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

end LineBundleClass

end

end AlgebraicGeometry

end TauCeti
