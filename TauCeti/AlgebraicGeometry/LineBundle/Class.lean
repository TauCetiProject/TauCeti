/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Dual
public import TauCeti.CategoryTheory.Skeletal

/-!
# Isomorphism classes of line bundles

The Picard group of a scheme consists of line bundles up to isomorphism, with tensor product as
its operation. This file constructs the type of isomorphism classes and descends tensor product,
the trivial line bundle, and duality to it. Tensor symmetry, associativity, the unit isomorphisms,
and evaluation against the dual give the commutative group laws.

## Main declarations

* `LineBundleClass X` is the type of line bundles on `X` up to isomorphism;
* `LineBundleClass.mk` sends a line bundle to its isomorphism class, and every class arises this
  way (`LineBundleClass.mk_surjective`);
* `LineBundleClass.lift` descends an isomorphism-invariant function to line-bundle classes;
* `LineBundleClass.mk_eq_mk_iff` characterizes equality by an isomorphism of the underlying
  sheaves;
* multiplication is induced by `InvertibleSheaf.tensorProduct`, and `1` is the class of the
  trivial line bundle, so that `LineBundleClass.mk_eq_one_iff` characterizes the classes of
  line bundles isomorphic to the structure sheaf;
* inversion is induced by `InvertibleSheaf.dual`;
* tensor product makes `LineBundleClass X` a commutative group.

The construction uses Mathlib's `CategoryTheory.Skeleton`, its standard implementation of the
isomorphism classes of objects of a category.
-/

public section

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace TauCeti

namespace AlgebraicGeometry

universe u v

noncomputable section

/-- The type of isomorphism classes of line bundles on a scheme. -/
def LineBundleClass (X : Scheme.{u}) : Type _ :=
  Skeleton (InvertibleSheaf X)

namespace LineBundleClass

variable {X : Scheme.{u}}

/-- The isomorphism class of a line bundle. -/
def mk (L : InvertibleSheaf X) : LineBundleClass X :=
  toSkeleton L

/-- Descend a function on invertible sheaves that is invariant under isomorphism to line-bundle
classes. -/
noncomputable def lift {α : Sort v} (f : InvertibleSheaf X → α)
    (hf : ∀ L M, Nonempty (L.obj ≅ M.obj) → f L = f M) : LineBundleClass X → α :=
  (SheafOfModules.isInvertible X).skeletonLift f hf

/-- Applying `lift` to the class represented by `L` recovers the original function at `L`. -/
@[simp]
theorem lift_mk {α : Sort v} {f : InvertibleSheaf X → α}
    {hf : ∀ L M, Nonempty (L.obj ≅ M.obj) → f L = f M} (L : InvertibleSheaf X) :
    lift f hf (mk L) = f L :=
  ObjectProperty.skeletonLift_toSkeleton _ L

/-- Two line bundles have the same class exactly when their underlying sheaves are isomorphic. -/
@[simp]
lemma mk_eq_mk_iff {L K : InvertibleSheaf X} :
    mk L = mk K ↔ Nonempty (L.obj ≅ K.obj) := by
  exact (ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso
    (SheafOfModules.isInvertible X) L.property K.property)

/-- Every line-bundle class is the class of a line bundle. -/
theorem mk_surjective : Function.Surjective (mk : InvertibleSheaf X → LineBundleClass X) :=
  fun a ↦ Quotient.inductionOn a fun L ↦ ⟨L, rfl⟩

/-- Duality of line bundles descends to their isomorphism classes. -/
noncomputable def dual (a : LineBundleClass X) : LineBundleClass X :=
  lift (fun L ↦ mk (InvertibleSheaf.dual L))
    (fun L K h ↦ by
      rw [mk_eq_mk_iff]
      obtain ⟨e⟩ := h
      exact ⟨(SheafOfModules.isInvertible X).ι.mapIso
        (InvertibleSheaf.dualCongr
          (ObjectProperty.isoMk (SheafOfModules.isInvertible X) e))⟩) a

noncomputable instance : Inv (LineBundleClass X) where
  inv := dual

/-- Inversion of line-bundle classes is induced by duality. -/
lemma inv_eq_dual (a : LineBundleClass X) : a⁻¹ = dual a :=
  rfl

/-- The inverse of the class of a line bundle is the class of its dual. -/
@[simp]
lemma inv_mk (L : InvertibleSheaf X) :
    (mk L)⁻¹ = mk (InvertibleSheaf.dual L) := by
  rw [inv_eq_dual]
  exact lift_mk L

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

/-- The unit for tensor product is the class of the trivial line bundle. -/
noncomputable instance : One (LineBundleClass X) where
  one := mk (InvertibleSheaf.trivial X)

/-- The class of the trivial line bundle is the tensor unit. -/
@[simp]
lemma mk_trivial : mk (InvertibleSheaf.trivial X) = (1 : LineBundleClass X) :=
  rfl

/-- The class of a line bundle is the tensor unit exactly when the line bundle is isomorphic to
the structure sheaf. -/
@[simp]
lemma mk_eq_one_iff {L : InvertibleSheaf X} :
    mk L = 1 ↔ Nonempty (L.obj ≅ 𝟙_ X.Modules) := by
  rw [← mk_trivial, mk_eq_mk_iff]
  exact ⟨fun ⟨e⟩ ↦ ⟨e ≪≫ InvertibleSheaf.trivialObjIsoUnit X⟩,
    fun ⟨e⟩ ↦ ⟨e ≪≫ (InvertibleSheaf.trivialObjIsoUnit X).symm⟩⟩

/-- Tensor product and duality make line-bundle classes a commutative group. -/
noncomputable instance : CommGroup (LineBundleClass X) := by
  let mulComm : ∀ a b : LineBundleClass X, a * b = b * a := by
    intro a b
    induction a using Quotient.inductionOn with
    | _ L =>
      induction b using Quotient.inductionOn with
      | _ K => exact congr_toSkeleton_of_iso (InvertibleSheaf.tensorProductComm L K)
  let mulAssoc : ∀ a b c : LineBundleClass X, a * b * c = a * (b * c) := by
    intro a b c
    induction a using Quotient.inductionOn with
    | _ L =>
      induction b using Quotient.inductionOn with
      | _ K =>
        induction c using Quotient.inductionOn with
        | _ M => exact congr_toSkeleton_of_iso (InvertibleSheaf.tensorProductAssoc L K M)
  let oneMul : ∀ a : LineBundleClass X, 1 * a = a := by
    intro a
    induction a using Quotient.inductionOn with
    | _ L => exact congr_toSkeleton_of_iso (InvertibleSheaf.tensorTrivialLeftIso L)
  let mulOne : ∀ a : LineBundleClass X, a * 1 = a := by
    intro a
    induction a using Quotient.inductionOn with
    | _ L => exact congr_toSkeleton_of_iso (InvertibleSheaf.tensorTrivialRightIso L)
  let invMulCancel : ∀ a : LineBundleClass X, a⁻¹ * a = 1 := by
    intro a
    obtain ⟨L, rfl⟩ := mk_surjective a
    rw [inv_mk, ← mk_tensorProduct, ← mk_trivial]
    exact congr_toSkeleton_of_iso
      (InvertibleSheaf.tensorProductComm (InvertibleSheaf.dual L) L ≪≫
        InvertibleSheaf.tensorDualIso L)
  exact
    { mul_assoc := mulAssoc
      one_mul := oneMul
      mul_one := mulOne
      inv_mul_cancel := invMulCancel
      mul_comm := mulComm }

end LineBundleClass

end

end AlgebraicGeometry

end TauCeti
