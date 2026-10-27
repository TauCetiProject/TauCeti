/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Monoidal.Basic
public import TauCeti.CategoryTheory.Monoidal.Rigid.Biproduct
public import TauCeti.CategoryTheory.Monoidal.Rigid.Mate

/-!
# Duality on the Grothendieck ring of a rigid category

In a right rigid monoidal additive category, taking right duals respects isomorphisms and binary
biproducts (`TauCeti.rightDualBiprodIso`), so it descends to an additive endomorphism
`TauCeti.SplitK0.dual` of the split Grothendieck group, `[X] ↦ [Xᘁ]`. Since
`(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ` and `(𝟙_ C)ᘁ ≅ 𝟙_ C`, it is an anti-endomorphism of the Grothendieck ring:
`dual (x * y) = dual y * dual x` and `dual 1 = 1`.

For a fusion category this is the involution of the Grothendieck ring as a based ring, which
permutes the basis of simple classes; that is developed in
`TauCeti/CategoryTheory/Semisimple/Rigid.lean`.

## Main declarations

* `TauCeti.SplitK0.dual`: the duality `[X] ↦ [Xᘁ]` on split `K₀`;
* `TauCeti.SplitK0.dual_one` and `TauCeti.SplitK0.dual_mul`: it reverses products.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.5
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace TauCeti

universe w v u

namespace SplitK0

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasBinaryBiproducts C] [EssentiallySmall.{w} C] [RightRigidCategory C]

variable (C) in
/-- The class of the right dual, as a biproduct-additive invariant. -/
private def dualInvariant : AdditiveInvariant C (SplitK0 C) where
  obj X := of Xᘁ
  map_iso _ _ e := of_congr e.rightAdjointMate.symm
  map_biprod X Y := by rw [of_congr (rightDualBiprodIso X Y), of_biprod]

/-- The duality `[X] ↦ [Xᘁ]` on the split Grothendieck group of a right rigid monoidal additive
category. It reverses products (`TauCeti.SplitK0.dual_mul`). -/
def dual : SplitK0 C →+ SplitK0 C :=
  lift (dualInvariant C)

/-- The dual of the class of an object is the class of its right dual. -/
@[simp]
theorem dual_of (X : C) : dual (of X : SplitK0 C) = of Xᘁ :=
  lift_of (dualInvariant C) X

/-- The duality fixes the unit, since the right dual of the tensor unit is the tensor unit. -/
@[simp]
theorem dual_one : dual (1 : SplitK0 C) = 1 := by
  rw [one_def, dual_of]
  exact of_congr (rightDualIso inferInstance exactPairingUnit)

/-- The duality reverses products, since `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ`. -/
@[simp]
theorem dual_mul (x y : SplitK0 C) : dual (x * y) = dual y * dual x := by
  -- Both sides are biadditive in `(x, y)`, so it suffices to compare them on classes of objects.
  suffices h : (mulHom C).compr₂ dual = ((mulHom C).flip.compl₂ dual).comp dual by
    simpa [mul_def] using DFunLike.congr_fun (DFunLike.congr_fun h x) y
  refine hom_ext fun X ↦ hom_ext fun Y ↦ ?_
  simp only [AddMonoidHom.compr₂_apply, AddMonoidHom.comp_apply, AddMonoidHom.compl₂_apply,
    AddMonoidHom.flip_apply, ← mul_def, of_mul_of, dual_of]
  exact of_congr (rightDualTensorIso X Y)

end SplitK0

end TauCeti
