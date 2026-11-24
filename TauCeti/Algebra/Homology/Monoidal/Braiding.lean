/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ComplexShape.Signs
public import TauCeti.Algebra.Homology.Monoidal.Summand
public import TauCeti.Algebra.Homology.Monoidal.Tensor.Symmetry
public import TauCeti.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Tactic.Ring

/-!
# The Koszul braiding on cochain complexes

Mathlib's `HomologicalComplex.monoidalCategory`, instantiated at `ComplexShape.up ℤ` and its
`ComplexShape.TensorSigns`, makes `CochainComplex C ℤ` monoidal by totalizing the
degreewise tensor product.  It does not make it braided: Mathlib's `GradedObject.braidedCategory`
uses the braiding of the base category on each summand with no sign, and that map does not commute
with the totalized differential.

Here `C` is any braided monoidal preadditive category with a zero object and the
coproduct and tensor-preservation hypotheses of Mathlib's totalized monoidal structure.
When the coefficient braiding is symmetric, so is the Koszul braiding.

The braiding is the signed interchange `HomologicalComplex.tensorBraiding`, whose sign comes from
Mathlib's `TotalComplexShapeSymmetry (up ℤ) (up ℤ) (up ℤ)`.  On the bidegree-`(p, q)` summand of
`X ⊗ Y` it is `(-1)^{p * q}` times the braiding of `C`. For modules, this is
`x ⊗ y ↦ (-1)^{|x| * |y|} y ⊗ x` on homogeneous elements.  The sign is forced: the totalized
differential carries `ComplexShape.up ℤ`'s tensor signs `ε₁ = 1` and `ε₂ (p, q) = (-1)^p`, and the
two Leibniz terms match after transposing exactly when the summand map is scaled by
`(-1)^{p * q}`.  This file proves the hexagon identities and assembles the braided and symmetric
structures.

## Main definitions

* `TauCeti.koszulBraidedCategory` and `TauCeti.koszulSymmetricCategory`: the `BraidedCategory`
  and `SymmetricCategory` instances on `CochainComplex C ℤ`, whose braiding `β_ X Y` is
  `HomologicalComplex.tensorBraiding X Y` (`TauCeti.braiding_eq_tensorBraiding`).

## Main results

* `TauCeti.tensorBraiding_hexagon_forward` and `TauCeti.tensorBraiding_hexagon_reverse`: the
  two hexagon identities.
* `TauCeti.ι_tensorμ`: on a homogeneous summand, the middle-four interchange
  `MonoidalCategory.tensorμ` of cochain complexes is that of `C`, with the Koszul sign of
  the two factors it exchanges.

The two auxiliary equations `HomologicalComplex.whiskerLeft_eq_mapBifunctorMap` and
`HomologicalComplex.whiskerRight_eq_mapBifunctorMap` of
`TauCeti/Algebra/Homology/Monoidal/Basic.lean`, which record that the whiskerings of
`CochainComplex C ℤ` are `HomologicalComplex.mapBifunctorMap`, are used in the hexagon proofs.

For module-valued complexes, this braiding supplies the signs in Hom-complex composition
and in the tensor product and opposite of differential graded categories.

## Implementation notes

The braiding `β_ X Y` is `HomologicalComplex.tensorBraiding X Y` for Mathlib's `up ℤ` symmetry
signs, so its summand formulas, naturality and involutivity come from the generic API of
`TauCeti/Algebra/Homology/Monoidal/Tensor/Symmetry.lean`: on the summand `X^p ⊗ Y^q` it is given by
`HomologicalComplex.ιTensorObj_tensorBraiding_hom_f`, whose sign `ComplexShape.σ_up_ℤ` rewrites to
`(p * q).negOnePow`. The inverse is identified with the
braiding for the reversed coefficient braiding
(`HomologicalComplex.tensorBraiding_inv_eq_reverseBraiding`), which turns the first hexagon
identity into the second.

The hypotheses are the graded-object tensor existence and preservation classes used by
Mathlib's `HomologicalComplex.monoidalCategory`. In particular, modules over a commutative
ring satisfy them through their closed symmetric monoidal structure.

## References

* The totalized monoidal structure `HomologicalComplex.monoidalCategory` in
  `Mathlib/Algebra/Homology/Monoidal.lean`, by Joël Riou and Kim Morrison, and the unsigned
  `GradedObject.Monoidal.braiding` of `Mathlib/CategoryTheory/GradedObject/Braiding.lean` and the
  signed `HomologicalComplex.mapBifunctorFlipIso` of `Mathlib/Algebra/Homology/BifunctorFlip.lean`,
  both by Joël Riou.  This file adds the complex-level braided-category axioms; nothing is
  vendored.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1, for the sign
  convention.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

variable (C : Type*) [Category* C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C]
  [∀ (X Y : GradedObject ℤ C), GradedObject.HasTensor X Y]
  [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X)]
  [∀ (X Y Z : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X Y Z]

section Braided

variable [BraidedCategory C]

section Summand

omit [HasZeroObject C] [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X)]
  [∀ (X Y Z : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X Y Z]

/- The summand formula `HomologicalComplex.ιTensorObj_tensorBraiding_hom_f` for `up ℤ`, with the
summand inclusions spelled as `HomologicalComplex.ιMapBifunctor` for the coefficient tensor
bifunctor, as the associator lemmas of `HomologicalComplex.monoidalCategory` produce them. -/
@[reassoc]
private lemma ιMapBifunctor_tensorBraiding_hom_f (X Y : CochainComplex C ℤ) (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j) :
    HomologicalComplex.ιMapBifunctor X Y (curriedTensor C) (ComplexShape.up ℤ) p q j h ≫
        (HomologicalComplex.tensorBraiding X Y).hom.f j =
      (p * q).negOnePow • ((β_ (X.X p) (Y.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor Y X (curriedTensor C)
          (ComplexShape.up ℤ) q p j (by dsimp at h ⊢; omega)) := by
  simpa only [ComplexShape.σ_up_ℤ] using
    HomologicalComplex.ιTensorObj_tensorBraiding_hom_f X Y p q j h

/- Composing a left whiskering into a signed braiding summand: the braiding of `C` is natural,
so a map into the second factor passes through it and becomes a right whiskering.  Stating this
with a general `g` avoids rewriting under the two different spellings (`⊗` and
`HomologicalComplex.mapBifunctor`) of a totalized tensor product. -/
@[reassoc]
private lemma whiskerLeft_comp_braiding_ιMapBifunctor (X W : CochainComplex C ℤ)
    (A : C) (p m j : ℤ) (g : A ⟶ W.X m)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (m, p) = j) :
    (X.X p ◁ g) ≫ ((p * m).negOnePow • ((β_ (X.X p) (W.X m)).hom ≫
        HomologicalComplex.ιMapBifunctor W X (curriedTensor C) (ComplexShape.up ℤ) m p j h)) =
      (p * m).negOnePow • ((β_ (X.X p) A).hom ≫ (g ▷ X.X p) ≫
        HomologicalComplex.ιMapBifunctor W X (curriedTensor C) (ComplexShape.up ℤ) m p j h) := by
  rw [Linear.comp_units_smul, BraidedCategory.braiding_naturality_right_assoc]

end Summand

section Hexagon

variable (X Y Z : CochainComplex C ℤ)

/- `ComplexShape.r` at `ComplexShape.up ℤ` is addition of the three degrees; Mathlib has no named
specialization reducing it. -/
private lemma up_r_eq {p q r j : ℤ}
    (h : ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j) : p + q + r = j := h

private lemma up_r_of {p q r j : ℤ} (h : p + q + r = j) :
    ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j := h

private lemma ι₁₂_hexagon_forward_lhs (p q r j : ℤ)
    (h : ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j) :
    HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor C)
        (curriedTensor C) X Y Z (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        p q r j h ≫
      ((α_ X Y Z).hom ≫ (HomologicalComplex.tensorBraiding X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom).f j =
      (p * (q + r)).negOnePow • ((α_ (X.X p) (Y.X q) (Z.X r)).hom ≫
        (β_ (X.X p) (Y.X q ⊗ Z.X r)).hom ≫ (α_ (Y.X q) (Z.X r) (X.X p)).hom ≫
          HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor C)
            (curriedTensor C) Y Z X (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) q r p j (up_r_of (by have := up_r_eq h; omega))) := by
  have h' := up_r_eq h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.mapBifunctor₁₂.ι_eq_whiskerRight X Y Z p q r (p + q) j rfl h',
    Category.assoc,
    HomologicalComplex.ι_ι_associator_hom_assoc _ _ _ p q r (p + q) (q + r) j rfl rfl h'
      (by omega),
    ιMapBifunctor_tensorBraiding_hom_f_assoc,
    whiskerLeft_comp_braiding_ιMapBifunctor_assoc C X (Y ⊗ Z) _ p (q + r) j
      (HomologicalComplex.ιTensorObj Y Z q r (q + r) rfl)]
  simp only [Linear.units_smul_comp, Category.assoc]
  rw [HomologicalComplex.ι_ι_associator_hom Y Z X q r p (q + r) (r + p) j rfl rfl (by omega)
    (by omega), Linear.comp_units_smul,
    ← HomologicalComplex.mapBifunctor₂₃.ι_eq_whiskerLeft Y Z X q r p (r + p) j rfl (by omega)]

private lemma ι₁₂_hexagon_forward_rhs (p q r j : ℤ)
    (h : ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j) :
    HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor C)
        (curriedTensor C) X Y Z (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        p q r j h ≫
      (((HomologicalComplex.tensorBraiding X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫
        (Y ◁ (HomologicalComplex.tensorBraiding X Z).hom)).f j =
      (p * (q + r)).negOnePow • (((β_ (X.X p) (Y.X q)).hom ▷ Z.X r) ≫
        (α_ (Y.X q) (X.X p) (Z.X r)).hom ≫ (Y.X q ◁ (β_ (X.X p) (Z.X r)).hom) ≫
          HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor C)
            (curriedTensor C) Y Z X (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) q r p j (up_r_of (by have := up_r_eq h; omega))) := by
  have h' := up_r_eq h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.mapBifunctor₁₂.ι_eq_whiskerRight X Y Z p q r (q + p) j (by omega)
      (by omega),
    Category.assoc, HomologicalComplex.whiskerRight_eq_mapBifunctorMap,
    HomologicalComplex.ι_mapBifunctorMap_assoc]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [curriedTensor_map_app]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, ιMapBifunctor_tensorBraiding_hom_f,
    Units.smul_def, ← tensorHom_id, zsmul_tensorHom, tensorHom_id, ← Units.smul_def,
    MonoidalCategory.comp_whiskerRight, Linear.units_smul_comp, Category.assoc]
  -- The whiskered `tensorBraiding X Y` ends in `HomologicalComplex.tensorObj Y X ⊗ Z`, which is
  -- `(Y ⊗ X) ⊗ Z` only after unfolding the monoidal structure.
  erw [HomologicalComplex.ι_ι_associator_hom_assoc Y X Z q p r (q + p) (p + r) j rfl rfl
      (by omega) (by omega)]
  rw [HomologicalComplex.whiskerLeft_eq_mapBifunctorMap, HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp]
  simp only [curriedTensor_obj_map]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, ιMapBifunctor_tensorBraiding_hom_f,
    Units.smul_def (p * r).negOnePow, ← id_tensorHom, tensorHom_zsmul, id_tensorHom,
    ← Units.smul_def,
    MonoidalCategory.whiskerLeft_comp, Linear.units_smul_comp, Category.assoc]
  -- As above, `Y ◁ tensorBraiding X Z` ends in `Y ⊗ HomologicalComplex.tensorObj Z X`.
  erw [← HomologicalComplex.mapBifunctor₂₃.ι_eq_whiskerLeft Y Z X q r p (p + r) j (by omega)
      (by omega)]
  rw [Linear.comp_units_smul, Linear.comp_units_smul, smul_smul, ← Int.negOnePow_add,
    show p * q + p * r = p * (q + r) by ring]

/-- **The first hexagon identity** for the signed interchange of cochain complexes, the
`hexagon_forward` axiom of `TauCeti.koszulBraidedCategory`. -/
lemma tensorBraiding_hexagon_forward :
    (α_ X Y Z).hom ≫ (HomologicalComplex.tensorBraiding X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
      ((HomologicalComplex.tensorBraiding X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫
        (Y ◁ (HomologicalComplex.tensorBraiding X Z).hom) := by
  ext j : 1
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r h
  rw [ι₁₂_hexagon_forward_lhs, ι₁₂_hexagon_forward_rhs]
  congr 1
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  exact BraidedCategory.hexagon_forward (X.X p) (Y.X q) (Z.X r)

end Hexagon

variable [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)]
  [∀ (W X Y Z : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt W X Y Z]

/-- **The second hexagon identity** for the signed interchange of cochain complexes, the
`hexagon_reverse` axiom of `TauCeti.koszulBraidedCategory`. -/
lemma tensorBraiding_hexagon_reverse (X Y Z : CochainComplex C ℤ) :
    (α_ X Y Z).inv ≫ (HomologicalComplex.tensorBraiding (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
      (X ◁ (HomologicalComplex.tensorBraiding Y Z).hom) ≫ (α_ X Z Y).inv ≫
        ((HomologicalComplex.tensorBraiding X Z).hom ▷ Y) := by
  apply (Iso.inv_eq_inv
      ((α_ X Y Z).symm ≪≫ HomologicalComplex.tensorBraiding (X ⊗ Y) Z ≪≫ (α_ Z X Y).symm)
      (whiskerLeftIso X (HomologicalComplex.tensorBraiding Y Z) ≪≫ (α_ X Z Y).symm ≪≫
        whiskerRightIso (HomologicalComplex.tensorBraiding X Z) Y)).1
  -- The forward hexagon for the inverse coefficient braiding is the inverse of this hexagon.
  simp only [Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv, whiskerRightIso_inv,
    HomologicalComplex.tensorBraiding_inv_eq_reverseBraiding, Category.assoc]
  let := reverseBraiding C
  exact tensorBraiding_hexagon_forward C Z X Y

/-- Cochain complexes in `C` form a braided monoidal category under the Koszul braiding: on the
summand `X^p ⊗ Y^q` of Mathlib's totalized tensor product it is `(-1)^(p * q)` times the
coefficient braiding of `X^p` and `Y^q`. For complexes of modules, whose coefficient braiding is
the tensor flip, this is `x ⊗ y ↦ (-1)^{|x| * |y|} y ⊗ x`. -/
noncomputable instance koszulBraidedCategory :
    BraidedCategory (CochainComplex C ℤ) where
  braiding X Y := HomologicalComplex.tensorBraiding X Y
  braiding_naturality_right X _ _ f := HomologicalComplex.tensorBraiding_hom_naturality (𝟙 X) f
  braiding_naturality_left f Z := HomologicalComplex.tensorBraiding_hom_naturality f (𝟙 Z)
  hexagon_forward X Y Z := tensorBraiding_hexagon_forward C X Y Z
  hexagon_reverse X Y Z := tensorBraiding_hexagon_reverse C X Y Z

/-- The braiding of the monoidal category `CochainComplex C ℤ` is the signed interchange
`HomologicalComplex.tensorBraiding`. -/
lemma braiding_eq_tensorBraiding (X Y : CochainComplex C ℤ) :
    β_ X Y = HomologicalComplex.tensorBraiding X Y :=
  (rfl)

section TensorMu

/-- **The middle-four interchange on a homogeneous summand.**  On the summand
`(X₁.X a ⊗ X₂.X b) ⊗ (Y₁.X c ⊗ Y₂.X d)` of `(X₁ ⊗ X₂) ⊗ (Y₁ ⊗ Y₂)`, the interchange
`MonoidalCategory.tensorμ` of cochain complexes is the interchange of the four coefficient objects,
landing
in the summand `(X₁.X a ⊗ Y₁.X c) ⊗ (X₂.X b ⊗ Y₂.X d)`, with the Koszul sign `(-1)^(b * c)` of
moving the degree-`b` factor past the degree-`c` factor. -/
@[reassoc]
lemma ι_tensorμ (X₁ X₂ Y₁ Y₂ : CochainComplex C ℤ) (a b c d ab cd n : ℤ)
    (hab : a + b = ab) (hcd : c + d = cd) (h : ab + cd = n) :
    (HomologicalComplex.ιTensorObj X₁ X₂ a b ab hab ⊗ₘ
        HomologicalComplex.ιTensorObj Y₁ Y₂ c d cd hcd) ≫
        HomologicalComplex.ιTensorObj (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) ab cd n h ≫
          (tensorμ X₁ X₂ Y₁ Y₂).f n =
      (b * c).negOnePow • (tensorμ (X₁.X a) (X₂.X b) (Y₁.X c) (Y₂.X d) ≫
        (HomologicalComplex.ιTensorObj X₁ Y₁ a c (a + c) rfl ⊗ₘ
          HomologicalComplex.ιTensorObj X₂ Y₂ b d (b + d) rfl) ≫
          HomologicalComplex.ιTensorObj (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) (a + c) (b + d) n (by omega)) := by
  subst hab hcd
  -- Follow the summand through the five factors of `tensorμ`.  The codomain of `ιTensorObj` is
  -- spelled `(HomologicalComplex.tensorObj K L).X j` rather than `(K ⊗ L).X j`, so the
  -- associator steps match the whiskered inclusions only up to unfolding the monoidal structure.
  simp only [tensorμ, HomologicalComplex.comp_f, tensorHom_def', Category.assoc]
  erw [HomologicalComplex.ι_ι_associator_hom_assoc X₁ X₂ (Y₁ ⊗ Y₂) a b (c + d)
    (a + b) (b + (c + d)) n rfl rfl h (by omega), associator_naturality_right_assoc]
  rw [HomologicalComplex.ι_whiskerLeft_assoc,
    ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, Category.assoc,
    HomologicalComplex.ι_ι_associator_inv X₂ Y₁ Y₂ b c d (b + c) (c + d) _ rfl rfl (by omega) rfl,
    HomologicalComplex.ι_whiskerLeft_assoc, ← whiskerLeft_comp_assoc, Category.assoc,
    Category.assoc, HomologicalComplex.ι_whiskerRight, ← comp_whiskerRight_assoc,
    braiding_eq_tensorBraiding, HomologicalComplex.ιTensorObj_tensorBraiding_hom_f,
    ComplexShape.σ_up_ℤ]
  -- Pull the Koszul sign out of the whiskerings; what remains is sign-free.
  simp only [Units.smul_def, ← tensorHom_id, ← id_tensorHom, zsmul_tensorHom, tensorHom_zsmul,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  simp only [tensorHom_id, id_tensorHom]
  congr 1
  rw [HomologicalComplex.ι_whiskerLeft_assoc, ← whiskerLeft_comp_assoc, comp_whiskerRight]
  simp only [Category.assoc]
  erw [HomologicalComplex.ι_ι_associator_hom Y₁ X₂ Y₂ c b d
    (b + c) (b + d) (b + (c + d)) (by omega) rfl (by omega) (by omega)]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [HomologicalComplex.ι_ι_associator_inv X₁ Y₁ (X₂ ⊗ Y₂) a c (b + d) (a + c) (b + (c + d)) n
    rfl (by omega) (by omega) (by omega), ← associator_inv_naturality_right_assoc]
  rfl

end TensorMu

end Braided

section Symmetric

variable [SymmetricCategory C]

variable [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)]
  [∀ (W X Y Z : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt W X Y Z]

/-- The Koszul braiding over symmetric coefficients is symmetric. -/
noncomputable instance koszulSymmetricCategory :
    SymmetricCategory (CochainComplex C ℤ) where
  symmetry X Y := HomologicalComplex.tensorBraiding_hom_comp_tensorBraiding_hom X Y

end Symmetric

end TauCeti
