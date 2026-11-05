/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.AlternatingConst

/-!
# The contraction of the alternating constant complex in degree zero

Mathlib's `ChainComplex.alternatingConstHomotopyEquiv` contracts the alternating constant complex
on `X` onto `X` placed in degree zero. This module records its degree-zero component
(`ChainComplex.alternatingConstHomotopyEquiv_hom_f_zero`): the identification of the two
degree-zero terms, both of which are `X`.
-/

public section

open CategoryTheory Limits AlgebraicTopology

namespace ChainComplex

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]

/-- In degree zero, the contraction of the alternating constant complex is the identification of
its degree-zero term with that of the single complex. -/
@[simp]
lemma alternatingConstHomotopyEquiv_hom_f_zero (X : C) :
    (alternatingConstHomotopyEquiv X).hom.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 X).inv := by
  -- Mathlib states no degree-zero formula for this contraction. By definition it is the
  -- degree-zero component of the identity identification `alternatingFaceMapComplexConst`,
  -- followed by the augmentation of the constant augmented simplicial object.
  change 𝟙 X ≫ (AlternatingFaceMapComplex.ε.app (SimplicialObject.Augmented.const.obj X)).f 0 = _
  simp only [AlternatingFaceMapComplex.ε_app_f_zero, SimplicialObject.Augmented.const_obj_hom,
    NatTrans.id_app, single₀ObjXSelf, Iso.refl_inv]
  exact Category.id_comp _

end ChainComplex
