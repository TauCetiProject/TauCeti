/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Abelian.LeftDerived.Coproduct
public import TauCeti.CategoryTheory.Monoidal.Tor.Basic

/-!
# `Tor` commutes with coproducts in its derived variable

Mathlib's `CategoryTheory.Tor C n` derives the tensor product in its second variable:
`((Tor C n).obj X).obj Y` is `Lₙ(X ⊗ -)(Y)`. When coproducts indexed by `J` are exact and
preserved by tensoring on the left, `Torₙ(X, -)` preserves them
(`CategoryTheory.preservesColimitsOfShape_Tor_obj`), as a left derived functor of the
coproduct-preserving functor `X ⊗ -`
(`CategoryTheory.Functor.preservesColimitsOfShape_leftDerived`).
Together with `CategoryTheory.preservesColimitsOfShape_Tor_flip_obj`, for the first variable,
`Torₙ` commutes with coproducts in either variable. Symmetrically, Mathlib's
`CategoryTheory.Tor' C n`, which derives the first variable, preserves coproducts in it
(`CategoryTheory.preservesColimitsOfShape_Tor'_flip_obj`).

In particular `Torₙ(X, -)` vanishes on a coproduct when it vanishes on every summand
(`CategoryTheory.isZero_Tor_obj_of_isColimit`).

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 2.4 and Section 3.1.
-/

public section

noncomputable section

namespace CategoryTheory

open Limits MonoidalCategory

universe w

variable {C : Type*} [Category* C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  [HasProjectiveResolutions C] {J : Type w} [HasColimitsOfShape (Discrete J) C]
  [HasExactColimitsOfShape (Discrete J) C]

/-- **`Tor` commutes with coproducts in its second variable.** When coproducts indexed by `J`
are exact and preserved by tensoring on the left, `Torₙ(X, -)` preserves them. -/
instance preservesColimitsOfShape_Tor_obj
    [∀ Z : C, PreservesColimitsOfShape (Discrete J) (tensorLeft Z)] (X : C) (n : ℕ) :
    PreservesColimitsOfShape (Discrete J) ((Tor C n).obj X) :=
  inferInstanceAs (PreservesColimitsOfShape (Discrete J) (((tensoringLeft C).obj X).leftDerived n))

/-- **`Tor'` commutes with coproducts in its first variable.** When coproducts indexed by `J`
are exact and preserved by tensoring on the right, `Tor'ₙ(-, Y)` preserves them. -/
instance preservesColimitsOfShape_Tor'_flip_obj
    [∀ Z : C, PreservesColimitsOfShape (Discrete J) (tensorRight Z)] (Y : C) (n : ℕ) :
    PreservesColimitsOfShape (Discrete J) ((Tor' C n).flip.obj Y) :=
  inferInstanceAs
    (PreservesColimitsOfShape (Discrete J) (((tensoringRight C).obj Y).leftDerived n))

/-- If coproducts indexed by `J` are exact and preserved by tensoring on the left, and
`Torₙ(X, -)` vanishes on every summand of a coproduct, then it vanishes on the coproduct. -/
lemma isZero_Tor_obj_of_isColimit [∀ Z : C, PreservesColimitsOfShape (Discrete J) (tensorLeft Z)]
    {F : Discrete J ⥤ C} {c : Cocone F} (hc : IsColimit c) (X : C) {n : ℕ}
    (h : ∀ j, IsZero (((Tor C n).obj X).obj (F.obj j))) :
    IsZero (((Tor C n).obj X).obj c.pt) :=
  (IsZero.iff_id_eq_zero _).2 <|
    (isColimitOfPreserves ((Tor C n).obj X) hc).hom_ext fun j ↦ by
      simpa using (h j).eq_of_src _ _

end CategoryTheory
