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
preserved by tensoring on the left with `X`, `Torₙ(X, -)` preserves them
(`CategoryTheory.preservesColimitsOfShape_Tor_obj`), as a left derived functor of the
coproduct-preserving functor `X ⊗ -`
(`CategoryTheory.Functor.preservesColimitsOfShape_leftDerived`).
Together with `CategoryTheory.preservesColimitsOfShape_Tor_flip_obj`, for the first variable,
`Torₙ` commutes with coproducts in either variable. Symmetrically, Mathlib's
`CategoryTheory.Tor' C n`, which derives the first variable, preserves coproducts in it
(`CategoryTheory.preservesColimitsOfShape_Tor'_flip_obj`).

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
are exact and preserved by tensoring on the left with `X`, `Torₙ(X, -)` preserves them. -/
instance preservesColimitsOfShape_Tor_obj (X : C)
    [PreservesColimitsOfShape (Discrete J) (tensorLeft X)] (n : ℕ) :
    PreservesColimitsOfShape (Discrete J) ((Tor C n).obj X) :=
  inferInstanceAs (PreservesColimitsOfShape (Discrete J) (((tensoringLeft C).obj X).leftDerived n))

/-- **`Tor'` commutes with coproducts in its first variable.** When coproducts indexed by `J`
are exact and preserved by tensoring on the right with `Y`, `Tor'ₙ(-, Y)` preserves them. -/
instance preservesColimitsOfShape_Tor'_flip_obj (Y : C)
    [PreservesColimitsOfShape (Discrete J) (tensorRight Y)] (n : ℕ) :
    PreservesColimitsOfShape (Discrete J) ((Tor' C n).flip.obj Y) :=
  inferInstanceAs
    (PreservesColimitsOfShape (Discrete J) (((tensoringRight C).obj Y).leftDerived n))

end CategoryTheory
