/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.ProjectionFormula

/-!
# Cohomology of twisted direct images along a closed immersion

Combining the closed-immersion cohomology comparison
(`TauCeti.AlgebraicGeometry.cohomologyPushforwardIso`) with the right-hand projection formula for a
finite locally free sheaf
(`TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.pushforwardTensorRightIso`) identifies
`Hⁿ(Y, (f_* F) ⊗ E)` with `Hⁿ(X, F ⊗ f^* E)` for any closed immersion `f : X ⟶ Y`, sheaf of modules
`F` on `X`, and finite locally free (in particular, invertible) sheaf `E` on `Y`.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.cohomologyPushforwardTensorRightIso`: the additive isomorphism
  `Hⁿ(Y, (f_* F) ⊗ E) ≅ Hⁿ(X, F ⊗ f^* E)`.
* `AlgebraicGeometry.Scheme.Hom.subsingleton_cohomology_pushforward_tensor_iff` and
  `AlgebraicGeometry.Scheme.Hom.subsingleton_cohomology_pushforward_tensor_iff_of_isInvertible`:
  equivalence of cohomology vanishing for `(f_* F) ⊗ E` on `Y` and `F ⊗ f^* E` on `X`.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.1(d) and Lemma III.2.10.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

/-- For a closed immersion `f : X ⟶ Y`, a sheaf of modules `F` on `X`, and a finite locally free
sheaf `E` on `Y`, the projection formula and closed-immersion cohomology comparison give an additive
isomorphism `Hⁿ(Y, (f_* F) ⊗ E) ≅ Hⁿ(X, F ⊗ f^* E)`. -/
def cohomologyPushforwardTensorRightIso (F : X.Modules) (E : FiniteLocallyFreeSheaf Y) (n : ℕ) :
    AddCommGrpCat.of (Cohomology ((pushforward f).obj F ⊗ E.obj) n) ≅
      AddCommGrpCat.of (Cohomology (F ⊗ (pullback f).obj E.obj) n) :=
  (cohomologyFunctor Y n).mapIso (FiniteLocallyFreeSheaf.pushforwardTensorRightIso f E F) ≪≫
    cohomologyPushforwardIso f (F ⊗ (pullback f).obj E.obj) n

/-- The forward map of `cohomologyPushforwardTensorRightIso` applies `pushforwardTensorRightIso` on
cohomology followed by `cohomologyPushforwardIso`. -/
@[simp]
theorem cohomologyPushforwardTensorRightIso_hom (F : X.Modules) (E : FiniteLocallyFreeSheaf Y)
    (n : ℕ) :
    (f.cohomologyPushforwardTensorRightIso F E n).hom =
      (cohomologyFunctor Y n).map (FiniteLocallyFreeSheaf.pushforwardTensorRightIso f E F).hom ≫
        (cohomologyPushforwardIso f (F ⊗ (pullback f).obj E.obj) n).hom :=
  (rfl)

/-- Along a closed immersion `f : X ⟶ Y`, `Hⁿ(Y, (f_* F) ⊗ E)` vanishes if and only if
`Hⁿ(X, F ⊗ f^* E)` vanishes, for any finite locally free sheaf `E` on `Y`. -/
@[simp]
theorem subsingleton_cohomology_pushforward_tensor_iff (F : X.Modules)
    (E : FiniteLocallyFreeSheaf Y) (n : ℕ) :
    Subsingleton (Cohomology ((pushforward f).obj F ⊗ E.obj) n) ↔
      Subsingleton (Cohomology (F ⊗ (pullback f).obj E.obj) n) :=
  (f.cohomologyPushforwardTensorRightIso F E n).addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr

/-- Along a closed immersion `f : X ⟶ Y`, `Hⁿ(Y, (f_* F) ⊗ L)` vanishes if and only if
`Hⁿ(X, F ⊗ f^* L)` vanishes, for any invertible `𝒪_Y`-module `L`. -/
theorem subsingleton_cohomology_pushforward_tensor_iff_of_isInvertible (F : X.Modules)
    (L : Y.Modules) [TauCeti.SheafOfModules.IsInvertible (R := Y.ringCatSheaf) L] (n : ℕ) :
    Subsingleton (Cohomology ((pushforward f).obj F ⊗ L) n) ↔
      Subsingleton (Cohomology (F ⊗ (pullback f).obj L) n) :=
  f.subsingleton_cohomology_pushforward_tensor_iff F
    ((InvertibleSheaf.toFiniteLocallyFree Y).obj ⟨L, inferInstance⟩) n

end AlgebraicGeometry.Scheme.Hom

end
