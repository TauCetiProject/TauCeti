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

Combining `TauCeti.AlgebraicGeometry.cohomologyPushforwardIso` with
`TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.pushforwardTensorRightIso` identifies
`Hⁿ(Y, (f_* F) ⊗ E)` with `Hⁿ(X, F ⊗ f^* E)` along any closed immersion `f : X ⟶ Y` for a sheaf of
modules `F` on `X` and finite locally free (in particular, invertible) sheaf `E` on `Y`.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.cohomologyPushforwardTensorRightIso`
* `AlgebraicGeometry.Scheme.Hom.subsingleton_cohomology_pushforward_tensor_iff`
* `AlgebraicGeometry.Scheme.Hom.subsingleton_cohomology_pushforward_tensor_iff_of_isInvertible`

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

/-- Additive isomorphism `Hⁿ(Y, (f_* F) ⊗ E) ≅ Hⁿ(X, F ⊗ f^* E)` along a closed immersion `f` for
finite locally free `E`. -/
def cohomologyPushforwardTensorRightIso (F : X.Modules) (E : FiniteLocallyFreeSheaf Y) (n : ℕ) :
    AddCommGrpCat.of (Cohomology ((pushforward f).obj F ⊗ E.obj) n) ≅
      AddCommGrpCat.of (Cohomology (F ⊗ (pullback f).obj E.obj) n) :=
  (cohomologyFunctor Y n).mapIso ((FiniteLocallyFreeSheaf.pushforwardTensorRightIso f E).app F) ≪≫
    cohomologyPushforwardIso f (F ⊗ (pullback f).obj E.obj) n

/-- Forward map of `cohomologyPushforwardTensorRightIso`. -/
@[simp]
theorem cohomologyPushforwardTensorRightIso_hom (F : X.Modules) (E : FiniteLocallyFreeSheaf Y)
    (n : ℕ) :
    (f.cohomologyPushforwardTensorRightIso F E n).hom =
      (cohomologyFunctor Y n).map
          ((FiniteLocallyFreeSheaf.pushforwardTensorRightIso f E).app F).hom ≫
        (cohomologyPushforwardIso f (F ⊗ (pullback f).obj E.obj) n).hom :=
  (rfl)

/-- Inverse map of `cohomologyPushforwardTensorRightIso`. -/
@[simp]
theorem cohomologyPushforwardTensorRightIso_inv (F : X.Modules) (E : FiniteLocallyFreeSheaf Y)
    (n : ℕ) :
    (f.cohomologyPushforwardTensorRightIso F E n).inv =
      (cohomologyPushforwardIso f (F ⊗ (pullback f).obj E.obj) n).inv ≫
        (cohomologyFunctor Y n).map
          ((FiniteLocallyFreeSheaf.pushforwardTensorRightIso f E).app F).inv :=
  (rfl)

/-- Naturality of `cohomologyPushforwardTensorRightIso` in `φ : F₁ ⟶ F₂`. -/
@[reassoc]
theorem cohomologyPushforwardTensorRightIso_naturality {F₁ F₂ : X.Modules} (φ : F₁ ⟶ F₂)
    (E : FiniteLocallyFreeSheaf Y) (n : ℕ) :
    (cohomologyFunctor Y n).map ((pushforward f).map φ ▷ E.obj) ≫
        (f.cohomologyPushforwardTensorRightIso F₂ E n).hom =
      (f.cohomologyPushforwardTensorRightIso F₁ E n).hom ≫
        (cohomologyFunctor X n).map (φ ▷ (pullback f).obj E.obj) := by
  have hnat :
      (cohomologyFunctor Y n).map ((pushforward f).map φ ▷ E.obj) ≫
          (cohomologyFunctor Y n).map
            ((FiniteLocallyFreeSheaf.pushforwardTensorRightIso f E).app F₂).hom =
        (cohomologyFunctor Y n).map
            ((FiniteLocallyFreeSheaf.pushforwardTensorRightIso f E).app F₁).hom ≫
          (pushforward f ⋙ cohomologyFunctor Y n).map (φ ▷ (pullback f).obj E.obj) :=
    ((cohomologyFunctor Y n).map_comp _ _).symm.trans ((congrArg (cohomologyFunctor Y n).map
      ((FiniteLocallyFreeSheaf.pushforwardTensorRightIso f E).hom.naturality φ)).trans
      ((cohomologyFunctor Y n).map_comp _ _))
  exact (Category.assoc _ _ _).symm.trans ((eq_whisker hnat _).trans
    ((Category.assoc _ _ _).trans ((whisker_eq _
      (cohomologyPushforwardIso_naturality f (φ ▷ (pullback f).obj E.obj) n)).trans
      (Category.assoc _ _ _).symm)))

/-- Along a closed immersion `f`, `Hⁿ(Y, (f_* F) ⊗ E)` vanishes iff `Hⁿ(X, F ⊗ f^* E)` does. -/
@[simp]
theorem subsingleton_cohomology_pushforward_tensor_iff (F : X.Modules)
    (E : FiniteLocallyFreeSheaf Y) (n : ℕ) :
    Subsingleton (Cohomology ((pushforward f).obj F ⊗ E.obj) n) ↔
      Subsingleton (Cohomology (F ⊗ (pullback f).obj E.obj) n) :=
  (f.cohomologyPushforwardTensorRightIso F E n).addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr

/-- Along a closed immersion `f`, `Hⁿ(Y, (f_* F) ⊗ L)` vanishes iff `Hⁿ(X, F ⊗ f^* L)` does for
invertible `L`. -/
@[simp]
theorem subsingleton_cohomology_pushforward_tensor_iff_of_isInvertible (F : X.Modules)
    (L : Y.Modules) [TauCeti.SheafOfModules.IsInvertible (R := Y.ringCatSheaf) L] (n : ℕ) :
    Subsingleton (Cohomology ((pushforward f).obj F ⊗ L) n) ↔
      Subsingleton (Cohomology (F ⊗ (pullback f).obj L) n) :=
  f.subsingleton_cohomology_pushforward_tensor_iff F
    ((InvertibleSheaf.toFiniteLocallyFree Y).obj ⟨L, inferInstance⟩) n

end AlgebraicGeometry.Scheme.Hom

end
