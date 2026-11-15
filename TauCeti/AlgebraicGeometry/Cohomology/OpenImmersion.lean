/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import TauCeti.CategoryTheory.Sites.ExtensionByZero
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Equivalence
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Over
public import TauCeti.Topology.Sheaves.Over

/-!
# Cohomology on the image of an open immersion

Let `f : Y ⟶ X` be an open immersion of schemes and `M` a sheaf of modules on `X`. This file
identifies the cohomology `Hⁿ(f(Y), M)` of the open subset `f(Y)` of `X` with the cohomology
`Hⁿ(Y, M|_Y)` of the restriction of `M` along `f`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.cohomologyOnOpensRangeNatIso`: the comparison
  `Hⁿ(f(Y), M) ≅ Hⁿ(Y, M|_Y)`, natural in `M`, and `cohomologyOnOpensRangeIso` its component at
  a single sheaf of modules.
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

/-- Transporting the underlying sheaf of a sheaf of modules restricted to `f.opensRange` along
the open-embedding equivalence agrees with restriction of modules along `f`. -/
def overPullbackSheafCongrIsoRestrict
    [f.isOpenEmbedding.overEquivalence.inverse.IsDenseSubsite
      (Opens.grothendieckTopology Y)
      ((Opens.grothendieckTopology X).over f.opensRange)] :
    SheafOfModules.toSheaf X.ringCatSheaf ⋙
        (Opens.grothendieckTopology X).overPullback AddCommGrpCat.{u} f.opensRange ⋙
          (f.isOpenEmbedding.overEquivalence.sheafCongr
            ((Opens.grothendieckTopology X).over f.opensRange)
            (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).functor ≅
      Scheme.Modules.restrictFunctor f ⋙ SheafOfModules.toSheaf Y.ringCatSheaf := by
  exact Functor.isoWhiskerLeft (SheafOfModules.toSheaf X.ringCatSheaf)
    (Topology.IsOpenEmbedding.overPullbackSheafCongrIso
      f.isOpenEmbedding AddCommGrpCat.{u})

/-- The cohomology of a sheaf of modules on the image of an open immersion `f : Y ⟶ X` is the
cohomology of its restriction along `f`, naturally in the sheaf of modules. -/
def cohomologyOnOpensRangeNatIso (n : ℕ) :
    SheafOfModules.toSheaf X.ringCatSheaf ⋙
        CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n ⋙
          (CategoryTheory.evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op f.opensRange) ≅
      Scheme.Modules.restrictFunctor f ⋙ cohomologyFunctor Y n :=
  let J := Opens.grothendieckTopology X
  let e := f.isOpenEmbedding.overEquivalence
  haveI : (J.overPullback AddCommGrpCat.{u} f.opensRange).IsLeftAdjoint :=
    ((Over.forget f.opensRange).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
      (J.over f.opensRange) J).isLeftAdjoint
  haveI : e.inverse.IsDenseSubsite (Opens.grothendieckTopology Y) (J.over f.opensRange) :=
    Topology.IsOpenEmbedding.isDenseSubsite_overEquivalence_inverse f.isOpenEmbedding
  -- Cohomology on `f(Y)` is cohomology on the over category of `f(Y)`, which is equivalent to the
  -- site of open subsets of `Y`; the transported sheaf is the underlying sheaf of `M|_Y`.
  Functor.isoWhiskerLeft (SheafOfModules.toSheaf X.ringCatSheaf)
      (J.cohomologyPresheafEvaluationIsoFunctorOverH f.opensRange n) ≪≫
    Functor.isoWhiskerLeft
      (SheafOfModules.toSheaf X.ringCatSheaf ⋙ J.overPullback AddCommGrpCat.{u} f.opensRange)
      ((CategoryTheory.Sheaf.cohomologyPresheafEvaluationIsoFunctorH (J.over f.opensRange) n
        (isTerminalTop.isTerminalObj e.inverse)).symm ≪≫
      (CategoryTheory.cohomologyPresheafEvaluationIsoSheafCongr (J.over f.opensRange)
        (Opens.grothendieckTopology Y) e n ⊤).symm) ≪≫
    Functor.isoWhiskerRight (overPullbackSheafCongrIsoRestrict f)
      (CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Y) n ⋙
        (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) ≪≫
    Functor.isoWhiskerLeft
      (Scheme.Modules.restrictFunctor f ⋙ SheafOfModules.toSheaf Y.ringCatSheaf)
      (CategoryTheory.Sheaf.cohomologyPresheafEvaluationIsoFunctorH
        (Opens.grothendieckTopology Y) n isTerminalTop)

variable (M : X.Modules)

/-- The cohomology of a sheaf of modules `M` on the image of an open immersion `f : Y ⟶ X` is the
cohomology of the restriction of `M` along `f`. -/
def cohomologyOnOpensRangeIso (n : ℕ) :
    cohomologyOn M n f.opensRange ≅ AddCommGrpCat.of (Cohomology (M.restrict f) n) :=
  (cohomologyOnOpensRangeNatIso f n).app M

end AlgebraicGeometry.Scheme.Modules

end
