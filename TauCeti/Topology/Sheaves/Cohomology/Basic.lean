/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda
public import TauCeti.Topology.Sheaves.ClosedEmbedding

/-!
# Cohomology of pushforward from a closed subspace

For a closed embedding `f : X ⟶ Y`, the cohomology of `f_* F` over an open `U`
of `Y` is naturally isomorphic to the cohomology of `F` over `f⁻¹(U)`.
The comparison uses Mathlib's `CategoryTheory.Adjunction.extEquiv` for the exact
inverse-image/direct-image adjunction, and identifies the first Ext argument by the
universal property of the free abelian sheaf on an open subset.

## References

* R. Hartshorne, *Algebraic Geometry*, III, Lemma 2.10.
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite _root_.Topology
open TauCeti.CategoryTheory

namespace TauCeti.Topology

universe u

noncomputable section

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

private def pullbackFreeYonedaCorepresentation (U : Opens Y) :
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op ((Opens.map f).obj U)) ⋙ forget AddCommGrpCat).CorepresentableBy
      ((TopCat.Sheaf.pullback AddCommGrpCat f).obj
        ((freeYonedaSheafFunctor (Opens.grothendieckTopology Y)).obj U)) where
  homEquiv :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f).homEquiv _ _).trans
      (freeYonedaSheafSectionsEquiv (Opens.grothendieckTopology Y) U _).toEquiv
  homEquiv_comp g α := by
    exact (congrArg (freeYonedaSheafSectionsEquiv (Opens.grothendieckTopology Y) U _)
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f).homEquiv_naturality_right
        α g)).trans
      (freeYonedaSheafSectionsEquiv_naturality_right (Opens.grothendieckTopology Y) _
        ((TopCat.Sheaf.pushforward AddCommGrpCat f).map g))

/-- Inverse image takes the free abelian sheaf on `U` to the free abelian sheaf on `f⁻¹(U)`. -/
def pullbackFreeYonedaIso (U : Opens Y) :
    (TopCat.Sheaf.pullback AddCommGrpCat f).obj
        ((freeYonedaSheafFunctor (Opens.grothendieckTopology Y)).obj U) ≅
      (freeYonedaSheafFunctor (Opens.grothendieckTopology X)).obj ((Opens.map f).obj U) :=
  (pullbackFreeYonedaCorepresentation f U).uniqueUpToIso
    (freeYonedaSheafCorepresentableBy (Opens.grothendieckTopology X) ((Opens.map f).obj U))

/-- Cohomology over `U` of the direct image from a closed subspace is cohomology over
`f⁻¹(U)`, naturally in the coefficient sheaf. -/
def cohomologyPushforwardNatIso (hf : IsClosedEmbedding f) (n : ℕ) (U : Opens Y) :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
        _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Y) n ⋙
          (evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅
      _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ((Opens.map f).obj U)) := by
  haveI : HasExt.{u} (X.Sheaf AddCommGrpCat.{u}) := inferInstance
  haveI : HasExt.{u} (Y.Sheaf AddCommGrpCat.{u}) := inferInstance
  haveI := preservesFiniteColimits_pushforward_of_isClosedEmbedding f hf
  haveI : RepresentablyFlat (Opens.map f) := _root_.CategoryTheory.flat_of_preservesFiniteLimits _
  haveI : PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits
      (Opens.map f) AddCommGrpCat.{u} _ _
  haveI : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).Additive :=
    Functor.additive_of_preserves_binary_products _
  rw [cohomologyPresheafFunctor_eq, cohomologyPresheafFunctor_eq]
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f
  exact NatIso.ofComponents (fun F ↦ (adj.extEquiv.{u, u} (n := n)).symm.toAddCommGrpIso)
      (by
        intro F G α
        ext x
        exact adj.extEquiv_symm_naturality_right₀.{u, u} x α) ≪≫
    (@Abelian.extFunctor (X.Sheaf AddCommGrpCat.{u}) _ _
      (IsGrothendieckAbelian.hasExt _) n).mapIso (pullbackFreeYonedaIso f U).symm.op

/-- The cohomology of a pushed-forward abelian sheaf along a closed embedding agrees
with the original cohomology over the inverse-image open. -/
def cohomologyPushforwardIso (hf : IsClosedEmbedding f)
    (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) (U : Opens Y) :
    _root_.CategoryTheory.Sheaf.H'.{u}
        ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) n U ≅
      _root_.CategoryTheory.Sheaf.H'.{u} F n ((Opens.map f).obj U) :=
  (cohomologyPushforwardNatIso f hf n U).app F

/-- The coefficientwise comparison is the component of the natural comparison. -/
@[simp]
lemma cohomologyPushforwardNatIso_app (hf : IsClosedEmbedding f)
    (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) (U : Opens Y) :
    (cohomologyPushforwardNatIso f hf n U).app F =
      cohomologyPushforwardIso f hf F n U :=
  (rfl)

@[simp]
lemma cohomologyPushforwardNatIso_hom_app (hf : IsClosedEmbedding f)
    (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) (U : Opens Y) :
    (cohomologyPushforwardNatIso f hf n U).hom.app F =
      (cohomologyPushforwardIso f hf F n U).hom :=
  (rfl)

/-- The cohomology comparison commutes with maps of coefficient sheaves. -/
@[reassoc]
lemma cohomologyPushforwardIso_naturality (hf : IsClosedEmbedding f)
    {F G : X.Sheaf AddCommGrpCat.{u}} (α : F ⟶ G) (n : ℕ) (U : Opens Y) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
        _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Y) n ⋙
          (evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj (op U)).map α ≫
        (cohomologyPushforwardIso f hf G n U).hom =
      (cohomologyPushforwardIso f hf F n U).hom ≫
        (_root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n ⋙
          (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ((Opens.map f).obj U))).map α :=
  (cohomologyPushforwardNatIso f hf n U).hom.naturality α

end

end TauCeti.Topology
