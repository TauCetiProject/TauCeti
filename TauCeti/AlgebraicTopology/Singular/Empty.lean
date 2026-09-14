/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Relative

/-!
# Relative singular homology of an empty-subspace pair

This file identifies the relative singular chains and homology of `(X, ∅)` with the ordinary
singular chains and homology of `X`.  The comparison is induced by the quotient map from ambient
chains, and is natural in the space.

The construction is the empty-subspace case of the quotient-chain presentation of relative
homology in Eilenberg--Steenrod, *Foundations of Algebraic Topology*, Chapters I--III.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TopPair

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  (R : C)

local instance hasDimensionLT_toSSetPair_ofTopCat (X : TopCat.{w}) :
    (toSSetPair.obj (incl.obj X)).left.HasDimensionLT 0 :=
  (SSet.notNonempty_iff_hasDimensionLT_zero _).mp fun h ↦ by
    obtain ⟨σ⟩ := h
    exact PEmpty.elim ((TopCat.toSSetObjEquiv _ _ σ) (Classical.arbitrary _))

/-- The quotient map from the singular chains of `X` to the relative singular chains of
`(X, ∅)` is an isomorphism. -/
instance isIso_singularChainComplexπ_ofTopCat (X : TopCat.{w}) :
    IsIso ((incl.obj X).singularChainComplexπ R) :=
  SSetPair.isIso_chainComplexπ (P := toSSetPair.obj (incl.obj X)) R

/-- The canonical chain-complex isomorphism from ordinary singular chains to the relative
singular chains of `(X, ∅)`. -/
noncomputable def singularChainComplexIsoOfTopCat (X : TopCat.{w}) :
    ((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅
      (incl.obj X).singularChainComplex R :=
  @asIso _ _ _ _ ((incl.obj X).singularChainComplexπ R)
    (isIso_singularChainComplexπ_ofTopCat C R X)

@[simp]
lemma singularChainComplexIsoOfTopCat_hom (X : TopCat.{w}) :
    (singularChainComplexIsoOfTopCat C R X).hom =
      (incl.obj X).singularChainComplexπ R := (rfl)

/-- The comparison between ordinary and relative singular chains for an empty-subspace pair is
natural in the space. -/
lemma singularChainComplexπ_naturality_ofTopCat {X Y : TopCat.{w}} (f : X ⟶ Y) :
    ((AlgebraicTopology.singularChainComplexFunctor C).obj R).map f ≫
        (incl.obj Y).singularChainComplexπ R =
      (incl.obj X).singularChainComplexπ R ≫
        singularChainComplexMap (incl.map f) R := by
  exact ((SSetPair.chainComplexFunctorπ C).app R).naturality
    (toSSetPair.map (incl.map f))

section Homology

variable [CategoryWithHomology C]

/-- The canonical isomorphism from ordinary singular homology to the relative singular homology
of `(X, ∅)`. -/
noncomputable def singularHomologyIsoOfTopCat (X : TopCat.{w}) (n : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor C n).obj R).obj X ≅
      (incl.obj X).singularHomology R n :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).mapIso
    (singularChainComplexIsoOfTopCat C R X)

@[simp]
lemma singularHomologyIsoOfTopCat_hom (X : TopCat.{w}) (n : ℕ) :
    (singularHomologyIsoOfTopCat C R X n).hom =
      (incl.obj X).singularHomologyπ R n := (rfl)

/-- The comparison between ordinary and relative singular homology for an empty-subspace pair is
natural in the space. -/
lemma singularHomologyπ_naturality_ofTopCat {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor C n).obj R).map f ≫
        (incl.obj Y).singularHomologyπ R n =
      (incl.obj X).singularHomologyπ R n ≫
        (incl.obj X).singularHomologyMap (incl.map f) R n := by
  exact SSetPair.homologyπ_naturality (toSSetPair.map (incl.map f)) R n

end Homology

end TopPair
