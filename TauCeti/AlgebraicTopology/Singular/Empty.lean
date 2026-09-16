/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Relative
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Relative singular homology of a space modulo the empty subspace

This file identifies the relative singular chains of `(X, ∅)` with the ordinary singular
chains of `X`.  The quotient map supplies the comparison, naturally in `X`, and applying homology
gives the corresponding natural isomorphism between ordinary and relative singular homology.

This is the quotient-chain comparison for the empty subspace, following the relative singular
chain construction in Eilenberg--Steenrod, *Foundations of Algebraic Topology*, Chapters I--III.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TopPair

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] (R : C)

/-- The singular simplicial set of the empty subspace in `(X, ∅)` has no simplices. -/
lemma hasDimensionLT_toSSetPair_incl_left (X : TopCat.{w}) :
    (toSSetPair.obj (incl.obj X)).left.HasDimensionLT 0 :=
  (SSet.notNonempty_iff_hasDimensionLT_zero _).mp fun h ↦ by
    obtain ⟨σ⟩ := h
    rw [toSSetPair_obj_left] at σ
    exact PEmpty.elim (TopCat.toSSetObj₀Equiv σ)

/-- Ordinary singular chains are the ambient chains of the singular pair associated to `(X, ∅)`. -/
lemma singularChainComplexFunctor_eq_incl_chainComplexFunctorRight :
    (AlgebraicTopology.singularChainComplexFunctor C).obj R =
      (incl ⋙ toSSetPair) ⋙ (SSetPair.chainComplexFunctorRight C).obj R := by
  rfl

/-- Restricting relative singular chains along `TopPair.incl` agrees with restricting relative
simplicial chains along the singular-pair functor. -/
lemma incl_comp_singularChainComplexFunctor_eq :
    incl ⋙ (singularChainComplexFunctor C).obj R =
      (incl ⋙ toSSetPair) ⋙ (SSetPair.chainComplexFunctor C).obj R := by
  apply CategoryTheory.Functor.ext
  · exact fun X Y f ↦ singularChainComplexFunctor_obj_map (C := C)
      (incl.obj X) (incl.obj Y) (incl.map f) R

/-- The quotient map from ordinary singular chains to the relative singular chains of `(X, ∅)`,
as a natural transformation in `X`. -/
@[no_expose]
noncomputable def singularChainComplexInclComparison :
    (AlgebraicTopology.singularChainComplexFunctor C).obj R ⟶
      incl ⋙ (singularChainComplexFunctor C).obj R :=
  eqToHom (singularChainComplexFunctor_eq_incl_chainComplexFunctorRight C R) ≫
    Functor.whiskerLeft (incl ⋙ toSSetPair) ((SSetPair.chainComplexFunctorπ C).app R) ≫
      eqToHom (incl_comp_singularChainComplexFunctor_eq C R).symm

/-- Each component of the comparison from ordinary to relative singular chains is the quotient
map, up to the transports identifying the source and target chain complexes. -/
@[simp]
lemma singularChainComplexInclComparison_app (X : TopCat.{w}) :
    (singularChainComplexInclComparison C R).app X =
      eqToHom (Functor.congr_obj
        (singularChainComplexFunctor_eq_incl_chainComplexFunctorRight C R) X) ≫
        (incl.obj X).singularChainComplexπ R ≫
          eqToHom (Functor.congr_obj
            (incl_comp_singularChainComplexFunctor_eq C R).symm X) := by
  simp only [singularChainComplexInclComparison, NatTrans.comp_app, eqToHom_app,
    Functor.whiskerLeft_app, Functor.comp_obj, singularChainComplexπ,
    SSetPair.chainComplexπ]

/-- Ordinary singular chains are naturally isomorphic to relative singular chains modulo the
empty subspace. -/
@[no_expose]
noncomputable def singularChainComplexInclIso :
    (AlgebraicTopology.singularChainComplexFunctor C).obj R ≅
      incl ⋙ (singularChainComplexFunctor C).obj R :=
  NatIso.ofComponents (fun X ↦ by
    let _ : (toSSetPair.obj (incl.obj X)).left.HasDimensionLT 0 :=
      hasDimensionLT_toSSetPair_incl_left X
    letI : IsIso ((singularChainComplexInclComparison C R).app X) := by
      let _ : IsIso (((SSetPair.chainComplexFunctorπ C).app R).app
          (toSSetPair.obj (incl.obj X))) :=
        inferInstanceAs (IsIso ((toSSetPair.obj (incl.obj X)).chainComplexπ R))
      dsimp [singularChainComplexInclComparison]
      infer_instance
    exact asIso ((singularChainComplexInclComparison C R).app X))
    (fun f ↦ (singularChainComplexInclComparison C R).naturality f)

@[simp]
lemma singularChainComplexInclIso_hom :
    (singularChainComplexInclIso C R).hom = singularChainComplexInclComparison C R := by
  ext X
  rfl

section Homology

variable [CategoryWithHomology C]

/-- Restricting relative singular homology to pairs `(X, ∅)` agrees with taking homology after
restricting the relative singular chain complex functor. -/
lemma incl_comp_singularHomologyFunctor_eq (n : ℕ) :
    incl ⋙ singularHomologyFunctor R n =
      (incl ⋙ (singularChainComplexFunctor C).obj R) ⋙
        HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n := by
  rw [singularHomologyFunctor_eq_chainComplexFunctor]
  rfl

/-- Ordinary singular homology is naturally isomorphic to relative singular homology modulo the
empty subspace.  Its forward map is induced by the quotient map on singular chains. -/
@[no_expose]
noncomputable def singularHomologyInclIso (n : ℕ) :
    (AlgebraicTopology.singularHomologyFunctor C n).obj R ≅
      incl ⋙ singularHomologyFunctor R n :=
  Functor.isoWhiskerRight (singularChainComplexInclIso C R)
    (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n) ≪≫
    eqToIso (incl_comp_singularHomologyFunctor_eq C R n).symm

@[simp]
lemma singularHomologyInclIso_hom (n : ℕ) :
    (singularHomologyInclIso C R n).hom =
      Functor.whiskerRight (singularChainComplexInclComparison C R)
        (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n) ≫
      eqToHom (incl_comp_singularHomologyFunctor_eq C R n).symm := by
  rw [singularHomologyInclIso.eq_def]
  ext X
  rfl

end Homology

end TopPair
