/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The comparison identifies the quotient transformation with its chain-complex map.
import all Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative

import all TauCeti.AlgebraicTopology.Singular.Relative

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
The formal infrastructure is Mathlib's relative simplicial chains: the comparison is the
quotient natural transformation `SSetPair.chainComplexFunctorπ`, and its invertibility for a
pair whose subcomplex is empty is Mathlib's `SSetPair.isIso_chainComplexπ`.

For any pair whose subspace is empty, the singular simplicial set of the subspace has no simplices
(`TopPair.hasDimensionLT_toSSetPair_left_of_isEmpty`), so by Mathlib's
`SSetPair.isIso_chainComplexπ` the quotient map `TopPair.singularHomologyπ` from ambient to
relative singular homology is an isomorphism, found by instance resolution.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TopPair

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] (R : C)

/-- The subspace of the pair `(X, ∅)` is empty. -/
instance isEmpty_incl_obj_snd (X : TopCat.{w}) : IsEmpty (incl.obj X).snd :=
  inferInstanceAs (IsEmpty PEmpty)

/-- The singular simplicial set of an empty subspace has no simplices. -/
instance hasDimensionLT_toSSetPair_left_of_isEmpty (P : TopPair.{w}) [IsEmpty P.snd] :
    (toSSetPair.obj P).left.HasDimensionLT 0 :=
  (SSet.notNonempty_iff_hasDimensionLT_zero _).mp fun h ↦ by
    obtain ⟨σ⟩ := h
    rw [toSSetPair_obj_left] at σ
    exact isEmptyElim (TopCat.toSSetObj₀Equiv σ)

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
noncomputable def singularChainComplexInclComparison :
    (AlgebraicTopology.singularChainComplexFunctor C).obj R ⟶
      incl ⋙ (singularChainComplexFunctor C).obj R :=
  eqToHom (singularChainComplexFunctor_eq_incl_chainComplexFunctorRight C R) ≫
    CategoryTheory.Functor.whiskerLeft (incl ⋙ toSSetPair)
      ((SSetPair.chainComplexFunctorπ C).app R) ≫
      eqToHom (incl_comp_singularChainComplexFunctor_eq C R).symm

/-- Each component of the comparison from ordinary to relative singular chains is the quotient
map, up to the transports identifying the source and target chain complexes. -/
@[simp]
lemma singularChainComplexInclComparison_app (X : TopCat.{w}) :
    (singularChainComplexInclComparison C R).app X =
      eqToHom (CategoryTheory.Functor.congr_obj
        (singularChainComplexFunctor_eq_incl_chainComplexFunctorRight C R) X) ≫
        (incl.obj X).singularChainComplexπ R ≫
          eqToHom (CategoryTheory.Functor.congr_obj
            (incl_comp_singularChainComplexFunctor_eq C R).symm X) := by
  simp only [singularChainComplexInclComparison, NatTrans.comp_app, eqToHom_app,
    CategoryTheory.Functor.whiskerLeft_app, CategoryTheory.Functor.comp_obj, singularChainComplexπ,
    SSetPair.chainComplexπ]

/-- Ordinary singular chains are naturally isomorphic to relative singular chains modulo the
empty subspace. -/
noncomputable def singularChainComplexInclIso :
    (AlgebraicTopology.singularChainComplexFunctor C).obj R ≅
      incl ⋙ (singularChainComplexFunctor C).obj R :=
  NatIso.ofComponents (fun X ↦ by
    let e := asIso ((toSSetPair.obj (incl.obj X)).chainComplexπ R)
    exact eqToIso (CategoryTheory.Functor.congr_obj
      (singularChainComplexFunctor_eq_incl_chainComplexFunctorRight C R) X) ≪≫
        e ≪≫
          eqToIso (CategoryTheory.Functor.congr_obj
            (incl_comp_singularChainComplexFunctor_eq C R).symm X))
    (fun f ↦ by
      dsimp only [Iso.trans, eqToIso, asIso]
      -- The component isomorphisms were assembled using transports. Their homs
      -- reduce to the comparison map, whose public naturality law proves this square.
      change _ ≫ (singularChainComplexInclComparison C R).app _ =
        (singularChainComplexInclComparison C R).app _ ≫ _
      exact (singularChainComplexInclComparison C R).naturality f)

@[simp]
lemma singularChainComplexInclIso_hom :
    (singularChainComplexInclIso C R).hom = singularChainComplexInclComparison C R := by
  apply NatTrans.ext
  funext X
  dsimp only [singularChainComplexInclIso, NatIso.ofComponents_hom_app, Iso.trans_hom,
    eqToIso.hom, asIso_hom]
  exact (singularChainComplexInclComparison_app C R X).symm

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
noncomputable def singularHomologyInclIso (n : ℕ) :
    (AlgebraicTopology.singularHomologyFunctor C n).obj R ≅
      incl ⋙ singularHomologyFunctor R n :=
  CategoryTheory.Functor.isoWhiskerRight (singularChainComplexInclIso C R)
    (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n) ≪≫
    eqToIso (incl_comp_singularHomologyFunctor_eq C R n).symm

@[simp]
lemma singularHomologyInclIso_hom (n : ℕ) :
    (singularHomologyInclIso C R n).hom =
      CategoryTheory.Functor.whiskerRight (singularChainComplexInclComparison C R)
        (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n) ≫
      eqToHom (incl_comp_singularHomologyFunctor_eq C R n).symm := by
  rw [singularHomologyInclIso.eq_def]
  -- Whiskering the composite isomorphism has this hom by definition; expose it
  -- before rewriting by the chain-complex comparison's public hom formula.
  change Functor.whiskerRight (singularChainComplexInclIso C R).hom _ ≫ _ = _
  rw [singularChainComplexInclIso_hom]
  rfl

/-- The component at `X` of the comparison from ordinary singular homology to relative singular
homology of `(X, ∅)` is the map induced by the quotient from ambient to relative chains. -/
lemma singularHomologyInclIso_hom_app (n : ℕ) (X : TopCat.{w}) :
    (singularHomologyInclIso C R n).hom.app X =
      (incl.obj X).singularHomologyπ R n ≫
        eqToHom (singularHomologyFunctor_obj (incl.obj X) R n).symm := by
  rw [singularHomologyInclIso_hom, NatTrans.comp_app, CategoryTheory.Functor.whiskerRight_app,
    singularChainComplexInclComparison_app]
  simp only [CategoryTheory.Functor.map_comp, eqToHom_map, eqToHom_app, Category.assoc]
  -- The remaining transports are between chain complexes and homology objects that agree only up
  -- to unfolding `singularChainComplexFunctor` and `TopCat.toSSet`, so `eqToHom_refl` has to be
  -- matched up to definitional equality; after that both sides are the homology of the quotient
  -- map followed by transports along proofs of the same equality.
  erw [eqToHom_refl, Category.id_comp, CategoryTheory.Functor.map_comp, eqToHom_map, Category.assoc,
    eqToHom_trans]
  rfl

end Homology

end TopPair
