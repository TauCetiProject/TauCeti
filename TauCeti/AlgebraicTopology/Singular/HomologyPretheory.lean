/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergSteenrod
public import TauCeti.AlgebraicTopology.Singular.Empty

/-!
# Singular homology as a homology pretheory

This file packages relative singular homology with coefficients in an object `R` of an abelian
category as a `TopPair.HomologyPretheory` indexed by `ComplexShape.down ℕ`: the relative homology
functors are `TopPair.singularHomologyFunctor R n`, the absolute ones are Mathlib's singular
homology functors, the two are compared on pairs `(X, ∅)` by `TopPair.singularHomologyInclIso`,
and the boundary morphisms are the connecting morphisms `Hₙ(X, A) ⟶ Hₘ(A)` (for `m + 1 = n`) of
the long exact sequence of a pair, which are natural in the pair.

The pretheory satisfies the exactness axiom `HomologyPretheory.HasPairSequence`, by the long exact
sequence of a pair, and the dimension axiom `HomologyPretheory.HasDimensionAxiom`, because the
singular homology of a point vanishes in positive degrees.

The source is Eilenberg--Steenrod, *Foundations of Algebraic Topology*, Chapters I--III.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TopPair

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- The connecting morphism `Hₙ(X, A) ⟶ Hₘ(A)` of the long exact sequence of a topological pair,
for `m + 1 = n`, as a natural transformation from relative singular homology to the singular
homology of the subspace. -/
@[no_expose]
noncomputable def singularHomologyδNatTrans (n m : ℕ) (h : m + 1 = n := by lia) :
    singularHomologyFunctor.{w} R n ⟶
      proj₂ ⋙ (AlgebraicTopology.singularHomologyFunctor A m).obj R :=
  eqToHom (singularHomologyFunctor_eq_toSSetPair_comp R n) ≫
    Functor.whiskerLeft toSSetPair (SSetPair.homologyδNatTrans R n m h) ≫
      eqToHom (proj₂_comp_singularHomologyFunctor_obj_eq_toSSetPair_comp R m).symm

@[simp]
lemma singularHomologyδNatTrans_app (n m : ℕ) (h : m + 1 = n) (P : TopPair.{w}) :
    (singularHomologyδNatTrans R n m h).app P =
      eqToHom (singularHomologyFunctor_obj P R n) ≫ P.singularHomologyδ R n m h ≫
        eqToHom (Functor.congr_obj
          (proj₂_comp_singularHomologyFunctor_obj_eq_toSSetPair_comp R m).symm P) := by
  rw [singularHomologyδNatTrans, NatTrans.comp_app, NatTrans.comp_app, eqToHom_app, eqToHom_app,
    Functor.whiskerLeft_app, SSetPair.homologyδNatTrans_app R n m h]
  -- `TopPair.singularHomologyδ` is an abbreviation for the connecting morphism of the pair.
  rfl

/-- Relative singular homology with coefficients in `R` as a homology pretheory: relative singular
homology of pairs, singular homology of spaces, their comparison on pairs `(X, ∅)`, and the
connecting morphisms `Hₙ(X, A) ⟶ Hₘ(A)` for `m + 1 = n`. -/
@[simps Hₚ H iso]
noncomputable def singularHomologyPretheory :
    HomologyPretheory.{w} A (ComplexShape.down ℕ) where
  Hₚ n := singularHomologyFunctor R n
  H n := (AlgebraicTopology.singularHomologyFunctor A n).obj R
  iso n := singularHomologyInclIso A R n
  δ n m := if h : m + 1 = n then singularHomologyδNatTrans R n m h else 0
  shape_δ n m h := by simp_all

@[simp]
lemma singularHomologyPretheory_δ (n m : ℕ) (h : m + 1 = n) :
    (singularHomologyPretheory.{w} R).δ n m = singularHomologyδNatTrans R n m h :=
  dite_eq_left h

open HomologyPretheory

/-- The map from the singular homology of the ambient space of a pair to the relative singular
homology of the pair is the map induced by the quotient from ambient to relative chains. -/
lemma singularHomologyPretheory_hFstToHₚ (n : ℕ) (P : TopPair.{w}) :
    (singularHomologyPretheory.{w} R).hFstToHₚ n P =
      P.singularHomologyπ R n ≫ eqToHom (singularHomologyFunctor_obj P R n).symm := by
  dsimp only [hFstToHₚ, singularHomologyPretheory]
  rw [singularHomologyInclIso_hom_app, singularHomologyFunctor_map]
  -- The transports come from the comparison of `(X, ∅)` with `X`; the ones between definitionally
  -- equal homology objects have to be matched up to definitional equality.
  erw [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, ← Category.assoc,
    ← SSetPair.homologyπ_naturality]
  -- The pair map `(X, ∅) ⟶ (X, A)` is the identity on the ambient space by definition.
  have hj : Hom.fst P.j = 𝟙 P.fst := rfl
  rw [toSSetPair_map_right, hj]
  erw [CategoryTheory.Functor.map_id, SSet.homologyMap_id, Category.id_comp]
  -- `P.singularHomologyπ` abbreviates the quotient map, and both transports have the same type.
  rfl

/-- Singular homology satisfies the exactness axiom: the long exact sequence of every
topological pair. -/
instance : (singularHomologyPretheory.{w} R).HasPairSequence where
  exact_pair P n m hnm := by
    have hnm : m + 1 = n := hnm
    rw [singularHomologyPretheory_hFstToHₚ, singularHomologyPretheory_δ R n m hnm,
      singularHomologyδNatTrans_app]
    -- The transport out of the subspace homology is between definitionally equal objects.
    erw [eqToHom_refl, Category.comp_id]
    -- The remaining transport identifies `P.singularHomology R n` with
    -- `(singularHomologyFunctor R n).obj P` only propositionally, so its target is generalized
    -- and the equation eliminated.
    have key : ∀ {Y : A} (e : P.singularHomology R n = Y),
        (ComposableArrows.mk₂ (P.singularHomologyπ R n ≫ eqToHom e)
          (eqToHom e.symm ≫ P.singularHomologyδ R n m hnm)).Exact := by
      rintro _ rfl
      rw [eqToHom_refl, Category.comp_id, Category.id_comp]
      exact (P.singularHomology_exact_relative R n m hnm).exact_toComposableArrows
    exact key _
  exact_snd P n m hnm := by
    have hnm : m + 1 = n := hnm
    rw [singularHomologyPretheory_δ R n m hnm, singularHomologyδNatTrans_app]
    -- The transport out of the subspace homology is between definitionally equal objects.
    erw [eqToHom_refl, Category.comp_id]
    have key : ∀ {Y : A} (e : Y = P.singularHomology R n),
        (ComposableArrows.mk₂ (eqToHom e ≫ P.singularHomologyδ R n m hnm)
          (SSet.homologyMap (TopCat.toSSet.map P.map) R m)).Exact := by
      rintro _ rfl
      rw [eqToHom_refl, Category.id_comp]
      exact (P.singularHomology_exact_subspace R n m hnm).exact_toComposableArrows
    exact key _
  exact_fst P n := by
    rw [singularHomologyPretheory_hFstToHₚ]
    have key : ∀ {Y : A} (e : P.singularHomology R n = Y),
        (ComposableArrows.mk₂ (SSet.homologyMap (toSSetPair.obj P).hom R n)
          (P.singularHomologyπ R n ≫ eqToHom e)).Exact := by
      rintro _ rfl
      rw [eqToHom_refl, Category.comp_id]
      exact (P.singularHomology_exact_space R n).exact_toComposableArrows
    exact key _
  epi_map_of_not_rel P n hn := by
    obtain rfl : n = 0 := by
      cases n with
      | zero => rfl
      | succ k => exact absurd (by simp) (hn k)
    have : Epi ((singularHomologyPretheory.{w} R).hFstToHₚ 0 P) := by
      rw [singularHomologyPretheory_hFstToHₚ]
      have key : ∀ {Y : A} (e : P.singularHomology R 0 = Y),
          Epi (P.singularHomologyπ R 0 ≫ eqToHom e) := by
        rintro _ rfl
        rw [eqToHom_refl, Category.comp_id]
        infer_instance
      exact key _
    exact epi_of_epi (((singularHomologyPretheory.{w} R).iso 0).hom.app P.fst) _

/-- Singular homology satisfies the dimension axiom: the singular homology of a point vanishes in
positive degrees. -/
instance : (singularHomologyPretheory.{w} R).HasDimensionAxiom where
  isZero_PUnit_of_gt_zero n hn :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace A n R _ hn

end TopPair
