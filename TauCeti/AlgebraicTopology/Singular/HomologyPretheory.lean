/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.EilenbergSteenrod
public import TauCeti.AlgebraicTopology.Singular.Empty

/-!
# Singular homology as a homology pretheory

This file packages relative singular homology with coefficients in an object `R` of an abelian
category as a `TopPair.HomologyPretheory` indexed by `ComplexShape.down ℕ`: the relative homology
functors are `TopPair.singularHomologyFunctor R n`, the absolute ones are Mathlib's singular
homology functors, the two are compared on pairs `(X, ∅)` by `TopPair.singularHomologyInclIso`,
and the boundary morphisms are the connecting morphisms `Hₙ(X, A) ⟶ Hₘ(A)` (for `m + 1 = n`) of
the long exact sequence of a pair, which are natural in the pair.

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

end TopPair
