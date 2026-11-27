/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DoldKan.SimplexChainMap.Basic

/-!
# Functoriality of the normalized-chain model

A cochain map induces a map of the normalized-simplex-chain models by
postcomposition. This operation commutes with simplicial pullback, so the models
form the functor `CochainComplex.simplexChainMapsFunctor`. It allows chain-level
constructions, such as signed vertex reversal, to be natural in the coefficient
complex without passing through the abstract Dold–Kan equivalence.
-/

public noncomputable section

open CategoryTheory Finset Simplicial

universe v u

namespace CochainComplex

variable {R : Type u} [Ring R]
variable {K L M : CochainComplex (ModuleCat.{v} R) ℤ}

namespace SimplexChainMap

variable {n m : ℕ}

/-- Postcompose a normalized simplex chain map with a cochain map. -/
def postcomp (g : K.SimplexChainMap n) (f : K ⟶ L) : L.SimplexChainMap n where
  val J d := (f.f d).hom (g.val J d)
  val_eq_zero_of_ne J d h := by rw [g.val_eq_zero_of_ne _ _ h, map_zero]
  val_empty := by rw [g.val_empty, map_zero]
  d_val J d := by
    calc
      _ = (f.f (d + 1)).hom ((K.d d (d + 1)).hom (g.val J d)) :=
        ConcreteCategory.congr_hom (f.comm d (d + 1)) _
      _ = _ := by simp [g.d_val, Units.smul_def]

/-- Postcomposition applies the cochain map to each face value. -/
@[simp]
lemma postcomp_val (g : K.SimplexChainMap n) (f : K ⟶ L)
    (J : Finset (Fin (n + 1))) (d : ℤ) :
    (g.postcomp f).val J d = (f.f d).hom (g.val J d) :=
  (rfl)

/-- Postcomposition with the identity fixes a simplex chain map. -/
@[simp]
lemma postcomp_id (g : K.SimplexChainMap n) : g.postcomp (𝟙 K) = g := by
  ext J d
  simp

/-- Successive postcompositions compose. -/
@[simp]
lemma postcomp_postcomp (g : K.SimplexChainMap n) (f : K ⟶ L) (f' : L ⟶ M) :
    (g.postcomp f).postcomp f' = g.postcomp (f ≫ f') := by
  ext J d
  simp

/-- Postcomposition commutes with all simplicial pullbacks. -/
@[simp]
lemma postcomp_map (g : K.SimplexChainMap n) (α : Fin (m + 1) →o Fin (n + 1)) (f : K ⟶ L) :
    (g.map α).postcomp f = (g.postcomp f).map α := by
  ext J d
  simp only [postcomp_val, map_val]
  split_ifs <;> simp

end SimplexChainMap

variable (R) in
/-- The normalized-simplex-chain model of the connective Dold–Kan construction,
functorial in cochain complexes. -/
-- Exposed so its values have simplices `K.SimplexChainMap n`, as required to
-- assemble natural transformations from operations on these chain maps.
@[expose] def simplexChainMapsFunctor : CochainComplex (ModuleCat.{v} R) ℤ ⥤ SSet.{v} where
  obj K := K.simplexChainMaps
  map f :=
    { app _ := ↾fun g ↦ g.postcomp f
      naturality _ _ θ := by
        ext g
        exact g.postcomp_map θ.unop.toOrderHom f }
  map_id _ := by ext Δ g; exact g.postcomp_id
  map_comp _ _ := by ext Δ g; exact (g.postcomp_postcomp _ _).symm

/-- The functor has the prescribed normalized-chain model as its value. -/
@[simp]
lemma simplexChainMapsFunctor_obj (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    (simplexChainMapsFunctor R).obj K = K.simplexChainMaps :=
  (rfl)

/-- The functor acts by postcomposition on each simplex. -/
@[simp]
lemma simplexChainMapsFunctor_map_app_apply (f : K ⟶ L) (Δ : SimplexCategoryᵒᵖ)
    (g : K.simplexChainMaps.obj Δ) :
    ((simplexChainMapsFunctor R).map f).app Δ g = g.postcomp f :=
  (rfl)

end CochainComplex
