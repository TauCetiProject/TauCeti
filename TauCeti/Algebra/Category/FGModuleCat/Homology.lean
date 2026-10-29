/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Homology.FullSubcategory

/-!
# Homology and the forgetful functor from `FGModuleCat`

This file records the comparison between taking homology in `FGModuleCat` and taking homology
after forgetting to `ModuleCat`.  It lets invariants of homology objects, such as finrank, be
transported between the two categories for Euler-characteristic computations.

Conversely, a homological complex of modules whose terms are finitely generated lifts to a complex
in `FGModuleCat` by Mathlib's `HomologicalComplex.liftObjectProperty`, which recovers the
original complex after forgetting (`FGModuleCat.liftObjectPropertyIso`).
-/

public section

open CategoryTheory

universe u v

namespace HomologicalComplex

variable {k : Type u} [DivisionRing k]

/-- The comparison between homology after forgetting an `FGModuleCat` cochain complex and the
underlying module of its homology. -/
noncomputable def homologyForgetIso (K : CochainComplex (FGModuleCat.{v} k) ℤ) (n : ℤ) :
    (((forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)).mapHomologicalComplex _).obj K).homology n ≅
      (forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)).obj (K.homology n) := by
  let i := n - 1
  let j := n
  let l := n + 1
  have hij : i + 1 = j := by dsimp [i, j]; omega
  have hjl : j + 1 = l := by dsimp [j, l]
  exact HomologicalComplex.homologyIsoSc'
      (((forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)).mapHomologicalComplex _).obj K) i j l
      ((ComplexShape.up ℤ).prev_eq' hij) ((ComplexShape.up ℤ).next_eq' hjl) ≪≫
    (K.sc' i j l).mapHomologyIso
      (forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)) ≪≫
    (forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)).mapIso
      (K.homologyIsoSc' i j l
        ((ComplexShape.up ℤ).prev_eq' hij) ((ComplexShape.up ℤ).next_eq' hjl)).symm

end HomologicalComplex

namespace FGModuleCat

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{v} R) c) (hK : ∀ i, Module.Finite R (K.X i))

/-- A homological complex of modules with finitely generated terms, lifted to `FGModuleCat R`
by Mathlib's `HomologicalComplex.liftObjectProperty`, recovers the original complex after
forgetting finite generation. -/
noncomputable def liftObjectPropertyIso :
    ((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapHomologicalComplex c).obj
      (K.liftObjectProperty (ModuleCat.isFG R) fun i ↦ (ModuleCat.isFG_iff _).2 (hK i)) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) fun i j _ ↦ by
    -- `forget₂` is the inclusion of the full subcategory, so it sends `homMk f` to `f`.
    simp only [Iso.refl_hom, Functor.mapHomologicalComplex_obj_d,
      HomologicalComplex.liftObjectProperty_d]
    exact (FGModuleCat.forget₂_map (ObjectProperty.homMk (K.d i j) :
      (⟨K.X i, (ModuleCat.isFG_iff _).2 (hK i)⟩ : FGModuleCat.{v} R) ⟶
        ⟨K.X j, (ModuleCat.isFG_iff _).2 (hK j)⟩)).symm

end FGModuleCat
