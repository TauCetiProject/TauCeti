/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Homology and the forgetful functor from `FGModuleCat`

This file records the comparison between taking homology in `FGModuleCat` and taking homology
after forgetting to `ModuleCat`.
-/

public section

open CategoryTheory

universe u v

namespace TauCeti.HomologicalComplex

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

end TauCeti.HomologicalComplex
