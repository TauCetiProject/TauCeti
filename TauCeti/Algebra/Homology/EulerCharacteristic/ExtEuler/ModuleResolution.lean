/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import TauCeti.Algebra.Category.ModuleCat.CartanMap
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Resolution

/-!
# Ext-Euler admissibility from module resolutions

This file specializes the finite-projective-resolution criterion for Ext-Euler admissibility to
finitely generated modules over a finite-dimensional algebra.

## Main results

* `TauCeti.isEulerAdmissibleOn_isFG`: if every finitely generated module has a finite resolution
  by finitely generated projectives, every pair of finitely generated modules is
  Euler-admissible.
-/

public section

namespace TauCeti

open CategoryTheory
open scoped ModuleCat

universe u

variable {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A]

variable (k) in
/-- If every finitely generated module over a finite-dimensional algebra has a finite resolution by
finitely generated projectives, then every pair of finitely generated modules is
Euler-admissible: the resolution bounds the `Ext` groups, and the Hom spaces from its terms are
finite-dimensional. -/
theorem isEulerAdmissibleOn_isFG [FiniteDimensional k A]
    (h : ModuleCat.isFG A ≤
      (ExactStructure.abelian (ModuleCat.{u} A)).admitsFiniteResolution
        (finiteProjectiveModules A)) :
    IsEulerAdmissibleOn.{u} k (ModuleCat.isFG A) (ModuleCat.isFG A) where
  isEulerAdmissible X Y hX hY := by
    obtain ⟨r⟩ := (ExactStructure.admitsFiniteResolution_iff _ _).mp (h X hX)
    refine r.isEulerAdmissible (finiteProjectiveModules_le_isProjective A) fun Z hZ => ?_
    have : Module.Finite A Z := (finiteProjectiveModules_iff.mp hZ).1
    have : Module.Finite A Y := (ModuleCat.isFG_iff Y).mp hY
    have : FiniteDimensional k Z := Module.Finite.trans A Z
    have : FiniteDimensional k Y := Module.Finite.trans A Y
    exact Module.Finite.equiv (ModuleCat.homLinearEquiv (S := k)).symm

end TauCeti
