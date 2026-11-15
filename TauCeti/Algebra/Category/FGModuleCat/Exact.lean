/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.CategoryTheory.Exact.ExtensionClosed
public import TauCeti.CategoryTheory.Exact.Abelian

/-!
# Finitely generated modules are extension closed

Over any ring `R`, the middle term of a short exact sequence of `R`-modules with finitely
generated ends is finitely generated. Equivalently, `ModuleCat.isFG R` is closed under extensions
for the canonical exact structure of the abelian category `ModuleCat R`.

## Main statements

* `TauCeti.isExtensionClosed_finiteModules`: `ModuleCat.isFG R` is extension closed.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v

variable (R : Type u) [Ring R]

/-- **The finitely generated modules are extension closed**: the middle term of a short exact
sequence with finitely generated ends is finitely generated. -/
theorem isExtensionClosed_finiteModules :
    (ExactStructure.abelian (ModuleCat.{v} R)).IsExtensionClosed (ModuleCat.isFG R) where
  prop_X₂ {S} hS h₁ h₃ := by
    rw [ExactStructure.abelian_conflation] at hS
    have : Module.Finite R S.X₁ := (ModuleCat.isFG_iff S.X₁).mp h₁
    have : Module.Finite R S.X₃ := (ModuleCat.isFG_iff S.X₃).mp h₃
    exact (ModuleCat.isFG_iff S.X₂).mpr <|
      Module.Finite.of_exact (f := S.f.hom) (g := S.g.hom)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact)
      hS.moduleCat_surjective_g

end TauCeti
