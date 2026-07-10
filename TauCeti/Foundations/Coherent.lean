/-
Copyright (c) 2026 daouid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Coherent and Quasi-Coherent Sheaves

This file defines the typeclass `IsCoherent` for sheaves of modules over a scheme.

This advances the roadmap at TauCetiRoadmap/JacobianChallenge/README.md.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace TauCeti.Foundations

/--
A sheaf of modules `F` over a scheme `X` is coherent if it is both
quasi-coherent and of finite presentation.
-/
class IsCoherent {X : Scheme.{u}} (F : SheafOfModules.{u} X.ringCatSheaf) : Prop where
  isQuasicoherent : IsQuasicoherent.{u, u, u} F
  isCoherent : IsFinitePresentation.{u} F

end TauCeti.Foundations
