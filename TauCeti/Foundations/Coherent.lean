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

This is part of the foundations for the Tau Ceti Jacobian roadmap.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace TauCeti.Foundations

class IsCoherent {X : Scheme.{u}} (F : SheafOfModules.{u} X.ringCatSheaf) : Prop where
  isQuasicoherent : IsQuasicoherent.{u, u, u} F
  isCoherent : IsFinitePresentation.{u} F

end TauCeti.Foundations
