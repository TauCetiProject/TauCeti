/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.BaseChange.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Projectivity of the reduced two-periodic complex

The terms of the reduction modulo `w` of a finite-projective matrix factorization of `w` are
projective modules over `S/(w)`
(`TauCeti.MatrixFactorization.projective_quotientPeriodicComplex_obj_X`).
-/

public section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory

variable {S : Type u} [CommRing S] {w : S}

/-- The terms of the reduction modulo `w` of a finite-projective matrix factorization are
projective `S/(w)`-modules. -/
instance projective_quotientPeriodicComplex_obj_X (X : MatrixFactorization S w) (i : ZMod 2) :
    Projective ((quotientPeriodicComplex.obj X).X i) := by
  rcases (by decide : ∀ j : ZMod 2, j = 0 ∨ j = 1) i with rfl | rfl
  · exact ModuleCat.projective_of_categoryTheory_projective
      ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X).obj.X₀.obj
  · exact ModuleCat.projective_of_categoryTheory_projective
      ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X).obj.X₁.obj

end TauCeti.MatrixFactorization
