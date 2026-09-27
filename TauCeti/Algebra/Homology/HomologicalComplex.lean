/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Powers of homological complex endomorphisms

Degreewise recursion for powers of a complex endomorphism. This only needs a category with
zero morphisms, so it is available independently of additive structure and chain homotopies.
-/

public section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type*}
  {c : ComplexShape ι} {K : HomologicalComplex C c} {s : K ⟶ K}

/-- Degreewise recursion for the powers of a chain endomorphism. -/
lemma pow_f_succ (m : ℕ) (i : ι) :
    (End.of s ^ (m + 1)).f i = (End.of s ^ m).f i ≫ s.f i := by
  rw [pow_succ', End.mul_def, comp_f]

end HomologicalComplex
