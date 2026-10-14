/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Lattice

/-!
# The trivial grading of a module

Every module has an integer grading concentrated in degree zero: the whole module in degree `0`
and the zero submodule in every other degree.  This file packages that family of submodules and
records its membership API.  For an algebra, `TauCeti.RingTheory.GradedAlgebra.Trivial` makes it a
`GradedAlgebra`.

## Main definitions

* `TauCeti.trivialGrading`: the integer grading with the whole module in degree zero.
* `TauCeti.toTrivialGradingZero`: the module viewed as the degree-zero piece of that grading.

## Main results

* `TauCeti.mem_trivialGrading_iff`: an element has degree `p` exactly when `p = 0` or it is zero.
-/

public section

namespace TauCeti

variable (R A : Type*) [Semiring R] [AddCommMonoid A] [Module R A]

/-- The trivial integer grading of an `R`-module: all elements have degree zero and every other
homogeneous piece is zero. -/
def trivialGrading (p : ℤ) : Submodule R A :=
  if p = 0 then ⊤ else ⊥

/-- The degree-zero piece of the trivial grading is the whole module. -/
@[simp]
theorem trivialGrading_zero : trivialGrading R A 0 = ⊤ := by
  simp [trivialGrading]

/-- Every nonzero-degree piece of the trivial grading is zero. -/
theorem trivialGrading_eq_bot {p : ℤ} (hp : p ≠ 0) : trivialGrading R A p = ⊥ := by
  simp [trivialGrading, hp]

/-- An element belongs to degree `p` of the trivial grading exactly when `p = 0` or the element
itself is zero. -/
@[simp]
theorem mem_trivialGrading_iff {p : ℤ} {a : A} :
    a ∈ trivialGrading R A p ↔ p = 0 ∨ a = 0 := by
  by_cases hp : p = 0
  · simp [hp]
  · simp [trivialGrading, hp]

/-- Every element of the module, viewed as an element of the degree-zero piece of the trivial
grading. -/
def toTrivialGradingZero : A →+ trivialGrading R A 0 where
  toFun a := ⟨a, by simp⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem coe_toTrivialGradingZero (a : A) : (toTrivialGradingZero R A a : A) = a := (rfl)


end TauCeti
