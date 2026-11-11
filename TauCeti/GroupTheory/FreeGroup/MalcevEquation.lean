/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import TauCeti.GroupTheory.MalcevEquation
import TauCeti.GroupTheory.FreeGroup.CSA
import TauCeti.GroupTheory.FreeGroup.Vaught

/-!
# Malcev's equation in a free group

In a free group with two elements `u`, `v` that do not commute, for instance two distinct basis
letters, Malcev's equation
`x ^ 2 * u * x ^ 2 * u⁻¹ = (y * v * y * v⁻¹) ^ 2` has only the trivial solution, so the system
`x = 1`, `y = 1` is equivalent to a single equation; likewise `x = 1 ∨ y = 1` is equivalent to a
single equation. Free groups are torsion-free and CSA, and satisfy Vaught's condition by
Lyndon's theorem, so both statements are instances of the corresponding statements for
torsion-free CSA groups satisfying Vaught's condition.

## Main results

* `IsFreeGroup.malcevWord_eq_one_iff`: Malcev's equation over a free group has only the trivial
  solution.
* `IsFreeGroup.malcevOrWord_eq_one_iff`: a single equation over a free group expressing
  `x = 1 ∨ y = 1`.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §3.1, Lemmas 3–4.
* A. I. Malcev, *On the equation `z x y x⁻¹ y⁻¹ z⁻¹ = a b a⁻¹ b⁻¹` in a free group*,
  Algebra i Logika 1 (1962).
* R. C. Lyndon, *The equation `a²b² = c²` in free groups*, Michigan Math. J. 6 (1959).
-/

public section

namespace IsFreeGroup

open TauCeti

variable {G : Type*} [Group G] [IsFreeGroup G] {u v x y : G}

/-- **Malcev's equation in a free group.** If `u` and `v` do not commute in a free group, the
equation `x ^ 2 * u * x ^ 2 * u⁻¹ = (y * v * y * v⁻¹) ^ 2` has only the solution `x = y = 1`. -/
theorem malcevWord_eq_one_iff (h : ¬Commute u v) :
    malcevWord u v x y = 1 ↔ x = 1 ∧ y = 1 :=
  isVaught.malcevWord_eq_one_iff isCSA h

/-- If `u` and `v` do not commute in a free group, the word `malcevOrWord u v x y` vanishes
exactly when `x = 1` or `y = 1`. -/
theorem malcevOrWord_eq_one_iff (h : ¬Commute u v) :
    malcevOrWord u v x y = 1 ↔ x = 1 ∨ y = 1 :=
  isVaught.malcevOrWord_eq_one_iff isCSA h

/-- In the free group on `a`, `b`, the system `x = 1`, `y = 1` is equivalent to Malcev's single
equation with the basis letters as coefficients. -/
example {x y : FreeGroup (Fin 2)} :
    malcevWord (FreeGroup.of 0) (FreeGroup.of 1) x y = 1 ↔ x = 1 ∧ y = 1 :=
  malcevWord_eq_one_iff fun h => absurd (FreeGroup.eq_of_commute_of_of h) (by decide)

/-- In the free group on `a`, `b`, the disjunction `x = 1 ∨ y = 1` is equivalent to a single
equation with the basis letters as coefficients. -/
example {x y : FreeGroup (Fin 2)} :
    malcevOrWord (FreeGroup.of 0) (FreeGroup.of 1) x y = 1 ↔ x = 1 ∨ y = 1 :=
  malcevOrWord_eq_one_iff fun h => absurd (FreeGroup.eq_of_commute_of_of h) (by decide)

end IsFreeGroup
