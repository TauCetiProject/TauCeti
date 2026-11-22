/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.LSeries.DirichletContinuation

import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Analytic and meromorphic orders of nonprincipal Dirichlet L-functions

For any nonprincipal Dirichlet character `χ ≠ 1` modulo `N` (`N ≠ 0`), primitive or not, the
continued L-function `χ.LFunction` is entire and nonzero at `s = 1`
(`DirichletCharacter.LFunction_apply_one_ne_zero`). Consequently its analytic order is finite
everywhere, its meromorphic order is the cast of `analyticOrderNatAt`, and vanishing at `s` is
equivalent both to `1 ≤ analyticOrderNatAt χ.LFunction s` and to
`0 < meromorphicOrderAt χ.LFunction s`.

## Main results

* `DirichletCharacter.analyticOrderAt_LFunction_ne_top`: `analyticOrderAt χ.LFunction s ≠ ⊤`.
* `DirichletCharacter.meromorphicOrderAt_LFunction_eq_analyticOrderNatAt`:
  `meromorphicOrderAt χ.LFunction s = (analyticOrderNatAt χ.LFunction s : ℤ)`.
* `DirichletCharacter.LFunction_eq_zero_iff_one_le_analyticOrderNatAt`:
  `χ.LFunction s = 0 ↔ 1 ≤ analyticOrderNatAt χ.LFunction s`.
* `DirichletCharacter.meromorphicOrderAt_LFunction_pos_iff`:
  `0 < meromorphicOrderAt χ.LFunction s ↔ χ.LFunction s = 0`.
* `DirichletCharacter.meromorphicOrderAt_LFunction_eq_one_iff`:
  `meromorphicOrderAt χ.LFunction s = 1 ↔ analyticOrderNatAt χ.LFunction s = 1`.
-/

public section

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- All analytic orders of a nonprincipal continued Dirichlet L-function are finite. -/
theorem analyticOrderAt_LFunction_ne_top (hne : χ ≠ 1) (s : ℂ) :
    analyticOrderAt χ.LFunction s ≠ ⊤ := by
  have ha : AnalyticOnNhd ℂ χ.LFunction Set.univ :=
    fun z _ ↦ (differentiable_LFunction hne).analyticAt z
  refine ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (x := 1) (by trivial) (by trivial) ?_
  rw [(ha 1 (by trivial)).analyticOrderAt_eq_zero.mpr (LFunction_apply_one_ne_zero hne)]
  simp

/-- At any point, the meromorphic order of a nonprincipal continued Dirichlet L-function is the
cast of its natural analytic order. -/
theorem meromorphicOrderAt_LFunction_eq_analyticOrderNatAt (hne : χ ≠ 1) (s : ℂ) :
    meromorphicOrderAt χ.LFunction s = (analyticOrderNatAt χ.LFunction s : ℤ) := by
  have haL := (differentiable_LFunction hne).analyticAt s
  rw [haL.meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt (χ.analyticOrderAt_LFunction_ne_top hne s)]
  rfl

/-- A nonprincipal continued Dirichlet L-function vanishes at `s` if and only if its natural
analytic order at `s` is at least `1`. -/
theorem LFunction_eq_zero_iff_one_le_analyticOrderNatAt (hne : χ ≠ 1) (s : ℂ) :
    χ.LFunction s = 0 ↔ 1 ≤ analyticOrderNatAt χ.LFunction s := by
  have haL := (differentiable_LFunction hne).analyticAt s
  rw [← haL.analyticOrderAt_ne_zero,
    ← Nat.cast_analyticOrderNatAt (χ.analyticOrderAt_LFunction_ne_top hne s)]
  exact_mod_cast Nat.one_le_iff_ne_zero.symm

/-- A nonprincipal continued Dirichlet L-function has positive meromorphic order at `s` if and only
if it vanishes at `s`. -/
theorem meromorphicOrderAt_LFunction_pos_iff (hne : χ ≠ 1) (s : ℂ) :
    0 < meromorphicOrderAt χ.LFunction s ↔ χ.LFunction s = 0 := by
  rw [χ.meromorphicOrderAt_LFunction_eq_analyticOrderNatAt hne s,
    χ.LFunction_eq_zero_iff_one_le_analyticOrderNatAt hne s]
  exact_mod_cast Nat.pos_iff_ne_zero.trans Nat.one_le_iff_ne_zero.symm

/-- A nonprincipal continued Dirichlet L-function has meromorphic order `1` at `s` if and only if
its natural analytic order at `s` is `1`. -/
theorem meromorphicOrderAt_LFunction_eq_one_iff (hne : χ ≠ 1) (s : ℂ) :
    meromorphicOrderAt χ.LFunction s = 1 ↔ analyticOrderNatAt χ.LFunction s = 1 := by
  rw [χ.meromorphicOrderAt_LFunction_eq_analyticOrderNatAt hne s]
  exact_mod_cast Iff.rfl

end DirichletCharacter
