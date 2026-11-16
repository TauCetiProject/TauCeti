/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.Algebra
public import TauCeti.RingTheory.Nilpotent.Log

/-!
# Exponential and logarithm in filtered completions

In the completion of an associative rational algebra, elements of the first
filtration ideal have nilpotent finite-order projections. Exponentiation of these
projections defines a completed exponential; finite logarithms similarly define
a completed logarithm on elements congruent to one. These maps are inverse,
without a norm, an adic presentation, or separatedness of the original algebra.
They provide the exponential coordinates used for complete pronilpotent groups.

The construction uses Mathlib's `IsNilpotent.exp` and its naturality theorem,
and Tau Ceti's `IsNilpotent.log`, `map_log`, `log_exp`, and `exp_log`.

Adapted from `Mei/RingTheory/FilteredAlgebra/Exp/Basic.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
-/

public section

open Opposite

namespace TauCeti.AlgFiltration

variable {A : Type*} [Ring A] (F : AlgFiltration A)

variable [Algebra ℚ A]

/-- The completed exponential, defined by the finite exponential at every order. -/
noncomputable def completedExp (x : F.completionIdeal 1) : F.completion :=
  ⟨fun k => IsNilpotent.exp (F.projection k.unop x),
    (F.mem_completion_iff _).mpr fun {k l} h => by
      rw [(F.isNilpotent_projection x.property l).map_exp, F.factor_projection h]⟩

/-- The completed logarithm, defined by finite logarithms at every order. -/
noncomputable def completedLog
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}) : F.completion :=
  ⟨fun k => IsNilpotent.log (F.projection k.unop u),
    (F.mem_completion_iff _).mpr fun {k l} h => by
      have hu : IsNilpotent (F.projection l u - 1) := by
        simpa using F.isNilpotent_projection u.property l
      rw [hu.map_log, F.factor_projection h]⟩

/-- Finite-order projections compute the completed exponential. -/
@[simp]
theorem projection_completedExp (x : F.completionIdeal 1) (k : ℕ) :
    F.projection k (F.completedExp x) = IsNilpotent.exp (F.projection k x) := by
  rw [F.projection_apply, completedExp]

/-- Finite-order projections compute the completed logarithm. -/
@[simp]
theorem projection_completedLog
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}) (k : ℕ) :
    F.projection k (F.completedLog u) = IsNilpotent.log (F.projection k u) := by
  rw [F.projection_apply, completedLog]

/-- The completed exponential is congruent to one modulo the first ideal. -/
theorem completedExp_sub_one_mem (x : F.completionIdeal 1) :
    F.completedExp x - 1 ∈ F.completionIdeal 1 := by
  have hx : F.projection 0 x = 0 := by
    simpa [completionIdeal_succ, RingHom.mem_ker] using x.property
  simp [completionIdeal_succ, RingHom.mem_ker, hx, IsNilpotent.exp_zero]

/-- The completed logarithm belongs to the first ideal. -/
theorem completedLog_mem
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}) :
    F.completedLog u ∈ F.completionIdeal 1 := by
  have hu : F.projection 0 u = 1 := by
    simpa [completionIdeal_succ, RingHom.mem_ker, sub_eq_zero] using u.property
  simp [completionIdeal_succ, RingHom.mem_ker, hu]

/-- The logarithm undoes the completed exponential. -/
@[simp]
theorem completedLog_completedExp (x : F.completionIdeal 1) :
    F.completedLog ⟨F.completedExp x, F.completedExp_sub_one_mem x⟩ = x := by
  apply F.completion_ext
  intro k
  simp [IsNilpotent.log_exp (F.isNilpotent_projection x.property k)]

/-- The exponential undoes the completed logarithm. -/
@[simp]
theorem completedExp_completedLog
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}) :
    F.completedExp ⟨F.completedLog u, F.completedLog_mem u⟩ = u := by
  apply F.completion_ext
  intro k
  have hu : IsNilpotent (F.projection k u - 1) := by
    simpa using F.isNilpotent_projection u.property k
  simp [IsNilpotent.exp_log hu]

/-- Exponential coordinates identify the first completion ideal with the elements
congruent to one. This is an equivalence of sets. -/
noncomputable def completedExpEquiv :
    F.completionIdeal 1 ≃ {u : F.completion // u - 1 ∈ F.completionIdeal 1} where
  toFun x := ⟨F.completedExp x, F.completedExp_sub_one_mem x⟩
  invFun u := ⟨F.completedLog u, F.completedLog_mem u⟩
  left_inv x := Subtype.ext (F.completedLog_completedExp x)
  right_inv u := Subtype.ext (F.completedExp_completedLog u)

/-- The forward exponential-coordinate map is the completed exponential. -/
@[simp]
theorem coe_completedExpEquiv (x : F.completionIdeal 1) :
    (F.completedExpEquiv x : F.completion) = F.completedExp x := (rfl)

/-- The inverse exponential-coordinate map is the completed logarithm. -/
@[simp]
theorem coe_completedExpEquiv_symm
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}) :
    (F.completedExpEquiv.symm u : F.completion) = F.completedLog u := (rfl)

/-- The completed exponential of zero is one. -/
@[simp]
theorem completedExp_zero : F.completedExp 0 = 1 := by
  apply F.completion_ext
  intro k
  simp [IsNilpotent.exp_zero]

/-- The completed logarithm of one is zero. -/
@[simp]
theorem completedLog_one : F.completedLog ⟨1, by simp⟩ = 0 := by
  apply F.completion_ext
  intro k
  simp

/-- Exponentials of commuting elements multiply by adding their arguments. -/
theorem completedExp_add (x y : F.completionIdeal 1)
    (h : Commute (x : F.completion) y) :
    F.completedExp (x + y) = F.completedExp x * F.completedExp y := by
  apply F.completion_ext
  intro k
  simpa using IsNilpotent.exp_add_of_commute (h.map (F.projection k))
    (F.isNilpotent_projection x.property k) (F.isNilpotent_projection y.property k)

/-- Negating the exponential argument gives a right multiplicative inverse. -/
@[simp]
theorem completedExp_mul_completedExp_neg (x : F.completionIdeal 1) :
    F.completedExp x * F.completedExp (-x) = 1 := by
  apply F.completion_ext
  intro k
  simpa using IsNilpotent.exp_mul_exp_neg_self (F.isNilpotent_projection x.property k)

/-- Negating the exponential argument gives a left multiplicative inverse. -/
@[simp]
theorem completedExp_neg_mul_completedExp (x : F.completionIdeal 1) :
    F.completedExp (-x) * F.completedExp x = 1 := by
  apply F.completion_ext
  intro k
  simpa using IsNilpotent.exp_neg_mul_exp_self (F.isNilpotent_projection x.property k)

/-- Every completed exponential is a unit. -/
theorem isUnit_completedExp (x : F.completionIdeal 1) : IsUnit (F.completedExp x) :=
  ⟨⟨F.completedExp x, F.completedExp (-x),
    F.completedExp_mul_completedExp_neg x, F.completedExp_neg_mul_completedExp x⟩, rfl⟩

/-- Exponentiation preserves and reflects every filtration order. -/
@[simp]
theorem completedExp_sub_one_mem_iff (x : F.completionIdeal 1) (n : ℕ) :
    F.completedExp x - 1 ∈ F.completionIdeal n ↔
      (x : F.completion) ∈ F.completionIdeal n := by
  cases n with
  | zero => simp
  | succ k =>
    simp only [completionIdeal_succ, RingHom.mem_ker, map_sub,
      projection_completedExp, map_one, sub_eq_zero]
    constructor
    · intro h
      have he := IsNilpotent.log_exp (F.isNilpotent_projection x.property k)
      rw [h, IsNilpotent.log_one] at he
      exact he.symm
    · intro h
      simp [h, IsNilpotent.exp_zero]

/-- Taking the logarithm preserves and reflects every filtration order. -/
@[simp]
theorem completedLog_mem_iff
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}) (n : ℕ) :
    F.completedLog u ∈ F.completionIdeal n ↔
      (u : F.completion) - 1 ∈ F.completionIdeal n := by
  simpa only [completedExp_completedLog, Subtype.coe_mk] using
    (F.completedExp_sub_one_mem_iff ⟨F.completedLog u, F.completedLog_mem u⟩ n).symm

end TauCeti.AlgFiltration
