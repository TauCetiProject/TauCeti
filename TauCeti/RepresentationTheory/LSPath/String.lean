/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Option.Iterate
public import TauCeti.RepresentationTheory.LSPath.RootOperator

/-!
# Root strings of piecewise-linear paths

For a root `x` and coroot form `f` with `f x = 2`, lowering a path decreases its minimum
height by one, and raising increases it by one. Consequently the iterated operators are
defined precisely up to the bounds `f p.endpoint - p.minHeight f` and `-p.minHeight f`.
These bounds apply to ambient paths over any ordered field; when they are integers they
are the usual normal-crystal string lengths.

The minimum-height formulas from `RootOperator` account for unchanged equal-height
excursions. No integrality of local minima, or simplified whole-interval reflection formula,
is assumed. Partial invertibility of the two operators is a separate assertion and is not
proved here.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142
  (1995), §1.
-/

public section

namespace TauCeti.PLPath

open Module

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]
  {f : Dual 𝕜 V} {x : V}

/-! ### Iterated root operators -/

variable (f x) in
/-- Apply lowering `n` times, returning `none` as soon as an application is undefined. -/
noncomputable def lowerIter : ℕ → PLPath 𝕜 V → Option (PLPath 𝕜 V) :=
  Option.iterate (lower f x)

variable (f x) in
/-- Apply raising `n` times, returning `none` as soon as an application is undefined. -/
noncomputable def raiseIter : ℕ → PLPath 𝕜 V → Option (PLPath 𝕜 V) :=
  Option.iterate (raise f x)

@[simp]
theorem lowerIter_zero (p : PLPath 𝕜 V) : lowerIter f x 0 p = some p :=
  Option.iterate_zero (lower f x) p

@[simp]
theorem raiseIter_zero (p : PLPath 𝕜 V) : raiseIter f x 0 p = some p :=
  Option.iterate_zero (raise f x) p

theorem lowerIter_succ (n : ℕ) (p : PLPath 𝕜 V) :
    lowerIter f x (n + 1) p = (lower f x p).bind (lowerIter f x n) :=
  Option.iterate_succ (lower f x) n p

theorem raiseIter_succ (n : ℕ) (p : PLPath 𝕜 V) :
    raiseIter f x (n + 1) p = (raise f x p).bind (raiseIter f x n) :=
  Option.iterate_succ (raise f x) n p

@[simp]
theorem lowerIter_one (p : PLPath 𝕜 V) : lowerIter f x 1 p = lower f x p :=
  Option.iterate_one (lower f x) p

@[simp]
theorem raiseIter_one (p : PLPath 𝕜 V) : raiseIter f x 1 p = raise f x p :=
  Option.iterate_one (raise f x) p

/-- Iterated raising is iterated lowering conjugated by reversal. -/
theorem raiseIter_eq_map_lowerIter_reverse (n : ℕ) (p : PLPath 𝕜 V) :
    raiseIter f x n p = (lowerIter f x n p.reverse).map reverse := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    simp only [raiseIter_succ, lowerIter_succ, raise_def, Option.bind_map,
      Option.map_bind, ih, Function.comp_def, reverse_reverse]

/-- Concatenating two runs of the lowering operator. -/
theorem lowerIter_add (m n : ℕ) (p : PLPath 𝕜 V) :
    lowerIter f x (m + n) p = (lowerIter f x m p).bind (lowerIter f x n) :=
  Option.iterate_add (lower f x) m n p

/-- Concatenating two runs of the raising operator. -/
theorem raiseIter_add (m n : ℕ) (p : PLPath 𝕜 V) :
    raiseIter f x (m + n) p = (raiseIter f x m p).bind (raiseIter f x n) :=
  Option.iterate_add (raise f x) m n p

variable {p q : PLPath 𝕜 V} {n : ℕ}

/-- Lowering `n` times subtracts `n` copies of the root from the endpoint. -/
theorem endpoint_of_lowerIter_eq_some (h : lowerIter f x n p = some q) :
    q.endpoint = p.endpoint - n • x := by
  induction n generalizing p with
  | zero =>
    simp only [lowerIter_zero, Option.some.injEq] at h
    subst q
    simp
  | succ n ih =>
    rw [lowerIter_succ, Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, hq⟩ := h
    rw [ih hq, endpoint_of_lower_eq_some hr, add_nsmul, one_nsmul]
    abel

/-- Lowering `n` times decreases the minimum height by `n`. -/
theorem minHeight_of_lowerIter_eq_some (hx : f x = 2)
    (h : lowerIter f x n p = some q) : q.minHeight f = p.minHeight f - n := by
  induction n generalizing p with
  | zero =>
    simp only [lowerIter_zero, Option.some.injEq] at h
    subst q
    simp
  | succ n ih =>
    rw [lowerIter_succ, Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, hq⟩ := h
    rw [ih hq, minHeight_of_lower_eq_some hx hr, Nat.cast_add, Nat.cast_one]
    ring

/-- Raising `n` times adds `n` copies of the root to the endpoint. -/
theorem endpoint_of_raiseIter_eq_some (h : raiseIter f x n p = some q) :
    q.endpoint = p.endpoint + n • x := by
  rw [raiseIter_eq_map_lowerIter_reverse] at h
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [endpoint_reverse, endpoint_of_lowerIter_eq_some hr, endpoint_reverse]
  abel

/-- Raising `n` times increases the minimum height by `n`. -/
theorem minHeight_of_raiseIter_eq_some (hx : f x = 2)
    (h : raiseIter f x n p = some q) : q.minHeight f = p.minHeight f + n := by
  rw [raiseIter_eq_map_lowerIter_reverse] at h
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [minHeight_reverse, minHeight_of_lowerIter_eq_some hx hr,
    endpoint_of_lowerIter_eq_some hr, map_sub, endpoint_reverse, map_neg, map_nsmul, hx,
    minHeight_reverse]
  simp only [nsmul_eq_mul]
  ring

/-- The exact bound for iterated lowering. No integrality hypothesis on the path is needed. -/
@[simp]
theorem isSome_lowerIter_iff (hx : f x = 2) :
    (lowerIter f x n p).isSome ↔ (n : 𝕜) ≤ f p.endpoint - p.minHeight f := by
  induction n generalizing p with
  | zero => simp [sub_nonneg.2 (minHeight_le_apply_endpoint p)]
  | succ n ih =>
    rw [lowerIter_succ]
    cases h : lower f x p with
    | none =>
      have hp := lower_eq_none_iff.1 h
      simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, false_iff,
        Nat.cast_add, Nat.cast_one, not_le]
      have hn : (0 : 𝕜) ≤ n := Nat.cast_nonneg n
      linarith
    | some r =>
      have he := endpoint_of_lower_eq_some h
      have hm := minHeight_of_lower_eq_some hx h
      simp only [Option.bind_some, ih, he, hm, map_sub, hx, Nat.cast_add, Nat.cast_one]
      constructor <;> intro hn <;> linarith

/-- The exact bound for iterated raising. Integral negative minimum height is therefore the
usual raising-string length. -/
@[simp]
theorem isSome_raiseIter_iff (hx : f x = 2) :
    (raiseIter f x n p).isSome ↔ (n : 𝕜) ≤ -p.minHeight f := by
  rw [raiseIter_eq_map_lowerIter_reverse, Option.isSome_map, isSome_lowerIter_iff hx,
    endpoint_reverse, map_neg, minHeight_reverse]
  constructor <;> intro h <;> linarith

/-- Iterated lowering is undefined precisely beyond its height bound. -/
@[simp]
theorem lowerIter_eq_none_iff (hx : f x = 2) :
    lowerIter f x n p = none ↔ f p.endpoint - p.minHeight f < n := by
  simpa using not_congr (isSome_lowerIter_iff (n := n) (p := p) hx)

/-- Iterated raising is undefined precisely beyond its height bound. -/
@[simp]
theorem raiseIter_eq_none_iff (hx : f x = 2) :
    raiseIter f x n p = none ↔ -p.minHeight f < n := by
  simpa using not_congr (isSome_raiseIter_iff (n := n) (p := p) hx)

end TauCeti.PLPath
