/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Option.Iterate
public import TauCeti.RepresentationTheory.LSPath.RootOperator

/-!
# String lengths of the root operators on piecewise-linear paths

Fix a vector `x : V` and a linear form `f : V → 𝕜` with `f x = 2`; in Littelmann's path model
`x` is a simple root `α` and `f` the pairing with its coroot. Write `H(t) = f (π t)` for the
running height of a path `π` and `h = min H` for its minimal height
(`TauCeti.PLPath.minHeight`). The single-step formulas in
`TauCeti.RepresentationTheory.LSPath.RootOperator` show that the root operators
`f_α = TauCeti.PLPath.lower f x` and `e_α = TauCeti.PLPath.raise f x` move the minimal height by
exactly one step: `min H(f_α π) = h - 1` and `min H(e_α π) = h + 1`. Since `f_α` lowers the final
height by `f x = 2`, it shortens `H(1) - h` by one.

Together with the criteria `f_α π = 0 ↔ H(1) - h < 1` and `e_α π = 0 ↔ -1 < h`, this computes
the lengths of the root strings through every path: `f_α ^ n π` is defined exactly when
`n ≤ H(1) - h`, and `e_α ^ n π` exactly when `n ≤ -h`. These ambient statements hold for every
path. When `h` and `H(1)` are integers, as on Littelmann's integral paths, they become the
string-length identities `ε_α(π) = -h` and `φ_α(π) = H(1) - h` of a normal crystal
(`TauCeti.NormalCrystal`).

The key computation is the minimal height of capped reflection
(`TauCeti.PLPath.listMinHeight_reflectRecords`): reflecting the pieces of a path along which the
height is at most `c` and at most every later height lowers the minimal height by the increase
`min (H 1) c - min h c`, just as it lowers the final height by twice that amount.

## Main results

* `TauCeti.PLPath.lowerIter`, `TauCeti.PLPath.raiseIter`: iterated partial root operators,
  with composition, reversal, endpoint and minimum-height formulas.
* `TauCeti.PLPath.isSome_lowerIter_iff`, `TauCeti.PLPath.isSome_raiseIter_iff`:
  the lengths of the root strings through a path.
* `TauCeti.PLPath.isSome_lowerIter_iff_of_eq_natCast`,
  `TauCeti.PLPath.isSome_raiseIter_iff_of_eq_natCast`: the string-length identities
  `φ_α = H(1) - h` and `ε_α = -h` when these are natural numbers.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §§1–2.
-/

public section

namespace TauCeti

namespace PLPath

open Module

variable {𝕜 : Type*} {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] {f : Dual 𝕜 V} {x : V}

variable {p q : PLPath 𝕜 V}

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

variable {n : ℕ}

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

/-! ### Lengths of the root strings -/

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

/-- **The string-length identity `φ_α = H(1) - min H`**: when `H(1) - min H` is a natural number
`φ`, the lowering string through the path has length exactly `φ`. -/
theorem isSome_lowerIter_iff_of_eq_natCast (hx : f x = 2) {φ : ℕ}
    (hφ : f p.endpoint - p.minHeight f = φ) (n : ℕ) :
    (lowerIter f x n p).isSome ↔ n ≤ φ := by
  rw [isSome_lowerIter_iff hx, hφ, Nat.cast_le]

/-- **The string-length identity `ε_α = -min H`**: when `-min H` is a natural number `ε`, the
raising string through the path has length exactly `ε`. -/
theorem isSome_raiseIter_iff_of_eq_natCast (hx : f x = 2) {ε : ℕ}
    (hε : -p.minHeight f = ε) (n : ℕ) :
    (raiseIter f x n p).isSome ↔ n ≤ ε := by
  rw [isSome_raiseIter_iff hx, hε, Nat.cast_le]

end PLPath

end TauCeti
