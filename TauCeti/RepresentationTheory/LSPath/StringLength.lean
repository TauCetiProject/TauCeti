/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.PartialInverse

/-!
# String lengths of the root operators on piecewise-linear paths

Fix a vector `x : V` and a linear form `f : V → 𝕜` with `f x = 2`; in Littelmann's path model
`x` is a simple root `α` and `f` the pairing with its coroot. Write `H(t) = f (π t)` for the
running height of a path `π` and `h = min H` for its minimal height
(`TauCeti.PLPath.minHeight`). This file proves that the root operators
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

* `TauCeti.PLPath.listMinHeight_reflectRecords`: the minimal height of capped reflection.
* `TauCeti.PLPath.minHeight_of_lower_eq_some`, `TauCeti.PLPath.minHeight_of_raise_eq_some`:
  `f_α` lowers and `e_α` raises the minimal height by one.
* `TauCeti.PLPath.isSome_iterate_bind_lower_iff`, `TauCeti.PLPath.isSome_iterate_bind_raise_iff`:
  the lengths of the root strings through a path.
* `TauCeti.PLPath.isSome_iterate_bind_lower_iff_of_eq_natCast`,
  `TauCeti.PLPath.isSome_iterate_bind_raise_iff_of_eq_natCast`: the string-length identities
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

/-! ### The minimal height of capped reflection -/

/-- Reflecting the records up to height `c` lowers the minimal height by the increase, along the
path, of the minimum of `c` and the later minimal height. Compare
`TauCeti.PLPath.sum_reflectRecords`, by which the final height drops by twice this amount. -/
theorem listMinHeight_reflectRecords (hx : f x = 2) (c : 𝕜) (l : List V) :
    listMinHeight f (reflectRecords f x c l) =
      listMinHeight f l - (min (f l.sum) c - min (listMinHeight f l) c) := by
  induction l generalizing c with
  | nil => simp
  | cons v l ih =>
    have hl := listMinHeight_nonpos (f := f) l
    have hls := listMinHeight_le_apply_sum (f := f) l
    by_cases h : 0 < min (f v + listMinHeight f l) c
    · set r := min (f v + listMinHeight f l) c with hr
      have hfv : f v ≠ 0 := (h.trans_le ((min_le_left _ _).trans (by linarith))).ne'
      -- The reflected initial piece of `v` descends by `r`; the kept piece climbs by `f v - r`.
      have h₁ : f (preReflection x f ((r / f v) • v)) = -r := by
        rw [preReflection_apply, map_sub, map_smul, map_smul, hx, smul_eq_mul, smul_eq_mul,
          div_mul_cancel₀ _ hfv]
        ring
      have h₂ : f ((1 - r / f v) • v) = f v - r := by
        rw [map_smul, smul_eq_mul, sub_mul, one_mul, div_mul_cancel₀ _ hfv]
      have hr₁ : r ≤ f v + listMinHeight f l := min_le_left _ _
      have hr₂ : r ≤ c := min_le_right _ _
      have hpos : 0 < f v + listMinHeight f l := h.trans_le hr₁
      have hc : 0 < c := h.trans_le hr₂
      rw [reflectRecords_cons_of_pos h, ← hr]
      simp only [listMinHeight_cons, ih, h₁, h₂, List.sum_cons, map_add, min_eq_left hpos.le,
        min_eq_left hc.le]
      rcases min_choice (f v + listMinHeight f l) c with hr₃ | hr₃ <;> rw [← hr] at hr₃
      · -- The whole of `v` lies below the cap, so the cap on `l` is above its minimal height.
        rw [min_eq_left (show listMinHeight f l ≤ c - f v by linarith)]
        simp only [min_def]
        split_ifs <;> linarith
      · -- The cap is reached inside `v`, so it stays below every later height.
        rw [min_eq_right (show c - f v ≤ f l.sum by linarith),
          min_eq_right (show c - f v ≤ listMinHeight f l by linarith)]
        simp only [min_def]
        split_ifs <;> linarith
    · rw [reflectRecords_cons_of_nonpos (not_lt.1 h)]
      simp only [listMinHeight_cons, ih, List.sum_cons, map_add]
      simp only [min_def] at h ⊢
      split_ifs at h ⊢ <;> linarith

/-! ### The root operators move the minimal height by one -/

variable {p q : PLPath 𝕜 V}

/-- **Lowering lowers the minimal height by one**: `min H(f_α π) = min H(π) - 1`. -/
theorem minHeight_of_lower_eq_some (hx : f x = 2) (h : lower f x p = some q) :
    q.minHeight f = p.minHeight f - 1 := by
  rw [← ofSegments_segments p, lower_ofSegments] at h
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [listLower_def] at hl
  split_ifs at hl with hdef
  obtain rfl := Option.some.inj hl
  rw [minHeight_ofSegments, listMinHeight_reflectRecords hx, minHeight_def,
    min_eq_right (by linarith), min_eq_left (by linarith)]
  ring

/-- **Raising raises the minimal height by one**: `min H(e_α π) = min H(π) + 1`. -/
theorem minHeight_of_raise_eq_some (hx : f x = 2) (h : raise f x p = some q) :
    q.minHeight f = p.minHeight f + 1 := by
  rw [minHeight_of_lower_eq_some hx ((raise_eq_some_iff hx).1 h)]
  ring

/-- Lowering shortens the lowering string by one: `H(1) - min H` drops by one under `f_α`. -/
theorem apply_endpoint_sub_minHeight_of_lower_eq_some (hx : f x = 2) (h : lower f x p = some q) :
    f q.endpoint - q.minHeight f + 1 = f p.endpoint - p.minHeight f := by
  rw [endpoint_of_lower_eq_some h, minHeight_of_lower_eq_some hx h, map_sub, hx]
  ring

/-! ### Lengths of the root strings -/

/-- **The lowering string through a path**: `f_α ^ n π` is defined exactly when
`n ≤ H(1) - min H`. -/
theorem isSome_iterate_bind_lower_iff (hx : f x = 2) (n : ℕ) (p : PLPath 𝕜 V) :
    ((fun o ↦ o.bind (lower f x))^[n] (some p)).isSome ↔
      (n : 𝕜) ≤ f p.endpoint - p.minHeight f := by
  induction n generalizing p with
  | zero => simpa using sub_nonneg.2 (minHeight_le_apply_endpoint p)
  | succ n ih =>
    rw [Function.iterate_succ_apply, Option.bind_some]
    cases h : lower f x p with
    | none =>
      rw [lower_eq_none_iff] at h
      rw [Function.iterate_fixed (Option.bind_none _), Option.isSome_none, Bool.false_eq_true,
        false_iff, not_le]
      push_cast
      linarith [(Nat.cast_nonneg n : (0 : 𝕜) ≤ n)]
    | some q =>
      rw [ih, ← apply_endpoint_sub_minHeight_of_lower_eq_some hx h]
      push_cast
      constructor <;> intro <;> linarith

/-- **The raising string through a path**: `e_α ^ n π` is defined exactly when `n ≤ -min H`. -/
theorem isSome_iterate_bind_raise_iff (hx : f x = 2) (n : ℕ) (p : PLPath 𝕜 V) :
    ((fun o ↦ o.bind (raise f x))^[n] (some p)).isSome ↔ (n : 𝕜) ≤ -p.minHeight f := by
  induction n generalizing p with
  | zero => simpa using minHeight_nonpos p
  | succ n ih =>
    rw [Function.iterate_succ_apply, Option.bind_some]
    cases h : raise f x p with
    | none =>
      rw [raise_eq_none_iff] at h
      rw [Function.iterate_fixed (Option.bind_none _), Option.isSome_none, Bool.false_eq_true,
        false_iff, not_le]
      push_cast
      linarith [(Nat.cast_nonneg n : (0 : 𝕜) ≤ n)]
    | some q =>
      rw [ih, minHeight_of_raise_eq_some hx h]
      push_cast
      constructor <;> intro <;> linarith

/-- **The string-length identity `φ_α = H(1) - min H`**: when `H(1) - min H` is a natural number
`φ`, the lowering string through the path has length exactly `φ`. -/
theorem isSome_iterate_bind_lower_iff_of_eq_natCast (hx : f x = 2) {φ : ℕ}
    (hφ : f p.endpoint - p.minHeight f = φ) (n : ℕ) :
    ((fun o ↦ o.bind (lower f x))^[n] (some p)).isSome ↔ n ≤ φ := by
  rw [isSome_iterate_bind_lower_iff hx, hφ, Nat.cast_le]

/-- **The string-length identity `ε_α = -min H`**: when `-min H` is a natural number `ε`, the
raising string through the path has length exactly `ε`. -/
theorem isSome_iterate_bind_raise_iff_of_eq_natCast (hx : f x = 2) {ε : ℕ}
    (hε : -p.minHeight f = ε) (n : ℕ) :
    ((fun o ↦ o.bind (raise f x))^[n] (some p)).isSome ↔ n ≤ ε := by
  rw [isSome_iterate_bind_raise_iff hx, hε, Nat.cast_le]

end PLPath

end TauCeti
