/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.RootOperator
import Mathlib.Algebra.Order.Group.MinMax

/-!
# The root operators on piecewise-linear paths are partial inverses

Fix a vector `x : V` and a linear form `f : V → 𝕜` with `f x = 2`; in Littelmann's path model
`x` is a simple root `α` and `f` the pairing with its coroot. This file proves that Littelmann's
lowering and raising operators `f_α = TauCeti.PLPath.lower f x` and
`e_α = TauCeti.PLPath.raise f x` are partial inverses on all piecewise-linear paths:
`f_α π = π'` exactly when `e_α π' = π`. This is the partial-inverse axiom of a crystal; no
integrality of the path is needed.

The proof works with segment lists. Lowering with cap `c` reflects the pieces of a path along
which the running height `H` is at most `c` and at most every later height
(`TauCeti.PLPath.reflectRecords`): it subtracts `(min c (m t) - min c h) • x` at time `t`, where
`m t` is the minimum of `H` on `[t, 1]` and `h` the minimal height. Since `e_α` is `f_α`
conjugated by reversal, the inverse of this capped reflection is again a capped reflection, on
the reversed lowered path, whose cap is `h` minus the final height of the lowered path. This is
`TauCeti.PLPath.normalize_reflectRecords_reverse_reflectRecords`, proved by splitting off the
first segment with `TauCeti.PLPath.reflectRecords_append`. The minimal height of the reversed
lowered path, which decides whether raising is defined, is then read off from the endpoints.

## Main results

* `TauCeti.PLPath.reflectRecords_append`: capped reflection of a concatenation.
* `TauCeti.PLPath.reflectRecords_of_le_listMinHeight`: capped reflection is the identity when
  the cap is at most the minimal height.
* `TauCeti.PLPath.normalize_reflectRecords_reverse_reflectRecords`: capped reflection of a
  reversed path undoes capped reflection.
* `TauCeti.PLPath.lower_eq_some_iff`, `TauCeti.PLPath.raise_eq_some_iff`: `f_α π = π'` exactly
  when `e_α π' = π`.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §1.
-/

public section

namespace TauCeti

namespace PLPath

open Module

variable {𝕜 : Type*} {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] {f : Dual 𝕜 V} {x : V}

/-! ### Undoing capped reflection -/

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The heights of the two pieces into which `TauCeti.PLPath.reflectRecords` cuts a segment `v`
at height `r`: the reflected initial piece and the kept final piece. -/
private theorem apply_reflect_cut (hx : f x = 2) {v : V} (hv : f v ≠ 0) (r : 𝕜) :
    f (preReflection x f ((r / f v) • v)) = -r ∧ f ((1 - r / f v) • v) = f v - r := by
  refine ⟨?_, ?_⟩
  · rw [preReflection_apply, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      div_mul_cancel₀ _ hv, hx]
    ring
  · rw [map_smul, smul_eq_mul, sub_mul, one_mul, div_mul_cancel₀ _ hv]

/-- Undoing the reflection of a single segment `v`, cut at height `r` with `0 < r ≤ f v`: on the
reversed segments, the formerly reflected piece is reflected back. -/
private theorem normalize_reflectRecords_reverse_cut (hx : f x = 2) {v : V} {r : 𝕜} (hr : 0 < r)
    (hrv : r ≤ f v) :
    normalize 𝕜 (reflectRecords f x (2 * r - f v)
        ([preReflection x f ((r / f v) • v), (1 - r / f v) • v].map Neg.neg).reverse) =
      normalize 𝕜 [-v] := by
  have hv : f v ≠ 0 := (hr.trans_le hrv).ne'
  obtain ⟨hs, hb⟩ := apply_reflect_cut hx hv r
  have hneg : f (-preReflection x f ((r / f v) • v)) = r := by rw [map_neg, hs, neg_neg]
  have h₁ : min (f (-((1 - r / f v) • v)) +
      listMinHeight f [-preReflection x f ((r / f v) • v)]) (2 * r - f v) ≤ 0 := by
    rw [map_neg, hb, listMinHeight_cons, listMinHeight_nil, add_zero, hneg,
      min_eq_left hr.le]
    exact min_le_of_left_le (by linarith)
  have hcap : 2 * r - f v - f (-((1 - r / f v) • v)) = r := by
    rw [map_neg, hb]
    ring
  have h₂ : min (f (-preReflection x f ((r / f v) • v)) + listMinHeight f ([] : List V)) r =
      r := by
    rw [hneg, listMinHeight_nil, add_zero, min_self]
  have hsame : SameRay 𝕜 (-((1 - r / f v) • v)) (-((r / f v) • v)) := by
    rw [← smul_neg, ← smul_neg]
    exact (SameRay.sameRay_nonneg_smul_left (-v) (by
      rw [sub_nonneg, div_le_one (hr.trans_le hrv)]; exact hrv)).nonneg_smul_right
      (div_nonneg hr.le (hr.trans_le hrv).le)
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append]
  -- The kept piece stays, the formerly reflected piece is reflected back entirely, and the two
  -- resulting pieces merge into `-v`.
  rw [reflectRecords_cons_of_nonpos h₁, hcap, reflectRecords_cons_of_pos (h₂.symm ▸ hr), h₂,
    hneg, div_self hr.ne', one_smul, sub_self, zero_smul, map_neg,
    involutive_preReflection hx, reflectRecords_nil]
  simp only [normalize_cons, normalize_nil, consMerge_zero]
  rw [consMerge_consMerge hsame, ← neg_add, ← add_smul, sub_add_cancel, one_smul]

/-- Reflecting the records of a reversed concatenation `P ++ l` splits into the reflections of the
two reversed pieces, as `TauCeti.PLPath.reflectRecords_append` dictates. -/
private theorem normalize_reflectRecords_reverse_append {P l A B : List V} {k : 𝕜}
    (hl : normalize 𝕜 (reflectRecords f x (min k (-f l.sum + listMinHeight f
        (P.map Neg.neg).reverse)) (l.map Neg.neg).reverse) = normalize 𝕜 B)
    (hP : normalize 𝕜 (reflectRecords f x (k + f l.sum) (P.map Neg.neg).reverse) =
        normalize 𝕜 A) :
    normalize 𝕜 (reflectRecords f x k ((P ++ l).map Neg.neg).reverse) = normalize 𝕜 (B ++ A) := by
  rw [List.map_append, List.reverse_append, reflectRecords_append, ← List.sum_neg_reverse,
    map_neg, sub_neg_eq_add, ← normalize_normalize_append, hl, normalize_normalize_append,
    ← normalize_append_normalize, hP, normalize_append_normalize]

/-- Reflecting the records of a reversed path undoes the reflection of the records up to any cap
`c`: if `l'` is obtained from `l` by reflecting its records up to `c`, then reflecting the records
of the reversal of `l'` up to the minimal height of `l` minus the final height of `l'` gives back
the reversal of `l`, up to the elementary moves. -/
theorem normalize_reflectRecords_reverse_reflectRecords (hx : f x = 2) (c : 𝕜) (l : List V) :
    normalize 𝕜 (reflectRecords f x (listMinHeight f l - f (reflectRecords f x c l).sum)
        ((reflectRecords f x c l).map Neg.neg).reverse) =
      normalize 𝕜 (l.map Neg.neg).reverse := by
  -- Induction on `l = v :: l₀`. The reversal of the reflected list is the reversed reflected tail
  -- followed by the reversed pieces of `v`; the first is handled by the induction hypothesis, the
  -- second by a direct computation.
  induction l generalizing c with
  | nil => simp
  | cons v l ih =>
    set l' := reflectRecords f x (c - f v) l with hl'
    clear_value l'
    have hl := listMinHeight_nonpos (f := f) l
    -- If the cap on the tail is below its minimal height, the tail is unchanged and so is its
    -- reversal; otherwise the cap seen by the reversed tail is the one of the induction
    -- hypothesis.
    have htail : ∀ k : 𝕜, (listMinHeight f l ≤ c - f v → k = listMinHeight f l - f l'.sum) →
        (c - f v < listMinHeight f l → k ≤ listMinHeight f l - f l.sum) →
        normalize 𝕜 (reflectRecords f x k (l'.map Neg.neg).reverse) =
          normalize 𝕜 (l.map Neg.neg).reverse := by
      intro k hk₁ hk₂
      by_cases hc : listMinHeight f l ≤ c - f v
      · rw [hk₁ hc, hl']
        exact ih (c - f v)
      · rw [not_le] at hc
        rw [hl', reflectRecords_of_le_listMinHeight hc.le, reflectRecords_of_le_listMinHeight
          (by rw [listMinHeight_reverse_map_neg]; exact hk₂ hc)]
    rw [List.map_cons, List.reverse_cons]
    by_cases hr : 0 < min (f v + listMinHeight f l) c
    · -- The first segment is cut at height `r` and its initial piece is reflected.
      set r := min (f v + listMinHeight f l) c with hr_def
      have hrc : r ≤ c := min_le_right _ _
      have hrl : r ≤ f v + listMinHeight f l := min_le_left _ _
      have hrv : r ≤ f v := by linarith
      obtain ⟨hs, hb⟩ := apply_reflect_cut hx (hr.trans_le hrv).ne' r
      have hm : listMinHeight f (v :: l) = 0 := by
        rw [listMinHeight_cons]
        exact min_eq_left (by linarith)
      have hPm : listMinHeight f
          ([preReflection x f ((r / f v) • v), (1 - r / f v) • v].map Neg.neg).reverse =
            r - f v := by
        rw [listMinHeight_reverse_map_neg]
        simp only [listMinHeight_cons, listMinHeight_nil, List.sum_cons, List.sum_nil, map_add,
          hs, hb, add_zero]
        rw [min_eq_left (by linarith : (0 : 𝕜) ≤ f v - r), add_zero,
          min_eq_right (by linarith : -r ≤ 0)]
        ring
      have hsum : f (preReflection x f ((r / f v) • v) :: (1 - r / f v) • v :: l').sum =
          f v - 2 * r + f l'.sum := by
        simp only [List.sum_cons, map_add, hs, hb]
        ring
      rw [reflectRecords_cons_of_pos hr, ← hl', hm, hsum]
      refine normalize_reflectRecords_reverse_append
        (P := [preReflection x f ((r / f v) • v), (1 - r / f v) • v]) ?_ ?_
      · rw [hPm, min_eq_right (by linarith)]
        refine htail _ (fun hc ↦ ?_) (fun hc ↦ ?_)
        · have : r = f v + listMinHeight f l := min_eq_left (by linarith)
          linarith
        · rw [hl', reflectRecords_of_le_listMinHeight hc.le]
          linarith
      · rw [show 0 - (f v - 2 * r + f l'.sum) + f l'.sum = 2 * r - f v by ring]
        exact normalize_reflectRecords_reverse_cut hx hr hrv
    · -- The first segment is kept.
      rw [not_lt] at hr
      have hPm : listMinHeight f ([v].map Neg.neg).reverse = min 0 (f v) - f v := by
        rw [listMinHeight_reverse_map_neg]
        simp
      rw [reflectRecords_cons_of_nonpos hr, ← hl', List.sum_cons, map_add, listMinHeight_cons]
      refine normalize_reflectRecords_reverse_append (P := [v]) ?_ ?_
      · rw [hPm]
        refine htail _ (fun hc ↦ ?_) (fun hc ↦ ?_)
        · -- Here the cap on the tail is at least its minimal height, so the first segment ends
          -- at a nonpositive height.
          have hneg : f v + listMinHeight f l ≤ 0 := by
            by_contra hpos
            rw [not_le] at hpos
            rcases min_le_iff.1 hr with h | h <;> linarith
          rw [min_eq_right hneg]
          simp only [min_def]
          split_ifs <;> linarith
        · rw [hl', reflectRecords_of_le_listMinHeight hc.le]
          exact (min_le_left _ _).trans
            (by linarith [min_le_right (0 : 𝕜) (f v + listMinHeight f l)])
      · simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
          List.nil_append]
        rw [reflectRecords_of_le_listMinHeight]
        rw [listMinHeight_cons, listMinHeight_nil, add_zero, map_neg]
        exact le_min (by linarith [min_le_right (0 : 𝕜) (f v + listMinHeight f l)])
          (by linarith [min_le_left (0 : 𝕜) (f v + listMinHeight f l)])

/-! ### The root operators are partial inverses -/

/-- If lowering `p` gives `q`, then raising `q` gives back `p`. -/
private theorem raise_eq_some_of_lower_eq_some (hx : f x = 2) {p q : PLPath 𝕜 V}
    (h : lower f x p = some q) : raise f x q = some p := by
  rw [← ofSegments_segments p, lower_ofSegments] at h
  obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.1 h
  set l := p.segments
  have hsum := sum_of_listLower_eq_some hl'
  rw [listLower_def] at hl'
  split_ifs at hl' with hdef
  obtain rfl := Option.some.inj hl'
  have hinv := normalize_reflectRecords_reverse_reflectRecords hx (listMinHeight f l + 1) l
  set l' := reflectRecords f x (listMinHeight f l + 1) l
  clear_value l'
  set k := listMinHeight f l - f l'.sum with hk
  have hl : listMinHeight f l ≤ 0 := listMinHeight_nonpos l
  -- Compare endpoints to find the minimal height of the reversed lowered path.
  have hmin : listMinHeight f (l'.map Neg.neg).reverse = k - 1 := by
    have hends : f (reflectRecords f x k (l'.map Neg.neg).reverse).sum =
        f (l.map Neg.neg).reverse.sum := by
      rw [← sum_normalize (𝕜 := 𝕜), hinv, sum_normalize]
    rw [sum_reflectRecords, map_sub, map_smul, smul_eq_mul, hx, ← List.sum_neg_reverse,
      ← List.sum_neg_reverse, map_neg, map_neg, hsum, map_sub, hx,
      min_eq_right (by rw [hk, hsum, map_sub, hx]; linarith)] at hends
    rcases le_total k (listMinHeight f (l'.map Neg.neg).reverse) with h' | h'
    · rw [min_eq_right h'] at hends
      linarith
    · rw [min_eq_left h'] at hends
      linarith
  have hdef' : 1 ≤ f (l'.map Neg.neg).reverse.sum - listMinHeight f (l'.map Neg.neg).reverse := by
    rw [hmin, ← List.sum_neg_reverse, map_neg, hk]
    linarith
  rw [raise_def, reverse_ofSegments, lower_ofSegments, listLower_def, ite_eq_left hdef', hmin,
    sub_add_cancel, Option.map_some, Option.map_some]
  have hp : ofSegments 𝕜 (reflectRecords f x k (l'.map Neg.neg).reverse) = p.reverse := by
    rw [← ofSegments_segments p, reverse_ofSegments]
    exact PLPath.ext (by rw [segments_ofSegments, segments_ofSegments, hinv])
  rw [hp, reverse_reverse]

/-- Littelmann's root operators are partial inverses: lowering `p` gives `q` exactly when raising
`q` gives `p`. -/
theorem lower_eq_some_iff (hx : f x = 2) {p q : PLPath 𝕜 V} :
    lower f x p = some q ↔ raise f x q = some p := by
  refine ⟨raise_eq_some_of_lower_eq_some hx, fun h ↦ ?_⟩
  rw [raise_def, Option.map_eq_some_iff] at h
  obtain ⟨r, hr, rfl⟩ := h
  rw [← reverse_reverse r] at hr
  have := raise_eq_some_of_lower_eq_some hx hr
  rw [raise_reverse, Option.map_eq_some_iff] at this
  obtain ⟨s, hs, hsr⟩ := this
  rwa [← reverse_involutive.injective hsr]

/-- Littelmann's root operators are partial inverses: raising `p` gives `q` exactly when lowering
`q` gives `p`. -/
theorem raise_eq_some_iff (hx : f x = 2) {p q : PLPath 𝕜 V} :
    raise f x p = some q ↔ lower f x q = some p :=
  (lower_eq_some_iff hx).symm

end PLPath

end TauCeti
