/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Reflection
public import TauCeti.RepresentationTheory.LSPath.PLPath
import Mathlib.Algebra.Order.Group.MinMax

/-!
# Running heights and root operators on piecewise-linear paths

Fix a vector `x : V` and a linear form `f : V → 𝕜`; in Littelmann's path model `x` is a simple
root `α` and `f` the pairing `⟨-, α^∨⟩` with its coroot, so that `f x = 2` and
`Module.preReflection x f` is the simple reflection `s_α`. The *running height* of a path `π`
is `t ↦ f (π t)`. For a path presented by a segment list `[v₁, …, vₙ]` the height is affine on
each segment, so its minimum `h` is attained at a vertex, that is at a partial sum
`v₁ + ⋯ + vₖ`; `TauCeti.PLPath.minHeight` is this minimum. It is independent of the
presentation. On Littelmann's path crystals the string lengths are `ε = -h` and
`φ = f (π 1) - h`.

Littelmann's *lowering operator* `f_α` is defined when `f (π 1) - h ≥ 1`. Let `t₀` be the **last**
time at which the height equals `h`, and `t₁` the **first** time from which on the height is at
least `h + 1`. Subdivide the piece of `π` from `t₀` to `t₁` into pieces of two kinds: those along
which the height increases and stays at most every later height, and equal-height excursions,
along which the height starts and ends at the same value and stays at least that value. Then
`f_α π` reflects the pieces of the first kind by `s_α`, keeps the excursions, and translates the
rest of `π` after `t₁` by `-α`. Equivalently, with `m t` the minimum of the height on `[t, 1]`,
`f_α π t = π t - min 1 (m t - h) • α`. In terms of segments, each segment is cut at most once,
and its reflected part is the initial piece along which the height stays at most both `h + 1` and
every later height. The *raising operator* `e_α` is conjugate to
`f_α` by the reversal `π ↦ π^∨` of paths; it is defined when `h ≤ -1`. With `t₁` the **first**
time at which the height equals `h` and `t₀` the **last** time up to which the height is at least
`h + 1`, it reflects the pieces between `t₀` and `t₁` along which the height decreases and stays
at most every earlier height, keeps the equal-height excursions, and translates the rest of `π`
after `t₁` by `α`.

The operators are defined on segment lists (`TauCeti.PLPath.reflectRecords`,
`TauCeti.PLPath.listLower`) and then on `TauCeti.PLPath`, using its reduced presentation. The
main result of this file is that the operators do not depend on the chosen presentation: the
elementary moves (subdividing a segment, inserting a stationary segment) commute with them up to
the same moves. The weight changes by `-α` under `f_α` and by `α` under `e_α`.

This file works with the ambient operators on all paths. That `e_α` and `f_α` are partial
inverses is proved in `TauCeti.RepresentationTheory.LSPath.PartialInverse`; the integral
string-length identities of Littelmann's path crystals are not proved here.

## Main definitions

* `TauCeti.PLPath.minHeight`: the minimum of the running height `t ↦ f (π t)`.
* `TauCeti.PLPath.lower`, `TauCeti.PLPath.raise`: Littelmann's root operators `f_α` and `e_α`,
  with `none` standing for `0`.

## Main results

* `TauCeti.PLPath.exists_listMinHeight_eq`, `TauCeti.PLPath.listMinHeight_le_apply_sum_take`:
  the minimal height of a presentation is the minimum of the heights of its vertices.
* `TauCeti.PLPath.minHeight_ofSegments`, `TauCeti.PLPath.minHeight_mul`,
  `TauCeti.PLPath.minHeight_reverse`: the minimal height is independent of the presentation, and
  its behaviour under concatenation and reversal.
* `TauCeti.PLPath.reflectRecords_append`: capped reflection `TauCeti.PLPath.reflectRecords` of a
  concatenation.
* `TauCeti.PLPath.reflectRecords_of_le_listMinHeight`: capped reflection is the identity when
  the cap is at most the minimal height.
* `TauCeti.PLPath.lower_ofSegments`: the lowering operator may be computed on any presentation.
* `TauCeti.PLPath.lower_eq_none_iff`, `TauCeti.PLPath.raise_eq_none_iff`: `f_α π = 0` exactly when
  `f (π 1) - h < 1`, and `e_α π = 0` exactly when `-1 < h`.
* `TauCeti.PLPath.endpoint_of_lower_eq_some`, `TauCeti.PLPath.endpoint_of_raise_eq_some`: the
  root operators change the endpoint by `∓ α`.
* `TauCeti.PLPath.lower_straight`: lowering a straight path `t ↦ t • v` with `f v ≥ 1`.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §1.
-/

public section

namespace TauCeti

namespace PLPath

open Module Relation

variable {𝕜 : Type*} {V : Type*}

/-! ### The minimal height of a segment list -/

section ListMinHeight

variable [Semiring 𝕜] [LinearOrder 𝕜] [AddCommMonoid V] [Module 𝕜 V]

variable (f : Dual 𝕜 V)

/-- The running-height recursion for a segment list. When addition preserves the scalar order,
this is the minimum of `f` over the vertices `0, v₁, v₁ + v₂, …, v₁ + ⋯ + vₙ`. For a
piecewise-linear path over an ordered field, the minimum of its affine height on each segment
is attained at a vertex. -/
def listMinHeight : List V → 𝕜
  | [] => 0
  | v :: l => min 0 (f v + listMinHeight l)

variable {f} {v w : V} {l l₁ l₂ : List V}

@[simp]
theorem listMinHeight_nil : listMinHeight f ([] : List V) = 0 :=
  (rfl)

@[simp]
theorem listMinHeight_cons (v : V) (l : List V) :
    listMinHeight f (v :: l) = min 0 (f v + listMinHeight f l) :=
  (rfl)

theorem listMinHeight_nonpos (l : List V) : listMinHeight f l ≤ 0 := by
  cases l <;> simp

/-- The minimal height is the height of some vertex. -/
theorem exists_listMinHeight_eq (l : List V) : ∃ n, listMinHeight f l = f (l.take n).sum := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons v l ih =>
    obtain ⟨n, hn⟩ := ih
    rcases le_total 0 (f v + listMinHeight f l) with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨n + 1, by rw [listMinHeight_cons, min_eq_right h, hn, List.take_succ_cons,
        List.sum_cons, map_add]⟩

variable [IsOrderedAddMonoid 𝕜]

/-- The minimal height is at most the height of each vertex. -/
theorem listMinHeight_le_apply_sum_take (l : List V) (n : ℕ) :
    listMinHeight f l ≤ f (l.take n).sum := by
  induction l generalizing n with
  | nil => simp
  | cons v l ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [listMinHeight_cons, List.take_succ_cons, List.sum_cons, map_add]
      exact min_le_of_right_le (add_le_add le_rfl (ih n))

theorem listMinHeight_le_apply_sum (l : List V) : listMinHeight f l ≤ f l.sum := by
  simpa using listMinHeight_le_apply_sum_take (f := f) l l.length

@[simp]
theorem listMinHeight_append (l₁ l₂ : List V) :
    listMinHeight f (l₁ ++ l₂) = min (listMinHeight f l₁) (f l₁.sum + listMinHeight f l₂) := by
  induction l₁ with
  | nil => simpa using (min_eq_right (listMinHeight_nonpos (f := f) l₂)).symm
  | cons v l ih => simp [ih, ← min_add_add_left, min_assoc, add_assoc]

end ListMinHeight

section ListMinHeightReverse

variable [Ring 𝕜] [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
  [AddCommGroup V] [Module 𝕜 V] {f : Dual 𝕜 V}

/-- Reversing and negating the segments shifts their minimal height by the negative final
height. -/
theorem listMinHeight_reverse_map_neg (l : List V) :
    listMinHeight f (l.map Neg.neg).reverse = listMinHeight f l - f l.sum := by
  induction l with
  | nil => simp
  | cons v l ih =>
    have hl : listMinHeight f l - f l.sum ≤ -f l.sum := by
      simpa using sub_le_sub_right (listMinHeight_nonpos (f := f) l) (f l.sum)
    simp only [List.map_cons, List.reverse_cons, listMinHeight_append, ih, listMinHeight_cons,
      listMinHeight_nil, map_neg, add_zero, ← List.sum_neg_reverse, List.sum_cons, map_add]
    -- Translate the minimum for the final reversed segment by the tail's final height.
    have hshift : -f l.sum + min 0 (-f v) = min (-f l.sum) (-(f v + f l.sum)) := by
      rw [← min_add_add_left, add_zero]
      congr 1
      abel
    calc
      min (listMinHeight f l - f l.sum) (-f l.sum + min 0 (-f v)) =
          min (min (listMinHeight f l - f l.sum) (-f l.sum)) (-(f v + f l.sum)) := by
        rw [hshift, min_assoc]
      -- The tail minimum is nonpositive, so its shifted value lies below this endpoint.
      _ = min (listMinHeight f l - f l.sum) (-(f v + f l.sum)) := by
        rw [min_eq_left hl]
      _ = min (-(f v + f l.sum)) (listMinHeight f l - f l.sum) := min_comm _ _
      -- Translate both candidates back by the total height of the original list.
      _ = min 0 (f v + listMinHeight f l) - (f v + f l.sum) := by
        rw [← min_sub_sub_right]
        congr 1 <;> abel

end ListMinHeightReverse

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-! ### The minimal height of a path -/

section MinHeight

variable {f : Dual 𝕜 V} {l l₁ l₂ : List V}

theorem listMinHeight_consMerge (v : V) (l : List V) :
    listMinHeight f (consMerge 𝕜 v l) = listMinHeight f (v :: l) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simpa using (min_eq_right (listMinHeight_nonpos (f := f) l)).symm
  cases l with
  | nil => simp [consMerge_nil_of_ne_zero hv]
  | cons w l =>
    by_cases hvw : SameRay 𝕜 v w
    · obtain ⟨μ, hμ, rfl⟩ := hvw.exists_nonneg_left hv
      have hl := listMinHeight_nonpos (f := f) l
      rw [consMerge_cons_of_sameRay hvw]
      simp only [listMinHeight_cons, map_add, map_smul, smul_eq_mul]
      rcases le_total 0 (f v) with h | h
      · rw [← min_add_add_left, add_zero, ← min_assoc, min_eq_left h, add_assoc]
      · have : μ * f v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hμ h
        rw [← min_add_add_left, add_zero, min_eq_right (a := f v) (by linarith), add_assoc]
    · rw [consMerge_cons_of_not_sameRay hvw]

@[simp]
theorem listMinHeight_normalize (l : List V) :
    listMinHeight f (normalize 𝕜 l) = listMinHeight f l := by
  induction l with
  | nil => simp
  | cons v l ih => rw [normalize_cons, listMinHeight_consMerge, listMinHeight_cons, ih,
      listMinHeight_cons]

/-- The minimal height is invariant under the elementary moves. -/
theorem Move.listMinHeight_eq (h : Move 𝕜 l₁ l₂) : listMinHeight f l₁ = listMinHeight f l₂ := by
  rw [← listMinHeight_normalize, h.normalize_eq, listMinHeight_normalize]

variable (f) in
/-- The minimal running height `min_t f (π t)` of a path. -/
def minHeight (p : PLPath 𝕜 V) : 𝕜 :=
  listMinHeight f p.segments

theorem minHeight_def (p : PLPath 𝕜 V) : p.minHeight f = listMinHeight f p.segments :=
  (rfl)

/-- The minimal height of a path may be computed on any presentation. -/
@[simp]
theorem minHeight_ofSegments (l : List V) : (ofSegments 𝕜 l).minHeight f = listMinHeight f l := by
  rw [minHeight_def, segments_ofSegments, listMinHeight_normalize]

@[simp]
theorem minHeight_one : (1 : PLPath 𝕜 V).minHeight f = 0 := by
  rw [minHeight_def, segments_one, listMinHeight_nil]

theorem minHeight_nonpos (p : PLPath 𝕜 V) : p.minHeight f ≤ 0 :=
  listMinHeight_nonpos _

theorem minHeight_le_apply_endpoint (p : PLPath 𝕜 V) : p.minHeight f ≤ f p.endpoint := by
  rw [minHeight_def, endpoint_def]
  exact listMinHeight_le_apply_sum _

@[simp]
theorem minHeight_mul (p q : PLPath 𝕜 V) :
    (p * q).minHeight f = min (p.minHeight f) (f p.endpoint + q.minHeight f) := by
  rw [← ofSegments_segments p, ← ofSegments_segments q, ← ofSegments_append]
  simp only [minHeight_ofSegments, endpoint_ofSegments, listMinHeight_append]

@[simp]
theorem minHeight_reverse (p : PLPath 𝕜 V) :
    p.reverse.minHeight f = p.minHeight f - f p.endpoint := by
  rw [minHeight_def, minHeight_def, segments_reverse, endpoint_def, listMinHeight_reverse_map_neg]

@[simp]
theorem minHeight_straight (v : V) : (straight 𝕜 v).minHeight f = min 0 (f v) := by
  simp [straight_def]

end MinHeight

/-! ### The lowering operator on segment lists -/

section ListLower

variable (f : Dual 𝕜 V) (x : V)

/-- `reflectRecords f x c l` reflects, by `Module.preReflection x f`, the pieces of the path
presented by `l` along which the running height (starting from `0`) increases, stays at most `c`,
and is at most every later height; it keeps the rest of the path, in particular every excursion
that returns to a height reached before. For a segment `v` followed by `l`, the height relative to
the start of `v` is at least `f v + listMinHeight f l` from the end of `v` on. When
`r = min (f v + listMinHeight f l) c` is positive, `v` is cut at height `r` into the reflected
initial piece `(r / f v) • v` and the kept piece `(1 - r / f v) • v`. -/
def reflectRecords (c : 𝕜) : List V → List V
  | [] => []
  | v :: l =>
    if 0 < min (f v + listMinHeight f l) c then
      preReflection x f ((min (f v + listMinHeight f l) c / f v) • v) ::
        (1 - min (f v + listMinHeight f l) c / f v) • v :: reflectRecords (c - f v) l
    else v :: reflectRecords (c - f v) l

/-- Littelmann's lowering operator on segment lists. With `h = listMinHeight f l`, it is defined
when the final height is at least `h + 1`, and then reflects the pieces of the path along which the
height increases from `h` to `h + 1` while staying at most every later height
(`TauCeti.PLPath.reflectRecords`). -/
def listLower (l : List V) : Option (List V) :=
  if 1 ≤ f l.sum - listMinHeight f l then some (reflectRecords f x (listMinHeight f l + 1) l)
  else none

variable {f x} {v w : V} {l l₁ l₂ : List V} {c : 𝕜}

omit [IsStrictOrderedRing 𝕜] in
@[simp]
theorem reflectRecords_nil (c : 𝕜) : reflectRecords f x c ([] : List V) = [] :=
  (rfl)

omit [IsStrictOrderedRing 𝕜] in
theorem reflectRecords_cons_of_pos (h : 0 < min (f v + listMinHeight f l) c) :
    reflectRecords f x c (v :: l) =
      preReflection x f ((min (f v + listMinHeight f l) c / f v) • v) ::
        (1 - min (f v + listMinHeight f l) c / f v) • v :: reflectRecords f x (c - f v) l :=
  ite_eq_left h

omit [IsStrictOrderedRing 𝕜] in
theorem reflectRecords_cons_of_nonpos (h : min (f v + listMinHeight f l) c ≤ 0) :
    reflectRecords f x c (v :: l) = v :: reflectRecords f x (c - f v) l :=
  ite_eq_right h.not_gt

omit [IsStrictOrderedRing 𝕜] in
theorem listLower_def (l : List V) :
    listLower f x l = if 1 ≤ f l.sum - listMinHeight f l then
      some (reflectRecords f x (listMinHeight f l + 1) l) else none :=
  (rfl)

/-- Reflecting the records up to height `c` subtracts from the endpoint `x` times the increase,
along the path, of the minimum of `c` and the later minimal height. -/
theorem sum_reflectRecords (c : 𝕜) (l : List V) :
    (reflectRecords f x c l).sum = l.sum - (min (f l.sum) c - min (listMinHeight f l) c) • x := by
  induction l generalizing c with
  | nil => simp
  | cons v l ih =>
    have hl := listMinHeight_nonpos (f := f) l
    have key : min (f v + f l.sum) c - min (min 0 (f v + listMinHeight f l)) c =
        max 0 (min (f v + listMinHeight f l) c) +
          (min (f l.sum) (c - f v) - min (listMinHeight f l) (c - f v)) := by
      simp only [min_def, max_def]
      split_ifs <;> linarith
    rw [listMinHeight_cons, List.sum_cons, map_add, key]
    by_cases h : 0 < min (f v + listMinHeight f l) c
    · have hfv : f v ≠ 0 := (h.trans_le ((min_le_left _ _).trans (by linarith))).ne'
      have hcv : f ((min (f v + listMinHeight f l) c / f v) • v) =
          min (f v + listMinHeight f l) c := by
        rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfv]
      rw [reflectRecords_cons_of_pos h, max_eq_right h.le]
      simp only [List.sum_cons, ih, preReflection_apply, hcv]
      module
    · rw [reflectRecords_cons_of_nonpos (not_lt.1 h), max_eq_left (not_lt.1 h)]
      simp only [List.sum_cons, ih]
      module

omit [IsStrictOrderedRing 𝕜] in
@[simp]
theorem listLower_eq_none_iff : listLower f x l = none ↔ f l.sum - listMinHeight f l < 1 := by
  rw [listLower_def]
  split_ifs with h <;> simpa using h

theorem sum_of_listLower_eq_some (h : listLower f x l₁ = some l₂) : l₂.sum = l₁.sum - x := by
  rw [listLower_def] at h
  split_ifs at h with h₁
  rw [← Option.some.inj h, sum_reflectRecords, min_eq_right (by linarith),
    min_eq_left (by linarith), add_sub_cancel_left, one_smul]

/-- Reflecting the records of a concatenation `l₁ ++ l₂` up to the cap `c`: on `l₁`, the later
heights in `l₂` act as a further cap. -/
theorem reflectRecords_append (c : 𝕜) (l₁ l₂ : List V) :
    reflectRecords f x c (l₁ ++ l₂) =
      reflectRecords f x (min c (f l₁.sum + listMinHeight f l₂)) l₁ ++
        reflectRecords f x (c - f l₁.sum) l₂ := by
  induction l₁ generalizing c with
  | nil => simp
  | cons v l ih =>
    have key : min (f v + listMinHeight f (l ++ l₂)) c =
        min (f v + listMinHeight f l) (min c (f (v :: l).sum + listMinHeight f l₂)) := by
      rw [listMinHeight_append, List.sum_cons, map_add, ← min_add_add_left, add_assoc]
      ac_rfl
    have hcap : min (c - f v) (f l.sum + listMinHeight f l₂) =
        min c (f (v :: l).sum + listMinHeight f l₂) - f v := by
      rw [← min_sub_sub_right, List.sum_cons, map_add]
      congr 1
      abel
    have hrest : c - f v - f l.sum = c - f (v :: l).sum := by
      rw [List.sum_cons, map_add, sub_sub]
    rw [List.cons_append]
    by_cases h : 0 < min (f v + listMinHeight f (l ++ l₂)) c
    · rw [reflectRecords_cons_of_pos h, reflectRecords_cons_of_pos (key ▸ h), key, ih, hcap,
        hrest, List.cons_append, List.cons_append]
    · rw [not_lt] at h
      rw [reflectRecords_cons_of_nonpos h, reflectRecords_cons_of_nonpos (key ▸ h), ih, hcap,
        hrest, List.cons_append]

/-- Reflecting the records up to a cap that is at most the minimal height does nothing. -/
@[simp]
theorem reflectRecords_of_le_listMinHeight (h : c ≤ listMinHeight f l) :
    reflectRecords f x c l = l := by
  induction l generalizing c with
  | nil => exact reflectRecords_nil c
  | cons v l ih =>
    rw [listMinHeight_cons] at h
    rw [reflectRecords_cons_of_nonpos (min_le_of_right_le (h.trans (min_le_left _ _))),
      ih (by linarith [min_le_right 0 (f v + listMinHeight f l)])]

/-! ### Independence of the presentation -/

omit [IsStrictOrderedRing 𝕜] in
theorem reflectRecords_zero_cons (c : 𝕜) (l : List V) :
    reflectRecords f x c (0 :: l) = 0 :: reflectRecords f x c l := by
  rw [reflectRecords_cons_of_nonpos (min_le_of_left_le (by simpa using listMinHeight_nonpos l)),
    map_zero, sub_zero]

/-- Merging `v` and `μ • v` when the first segment is reflected entirely and the second one in
part. -/
private theorem normalize_reflectRecords_cons_smul_of_pos {μ : 𝕜} (hfv : 0 < f v) (hμ : 0 < μ)
    (h₂ : 0 < min (μ * f v + listMinHeight f l) (c - f v)) :
    normalize 𝕜 (reflectRecords f x c (v :: μ • v :: l)) =
      normalize 𝕜 (reflectRecords f x c ((1 + μ) • v :: l)) := by
  have hfμ : f (μ • v) = μ * f v := by simp
  have hf1μ : f ((1 + μ) • v) = (1 + μ) * f v := by simp
  have hl := listMinHeight_nonpos (f := f) l
  set r := min (μ * f v + listMinHeight f l) (c - f v) with hr₂
  have e₁ : min (f v + min 0 (μ * f v + listMinHeight f l)) c = f v := by
    have := min_le_left (μ * f v + listMinHeight f l) (c - f v)
    have := min_le_right (μ * f v + listMinHeight f l) (c - f v)
    rw [min_eq_left (by linarith : (0 : 𝕜) ≤ μ * f v + listMinHeight f l), add_zero,
      min_eq_left (by linarith)]
  have e' : min ((1 + μ) * f v + listMinHeight f l) c = f v + r := by
    rw [hr₂, ← min_add_add_left]
    congr 1 <;> ring
  have h₁ : 0 < min (f v + listMinHeight f (μ • v :: l)) c := by
    rwa [listMinHeight_cons, hfμ, e₁]
  have h' : 0 < min (f ((1 + μ) • v) + listMinHeight f l) c := by
    rw [hf1μ, e']; linarith
  rw [reflectRecords_cons_of_pos h₁, reflectRecords_cons_of_pos (by rwa [hfμ]),
    reflectRecords_cons_of_pos h', listMinHeight_cons, hfμ, hf1μ, e₁, e', ← hr₂,
    show c - f v - μ * f v = c - (1 + μ) * f v by ring, div_self hfv.ne', one_smul, sub_self,
    zero_smul]
  have hk : 0 ≤ r / f v := div_nonneg h₂.le hfv.le
  have h1μ : (1 + μ) ≠ 0 := (by linarith : (0 : 𝕜) < 1 + μ).ne'
  have hfr : (f v + r) / f v = 1 + r / f v := by rw [add_div, div_self hfv.ne']
  have hd₁ (a : 𝕜) : (a / (μ * f v)) • μ • v = (a / f v) • v := by
    rw [smul_smul, div_mul_eq_mul_div, mul_comm a, mul_div_mul_left _ _ hμ.ne']
  have hd₂ (a : 𝕜) : (a / ((1 + μ) * f v)) • (1 + μ) • v = (a / f v) • v := by
    rw [smul_smul, div_mul_eq_mul_div, mul_comm a, mul_div_mul_left _ _ h1μ]
  have e₃ : (1 - r / (μ * f v)) • μ • v = (μ - r / f v) • v := by
    rw [sub_smul, one_smul, hd₁, sub_smul]
  have e₅ : (1 - (f v + r) / ((1 + μ) * f v)) • (1 + μ) • v = (μ - r / f v) • v := by
    rw [sub_smul, one_smul, hd₂, hfr]; module
  have hm₁ := (Move.erase_zero (𝕜 := 𝕜) [preReflection x f v]
    (preReflection x f ((r / f v) • v) :: (μ - r / f v) • v ::
      reflectRecords f x (c - (1 + μ) * f v) l)).normalize_eq
  have hm₂ := (Move.merge [] ((μ - r / f v) • v :: reflectRecords f x (c - (1 + μ) * f v) l)
    (by rw [map_smul]; exact SameRay.sameRay_nonneg_smul_right _ hk :
      SameRay 𝕜 (preReflection x f v) (preReflection x f ((r / f v) • v)))).normalize_eq
  simp only [List.cons_append, List.nil_append] at hm₁ hm₂
  rw [hd₁, e₃, hd₂, hfr, e₅, add_smul, one_smul,
    map_add, hm₁, hm₂]

/-- Merging `v` and `μ • v` when the first segment is reflected in part and the second one is
kept. -/
private theorem normalize_reflectRecords_cons_smul_of_nonpos {μ : 𝕜} (hfv : 0 < f v)
    (hμ : 0 ≤ μ) (h₁ : 0 < min (f v + listMinHeight f (μ • v :: l)) c)
    (h₂ : min (μ * f v + listMinHeight f l) (c - f v) ≤ 0) :
    normalize 𝕜 (reflectRecords f x c (v :: μ • v :: l)) =
      normalize 𝕜 (reflectRecords f x c ((1 + μ) • v :: l)) := by
  have hfμ : f (μ • v) = μ * f v := by simp
  have hf1μ : f ((1 + μ) • v) = (1 + μ) * f v := by simp
  have hl := listMinHeight_nonpos (f := f) l
  have e : min (f v + min 0 (μ * f v + listMinHeight f l)) c =
      min ((1 + μ) * f v + listMinHeight f l) c := by
    simp only [min_def] at h₂ ⊢
    split_ifs at h₂ ⊢ <;> linarith
  have h' : 0 < min (f ((1 + μ) • v) + listMinHeight f l) c := by
    rw [hf1μ, ← e]; rwa [listMinHeight_cons, hfμ] at h₁
  set r := min (f v + min 0 (μ * f v + listMinHeight f l)) c with hr₁
  have hr : r ≤ f v := (min_le_left _ _).trans (by simp)
  rw [reflectRecords_cons_of_pos h₁, reflectRecords_cons_of_nonpos (by rwa [hfμ]),
    reflectRecords_cons_of_pos h', listMinHeight_cons, hfμ, hf1μ, ← e, ← hr₁,
    show c - f v - μ * f v = c - (1 + μ) * f v by ring]
  have hk : 0 ≤ 1 - r / f v := sub_nonneg.2 ((div_le_one hfv).2 hr)
  have h1μ : (1 + μ) ≠ 0 := (by linarith : (0 : 𝕜) < 1 + μ).ne'
  have hd (a : 𝕜) : (a / ((1 + μ) * f v)) • (1 + μ) • v = (a / f v) • v := by
    rw [smul_smul, div_mul_eq_mul_div, mul_comm a, mul_div_mul_left _ _ h1μ]
  have e₂ : (1 - r / ((1 + μ) * f v)) • (1 + μ) • v = (1 - r / f v) • v + μ • v := by
    rw [sub_smul, one_smul, hd]; module
  have hm := (Move.merge [preReflection x f ((r / f v) • v)]
    (reflectRecords f x (c - (1 + μ) * f v) l)
    ((SameRay.sameRay_nonneg_smul_left v hk).nonneg_smul_right hμ :
      SameRay 𝕜 ((1 - r / f v) • v) (μ • v))).normalize_eq
  simp only [List.cons_append, List.nil_append] at hm
  rw [hm, hd, e₂]

/-- Reflecting the records commutes with merging the first two segments, up to elementary
moves. -/
private theorem normalize_reflectRecords_cons_cons (hvw : SameRay 𝕜 v w) (c : 𝕜) (l : List V) :
    normalize 𝕜 (reflectRecords f x c (v :: w :: l)) =
      normalize 𝕜 (reflectRecords f x c ((v + w) :: l)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [reflectRecords_zero_cons]
  obtain ⟨μ, hμ, rfl⟩ := hvw.exists_nonneg_left hv
  have hl := listMinHeight_nonpos (f := f) l
  have hvμ : v + μ • v = (1 + μ) • v := by module
  have hfμ : f (μ • v) = μ * f v := by simp
  rw [hvμ]
  by_cases h₁ : 0 < min (f v + listMinHeight f (μ • v :: l)) c
  · have h₁' := h₁
    rw [listMinHeight_cons, hfμ] at h₁'
    have hfv : 0 < f v := by
      by_contra! h
      have := min_le_left (f v + min 0 (μ * f v + listMinHeight f l)) c
      have := min_le_left 0 (μ * f v + listMinHeight f l)
      linarith
    by_cases h₂ : 0 < min (μ * f v + listMinHeight f l) (c - f v)
    · have hμ0 : 0 < μ := by
        rcases hμ.lt_or_eq with h | h
        · exact h
        · rw [← h, zero_mul, zero_add] at h₂
          linarith [min_le_left (listMinHeight f l) (c - f v)]
      exact normalize_reflectRecords_cons_smul_of_pos hfv hμ0 h₂
    · exact normalize_reflectRecords_cons_smul_of_nonpos hfv hμ h₁ (not_lt.1 h₂)
  · -- No part of the first two segments is reflected.
    rw [not_lt] at h₁
    have h₁' := h₁
    rw [listMinHeight_cons, hfμ] at h₁'
    have hf1μ : f ((1 + μ) • v) = (1 + μ) * f v := by simp
    -- `μ * f v` has the sign of `f v`, which is what the bound `h₁'` needs.
    obtain ⟨h₂, h'⟩ : min (μ * f v + listMinHeight f l) (c - f v) ≤ 0 ∧
        min ((1 + μ) * f v + listMinHeight f l) c ≤ 0 := by
      have hs : 0 < f v ∧ 0 ≤ μ * f v ∨ f v ≤ 0 ∧ μ * f v ≤ 0 :=
        (lt_or_ge 0 (f v)).imp (fun h ↦ ⟨h, mul_nonneg hμ h.le⟩)
        (fun h ↦ ⟨h, mul_nonpos_of_nonneg_of_nonpos hμ h⟩)
      simp only [min_def] at h₁' ⊢
      rcases hs with ⟨_, _⟩ | ⟨_, _⟩ <;> split_ifs at h₁' ⊢ <;> constructor <;> linarith
    rw [reflectRecords_cons_of_nonpos h₁, reflectRecords_cons_of_nonpos (by rwa [hfμ]),
      reflectRecords_cons_of_nonpos (by rwa [hf1μ]), hfμ, hf1μ,
      show c - f v - μ * f v = c - (1 + μ) * f v by ring]
    have hm := (Move.merge [] (reflectRecords f x (c - (1 + μ) * f v) l)
      (SameRay.sameRay_nonneg_smul_right (R := 𝕜) v hμ)).normalize_eq
    simp only [List.nil_append, hvμ] at hm
    exact hm

/-- Reflecting the records commutes with the elementary moves, up to elementary moves. -/
theorem Move.normalize_reflectRecords (h : Move 𝕜 l₁ l₂) (c : 𝕜) :
    normalize 𝕜 (reflectRecords f x c l₁) = normalize 𝕜 (reflectRecords f x c l₂) := by
  have hcons : ∀ (u : V) {m₁ m₂ : List V}, Move 𝕜 m₁ m₂ →
      (∀ c, normalize 𝕜 (reflectRecords f x c m₁) = normalize 𝕜 (reflectRecords f x c m₂)) →
      ∀ c, normalize 𝕜 (reflectRecords f x c (u :: m₁)) =
        normalize 𝕜 (reflectRecords f x c (u :: m₂)) := by
    intro u m₁ m₂ hm ih c
    have hmin := hm.listMinHeight_eq (f := f)
    by_cases hu : 0 < min (f u + listMinHeight f m₁) c
    · rw [reflectRecords_cons_of_pos hu]
      rw [hmin] at hu ⊢
      rw [reflectRecords_cons_of_pos hu, normalize_cons, normalize_cons, normalize_cons,
        normalize_cons, ih]
    · rw [not_lt] at hu
      rw [reflectRecords_cons_of_nonpos hu]
      rw [hmin] at hu
      rw [reflectRecords_cons_of_nonpos hu, normalize_cons, normalize_cons, ih]
  cases h with
  | merge m₁ m₂ hvw =>
    induction m₁ generalizing c with
    | nil => exact normalize_reflectRecords_cons_cons hvw c m₂
    | cons u m ih => exact hcons u (.merge m m₂ hvw) ih c
  | erase_zero m₁ m₂ =>
    induction m₁ generalizing c with
    | nil => simp [reflectRecords_zero_cons]
    | cons u m ih => exact hcons u (.erase_zero m m₂) ih c

/-- Lowering commutes with the elementary moves, up to elementary moves. -/
theorem Move.map_normalize_listLower (h : Move 𝕜 l₁ l₂) :
    (listLower f x l₁).map (normalize 𝕜) = (listLower f x l₂).map (normalize 𝕜) := by
  have hmin := h.listMinHeight_eq (f := f)
  have hsum : l₁.sum = l₂.sum := by rw [← sum_normalize (𝕜 := 𝕜), h.normalize_eq, sum_normalize]
  rw [listLower_def, listLower_def, hmin, hsum]
  split_ifs
  · simpa using h.normalize_reflectRecords _
  · rfl

/-- Lowering does not depend on the presentation: presentations of the same path have lowerings
presenting the same path. -/
theorem map_normalize_listLower_eq (h : normalize 𝕜 l₁ = normalize 𝕜 l₂) :
    (listLower f x l₁).map (normalize 𝕜) = (listLower f x l₂).map (normalize 𝕜) := by
  have hm := normalize_eq_normalize_iff.1 h
  clear h
  induction hm with
  | rel _ _ hm => exact hm.map_normalize_listLower
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end ListLower

/-! ### Root operators on paths -/

section RootOperator

variable (f : Dual 𝕜 V) (x : V)

/-- Littelmann's lowering operator `f_α` on paths, for the root `α = x` and the coroot pairing
`f = ⟨-, α^∨⟩`. Let `h` be the minimal height, `t₀` the last time at which the height equals `h`
and `t₁` the first time from which on the height is at least `h + 1`. Between `t₀` and `t₁`, the
pieces along which the height increases and stays at most every later height are reflected by
`Module.preReflection x f`, the equal-height excursions are kept, and the rest of the path after
`t₁` is translated by `-x`. It is `none` when `f (π 1) - h < 1`. -/
noncomputable def lower (p : PLPath 𝕜 V) : Option (PLPath 𝕜 V) :=
  (listLower f x p.segments).map (ofSegments 𝕜)

/-- Littelmann's raising operator `e_α` on paths, the conjugate of `TauCeti.PLPath.lower` by the
reversal of paths. Let `h` be the minimal height, `t₁` the first time at which the height equals
`h` and `t₀` the last time up to which the height is at least `h + 1`. Between `t₀` and `t₁`, the
pieces along which the height decreases and stays at most every earlier height are reflected by
`Module.preReflection x f`, the equal-height excursions are kept, and the rest of the path after
`t₁` is translated by `x`. It is `none` when `-1 < h`. -/
noncomputable def raise (p : PLPath 𝕜 V) : Option (PLPath 𝕜 V) :=
  (lower f x p.reverse).map reverse

variable {f x} {v : V} {p q : PLPath 𝕜 V}

/-- The lowering operator may be computed on any presentation of a path. -/
theorem lower_ofSegments (l : List V) :
    lower f x (ofSegments 𝕜 l) = (listLower f x l).map (ofSegments 𝕜) := by
  have hof : (ofSegments 𝕜 : List V → PLPath 𝕜 V) = ofSegments 𝕜 ∘ normalize 𝕜 :=
    funext fun m ↦ PLPath.ext (by
      rw [Function.comp_apply, segments_ofSegments, segments_ofSegments, normalize_normalize])
  rw [lower, segments_ofSegments, hof, ← Option.map_map, ← Option.map_map,
    map_normalize_listLower_eq (normalize_normalize l)]

theorem raise_def (p : PLPath 𝕜 V) : raise f x p = (lower f x p.reverse).map reverse :=
  (rfl)

@[simp]
theorem raise_reverse (p : PLPath 𝕜 V) : raise f x p.reverse = (lower f x p).map reverse := by
  rw [raise_def, reverse_reverse]

@[simp]
theorem lower_reverse (p : PLPath 𝕜 V) : lower f x p.reverse = (raise f x p).map reverse := by
  simp [raise_def, Option.map_map, reverse_involutive.comp_self]

/-- The lowering operator is defined exactly when the final height exceeds the minimal height by
at least `1`. -/
@[simp]
theorem lower_eq_none_iff : lower f x p = none ↔ f p.endpoint - p.minHeight f < 1 := by
  rw [lower, Option.map_eq_none_iff, listLower_eq_none_iff, endpoint_def, minHeight_def]

/-- The raising operator is defined exactly when the minimal height is at most `-1`. -/
@[simp]
theorem raise_eq_none_iff : raise f x p = none ↔ -1 < p.minHeight f := by
  rw [raise_def, Option.map_eq_none_iff, lower_eq_none_iff, minHeight_reverse, endpoint_reverse,
    map_neg]
  constructor <;> intro h <;> linarith

/-- Lowering subtracts `x` from the endpoint. -/
theorem endpoint_of_lower_eq_some (h : lower f x p = some q) : q.endpoint = p.endpoint - x := by
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [endpoint_ofSegments, sum_of_listLower_eq_some hl, endpoint_def]

/-- Raising adds `x` to the endpoint. -/
theorem endpoint_of_raise_eq_some (h : raise f x p = some q) : q.endpoint = p.endpoint + x := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [endpoint_reverse, endpoint_of_lower_eq_some hr, endpoint_reverse]
  abel

/-- Lowering the straight path `t ↦ t • v` with `f v ≥ 1` reflects its initial piece, up to the
time `1 / f v` at which the height reaches `1`. -/
theorem lower_straight (h : 1 ≤ f v) :
    lower f x (straight 𝕜 v) =
      some (straight 𝕜 (preReflection x f ((f v)⁻¹ • v)) * straight 𝕜 ((1 - (f v)⁻¹) • v)) := by
  have hm : listMinHeight f [v] = 0 := by
    rw [listMinHeight_cons, listMinHeight_nil, add_zero]
    exact min_eq_left (by linarith)
  have hr : min (f v + listMinHeight f []) (listMinHeight f [v] + 1) = 1 := by
    rw [hm, listMinHeight_nil, add_zero, zero_add, min_eq_right h]
  rw [straight_def, lower_ofSegments, listLower_def, ite_eq_left (by simpa [hm] using h),
    reflectRecords_cons_of_pos (by rw [hr]; exact one_pos), hr]
  simp [ofSegments_cons]

end RootOperator

end PLPath

end TauCeti
