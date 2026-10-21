/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Reflection
public import TauCeti.RepresentationTheory.LSPath.PLPath

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
time at which the height equals `h`, and `t₁` the **first** time after `t₀` at which it equals
`h + 1`. Then `f_α π` traverses `π` up to `t₀`, then the reflection by `s_α` of the piece of `π`
from `t₀` to `t₁`, and then the rest of `π`, translated by `-α`. In terms of segments the rest of
`π` is unchanged: only the piece between `t₀` and `t₁` is reflected, after cutting the segment in
which the height first reaches `h + 1` at the corresponding point. The *raising operator* `e_α`
is conjugate to `f_α` by the reversal `π ↦ π^∨` of paths; it is defined when `h ≤ -1`, and it
reflects the piece of `π` between the last time `t₀` before `t₁` at which the height equals
`h + 1` and the **first** time `t₁` at which the height equals `h`.

The operators are defined on segment lists (`TauCeti.PLPath.reflectUntil`,
`TauCeti.PLPath.listLower`) and then on `TauCeti.PLPath`, using its reduced presentation. The
main result of this file is that the operators do not depend on the chosen presentation: the
elementary moves (subdividing a segment, inserting a stationary segment) commute with them up to
the same moves. The weight changes by `-α` under `f_α` and by `α` under `e_α`.

This file works with the ambient operators on all paths. It does not prove that `e_α` and `f_α`
are partial inverses: that needs an integrality condition on the local minima of the height,
satisfied by Lakshmibai-Seshadri paths.

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
* `TauCeti.PLPath.lower_ofSegments`: the lowering operator may be computed on any presentation.
* `TauCeti.PLPath.lower_eq_none_iff`, `TauCeti.PLPath.raise_eq_none_iff`: `f_α π = 0` exactly when
  `f (π 1) - h < 1`, and `e_α π = 0` exactly when `-1 < h`.
* `TauCeti.PLPath.endpoint_of_lower_eq_some`, `TauCeti.PLPath.endpoint_of_raise_eq_some`: the
  root operators change the endpoint by `∓ α`.
* `TauCeti.PLPath.lower_straight`: lowering a straight path `t ↦ t • v` with `f v ≥ 1`.

## References

* P. Littelmann, *A Littlewood-Richardson rule for symmetrizable Kac-Moody algebras*, Invent.
  Math. 116 (1994), §1.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §1.
-/

public section

namespace TauCeti

namespace PLPath

open Module Relation

variable {𝕜 : Type*} {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-! ### The minimal height -/

section MinHeight

variable (f : Dual 𝕜 V)

/-- The minimal running height of the path presented by a segment list: the minimum of `f` over
the vertices `0, v₁, v₁ + v₂, …, v₁ + ⋯ + vₙ`, at which the minimum of the piecewise-affine
function `t ↦ f (π t)` is attained. -/
def listMinHeight : List V → 𝕜
  | [] => 0
  | v :: l => min 0 (f v + listMinHeight l)

variable {f} {v w : V} {l l₁ l₂ : List V}

omit [IsStrictOrderedRing 𝕜] in
@[simp]
theorem listMinHeight_nil : listMinHeight f ([] : List V) = 0 :=
  (rfl)

omit [IsStrictOrderedRing 𝕜] in
@[simp]
theorem listMinHeight_cons (v : V) (l : List V) :
    listMinHeight f (v :: l) = min 0 (f v + listMinHeight f l) :=
  (rfl)

omit [IsStrictOrderedRing 𝕜] in
theorem listMinHeight_nonpos (l : List V) : listMinHeight f l ≤ 0 := by
  cases l <;> simp

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
      exact min_le_of_right_le (by linarith [ih n])

omit [IsStrictOrderedRing 𝕜] in
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

theorem listMinHeight_le_apply_sum (l : List V) : listMinHeight f l ≤ f l.sum := by
  simpa using listMinHeight_le_apply_sum_take (f := f) l l.length

@[simp]
theorem listMinHeight_append (l₁ l₂ : List V) :
    listMinHeight f (l₁ ++ l₂) = min (listMinHeight f l₁) (f l₁.sum + listMinHeight f l₂) := by
  induction l₁ with
  | nil => simpa using (min_eq_right (listMinHeight_nonpos (f := f) l₂)).symm
  | cons v l ih => simp [ih, ← min_add_add_left, min_assoc, add_assoc]

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
      · have : 0 ≤ μ * f v := mul_nonneg hμ h
        rw [← min_add_add_left, add_zero, ← min_assoc, min_eq_left h, add_assoc]
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

theorem listMinHeight_reverse_map_neg (l : List V) :
    listMinHeight f (l.map Neg.neg).reverse = listMinHeight f l - f l.sum := by
  induction l with
  | nil => simp
  | cons v l ih =>
    have hl := listMinHeight_nonpos (f := f) l
    have hs : ((l.map Neg.neg).reverse).sum = -l.sum := (List.sum_neg_reverse l).symm
    simp only [List.map_cons, List.reverse_cons, listMinHeight_append, ih, listMinHeight_cons,
      listMinHeight_nil, map_neg, add_zero, hs, List.sum_cons, map_add, min_def]
    split_ifs <;> linarith

variable (f) in
/-- The minimal running height `min_t f (π t)` of a path. -/
def minHeight (p : PLPath 𝕜 V) : 𝕜 :=
  listMinHeight f p.segments

/-- The minimal height of a path may be computed on any presentation. -/
@[simp]
theorem minHeight_ofSegments (l : List V) : (ofSegments 𝕜 l).minHeight f = listMinHeight f l := by
  rw [minHeight, segments_ofSegments, listMinHeight_normalize]

@[simp]
theorem minHeight_one : (1 : PLPath 𝕜 V).minHeight f = 0 := by
  rw [minHeight, segments_one, listMinHeight_nil]

theorem minHeight_nonpos (p : PLPath 𝕜 V) : p.minHeight f ≤ 0 :=
  listMinHeight_nonpos _

theorem minHeight_le_apply_endpoint (p : PLPath 𝕜 V) : p.minHeight f ≤ f p.endpoint := by
  rw [minHeight, endpoint_def]
  exact listMinHeight_le_apply_sum _

@[simp]
theorem minHeight_mul (p q : PLPath 𝕜 V) :
    (p * q).minHeight f = min (p.minHeight f) (f p.endpoint + q.minHeight f) := by
  rw [← ofSegments_segments p, ← ofSegments_segments q, ← ofSegments_append]
  simp only [minHeight_ofSegments, endpoint_ofSegments, listMinHeight_append]

@[simp]
theorem minHeight_reverse (p : PLPath 𝕜 V) :
    p.reverse.minHeight f = p.minHeight f - f p.endpoint := by
  rw [minHeight, minHeight, segments_reverse, endpoint_def, listMinHeight_reverse_map_neg]

@[simp]
theorem minHeight_straight (v : V) : (straight 𝕜 v).minHeight f = min 0 (f v) := by
  simp [straight_def]

end MinHeight

/-! ### The lowering operator on segment lists -/

section ListLower

variable (f : Dual 𝕜 V) (x : V)

/-- `reflectUntil f x c l` reflects, by `Module.preReflection x f`, the part of the path
presented by `l` up to the first time its running height (starting from `0`) reaches `c`, and
keeps the rest. If the height first reaches `c` inside a segment `v`, that segment is cut into
`(c / f v) • v` and `(1 - c / f v) • v` first. This is meant for `0 < c`. -/
def reflectUntil (c : 𝕜) : List V → List V
  | [] => []
  | v :: l => if c ≤ f v then preReflection x f ((c / f v) • v) :: (1 - c / f v) • v :: l
      else preReflection x f v :: reflectUntil (c - f v) l

/-- Littelmann's lowering operator on segment lists. For `v :: l`, if the minimal height of the
path is also attained after its start, that is `f v + listMinHeight f l ≤ 0`, then the operator
keeps `v` and acts on `l`; otherwise the minimal height `0` is attained only at the start, and if
the final height is at least `1` the path is reflected up to the first time its height reaches
`1`. -/
def listLower : List V → Option (List V)
  | [] => none
  | v :: l => if f v + listMinHeight f l ≤ 0 then (listLower l).map (v :: ·)
      else if 1 ≤ f v + f l.sum then some (reflectUntil f x 1 (v :: l)) else none

variable {f x} {v w : V} {l l₁ l₂ : List V} {c : 𝕜}

omit [IsStrictOrderedRing 𝕜] in
theorem reflectUntil_cons_of_le (h : c ≤ f v) (l : List V) :
    reflectUntil f x c (v :: l) = preReflection x f ((c / f v) • v) :: (1 - c / f v) • v :: l :=
  ite_eq_left h

omit [IsStrictOrderedRing 𝕜] in
theorem reflectUntil_cons_of_lt (h : f v < c) (l : List V) :
    reflectUntil f x c (v :: l) = preReflection x f v :: reflectUntil f x (c - f v) l :=
  ite_eq_right h.not_ge

omit [IsStrictOrderedRing 𝕜] in
theorem listLower_cons (v : V) (l : List V) :
    listLower f x (v :: l) = if f v + listMinHeight f l ≤ 0 then (listLower f x l).map (v :: ·)
      else if 1 ≤ f v + f l.sum then some (reflectUntil f x 1 (v :: l)) else none :=
  (rfl)

/-- Reflecting up to height `c` subtracts `c • x` from the endpoint, provided the height reaches
`c`. -/
theorem sum_reflectUntil (hc : 0 < c) (h : c ≤ f l.sum) :
    (reflectUntil f x c l).sum = l.sum - c • x := by
  induction l generalizing c with
  | nil => simp at h; linarith
  | cons v l ih =>
    rcases le_or_gt c (f v) with hv | hv
    · have hfv : f v ≠ 0 := (hc.trans_le hv).ne'
      rw [reflectUntil_cons_of_le hv]
      have hcv : f ((c / f v) • v) = c := by rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hfv]
      simp only [List.sum_cons, preReflection_apply, hcv]
      module
    · rw [List.sum_cons, map_add] at h
      simp only [reflectUntil_cons_of_lt hv, List.sum_cons, ih (sub_pos.2 hv) (by linarith),
        preReflection_apply]
      module

theorem listLower_eq_none_iff : listLower f x l = none ↔ f l.sum - listMinHeight f l < 1 := by
  induction l with
  | nil => simp [listLower]
  | cons v l ih =>
    rw [listLower_cons]
    split_ifs with h₁ h₂
    · rw [Option.map_eq_none_iff, ih, listMinHeight_cons, min_eq_right h₁, List.sum_cons, map_add]
      constructor <;> intro h <;> linarith
    · simp only [false_iff, not_lt, listMinHeight_cons,
        min_eq_left (le_of_not_ge h₁), List.sum_cons, map_add, sub_zero]
      exact h₂
    · simp only [listMinHeight_cons, min_eq_left (le_of_not_ge h₁), List.sum_cons, map_add,
        sub_zero, true_iff]
      exact lt_of_not_ge h₂

theorem sum_of_listLower_eq_some (h : listLower f x l₁ = some l₂) : l₂.sum = l₁.sum - x := by
  induction l₁ generalizing l₂ with
  | nil => simp [listLower] at h
  | cons v l ih =>
    rw [listLower_cons] at h
    split_ifs at h with h₁ h₂
    · obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 h
      rw [List.sum_cons, ih hm, List.sum_cons, add_sub_assoc]
    · rw [← Option.some.inj h, sum_reflectUntil one_pos (by simpa using h₂), one_smul]

/-! ### Independence of the presentation -/

omit [IsStrictOrderedRing 𝕜] in
theorem reflectUntil_zero_cons (hc : 0 < c) (l : List V) :
    reflectUntil f x c (0 :: l) = 0 :: reflectUntil f x c l := by
  rw [reflectUntil_cons_of_lt (by simpa using hc), map_zero, map_zero, sub_zero]

/-- Reflecting up to a positive height commutes with merging the first two segments. -/
private theorem normalize_reflectUntil_cons_cons (hvw : SameRay 𝕜 v w) (hc : 0 < c) (l : List V) :
    normalize 𝕜 (reflectUntil f x c (v :: w :: l)) =
      normalize 𝕜 (reflectUntil f x c ((v + w) :: l)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [reflectUntil_zero_cons hc]
  obtain ⟨μ, hμ, rfl⟩ := hvw.exists_nonneg_left hv
  have hvμ : v + μ • v = (1 + μ) • v := by module
  have hfμ : f (μ • v) = μ * f v := by simp
  have hf1μ : f ((1 + μ) • v) = (1 + μ) * f v := by simp
  rw [hvμ]
  rcases le_or_gt c (f v) with h | h
  · -- The height reaches `c` inside the first segment.
    have hfv : 0 < f v := hc.trans_le h
    have h' : c ≤ f ((1 + μ) • v) := by rw [hf1μ]; nlinarith
    rw [reflectUntil_cons_of_le h, reflectUntil_cons_of_le h', hf1μ]
    have hr : 0 ≤ 1 - c / f v := sub_nonneg.2 ((div_le_one hfv).2 h)
    have hm := (Move.merge [preReflection x f ((c / f v) • v)] l
      ((SameRay.sameRay_nonneg_smul_left v hr).nonneg_smul_right hμ :
        SameRay 𝕜 ((1 - c / f v) • v) (μ • v))).normalize_eq
    simp only [List.cons_append, List.nil_append] at hm
    have h1μ : (1 + μ) ≠ 0 := (by linarith : (0 : 𝕜) < 1 + μ).ne'
    have e₁ : (c / ((1 + μ) * f v)) • (1 + μ) • v = (c / f v) • v := by
      rw [smul_smul]; congr 1; field_simp
    have e₂ : (1 - c / ((1 + μ) * f v)) • (1 + μ) • v = (1 - c / f v) • v + μ • v := by
      rw [smul_smul, ← add_smul]; congr 1; field_simp; ring
    rw [hm, e₁, e₂]
  rcases le_or_gt (c - f v) (f (μ • v)) with h₂ | h₂
  · -- The height reaches `c` inside the second segment.
    have hfv : 0 < f v := by
      by_contra! h₃
      rw [hfμ] at h₂
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hμ h₃]
    have hμ0 : 0 < μ := by rw [hfμ] at h₂; nlinarith
    have h' : c ≤ f ((1 + μ) • v) := by rw [hf1μ]; rw [hfμ] at h₂; linarith
    rw [reflectUntil_cons_of_lt h, reflectUntil_cons_of_le h₂, reflectUntil_cons_of_le h', hfμ,
      hf1μ]
    have hr : 0 ≤ (c - f v) / (μ * f v) := div_nonneg (by linarith) (mul_pos hμ0 hfv).le
    have hm := (Move.merge [] ((1 - (c - f v) / (μ * f v)) • μ • v :: l)
      (SameRay.sameRay_nonneg_smul_right (R := 𝕜) (preReflection x f v)
        (mul_nonneg hr hμ))).normalize_eq
    simp only [List.nil_append] at hm
    have h1μ : (1 + μ) ≠ 0 := (by linarith : (0 : 𝕜) < 1 + μ).ne'
    have hk : 1 + (c - f v) / (μ * f v) * μ = c / ((1 + μ) * f v) * (1 + μ) := by
      field_simp; ring
    have e₁ : preReflection x f v + ((c - f v) / (μ * f v) * μ) • preReflection x f v =
        preReflection x f ((c / ((1 + μ) * f v)) • (1 + μ) • v) := by
      rw [map_smul, map_smul, smul_smul, ← hk, add_smul, one_smul]
    have e₂ : (1 - (c - f v) / (μ * f v)) • μ • v = (1 - c / ((1 + μ) * f v)) • (1 + μ) • v := by
      rw [smul_smul, smul_smul]; congr 1; field_simp; ring
    rw [smul_smul, map_smul, hm, e₁, e₂]
  · -- The height does not reach `c` on the first two segments.
    have h' : f ((1 + μ) • v) < c := by rw [hf1μ]; rw [hfμ] at h₂; linarith
    rw [reflectUntil_cons_of_lt h, reflectUntil_cons_of_lt h₂, reflectUntil_cons_of_lt h']
    simp only [normalize_cons]
    rw [consMerge_consMerge (by rw [map_smul]; exact SameRay.sameRay_nonneg_smul_right _ hμ),
      ← map_add, hvμ, hfμ, hf1μ, sub_sub, show f v + μ * f v = (1 + μ) * f v by ring]

/-- Reflecting up to a positive height commutes with the elementary moves, up to elementary
moves. -/
theorem Move.normalize_reflectUntil (h : Move 𝕜 l₁ l₂) (hc : 0 < c) :
    normalize 𝕜 (reflectUntil f x c l₁) = normalize 𝕜 (reflectUntil f x c l₂) := by
  cases h with
  | merge m₁ m₂ hvw =>
    induction m₁ generalizing c with
    | nil => exact normalize_reflectUntil_cons_cons hvw hc m₂
    | cons u m ih =>
      simp only [List.cons_append]
      rcases le_or_gt c (f u) with hu | hu
      · rw [reflectUntil_cons_of_le hu, reflectUntil_cons_of_le hu, normalize_cons,
          normalize_cons, normalize_cons, normalize_cons, (Move.merge m m₂ hvw).normalize_eq]
      · rw [reflectUntil_cons_of_lt hu, reflectUntil_cons_of_lt hu, normalize_cons,
          normalize_cons, ih (sub_pos.2 hu)]
  | erase_zero m₁ m₂ =>
    induction m₁ generalizing c with
    | nil => simp [reflectUntil_zero_cons hc]
    | cons u m ih =>
      simp only [List.cons_append]
      rcases le_or_gt c (f u) with hu | hu
      · rw [reflectUntil_cons_of_le hu, reflectUntil_cons_of_le hu, normalize_cons,
          normalize_cons, normalize_cons, normalize_cons, (Move.erase_zero m m₂).normalize_eq]
      · rw [reflectUntil_cons_of_lt hu, reflectUntil_cons_of_lt hu, normalize_cons,
          normalize_cons, ih (sub_pos.2 hu)]

private theorem map_normalize_listLower_zero_cons (l : List V) :
    (listLower f x (0 :: l)).map (normalize 𝕜) = (listLower f x l).map (normalize 𝕜) := by
  rw [listLower_cons, ite_eq_left (by simpa using listMinHeight_nonpos l), Option.map_map]
  congr 1
  ext m : 1
  simp

/-- Lowering commutes with merging the first two segments, up to elementary moves. -/
private theorem map_normalize_listLower_cons_cons (hvw : SameRay 𝕜 v w) (l : List V) :
    (listLower f x (v :: w :: l)).map (normalize 𝕜) =
      (listLower f x ((v + w) :: l)).map (normalize 𝕜) := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [map_normalize_listLower_zero_cons, zero_add]
  obtain ⟨μ, hμ, rfl⟩ := hvw.exists_nonneg_left hv
  have hl := listMinHeight_nonpos (f := f) l
  rw [listLower_cons, listLower_cons, listLower_cons (v + μ • v)]
  simp only [listMinHeight_cons, List.sum_cons, map_add, map_smul, smul_eq_mul, ← add_assoc]
  by_cases hA : f v + μ * f v + listMinHeight f l ≤ 0
  · -- The minimal height is attained after the first two segments.
    have hB : μ * f v + listMinHeight f l ≤ 0 := by
      rcases le_total 0 (f v) with h | h
      · linarith
      · nlinarith [mul_nonpos_of_nonneg_of_nonpos hμ h]
    rw [min_eq_right hB, ← add_assoc, ite_eq_left hA, ite_eq_left hB, ite_eq_left hA,
      Option.map_map, Option.map_map, Option.map_map]
    congr 1
    ext m : 1
    simp only [Function.comp_apply]
    exact (Move.merge [] m (SameRay.sameRay_nonneg_smul_right v hμ)).normalize_eq
  · -- The minimal height `0` is attained only at the start.
    have hA' : ¬ f v + min 0 (μ * f v + listMinHeight f l) ≤ 0 := by
      intro h
      rcases le_total 0 (μ * f v + listMinHeight f l) with h' | h'
      · rw [min_eq_left h', add_zero] at h
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hμ h]
      · rw [min_eq_right h', ← add_assoc] at h
        exact hA h
    rw [ite_eq_right hA', ite_eq_right hA]
    split_ifs
    · simpa using normalize_reflectUntil_cons_cons (SameRay.sameRay_nonneg_smul_right v hμ)
        one_pos l
    · rfl

/-- Lowering commutes with the elementary moves, up to elementary moves. -/
theorem Move.map_normalize_listLower (h : Move 𝕜 l₁ l₂) :
    (listLower f x l₁).map (normalize 𝕜) = (listLower f x l₂).map (normalize 𝕜) := by
  have hcons : ∀ (u : V) {m₁ m₂ : List V}, Move 𝕜 m₁ m₂ →
      (listLower f x m₁).map (normalize 𝕜) = (listLower f x m₂).map (normalize 𝕜) →
      (listLower f x (u :: m₁)).map (normalize 𝕜) =
        (listLower f x (u :: m₂)).map (normalize 𝕜) := by
    intro u m₁ m₂ hm ih
    have hmin : listMinHeight f m₁ = listMinHeight f m₂ := by
      rw [← listMinHeight_normalize, hm.normalize_eq, listMinHeight_normalize]
    have hsum : m₁.sum = m₂.sum := by rw [← sum_normalize (𝕜 := 𝕜), hm.normalize_eq, sum_normalize]
    rw [listLower_cons, listLower_cons, hmin, hsum]
    split_ifs
    · have := congrArg (Option.map (consMerge 𝕜 u)) ih
      simpa [Option.map_map, Function.comp_def] using this
    · simpa using (hm.cons u).normalize_reflectUntil one_pos
    · rfl
  cases h with
  | merge m₁ m₂ hvw =>
    induction m₁ with
    | nil => exact map_normalize_listLower_cons_cons hvw m₂
    | cons u m ih => exact hcons u (.merge m m₂ hvw) ih
  | erase_zero m₁ m₂ =>
    induction m₁ with
    | nil => exact map_normalize_listLower_zero_cons m₂
    | cons u m ih => exact hcons u (.erase_zero m m₂) ih

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
`f = ⟨-, α^∨⟩`: with `h` the minimal height, `t₀` the last time at which the height equals `h`
and `t₁` the first time after `t₀` at which it equals `h + 1`, the piece of the path between `t₀`
and `t₁` is reflected by `Module.preReflection x f` and the rest is translated by `-x`. It is
`none` when `f (π 1) - h < 1`. -/
noncomputable def lower (p : PLPath 𝕜 V) : Option (PLPath 𝕜 V) :=
  (listLower f x p.segments).map (ofSegments 𝕜)

/-- Littelmann's raising operator `e_α` on paths, the conjugate of `TauCeti.PLPath.lower` by the
reversal of paths: with `h` the minimal height, `t₁` the first time at which the height equals
`h` and `t₀` the last time before `t₁` at which it equals `h + 1`, the piece of the path between
`t₀` and `t₁` is reflected by `Module.preReflection x f` and the rest is translated by `x`. It is
`none` when `-1 < h`. -/
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
theorem lower_eq_none_iff : lower f x p = none ↔ f p.endpoint - p.minHeight f < 1 := by
  rw [lower, Option.map_eq_none_iff, listLower_eq_none_iff, endpoint_def, minHeight]

/-- The raising operator is defined exactly when the minimal height is at most `-1`. -/
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
  rw [straight_def, lower_ofSegments, listLower_cons, ite_eq_right (by simp; linarith),
    ite_eq_left (by simpa using h), reflectUntil_cons_of_le h, Option.map_some, one_div,
    ofSegments_cons, ofSegments_cons, ofSegments_nil, mul_one]

end RootOperator

end PLPath

end TauCeti
