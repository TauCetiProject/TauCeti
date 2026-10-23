/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Chain
public import TauCeti.LinearAlgebra.Ray

/-!
# Piecewise-linear paths up to reparametrization

Littelmann's path model works with piecewise-linear paths `π : [0, 1] → V` starting at `π 0 = 0`
in a vector space `V` over an ordered field `𝕜` (the weight space `X ⊗ ℚ` or `X ⊗ ℝ` of a root
datum), identified up to nondecreasing surjective piecewise-linear reparametrization. A finite
presentation of such a path is a subdivision `0 = t₀ ≤ t₁ ≤ ⋯ ≤ tₙ = 1` on whose pieces `π` is
affine; it is recorded by its list of *segments* `[v₁, …, vₙ]`, `vₖ = π tₖ - π tₖ₋₁`. The lengths
`tₖ - tₖ₋₁` are not recorded, since a reparametrization can change them at will. Two elementary
moves change a presentation but are meant not to change the path it presents:

* a *merge* `[…, v, w, …] ↦ […, v + w, …]` of two adjacent segments pointing in the same
  direction (`SameRay 𝕜 v w`), whose inverse subdivides a segment;
* the removal `[…, 0, …] ↦ […, …]` of a stationary segment.

This file develops these presentations and their normal form. The algorithm
`TauCeti.PLPath.normalize` removes the stationary segments and merges adjacent segments pointing
in the same direction, using only the vector-space operations of `V` (so a presentation over `ℚ`
stays over `ℚ`; no Euclidean arc length is involved). Its output is reduced, and two segment lists
have the same normal form exactly when they are related by the elementary moves. The type
`TauCeti.PLPath 𝕜 V` models paths by reduced segment lists, with Littelmann's concatenation
`π₁ * π₂` as a monoid structure, the endpoint `π 1`, and the reversed path `t ↦ π (1 - t) - π 1`.

This file works with segment lists only: it does not evaluate a presentation as a function
`[0, 1] → V`, and it does not prove that two presentations give paths related by a nondecreasing
surjective piecewise-linear reparametrization exactly when their normal forms agree.

## Main definitions

* `TauCeti.PLPath.normalize`: the normal form of a segment list, computed by
  `TauCeti.PLPath.consMerge`.
* `TauCeti.PLPath.IsReduced`: a segment list with no stationary segment and no two adjacent
  segments pointing in the same direction.
* `TauCeti.PLPath.Move`: the elementary moves between segment lists.
* `TauCeti.PLPath`: the model of piecewise-linear paths up to reparametrization by reduced
  segment lists.
* `TauCeti.PLPath.ofSegments`: the path presented by a segment list.
* `TauCeti.PLPath.endpoint`, `TauCeti.PLPath.reverse`, `TauCeti.PLPath.straight`: the endpoint,
  the reversed path and the straight path `t ↦ t • v`.

## Main results

* `TauCeti.PLPath.normalize_eq_self_iff`: a segment list is its own normal form exactly when it is
  reduced.
* `TauCeti.PLPath.normalize_eq_normalize_iff`, `TauCeti.PLPath.ofSegments_eq_ofSegments_iff`: two
  segment lists have the same normal form, that is define the same `TauCeti.PLPath`, exactly when
  they are related by the elementary moves.
* `TauCeti.PLPath.ofSegments_append`: concatenation of presentations presents the product.
* `TauCeti.PLPath.endpoint_mul`, `TauCeti.PLPath.reverse_mul`, `TauCeti.PLPath.reverse_reverse`:
  the endpoint is additive and reversal is an involutive anti-automorphism.
* `TauCeti.PLPath.straight_add`: a straight path along `v + w`, for `v` and `w` in the same ray,
  is the concatenation of the straight paths along `v` and along `w`.

## References

* P. Littelmann, *A Littlewood-Richardson rule for symmetrizable Kac-Moody algebras*, Invent.
  Math. 116 (1994), §1.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §1.
-/

public section

namespace TauCeti

universe u v

namespace PLPath

open Relation

variable (𝕜 : Type u) {V : Type v} [Field 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-! ### The normalization algorithm -/

open scoped Classical in
/-- Prepend the segment `v` to the segment list `l`, merging it into the first segment of `l` when
the two point in the same direction, and dropping it when `v = 0` and `l` is empty. This is the
single step of `TauCeti.PLPath.normalize`. -/
noncomputable def consMerge (v : V) : List V → List V
  | [] => if v = 0 then [] else [v]
  | w :: l => if SameRay 𝕜 v w then (v + w) :: l else v :: w :: l

/-- The normal form of a segment list: the stationary segments are removed and adjacent segments
pointing in the same direction are merged, by prepending the segments one at a time with
`TauCeti.PLPath.consMerge`. -/
noncomputable def normalize (l : List V) : List V :=
  l.foldr (consMerge 𝕜) []

/-- A segment list is *reduced* if it has no stationary (zero) segment and no two adjacent segments
point in the same direction. Reduced lists are the normal forms of
`TauCeti.PLPath.normalize`. -/
structure IsReduced (l : List V) : Prop where
  /-- No segment is stationary. -/
  ne_zero : ∀ v ∈ l, v ≠ 0
  /-- No two adjacent segments point in the same direction. -/
  isChain : l.IsChain fun v w ↦ ¬ SameRay 𝕜 v w

/-- The elementary moves between segment lists, which change the presentation of a path but are
meant not to change the path: merging two adjacent segments in the same ray (the inverse of
subdividing a segment), and removing a stationary segment. -/
inductive Move : List V → List V → Prop
  /-- Merge two adjacent segments pointing in the same direction. -/
  | merge (l₁ l₂ : List V) {v w : V} :
      SameRay 𝕜 v w → Move (l₁ ++ v :: w :: l₂) (l₁ ++ (v + w) :: l₂)
  /-- Remove a stationary segment. -/
  | erase_zero (l₁ l₂ : List V) : Move (l₁ ++ 0 :: l₂) (l₁ ++ l₂)

variable {𝕜} {v w : V} {l l₁ l₂ : List V}

@[simp]
theorem consMerge_zero (l : List V) : consMerge 𝕜 0 l = l := by
  cases l <;> simp [consMerge, SameRay.zero_left]

theorem consMerge_nil_of_ne_zero (hv : v ≠ 0) : consMerge 𝕜 v [] = [v] := by
  simp [consMerge, hv]

theorem consMerge_cons_of_sameRay (h : SameRay 𝕜 v w) : consMerge 𝕜 v (w :: l) = (v + w) :: l := by
  simp [consMerge, h]

theorem consMerge_cons_of_not_sameRay (h : ¬ SameRay 𝕜 v w) :
    consMerge 𝕜 v (w :: l) = v :: w :: l := by
  simp [consMerge, h]

/-- Prepending two segments in the same ray one after the other is the same as prepending their
sum. -/
theorem consMerge_consMerge (h : SameRay 𝕜 v w) (l : List V) :
    consMerge 𝕜 v (consMerge 𝕜 w l) = consMerge 𝕜 (v + w) l := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  cases l with
  | nil => simp [consMerge_nil_of_ne_zero, hw, h.add_ne_zero hv, consMerge_cons_of_sameRay h]
  | cons u l =>
    by_cases hwu : SameRay 𝕜 w u
    · rw [consMerge_cons_of_sameRay hwu,
        consMerge_cons_of_sameRay (h.trans_of_ne_zero (SameRay.rfl.add_right hwu) hw),
        consMerge_cons_of_sameRay ((h.sameRay_add_left_iff hw).2 hwu), add_assoc]
    · rw [consMerge_cons_of_not_sameRay hwu, consMerge_cons_of_sameRay h,
        consMerge_cons_of_not_sameRay (mt (h.sameRay_add_left_iff hw).1 hwu)]

private theorem foldr_consMerge_consMerge (v : V) (m r : List V) :
    (consMerge 𝕜 v m).foldr (consMerge 𝕜) r = consMerge 𝕜 v (m.foldr (consMerge 𝕜) r) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  cases m with
  | nil => simp [consMerge_nil_of_ne_zero hv]
  | cons w m =>
    by_cases h : SameRay 𝕜 v w
    · simp [consMerge_cons_of_sameRay h, consMerge_consMerge h]
    · simp [consMerge_cons_of_not_sameRay h]

private theorem foldr_consMerge_normalize (l r : List V) :
    (normalize 𝕜 l).foldr (consMerge 𝕜) r = l.foldr (consMerge 𝕜) r := by
  induction l with
  | nil => rfl
  | cons v l ih => simp [normalize, ← ih, foldr_consMerge_consMerge]

@[simp]
theorem normalize_nil : normalize 𝕜 ([] : List V) = [] :=
  (rfl)

@[simp]
theorem normalize_cons (v : V) (l : List V) :
    normalize 𝕜 (v :: l) = consMerge 𝕜 v (normalize 𝕜 l) :=
  (rfl)

theorem normalize_append (l₁ l₂ : List V) :
    normalize 𝕜 (l₁ ++ l₂) = l₁.foldr (consMerge 𝕜) (normalize 𝕜 l₂) :=
  List.foldr_append

@[simp]
theorem normalize_normalize (l : List V) : normalize 𝕜 (normalize 𝕜 l) = normalize 𝕜 l :=
  foldr_consMerge_normalize l []

@[simp]
theorem normalize_normalize_append (l₁ l₂ : List V) :
    normalize 𝕜 (normalize 𝕜 l₁ ++ l₂) = normalize 𝕜 (l₁ ++ l₂) := by
  rw [normalize_append, normalize_append, foldr_consMerge_normalize]

@[simp]
theorem normalize_append_normalize (l₁ l₂ : List V) :
    normalize 𝕜 (l₁ ++ normalize 𝕜 l₂) = normalize 𝕜 (l₁ ++ l₂) := by
  rw [normalize_append, normalize_append, normalize_normalize]

/-- Prepending a segment with `TauCeti.PLPath.consMerge` adds it to the endpoint. -/
@[simp]
theorem sum_consMerge (v : V) (l : List V) : (consMerge 𝕜 v l).sum = v + l.sum := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  cases l with
  | nil => simp [consMerge_nil_of_ne_zero hv]
  | cons w m =>
    by_cases hvw : SameRay 𝕜 v w
    · simp [consMerge_cons_of_sameRay hvw, add_assoc]
    · simp [consMerge_cons_of_not_sameRay hvw]

/-- Normalization preserves the endpoint `v₁ + ⋯ + vₙ` of a presentation. -/
@[simp]
theorem sum_normalize (l : List V) : (normalize 𝕜 l).sum = l.sum := by
  induction l <;> simp [*]

/-! ### Reduced segment lists -/

@[simp]
theorem isReduced_nil : IsReduced 𝕜 ([] : List V) :=
  ⟨by simp, .nil⟩

theorem isReduced_cons_iff :
    IsReduced 𝕜 (v :: l) ↔ v ≠ 0 ∧ (∀ w ∈ l.head?, ¬ SameRay 𝕜 v w) ∧ IsReduced 𝕜 l := by
  constructor
  · rintro ⟨h0, hc⟩
    rw [List.isChain_cons] at hc
    exact ⟨h0 v (by simp), hc.1, fun u hu ↦ h0 u (by simp [hu]), hc.2⟩
  · rintro ⟨hv, hh, h0, hc⟩
    refine ⟨?_, List.isChain_cons.2 ⟨hh, hc⟩⟩
    simpa [hv] using h0

theorem IsReduced.consMerge (h : IsReduced 𝕜 l) (v : V) : IsReduced 𝕜 (consMerge 𝕜 v l) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simpa
  cases l with
  | nil => simpa [consMerge_nil_of_ne_zero hv, isReduced_cons_iff]
  | cons w m =>
    obtain ⟨hw, hwm, hm⟩ := isReduced_cons_iff.1 h
    by_cases hvw : SameRay 𝕜 v w
    · rw [consMerge_cons_of_sameRay hvw, isReduced_cons_iff]
      exact ⟨hvw.add_ne_zero hv, fun u hu h' ↦ hwm u hu ((hvw.sameRay_add_left_iff hw).1 h'), hm⟩
    · rw [consMerge_cons_of_not_sameRay hvw, isReduced_cons_iff]
      exact ⟨hv, by simpa using hvw, h⟩

theorem isReduced_normalize (l : List V) : IsReduced 𝕜 (normalize 𝕜 l) := by
  induction l with
  | nil => exact isReduced_nil
  | cons v l ih => exact ih.consMerge v

theorem IsReduced.normalize_eq (h : IsReduced 𝕜 l) : normalize 𝕜 l = l := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    obtain ⟨hv, hvl, hl⟩ := isReduced_cons_iff.1 h
    rw [normalize_cons, ih hl]
    cases l with
    | nil => exact consMerge_nil_of_ne_zero hv
    | cons w m => exact consMerge_cons_of_not_sameRay (hvl w rfl)

/-- A segment list is its own normal form exactly when it is reduced. -/
theorem normalize_eq_self_iff : normalize 𝕜 l = l ↔ IsReduced 𝕜 l :=
  ⟨fun h ↦ h ▸ isReduced_normalize l, IsReduced.normalize_eq⟩

/-- Reversing the order of the segments and negating them preserves reducedness. -/
theorem IsReduced.reverse_map_neg (h : IsReduced 𝕜 l) : IsReduced 𝕜 (l.map Neg.neg).reverse := by
  refine ⟨?_, ?_⟩
  · simp only [List.mem_reverse, List.mem_map]
    rintro _ ⟨v, hv, rfl⟩
    exact neg_ne_zero.2 (h.ne_zero v hv)
  rw [List.isChain_reverse, List.isChain_map]
  exact h.isChain.imp fun v w hvw h' ↦ hvw (sameRay_neg_iff.1 h').symm

/-! ### Elementary moves -/

theorem Move.cons (h : Move 𝕜 l₁ l₂) (v : V) : Move 𝕜 (v :: l₁) (v :: l₂) := by
  cases h with
  | merge m₁ m₂ hvw => exact .merge (v :: m₁) m₂ hvw
  | erase_zero m₁ m₂ => exact .erase_zero (v :: m₁) m₂

theorem Move.reverse_map_neg (h : Move 𝕜 l₁ l₂) :
    Move 𝕜 (l₁.map Neg.neg).reverse (l₂.map Neg.neg).reverse := by
  cases h with
  | merge m₁ m₂ hvw =>
    have := Move.merge ((m₂.map Neg.neg).reverse) ((m₁.map Neg.neg).reverse)
      (sameRay_neg_iff.2 hvw.symm)
    simpa [add_comm] using this
  | erase_zero m₁ m₂ =>
    simpa using Move.erase_zero ((m₂.map Neg.neg).reverse) ((m₁.map Neg.neg).reverse)

/-- An elementary move does not change the normal form. -/
theorem Move.normalize_eq (h : Move 𝕜 l₁ l₂) : normalize 𝕜 l₁ = normalize 𝕜 l₂ := by
  cases h with
  | merge m₁ m₂ hvw => simp [normalize_append, consMerge_consMerge hvw]
  | erase_zero m₁ m₂ => simp [normalize_append]

/-- Prepending a segment with `TauCeti.PLPath.consMerge` is a sequence of elementary moves. -/
theorem reflTransGen_move_consMerge (v : V) (l : List V) :
    ReflTransGen (Move 𝕜) (v :: l) (consMerge 𝕜 v l) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simpa using ReflTransGen.single (Move.erase_zero [] l)
  cases l with
  | nil => simpa [consMerge_nil_of_ne_zero hv] using ReflTransGen.refl
  | cons w m =>
    by_cases hvw : SameRay 𝕜 v w
    · simpa [consMerge_cons_of_sameRay hvw] using ReflTransGen.single (Move.merge [] m hvw)
    · simpa [consMerge_cons_of_not_sameRay hvw] using ReflTransGen.refl

/-- Every segment list is connected to its normal form by elementary moves. -/
theorem reflTransGen_move_normalize (l : List V) : ReflTransGen (Move 𝕜) l (normalize 𝕜 l) := by
  induction l with
  | nil => exact .refl
  | cons v l ih =>
    exact (ih.lift (v :: ·) fun _ _ h ↦ h.cons v).trans (reflTransGen_move_consMerge v _)

/-- Two segment lists have the same normal form exactly when they are related by elementary
moves: the normal form is a complete invariant for the elementary moves. -/
theorem normalize_eq_normalize_iff :
    normalize 𝕜 l₁ = normalize 𝕜 l₂ ↔ EqvGen (Move 𝕜) l₁ l₂ := by
  constructor
  · intro h
    have h₁ := EqvGen.reflTransGen_le_eqvGen _ _ _ (reflTransGen_move_normalize (𝕜 := 𝕜) l₁)
    have h₂ := EqvGen.reflTransGen_le_eqvGen _ _ _ (reflTransGen_move_normalize (𝕜 := 𝕜) l₂)
    exact h₁.trans _ _ _ (h ▸ h₂.symm _ _)
  · intro h
    induction h with
    | rel _ _ h => exact h.normalize_eq
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem normalize_reverse_map_neg (l : List V) :
    normalize 𝕜 (l.map Neg.neg).reverse = ((normalize 𝕜 l).map Neg.neg).reverse := by
  rw [← (isReduced_normalize l).reverse_map_neg.normalize_eq, normalize_eq_normalize_iff]
  exact EqvGen.reflTransGen_le_eqvGen _ _ _
    ((reflTransGen_move_normalize l).lift _ fun _ _ h ↦ h.reverse_map_neg)

end PLPath

/-- A model of piecewise-linear paths `π : [0, 1] → V` with `π 0 = 0`, up to nondecreasing
surjective piecewise-linear reparametrization, by reduced segment lists: a path is meant to be
recorded by the successive displacements along its maximal straight pieces. The comparison with
parametrized functions `[0, 1] → V` is not proved here. See `TauCeti.PLPath.ofSegments` for the
path presented by an arbitrary segment list. -/
@[ext]
structure PLPath (𝕜 : Type u) (V : Type v) [Field 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] where
  /-- The segments of the path, in order. -/
  segments : List V
  /-- The segment list is reduced. -/
  isReduced : PLPath.IsReduced 𝕜 segments

namespace PLPath

open Relation

variable (𝕜 : Type u) {V : Type v} [Field 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] {v w : V} {l l₁ l₂ : List V}

/-! ### Paths presented by segment lists -/

/-- The path presented by a segment list: it traverses the segments in order. -/
noncomputable def ofSegments (l : List V) : PLPath 𝕜 V :=
  ⟨normalize 𝕜 l, isReduced_normalize l⟩

/-- The straight path `t ↦ t • v`. -/
noncomputable def straight (v : V) : PLPath 𝕜 V :=
  ofSegments 𝕜 [v]

variable {𝕜}

theorem straight_def (v : V) : straight 𝕜 v = ofSegments 𝕜 [v] :=
  (rfl)

@[simp]
theorem segments_ofSegments (l : List V) : (ofSegments 𝕜 l).segments = normalize 𝕜 l :=
  (rfl)

@[simp]
theorem ofSegments_segments (p : PLPath 𝕜 V) : ofSegments 𝕜 p.segments = p :=
  PLPath.ext p.isReduced.normalize_eq

theorem ofSegments_surjective : Function.Surjective (ofSegments 𝕜 : List V → PLPath 𝕜 V) :=
  fun p ↦ ⟨p.segments, ofSegments_segments p⟩

/-- Two segment lists define the same `TauCeti.PLPath`, that is have the same normal form, exactly
when they are related by elementary moves. -/
theorem ofSegments_eq_ofSegments_iff :
    ofSegments 𝕜 l₁ = ofSegments 𝕜 l₂ ↔ EqvGen (Move 𝕜) l₁ l₂ := by
  rw [PLPath.ext_iff, segments_ofSegments, segments_ofSegments, normalize_eq_normalize_iff]

/-! ### Concatenation -/

/-- The constant path at `0`. -/
instance : One (PLPath 𝕜 V) :=
  ⟨⟨[], isReduced_nil⟩⟩

/-- Littelmann's concatenation `π₁ * π₂`: traverse `π₁`, then the translate of `π₂` by the endpoint
of `π₁`. -/
noncomputable instance : Mul (PLPath 𝕜 V) :=
  ⟨fun p q ↦ ofSegments 𝕜 (p.segments ++ q.segments)⟩

@[simp]
theorem segments_one : (1 : PLPath 𝕜 V).segments = [] :=
  (rfl)

@[simp]
theorem segments_mul (p q : PLPath 𝕜 V) :
    (p * q).segments = normalize 𝕜 (p.segments ++ q.segments) :=
  (rfl)

@[simp]
theorem ofSegments_nil : ofSegments 𝕜 ([] : List V) = 1 :=
  (rfl)

@[simp]
theorem ofSegments_append (l₁ l₂ : List V) :
    ofSegments 𝕜 (l₁ ++ l₂) = ofSegments 𝕜 l₁ * ofSegments 𝕜 l₂ :=
  PLPath.ext (by simp)

noncomputable instance : Monoid (PLPath 𝕜 V) where
  mul_assoc p q r := PLPath.ext (by simp)
  one_mul p := by
    rw [← ofSegments_nil, ← ofSegments_segments p, ← ofSegments_append, List.nil_append]
  mul_one p := by
    rw [← ofSegments_nil, ← ofSegments_segments p, ← ofSegments_append, List.append_nil]

/-- A path presented by `v :: l` is the straight path along `v` followed by the path presented by
`l`. -/
theorem ofSegments_cons (v : V) (l : List V) :
    ofSegments 𝕜 (v :: l) = straight 𝕜 v * ofSegments 𝕜 l := by
  rw [straight, ← ofSegments_append, List.singleton_append]

/-- Every path is the concatenation of the straight paths along its segments. -/
theorem prod_map_straight (l : List V) : (l.map (straight 𝕜)).prod = ofSegments 𝕜 l := by
  induction l with
  | nil => rfl
  | cons v l ih => rw [List.map_cons, List.prod_cons, ih, ofSegments_cons]

/-! ### The endpoint -/

/-- The endpoint `π 1` of a path, the sum of its segments. -/
def endpoint (p : PLPath 𝕜 V) : V :=
  p.segments.sum

theorem endpoint_def (p : PLPath 𝕜 V) : p.endpoint = p.segments.sum :=
  (rfl)

@[simp]
theorem endpoint_ofSegments (l : List V) : (ofSegments 𝕜 l).endpoint = l.sum :=
  sum_normalize l

@[simp]
theorem endpoint_one : (1 : PLPath 𝕜 V).endpoint = 0 :=
  (rfl)

@[simp]
theorem endpoint_mul (p q : PLPath 𝕜 V) : (p * q).endpoint = p.endpoint + q.endpoint := by
  simp [endpoint]

/-! ### Reversal -/

/-- The reversed path `t ↦ π (1 - t) - π 1`: its segments are those of `π`, negated and in the
opposite order. -/
def reverse (p : PLPath 𝕜 V) : PLPath 𝕜 V :=
  ⟨(p.segments.map Neg.neg).reverse, p.isReduced.reverse_map_neg⟩

@[simp]
theorem segments_reverse (p : PLPath 𝕜 V) :
    p.reverse.segments = (p.segments.map Neg.neg).reverse :=
  (rfl)

@[simp]
theorem reverse_ofSegments (l : List V) :
    (ofSegments 𝕜 l).reverse = ofSegments 𝕜 (l.map Neg.neg).reverse :=
  PLPath.ext (normalize_reverse_map_neg l).symm

@[simp]
theorem reverse_reverse (p : PLPath 𝕜 V) : p.reverse.reverse = p :=
  PLPath.ext (by simp [List.map_reverse])

theorem reverse_involutive : Function.Involutive (reverse : PLPath 𝕜 V → PLPath 𝕜 V) :=
  reverse_reverse

@[simp]
theorem reverse_one : (1 : PLPath 𝕜 V).reverse = 1 :=
  (rfl)

@[simp]
theorem reverse_mul (p q : PLPath 𝕜 V) : (p * q).reverse = q.reverse * p.reverse :=
  PLPath.ext (by simp [← normalize_reverse_map_neg])

@[simp]
theorem endpoint_reverse (p : PLPath 𝕜 V) : p.reverse.endpoint = -p.endpoint := by
  rw [endpoint, endpoint, segments_reverse, List.sum_neg_reverse]

/-! ### Straight paths -/

theorem segments_straight_of_ne_zero (hv : v ≠ 0) : (straight 𝕜 v).segments = [v] := by
  simp [straight, consMerge_nil_of_ne_zero hv]

@[simp]
theorem straight_zero : straight 𝕜 (0 : V) = 1 :=
  PLPath.ext (by simp [straight])

@[simp]
theorem endpoint_straight (v : V) : (straight 𝕜 v).endpoint = v := by
  simp [straight]

@[simp]
theorem reverse_straight (v : V) : (straight 𝕜 v).reverse = straight 𝕜 (-v) := by
  simp [straight]

/-- Subdivision: the straight path along `v + w`, for `v` and `w` in the same ray, is the straight
path along `v` followed by the straight path along `w`. -/
theorem straight_add (h : SameRay 𝕜 v w) : straight 𝕜 (v + w) = straight 𝕜 v * straight 𝕜 w := by
  rw [straight, straight, straight, ← ofSegments_append, List.singleton_append,
    ofSegments_eq_ofSegments_iff]
  exact .symm _ _ (.rel _ _ (Move.merge [] [] h))

end PLPath

end TauCeti
