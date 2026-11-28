/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Basic

/-!
# Joint raw boxes and public interval states for affine bound tightening

Finite simultaneous affine bound tightening (Belotti, Cafieri, Lee and Liberti, 2010, §4) acts on
joint boxes for `n` variables and `m` affine rows. This file sets up the two views of such a box.

* `Coord n m = Fin n ⊕ Fin m` indexes the joint coordinates: variables are `Sum.inl j` and rows
  are `Sum.inr i`. Either dimension may be zero.
* A raw tuple `q : Raw n m` is a pair of finite real lower and upper endpoint functions. Raw
  tuples need not be ordered: the later tightening formulas stay defined after an empty
  intersection. Raw tuples are plain pairs, so their constructor, projections `q.1`, `q.2` and
  extensionality are those of `Prod`.
* The public state `State n m` is Mathlib's `Interval (Coord n m → ℝ)`: a nonempty closed box,
  bundled with its ordered endpoints as a `NonemptyInterval`, or the single global bottom `⊥`.
  Emptiness is not recorded coordinatewise.
* `pack q` sends an ordered raw tuple to its nonempty interval and any other raw tuple to `⊥`.

## Main statements

* `mem_pack`: membership in `pack q` is membership in `Set.Icc q.1 q.2`, for every raw tuple.
* `pack_eq_bot_iff`: `pack q = ⊥` exactly when `¬ q.1 ≤ q.2`.
* `pack_toProd`, `pack_eq_coe_iff`, `pack_bijOn`: ordered raw tuples correspond bijectively to
  nonbottom public states.
* `pack_le_pack_iff`: for an ordered tuple, inclusion of packed states is endpoint containment.
* `pack_mk_self`: a singleton raw tuple packs to `Interval.pure`.

When `n = m = 0` the coordinate type is empty, so every raw tuple is ordered and packs to the
nonbottom state whose only member is the empty function; this state differs from `⊥`.

## References

* P. Belotti, S. Cafieri, J. Lee and L. Liberti, *Feasibility-based bounds tightening via fixed
  points*, COCOA 2010, Lecture Notes in Computer Science 6508, §4, pp. 71–73.
-/

public section

namespace TauCeti.AffineBoundTightening

/-- Joint coordinates for `n` variables and `m` affine rows: variables are `Sum.inl j` and rows
are `Sum.inr i`. -/
abbrev Coord (n m : ℕ) : Type := Fin n ⊕ Fin m

/-- Raw finite real lower and upper endpoint functions on the joint coordinates. The lower
endpoint may exceed the upper one; such a tuple describes the empty box. -/
abbrev Raw (n m : ℕ) : Type := (Coord n m → ℝ) × (Coord n m → ℝ)

/-- The public joint state: a nonempty closed box with ordered endpoints, or one global empty
state `⊥`. -/
abbrev State (n m : ℕ) : Type := Interval (Coord n m → ℝ)

variable {n m : ℕ} {q r : Raw n m} {x : Coord n m → ℝ}

open scoped Classical in
/-- Convert a raw tuple to a public state: an ordered tuple becomes its nonempty closed interval
and any other tuple becomes the global bottom. -/
noncomputable def pack (q : Raw n m) : State n m :=
  if h : q.1 ≤ q.2 then ((⟨q, h⟩ : NonemptyInterval (Coord n m → ℝ)) : State n m) else ⊥

/-- An ordered raw tuple packs to the nonempty interval with the same endpoints. -/
theorem pack_of_le (h : q.1 ≤ q.2) :
    pack q = ((⟨q, h⟩ : NonemptyInterval (Coord n m → ℝ)) : State n m) := by
  simp [pack, h]

/-- A raw tuple whose lower endpoint is not below its upper endpoint packs to the global bottom. -/
theorem pack_of_not_le (h : ¬ q.1 ≤ q.2) : pack q = ⊥ := by
  simp [pack, h]

/-- A raw tuple packs to the global bottom exactly when it is not ordered. -/
@[simp]
theorem pack_eq_bot_iff : pack q = ⊥ ↔ ¬ q.1 ≤ q.2 := by
  by_cases h : q.1 ≤ q.2
  · rw [pack_of_le h]
    exact iff_of_false WithBot.coe_ne_bot (not_not.2 h)
  · simp [pack_of_not_le h, h]

/-- A raw tuple packs to a nonbottom state exactly when it is ordered. -/
theorem pack_ne_bot_iff : pack q ≠ ⊥ ↔ q.1 ≤ q.2 := by
  simp

/-- The points of `pack q` are those of the closed box `Set.Icc q.1 q.2`, also when `q` is not
ordered. -/
@[simp, norm_cast]
theorem coe_pack (q : Raw n m) : (pack q : Set (Coord n m → ℝ)) = Set.Icc q.1 q.2 := by
  by_cases h : q.1 ≤ q.2
  · rw [pack_of_le h, Interval.coe_coe]
    rfl
  · rw [pack_of_not_le h, Interval.coe_bot, eq_comm, Set.Icc_eq_empty h]

/-- Membership in `pack q` is membership in `Set.Icc q.1 q.2`, with no order hypothesis. -/
@[simp]
theorem mem_pack : x ∈ pack q ↔ x ∈ Set.Icc q.1 q.2 := by
  rw [← SetLike.mem_coe, coe_pack]

/-- Packing the endpoints of a nonempty interval returns that interval. -/
@[simp]
theorem pack_toProd (s : NonemptyInterval (Coord n m → ℝ)) : pack s.toProd = s :=
  pack_of_le s.fst_le_snd

/-- A raw tuple packs to a given nonempty interval exactly when it is that interval's endpoint
pair. -/
@[simp]
theorem pack_eq_coe_iff {s : NonemptyInterval (Coord n m → ℝ)} :
    pack q = s ↔ q = s.toProd := by
  constructor
  · intro hq
    have h : q.1 ≤ q.2 := pack_ne_bot_iff.1 (hq ▸ WithBot.coe_ne_bot)
    rw [pack_of_le h, Interval.coe_inj] at hq
    rw [← hq]
  · rintro rfl
    exact pack_toProd s

/-- `pack` is a bijection from ordered raw tuples onto the nonbottom public states. -/
theorem pack_bijOn : Set.BijOn pack {q : Raw n m | q.1 ≤ q.2} {s : State n m | s ≠ ⊥} where
  left := fun _ hq => pack_ne_bot_iff.2 hq
  right := by
    refine ⟨fun q _ r hr hqr => ?_, fun s hs => ?_⟩
    · rw [pack_of_le hr, pack_eq_coe_iff] at hqr
      exact hqr
    · induction s using Interval.recBotCoe with
      | bot => exact absurd rfl hs
      | coe s => exact ⟨s.toProd, s.fst_le_snd, pack_toProd s⟩

/-- For an ordered raw tuple, inclusion of packed states is endpoint containment. -/
theorem pack_le_pack_iff (hq : q.1 ≤ q.2) : pack q ≤ pack r ↔ r.1 ≤ q.1 ∧ q.2 ≤ r.2 := by
  rw [← Interval.coe_subset_coe, coe_pack, coe_pack, Set.Icc_subset_Icc_iff hq]

/-- The singleton raw tuple `(x, x)` packs to the singleton interval at `x`. -/
@[simp]
theorem pack_mk_self (x : Coord n m → ℝ) : pack (x, x) = Interval.pure x :=
  pack_toProd (NonemptyInterval.pure x)

end TauCeti.AffineBoundTightening
