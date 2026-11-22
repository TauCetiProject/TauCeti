/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Multiset.Sort
public import TauCeti.NumberTheory.Hypergeometric.Parameters
import Mathlib.Tactic.Ring
import TauCeti.Data.List.TakeDrop

/-!
# The zigzag walk of a hypergeometric parameter pair

The weight and the Hodge numbers of a hypergeometric family are read off a closed walk. List the
`2d` representatives in `(0, 1]` of the classes of `α` and `β`, with multiplicity, in increasing
order; start at height `0`, step up at each class of `α` and down at each class of `β`. The copies
of one class of `α` sit side by side in the list, and they are recorded at the heights from which
their up-steps leave; the Hodge vector counts the records at each height.

This file sets up the walk and the counting function
`Z(x) = #{a ∈ α : rep a ≤ x} - #{b ∈ β : rep b ≤ x}` (copies counted with multiplicity), and
proves that the walk is `Z` read at the ends of its blocks of equal entries:

* the walk starts and ends at `0` and moves by a unit step `2d` times;
* after the entries at most `x` it is at height `Z(x)`; in particular, after the last entry of a
  block of equal entries it is at `Z` of that entry;
* the block form: if a class `a ∈ α` has multiplicity `c`, its block starts at height
  `Z(rep a) - c`, and its copies are recorded at the `c` consecutive heights
  `Z(rep a) - c, …, Z(rep a) - 1`, not all at `Z(rep a) - 1`. For `α = (1/2, 1/2)`,
  `β = (1, 1)` the walk is `0, 1, 2, 1, 0` and the two copies of `1/2` are recorded at `0` and `1`.

The swap reflects the walk and negates `Z`.

## Main declarations

* `TauCeti.Hypergeometric.Parameters.sortedReps`: the increasing list of representatives,
  characterized by `sortedReps_eq_iff`.
* `TauCeti.Hypergeometric.Parameters.height`: the height of the walk after `i` steps, with
  `height_zero`, `height_succ`, `height_two_mul_degree` and
  `height_succ_eq_add_one_or_sub_one`.
* `TauCeti.Hypergeometric.Parameters.countingFunction`: the counting function `Z`, with
  `height_card_filter_rep_le` and `height_succ_eq_countingFunction`.
* `TauCeti.Hypergeometric.Parameters.blockStart`: the position of the block of a class, with
  `take_count_drop_blockStart` and the block form `height_blockStart_add_of_mem_α`.

## References

* D. P. Roberts and F. Rodriguez-Villegas, *Hypergeometric motives*, Notices Amer. Math. Soc. 69
  (2022) (the zigzag procedure for the Hodge numbers).
* The LMFDB knowl `hgm.zigzagplot`, which fixes the representatives in `(0, 1]` read by the walk.
-/

public section

namespace TauCeti.Hypergeometric.Parameters

variable (P : Parameters) {a : AddCircle (1 : ℚ)} {i j : ℕ} {x : ℚ}

/-! ### The sorted list of representatives -/

/-- The representatives in `(0, 1]` of the `2d` classes of `α + β`, with multiplicity, in
increasing order. An entry belongs to `α` or to `β` according to its class, since no class is in
both. -/
noncomputable def sortedReps : List ℚ := ((P.α + P.β).map rep).sort

@[simp]
theorem coe_sortedReps : (P.sortedReps : Multiset ℚ) = (P.α + P.β).map rep :=
  Multiset.sort_eq _ _

theorem sortedLE_sortedReps : P.sortedReps.SortedLE :=
  List.sortedLE_iff_pairwise.2 (Multiset.pairwise_sort _ _)

/-- The sorted list of representatives is the unique weakly increasing list of the
representatives of `α + β`. -/
theorem sortedReps_eq_iff {l : List ℚ} :
    P.sortedReps = l ↔ l.SortedLE ∧ (l : Multiset ℚ) = (P.α + P.β).map rep := by
  refine ⟨fun h ↦ h ▸ ⟨P.sortedLE_sortedReps, P.coe_sortedReps⟩, fun ⟨hl, hlrep⟩ ↦ ?_⟩
  exact List.Perm.eq_of_sortedLE P.sortedLE_sortedReps hl
    (Multiset.coe_eq_coe.1 (P.coe_sortedReps.trans hlrep.symm))

@[simp]
theorem length_sortedReps : P.sortedReps.length = 2 * P.degree := by
  rw [← Multiset.coe_card, coe_sortedReps]
  simp [two_mul]

theorem mem_sortedReps : x ∈ P.sortedReps ↔ ∃ a ∈ P.α + P.β, rep a = x := by
  rw [← Multiset.mem_coe, coe_sortedReps, Multiset.mem_map]

/-! ### The walk and the counting function -/

/-- The step of the walk at a rational number: `1` if its class is in `α`, and `-1` otherwise,
so `-1` at every representative of a class of `β`. -/
noncomputable def step (q : ℚ) : ℤ := if (q : AddCircle (1 : ℚ)) ∈ P.α then 1 else -1

theorem step_of_mem {q : ℚ} (hq : (q : AddCircle (1 : ℚ)) ∈ P.α) : P.step q = 1 :=
  ite_eq_left hq

theorem step_of_notMem {q : ℚ} (hq : (q : AddCircle (1 : ℚ)) ∉ P.α) : P.step q = -1 :=
  ite_eq_right hq

theorem step_eq_one_or_eq_neg_one (q : ℚ) : P.step q = 1 ∨ P.step q = -1 := by
  by_cases hq : (q : AddCircle (1 : ℚ)) ∈ P.α
  exacts [.inl (P.step_of_mem hq), .inr (P.step_of_notMem hq)]

theorem step_rep_of_mem_α (ha : a ∈ P.α) : P.step (rep a) = 1 :=
  P.step_of_mem (by rwa [coe_rep])

theorem step_rep_of_mem_β (ha : a ∈ P.β) : P.step (rep a) = -1 :=
  P.step_of_notMem (by rw [coe_rep]; exact Multiset.disjoint_right.1 P.disjoint ha)

/-- The height of the zigzag walk after its first `i` steps: the walk starts at `0` and steps
up at each entry of `sortedReps` from `α` and down at each entry from `β`. It is `0` from step
`2d` on (`height_of_two_mul_degree_le`). -/
noncomputable def height (i : ℕ) : ℤ := ((P.sortedReps.take i).map P.step).sum

theorem height_def (i : ℕ) : P.height i = ((P.sortedReps.take i).map P.step).sum := (rfl)

/-- The counting function `Z(x) = #{a ∈ α : rep a ≤ x} - #{b ∈ β : rep b ≤ x}`, copies counted
with multiplicity. -/
noncomputable def countingFunction (x : ℚ) : ℤ :=
  (P.α.filter fun a ↦ rep a ≤ x).card - (P.β.filter fun b ↦ rep b ≤ x).card

theorem countingFunction_def (x : ℚ) :
    P.countingFunction x =
      (P.α.filter fun a ↦ rep a ≤ x).card - (P.β.filter fun b ↦ rep b ≤ x).card := (rfl)

@[simp]
theorem height_zero : P.height 0 = 0 := by
  simp [height]

theorem height_succ (hi : i < P.sortedReps.length) :
    P.height (i + 1) = P.height i + P.step P.sortedReps[i] := by
  rw [height, height, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
    List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]

/-- The walk moves by a unit step at each of its `2d` steps. -/
theorem height_succ_eq_add_one_or_sub_one (hi : i < 2 * P.degree) :
    P.height (i + 1) = P.height i + 1 ∨ P.height (i + 1) = P.height i - 1 := by
  rw [P.height_succ (by simpa using hi), sub_eq_add_neg]
  exact (P.step_eq_one_or_eq_neg_one _).imp (congrArg _) (congrArg _)

theorem countingFunction_of_nonpos (hx : x ≤ 0) : P.countingFunction x = 0 := by
  have h (s : Multiset (AddCircle (1 : ℚ))) : s.filter (fun a ↦ rep a ≤ x) = 0 :=
    Multiset.filter_eq_nil.2 fun a _ ↦ (hx.trans_lt (rep_pos a)).not_ge
  simp [countingFunction, h]

theorem countingFunction_of_one_le (hx : 1 ≤ x) : P.countingFunction x = 0 := by
  have h (s : Multiset (AddCircle (1 : ℚ))) : s.filter (fun a ↦ rep a ≤ x) = s :=
    Multiset.filter_eq_self.2 fun a _ ↦ (rep_le_one a).trans hx
  simp [countingFunction, h]

/-! ### The walk reads the counting function -/

/-- Counting classes by a property of their representatives is counting entries of the sorted
list. -/
private theorem card_filter_eq_countP (p : ℚ → Prop) [DecidablePred p] :
    ((P.α + P.β).filter fun a ↦ p (rep a)).card = P.sortedReps.countP (p ·) := by
  rw [← Multiset.coe_countP, coe_sortedReps, Multiset.countP_eq_card_filter,
    Multiset.filter_map, Multiset.card_map]
  simp only [Function.comp_def]

/-- For a predicate `p` closed downwards, the walk after the entries satisfying `p` is at the
number of classes of `α` whose representatives satisfy `p` minus the number of those of `β`. -/
private theorem height_card_filter (p : ℚ → Prop) [DecidablePred p]
    (hp : ∀ x y, x ≤ y → p y → p x) :
    P.height ((P.α + P.β).filter fun a ↦ p (rep a)).card =
      (P.α.filter fun a ↦ p (rep a)).card - (P.β.filter fun b ↦ p (rep b)).card := by
  have hpw : P.sortedReps.Pairwise fun x y ↦ decide (p y) → decide (p x) :=
    (List.sortedLE_iff_pairwise.1 P.sortedLE_sortedReps).imp fun hxy ↦ by simpa using hp _ _ hxy
  rw [card_filter_eq_countP, height, List.take_countP_eq_filter hpw, ← Multiset.sum_coe,
    ← Multiset.map_coe, ← Multiset.filter_coe, coe_sortedReps, Multiset.filter_map,
    Multiset.map_map, Multiset.filter_add, Multiset.map_add, Multiset.sum_add, Function.comp_def,
    Multiset.map_congr rfl fun a ha ↦ P.step_rep_of_mem_α (Multiset.mem_filter.1 ha).1,
    Multiset.map_congr rfl fun b hb ↦ P.step_rep_of_mem_β (Multiset.mem_filter.1 hb).1]
  simp [sub_eq_add_neg]

/-- After the entries at most `x`, the walk is at height `Z(x)`. -/
theorem height_card_filter_rep_le (x : ℚ) :
    P.height ((P.α + P.β).filter fun a ↦ rep a ≤ x).card = P.countingFunction x :=
  P.height_card_filter (· ≤ x) fun _ _ hxy hy ↦ hxy.trans hy

/-- The walk returns to `0` after its `2d` steps, and stays there. -/
theorem height_of_two_mul_degree_le (hi : 2 * P.degree ≤ i) : P.height i = 0 := by
  have h : ((P.α + P.β).filter fun a ↦ rep a ≤ 1) = P.α + P.β :=
    Multiset.filter_eq_self.2 fun a _ ↦ rep_le_one a
  have hL : P.sortedReps.take i = P.sortedReps.take (2 * P.degree) := by
    rw [List.take_of_length_le (by simpa using hi), List.take_of_length_le (by simp)]
  rw [height, hL, ← height, ← P.countingFunction_of_one_le le_rfl,
    ← P.height_card_filter_rep_le, h]
  simp [two_mul]

theorem height_two_mul_degree : P.height (2 * P.degree) = 0 :=
  P.height_of_two_mul_degree_le le_rfl

/-- At the last entry of a block of equal entries the walk is at the counting function: if the
`i`-th entry is followed by no entry or by a larger one, the height after it is `Z` of it. -/
theorem height_succ_eq_countingFunction (hi : i < P.sortedReps.length)
    (hlast : ∀ h : i + 1 < P.sortedReps.length, P.sortedReps[i] < P.sortedReps[i + 1]) :
    P.height (i + 1) = P.countingFunction P.sortedReps[i] := by
  -- The entries up to position `i` are at most the `i`-th one, and the later ones exceed it.
  obtain ⟨x, hx⟩ : ∃ x, P.sortedReps[i] = x := ⟨_, rfl⟩
  rw [hx, ← P.height_card_filter_rep_le, P.card_filter_eq_countP (· ≤ x)]
  congr 1
  rw [← List.take_append_drop (i + 1) P.sortedReps, List.countP_append,
    List.countP_eq_length.2, List.countP_eq_zero.2, List.length_take_of_le hi, add_zero]
  · intro q hq
    obtain ⟨m, hm, rfl⟩ := List.mem_drop_iff_getElem.1 hq
    have h1 : i + 1 < P.sortedReps.length := by omega
    have := P.sortedLE_sortedReps.getElem_le_getElem_of_le (Nat.le_add_right (i + 1) m)
      (hi := h1) (hj := by omega)
    simpa [← hx] using (hlast h1).trans_le this
  · intro q hq
    obtain ⟨m, hm, rfl⟩ := List.mem_take_iff_getElem.1 hq
    simpa [← hx] using P.sortedLE_sortedReps.getElem_le_getElem_of_le (by omega : m ≤ i)

/-! ### Blocks of equal entries -/

/-- The position in `sortedReps` at which the block of copies of the representative of `a`
starts: the number of classes of `α + β` with smaller representative. -/
noncomputable def blockStart (a : AddCircle (1 : ℚ)) : ℕ :=
  ((P.α + P.β).filter fun c ↦ rep c < rep a).card

theorem blockStart_def (a : AddCircle (1 : ℚ)) :
    P.blockStart a = ((P.α + P.β).filter fun c ↦ rep c < rep a).card := (rfl)

/-- The number of classes with representative at most that of `a` is the number with smaller
representative plus the multiplicity of `a`. -/
private theorem card_filter_rep_le (s : Multiset (AddCircle (1 : ℚ))) (a : AddCircle (1 : ℚ)) :
    (s.filter fun c ↦ rep c ≤ rep a).card = (s.filter fun c ↦ rep c < rep a).card + s.count a := by
  rw [← Multiset.filter_add_not (fun c ↦ rep c < rep a) (s.filter fun c ↦ rep c ≤ rep a),
    Multiset.card_add, Multiset.filter_filter, Multiset.filter_filter,
    Multiset.count_eq_card_filter_eq]
  congr 2
  · exact Multiset.filter_congr fun c _ ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, h.le⟩⟩
  · exact Multiset.filter_congr fun c _ ↦ by
      rw [not_lt, ← le_antisymm_iff, rep_inj, eq_comm]

/-- The block of a class `a`: the `c` entries of `sortedReps` from position `blockStart a` on,
with `c` the multiplicity of `a` in `α + β`, all equal `rep a`. -/
theorem take_count_drop_blockStart (a : AddCircle (1 : ℚ)) :
    (P.sortedReps.drop (P.blockStart a)).take ((P.α + P.β).count a) =
      List.replicate ((P.α + P.β).count a) (rep a) := by
  have hpw := List.sortedLE_iff_pairwise.1 P.sortedLE_sortedReps
  -- The block ends where the entries at most `rep a` end, and starts where those below end.
  have hle : P.sortedReps.take (P.blockStart a + (P.α + P.β).count a) =
      P.sortedReps.filter (· ≤ rep a) := by
    rw [blockStart, ← card_filter_rep_le, P.card_filter_eq_countP (· ≤ rep a),
      List.take_countP_eq_filter (hpw.imp fun hxy ↦ by simpa using fun h ↦ hxy.trans h)]
  have hlt : P.sortedReps.drop (P.blockStart a) = P.sortedReps.filter (rep a ≤ ·) := by
    rw [blockStart, P.card_filter_eq_countP (· < rep a),
      List.drop_countP_eq_filter (hpw.imp fun hxy ↦ by simpa using fun h ↦ hxy.trans_lt h)]
    exact List.filter_congr fun x _ ↦ by simp only [← decide_not, not_lt]
  have hlen : P.blockStart a + (P.α + P.β).count a ≤ P.sortedReps.length := by
    rw [blockStart, ← card_filter_rep_le, ← Multiset.coe_card, coe_sortedReps, Multiset.card_map]
    exact Multiset.card_le_card (Multiset.filter_le _ _)
  rw [List.eq_replicate_iff]
  refine ⟨by rw [List.length_take, List.length_drop]; omega, fun q hq ↦ le_antisymm ?_ ?_⟩
  · rw [List.take_drop, hle] at hq
    exact of_decide_eq_true (List.mem_filter.1 (List.mem_of_mem_drop hq)).2
  · have hq' := List.mem_of_mem_take hq
    rw [hlt] at hq'
    exact of_decide_eq_true (List.mem_filter.1 hq').2

/-- Inside the block of a class `a`, the walk takes steps of the colour of `a`. -/
theorem height_blockStart_add (a : AddCircle (1 : ℚ)) (hj : j ≤ (P.α + P.β).count a) :
    P.height (P.blockStart a + j) = P.height (P.blockStart a) + j * P.step (rep a) := by
  have hblock : (P.sortedReps.drop (P.blockStart a)).take j = List.replicate j (rep a) := by
    rw [← min_eq_left hj, ← List.take_take, P.take_count_drop_blockStart, List.take_replicate]
  rw [height, height, List.take_add, hblock, List.map_append, List.sum_append, List.map_replicate,
    List.sum_replicate, nsmul_eq_mul]

/-- The block of a class `a ∈ α` of multiplicity `c` starts at height `Z(rep a) - c`. -/
theorem height_blockStart_of_mem_α (ha : a ∈ P.α) :
    P.height (P.blockStart a) = P.countingFunction (rep a) - P.α.count a := by
  rw [blockStart, P.height_card_filter (· < rep a) fun _ _ hxy hy ↦ hxy.trans_lt hy,
    countingFunction, card_filter_rep_le, card_filter_rep_le,
    Multiset.count_eq_zero.2 (Multiset.disjoint_left.1 P.disjoint ha)]
  push_cast
  ring

/-- The block of a class `a ∈ β` of multiplicity `c` starts at height `Z(rep a) + c`. -/
theorem height_blockStart_of_mem_β (ha : a ∈ P.β) :
    P.height (P.blockStart a) = P.countingFunction (rep a) + P.β.count a := by
  rw [blockStart, P.height_card_filter (· < rep a) fun _ _ hxy hy ↦ hxy.trans_lt hy,
    countingFunction, card_filter_rep_le, card_filter_rep_le,
    Multiset.count_eq_zero.2 (Multiset.disjoint_right.1 P.disjoint ha)]
  push_cast
  ring

/-- The block form of the walk at a class `a ∈ α` of multiplicity `c`: after `j ≤ c` steps into
its block the walk is at `Z(rep a) - c + j`. So the `c` copies of `a` are recorded at the
consecutive heights `Z(rep a) - c, …, Z(rep a) - 1`. -/
theorem height_blockStart_add_of_mem_α (ha : a ∈ P.α) (hj : j ≤ P.α.count a) :
    P.height (P.blockStart a + j) = P.countingFunction (rep a) - P.α.count a + j := by
  have hβ := Multiset.count_eq_zero.2 (Multiset.disjoint_left.1 P.disjoint ha)
  rw [P.height_blockStart_add a (by simpa [hβ] using hj), P.height_blockStart_of_mem_α ha,
    P.step_rep_of_mem_α ha, mul_one]

/-- The block form of the walk at a class `a ∈ β` of multiplicity `c`: after `j ≤ c` steps into
its block the walk is at `Z(rep a) + c - j`. -/
theorem height_blockStart_add_of_mem_β (ha : a ∈ P.β) (hj : j ≤ P.β.count a) :
    P.height (P.blockStart a + j) = P.countingFunction (rep a) + P.β.count a - j := by
  have hα := Multiset.count_eq_zero.2 (Multiset.disjoint_right.1 P.disjoint ha)
  rw [P.height_blockStart_add a (by simpa [hα] using hj), P.height_blockStart_of_mem_β ha,
    P.step_rep_of_mem_β ha]
  ring

/-! ### The swap -/

@[simp]
theorem sortedReps_swap : P.swap.sortedReps = P.sortedReps := by
  simp [sortedReps, add_comm]

@[simp]
theorem blockStart_swap (a : AddCircle (1 : ℚ)) : P.swap.blockStart a = P.blockStart a := by
  simp [blockStart, add_comm]

/-- On the entries of the sorted list, the swap reverses every step. -/
theorem step_swap (hx : x ∈ P.sortedReps) : P.swap.step x = -P.step x := by
  obtain ⟨a, ha, rfl⟩ := P.mem_sortedReps.1 hx
  rcases Multiset.mem_add.1 ha with ha | ha
  · rw [P.step_rep_of_mem_α ha, P.swap.step_rep_of_mem_β (by rwa [swap_β])]
  · rw [P.step_rep_of_mem_β ha, P.swap.step_rep_of_mem_α (by rwa [swap_α]), neg_neg]

/-- The swap reflects the walk. -/
@[simp]
theorem height_swap (i : ℕ) : P.swap.height i = -P.height i := by
  rw [height, height, sortedReps_swap,
    List.map_congr_left fun q hq ↦ P.step_swap (List.mem_of_mem_take hq), List.sum_neg,
    List.map_map, Function.comp_def]

@[simp]
theorem countingFunction_swap (x : ℚ) : P.swap.countingFunction x = -P.countingFunction x := by
  simp [countingFunction]

end TauCeti.Hypergeometric.Parameters
