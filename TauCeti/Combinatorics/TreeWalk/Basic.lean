/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Sym.Sym2
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.Combinatorics.Enumerative.DyckWord
public import TauCeti.Data.List.OfFn

/-!
# Closed tree walks traversing every edge twice

Closed walks `w₀, …, w_{2k}` whose steps traverse every edge exactly twice and which visit `k + 1`
distinct vertices are the leading terms in the moment method for Wigner matrices
(Anderson–Guionnet–Zeitouni, §2.1.3, Lemma 2.1.6). Such a walk lives on a tree with `k` edges and
goes once along each edge in each direction.

Up to relabelling of vertices, a walk is recorded by labelling every vertex with the time of its
first visit. A walk is then a function `w : ℕ → ℕ` with `w t ≤ t` and `w (w t) = w t`, and the
vertex visited at time `t` is `w t`. A step `t → t + 1` is *up* if it discovers a new vertex
(`w (t + 1) = t + 1`), and *down* otherwise.

This file shows that these walks correspond to Dyck words. The walk attached to a pattern of up
and down steps is defined by the recursion "an up step discovers vertex `t + 1`, a down step
returns to the parent `w (w t - 1)` of the current vertex"; conversely every walk satisfying the
conditions is of this form.

The Boolean step-pattern predicate is the recursive construction's internal representation; the
public counting equivalence is stated using Mathlib's `DyckWord`.

## Main definitions

* `TauCeti.TreeWalk.walkOf s`: the walk whose up steps are the times at which `s` holds.
* `TauCeti.TreeWalk.IsTreeWalk k w`: `w` is a closed walk of length `2 * k` in first-visit
  labelling, visiting `k + 1` vertices and traversing every edge exactly twice.
* `TauCeti.TreeWalk.IsDyckPattern k s`: a Boolean step sequence representing a Dyck path.

## Main results

* `TauCeti.TreeWalk.isTreeWalk_walkOf`: the walk of a Dyck pattern is a tree walk.
* `TauCeti.TreeWalk.closedTreeWalkEquiv`: closed tree walks of length `2 * k` (padded by zeros)
  are in bijection with Dyck words of semilength `k`.
* `TauCeti.TreeWalk.card_closedTreeWalk`: there are `catalan k` of them.

This file does not show that every closed walk is a relabelling of a unique first-visit walk,
and contains no Wigner matrix content.
-/

public section

open Finset

namespace TauCeti.TreeWalk

/-- The depth of the vertex labelled `t` in the tree of first visits, where the parent of a
vertex `t + 1` is `w t`. The `min` only serves to make the recursion well founded. -/
def depth (w : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => depth w (min (w t) t) + 1
decreasing_by exact Nat.lt_succ_of_le (min_le_right _ _)

/-- The walk whose up steps (first visits of a new vertex) are the times `t` with `s t = true`,
and whose other steps return to the parent of the current vertex. -/
def walkOf (s : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | j + 1 => if s j then j + 1 else walkOf s (min (walkOf s j - 1) j)
decreasing_by
  all_goals first
    | exact Nat.lt_succ_self _
    | exact Nat.lt_succ_of_le (min_le_right _ _)

/-- The parent of the vertex `v` in the tree of first visits. -/
def par (w : ℕ → ℕ) (v : ℕ) : ℕ := w (v - 1)

/-- The number of up steps among the first `n` steps. -/
def ups (s : ℕ → Bool) (n : ℕ) : ℕ := #{i ∈ range n | s i}

/-- There are no up steps in an empty prefix. -/
@[simp] theorem ups_zero (s : ℕ → Bool) : ups s 0 = 0 := by simp [ups]

/-- The depth of the vertex `t + 1` is one more than the depth of its parent `w t`. -/
theorem depth_succ_of_le {w : ℕ → ℕ} {t : ℕ} (h : w t ≤ t) :
    depth w (t + 1) = depth w (w t) + 1 := by
  rw [depth, min_eq_left h]

/-- The root has depth zero. -/
@[simp] theorem depth_zero (w : ℕ → ℕ) : depth w 0 = 0 := by simp [depth]

@[simp] theorem depth_eq_zero_iff {w : ℕ → ℕ} {v : ℕ} : depth w v = 0 ↔ v = 0 := by
  cases v <;> simp [depth]

section WalkOf

variable (s : ℕ → Bool)

@[simp] theorem walkOf_zero : walkOf s 0 = 0 := by rw [walkOf]

@[simp] theorem walkOf_up {j : ℕ} (h : s j = true) : walkOf s (j + 1) = j + 1 := by
  simp [walkOf, h]

/-- The vertex visited at time `j` has label at most `j`. -/
theorem walkOf_le : ∀ j, walkOf s j ≤ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    cases j with
    | zero => simp [walkOf_zero]
    | succ j =>
      rw [walkOf]
      split_ifs
      · exact le_rfl
      · exact (ih _ (Nat.lt_succ_of_le (min_le_right _ _))).trans
          ((min_le_right _ _).trans (Nat.le_succ _))

/-- A down step returns to the parent of the current vertex. -/
theorem walkOf_down {j : ℕ} (h : s j = false) :
    walkOf s (j + 1) = walkOf s (walkOf s j - 1) := by
  have : walkOf s j - 1 ≤ j := (Nat.sub_le _ _).trans (walkOf_le s j)
  simp [walkOf, h, min_eq_left this]

private theorem walkOf_succ_le_of_down {j : ℕ} (h : s j = false) : walkOf s (j + 1) ≤ j := by
  have : walkOf s j - 1 ≤ j := (Nat.sub_le _ _).trans (walkOf_le s j)
  rw [walkOf_down s h]
  exact (walkOf_le s _).trans this

/-- A step discovers a new vertex exactly when it is marked as an up step. -/
@[simp] theorem walkOf_succ_eq_iff {j : ℕ} : walkOf s (j + 1) = j + 1 ↔ s j = true := by
  constructor
  · intro h
    by_contra hs
    have := walkOf_succ_le_of_down s (Bool.eq_false_iff.mpr hs)
    omega
  · exact walkOf_up s

@[simp] theorem walkOf_walkOf : ∀ j, walkOf s (walkOf s j) = walkOf s j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    cases j with
    | zero => simp [walkOf_zero]
    | succ j =>
      cases hs : s j
      · have hlt : walkOf s j - 1 < j + 1 :=
          Nat.lt_succ_of_le ((Nat.sub_le _ _).trans (walkOf_le s j))
        rw [walkOf_down s hs]
        exact ih _ hlt
      · rw [walkOf_up s hs, walkOf_up s hs]

end WalkOf

/-- The number of up steps in a prefix after one more step. -/
theorem ups_succ (s : ℕ → Bool) (n : ℕ) :
    ups s (n + 1) = ups s n + if s n then 1 else 0 := by
  unfold ups
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · simp

/-- A prefix of length `n` contains at most `n` up steps. -/
theorem ups_le (s : ℕ → Bool) (n : ℕ) : ups s n ≤ n := by
  unfold ups
  exact (card_filter_le _ _).trans (by simp)

/-- A Boolean sequence of up and down steps forms a Dyck path of semilength `k`. -/
structure IsDyckPattern (k : ℕ) (s : ℕ → Bool) : Prop where
  ups_eq : ups s (2 * k) = k
  le_two_mul_ups : ∀ n ≤ 2 * k, n ≤ 2 * ups s n
  eq_false : ∀ j, 2 * k ≤ j → s j = false

namespace IsDyckPattern

variable {k : ℕ} {s : ℕ → Bool}

/-- The depth after `n` steps is the number of up steps minus the number of down steps so far. -/
theorem depth_walkOf (hs : IsDyckPattern k s) :
    ∀ n ≤ 2 * k, (depth (walkOf s) (walkOf s n) : ℤ) = 2 * ups s n - n := by
  intro n
  induction n with
  | zero => intro _; simp [walkOf_zero, ups]
  | succ n ih =>
    intro hn
    have ih := ih (by omega)
    have hup := ups_succ s n
    have hge := hs.le_two_mul_ups (n + 1) hn
    cases hsn : s n
    · rw [hsn] at hup
      simp only [Bool.false_eq_true, ite_false, add_zero] at hup
      rw [hup] at hge ⊢
      have hd : 1 ≤ depth (walkOf s) (walkOf s n) := by omega
      have hc : walkOf s n ≠ 0 := fun h => by simp [h] at hd
      have h1 := depth_succ_of_le (w := walkOf s) (walkOf_le s (walkOf s n - 1))
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hc)] at h1
      rw [walkOf_down s hsn]
      push_cast
      omega
    · rw [hsn] at hup
      simp only [ite_true] at hup
      rw [hup, walkOf_up s hsn, depth_succ_of_le (walkOf_le s n)]
      push_cast
      omega

private theorem one_le_walkOf (hs : IsDyckPattern k s) {n : ℕ} (hn : n < 2 * k)
    (hsn : s n = false) :
    1 ≤ walkOf s n := by
  have ih := hs.depth_walkOf n (by omega)
  have hup := ups_succ s n
  have hge := hs.le_two_mul_ups (n + 1) hn
  simp only [hsn, Bool.false_eq_true, ite_false, add_zero] at hup
  rw [hup] at hge
  have hd : 1 ≤ depth (walkOf s) (walkOf s n) := by omega
  exact Nat.one_le_iff_ne_zero.mpr fun h => by simp [h] at hd

/-- The walk of a Dyck pattern returns to the root at time `2 * k`. -/
theorem walkOf_two_mul (hs : IsDyckPattern k s) : walkOf s (2 * k) = 0 := by
  have := hs.depth_walkOf (2 * k) le_rfl
  rw [hs.ups_eq] at this
  exact (depth_eq_zero_iff (w := walkOf s)).mp (by omega)

/-- After the endpoint at time `2 * k`, the walk of a Dyck pattern remains at the root. -/
theorem walkOf_eq_zero (hs : IsDyckPattern k s) {i : ℕ} (hi : 2 * k ≤ i) : walkOf s i = 0 := by
  induction i, hi using Nat.le_induction with
  | base => exact hs.walkOf_two_mul
  | succ i hi ih => rw [walkOf_down s (hs.eq_false i hi), ih]; simp [walkOf_zero]

private theorem card_fixed (hs : IsDyckPattern k s) :
    #{i ∈ range (2 * k + 1) | walkOf s i = i} = k + 1 := by
  rw [card_filter, sum_range_succ']
  have : ∀ i, (if walkOf s (i + 1) = i + 1 then 1 else 0) = if s i = true then 1 else 0 :=
    fun i => by simp [walkOf_succ_eq_iff]
  simp_rw [this, ← card_filter]
  have h := hs.ups_eq
  unfold ups at h
  simp [walkOf_zero, h]

end IsDyckPattern

section Ancestors

variable (s : ℕ → Bool)

private theorem par_le (v : ℕ) : par (walkOf s) v ≤ v := (walkOf_le s _).trans (Nat.sub_le _ _)

private theorem iterate_par_le (n x : ℕ) : (par (walkOf s))^[n] x ≤ x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply']; exact (par_le s _).trans ih

private theorem par_lt {v : ℕ} (hv : 1 ≤ v) : par (walkOf s) v < v :=
  lt_of_le_of_lt (walkOf_le s _) (by omega)

private theorem iterate_par_succ_ne {c : ℕ} (hc : 1 ≤ c) (n : ℕ) :
    (par (walkOf s))^[n + 1] c ≠ c := by
  rw [Function.iterate_succ_apply]
  exact ((iterate_par_le s n _).trans_lt (par_lt s hc)).ne

private theorem iterate_par_zero (n : ℕ) : (par (walkOf s))^[n] 0 = 0 :=
  Function.iterate_fixed (by simp [par, walkOf_zero]) n

/-- Once a vertex `c` has been left by a down step at time `j`, the walk never again visits
a descendant of `c`. -/
private theorem not_exists_iterate_par_walkOf_eq_of_down {j c : ℕ} (hj : s j = false)
    (hc : walkOf s j = c) (hc1 : 1 ≤ c) :
    ∀ m, j + 1 ≤ m → ¬ ∃ n, (par (walkOf s))^[n] (walkOf s m) = c := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    rintro ⟨n, hn⟩
    rw [walkOf_down s hj, hc] at hn
    exact iterate_par_succ_ne s hc1 n (by rw [Function.iterate_succ_apply]; exact hn)
  | succ m hm ih =>
    rintro ⟨n, hn⟩
    cases hsm : s m
    · rw [walkOf_down s hsm] at hn
      exact ih ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩
    · rw [walkOf_up s hsm] at hn
      cases n with
      | zero =>
        have := walkOf_le s j
        simp only [Function.iterate_zero, id] at hn
        omega
      | succ n =>
        rw [Function.iterate_succ_apply] at hn
        exact ih ⟨n, by simpa [par] using hn⟩

end Ancestors

namespace IsDyckPattern

variable {k : ℕ} {s : ℕ → Bool}

/-- Every fixed non-root vertex label within the walk interval is left by a down step. -/
private theorem exists_down (hs : IsDyckPattern k s) {c : ℕ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2 * k)
    (hcW : walkOf s c = c) :
    ∃ m, c ≤ m ∧ m < 2 * k ∧ s m = false ∧ walkOf s m = c := by
  by_contra hno
  push Not at hno
  have key : ∀ m, c ≤ m → m ≤ 2 * k → ∃ n, (par (walkOf s))^[n] (walkOf s m) = c := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => intro _; exact ⟨0, by simpa using hcW⟩
    | succ m hm ih =>
      intro hm2
      obtain ⟨n, hn⟩ := ih (by omega)
      cases hsm : s m
      · have hne : walkOf s m ≠ c := hno m hm (by omega) hsm
        cases n with
        | zero => exact absurd (by simpa using hn) hne
        | succ n =>
          rw [Function.iterate_succ_apply] at hn
          exact ⟨n, by rw [walkOf_down s hsm]; exact hn⟩
      · exact ⟨n + 1, by
          rw [walkOf_up s hsm, Function.iterate_succ_apply]; simpa [par] using hn⟩
  obtain ⟨n, hn⟩ := key (2 * k) hc2 le_rfl
  rw [hs.walkOf_two_mul, iterate_par_zero] at hn
  omega

end IsDyckPattern

/-- The vertex at the lower end of the edge traversed by the step `j`. -/
private def child (s : ℕ → Bool) (j : ℕ) : ℕ :=
  if s j then j + 1 else walkOf s j

private theorem sym2_walkOf_eq_child {s : ℕ → Bool} (j : ℕ) :
    s(walkOf s j, walkOf s (j + 1)) = s(walkOf s (child s j - 1), child s j) := by
  cases hsj : s j
  · simp only [child, hsj, Bool.false_eq_true, ite_false]
    rw [walkOf_down s hsj, Sym2.eq_swap]
  · simp [child, hsj]

private theorem walkOf_child {s : ℕ → Bool} (j : ℕ) : walkOf s (child s j) = child s j := by
  cases hsj : s j
  · simp [child, hsj, walkOf_walkOf]
  · simp [child, hsj]

private theorem child_le {k : ℕ} {s : ℕ → Bool} {j : ℕ} (hj : j < 2 * k) :
    child s j ≤ 2 * k := by
  cases hsj : s j
  · simpa [child, hsj] using (walkOf_le s j).trans hj.le
  · simpa [child, hsj] using hj

namespace IsDyckPattern

variable {k : ℕ} {s : ℕ → Bool}

private theorem one_le_child (hs : IsDyckPattern k s) {j : ℕ} (hj : j < 2 * k) :
    1 ≤ child s j := by
  cases hsj : s j
  · simpa [child, hsj] using hs.one_le_walkOf hj hsj
  · simp [child, hsj]

private theorem sym2_eq_iff_child (hs : IsDyckPattern k s) {i j : ℕ} (hi : i < 2 * k)
    (hj : j < 2 * k) :
    s(walkOf s j, walkOf s (j + 1)) = s(walkOf s i, walkOf s (i + 1)) ↔ child s j = child s i := by
  rw [sym2_walkOf_eq_child, sym2_walkOf_eq_child]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have h1 := hs.one_le_child hi
  have h2 := hs.one_le_child hj
  have h3 := walkOf_le s (child s i - 1)
  have h4 := walkOf_le s (child s j - 1)
  rw [Sym2.eq_iff] at h
  omega

private theorem card_child_eq_two (hs : IsDyckPattern k s) {c : ℕ} (hc1 : 1 ≤ c)
    (hc2 : c ≤ 2 * k)
    (hcW : walkOf s c = c) : #{j ∈ range (2 * k) | child s j = c} = 2 := by
  obtain ⟨m, hcm, hm2k, hsm, hWm⟩ := hs.exists_down hc1 hc2 hcW
  have hup : s (c - 1) = true := by
    have h := (walkOf_succ_eq_iff s (j := c - 1)).mp
    rw [Nat.sub_add_cancel hc1] at h
    exact h hcW
  have hne : c - 1 ≠ m := fun h => by rw [h, hsm] at hup; exact Bool.false_ne_true hup
  have : filter (fun j => child s j = c) (range (2 * k)) = {c - 1, m} := by
    ext j
    simp only [mem_filter, mem_range, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hj, hjc⟩
      cases hsj : s j
      · right
        simp only [child, hsj, Bool.false_eq_true, ite_false] at hjc
        rcases lt_trichotomy j m with h | h | h
        · exact absurd ⟨0, by simpa using hjc.symm ▸ hWm⟩
            (not_exists_iterate_par_walkOf_eq_of_down s hsj hjc hc1 m h)
        · exact h
        · exact absurd ⟨0, by simpa using hjc⟩
            (not_exists_iterate_par_walkOf_eq_of_down s hsm hWm hc1 j h)
      · left
        simp only [child, hsj, ite_true] at hjc
        omega
    · rintro (h | h)
      · refine ⟨by omega, ?_⟩
        simp only [child, h ▸ hup, ite_eq_left]
        omega
      · exact ⟨h ▸ hm2k, by simp [child, h ▸ hsm, h ▸ hWm]⟩
  rw [this, card_pair hne]

end IsDyckPattern

/-- `w` is a closed walk of length `2 * k` in first-visit labelling (the vertex visited at time
`t` is labelled by the time of its first visit), which visits `k + 1` distinct vertices and
traverses every edge exactly twice. -/
structure IsTreeWalk (k : ℕ) (w : ℕ → ℕ) : Prop where
  root : w 0 = 0
  closed : w (2 * k) = 0
  le_self : ∀ i ≤ 2 * k, w i ≤ i
  card_vertices : #{i ∈ range (2 * k + 1) | w i = i} = k + 1
  card_edge : ∀ i < 2 * k,
    #{j ∈ range (2 * k) | s(w j, w (j + 1)) = s(w i, w (i + 1))} = 2

/-- The walk attached to a Dyck pattern of semilength `k` is a closed tree walk of length `2 * k`.
-/
theorem isTreeWalk_walkOf {k : ℕ} {s : ℕ → Bool} (hs : IsDyckPattern k s) :
    IsTreeWalk k (walkOf s) where
  root := walkOf_zero s
  closed := hs.walkOf_two_mul
  le_self i _ := walkOf_le s i
  card_vertices := hs.card_fixed
  card_edge i hi := by
    have := hs.card_child_eq_two (c := child s i) (hs.one_le_child hi) (child_le hi)
      (walkOf_child i)
    refine Eq.trans ?_ this
    refine congrArg card (filter_congr fun j hj => ?_)
    exact hs.sym2_eq_iff_child hi (mem_range.mp hj)

/-- The pattern of up steps (steps discovering a new vertex) of a walk of length `2 * k`. -/
def upSteps (k : ℕ) (w : ℕ → ℕ) (j : ℕ) : Bool := decide (j < 2 * k ∧ w (j + 1) = j + 1)

@[simp] theorem upSteps_eq_true_iff {k : ℕ} {w : ℕ → ℕ} {j : ℕ} :
    upSteps k w j = true ↔ j < 2 * k ∧ w (j + 1) = j + 1 := by
  simp [upSteps]

namespace IsTreeWalk

variable {k : ℕ} {w : ℕ → ℕ} (hw : IsTreeWalk k w)
include hw

private theorem card_up : #{j ∈ range (2 * k) | w (j + 1) = j + 1} = k := by
  have h := hw.card_vertices
  rw [card_filter, sum_range_succ'] at h
  have : ∑ i ∈ range (2 * k), (if w (i + 1) = i + 1 then 1 else 0) = k := by
    simpa [hw.root] using h
  rw [card_filter]
  exact this

/-- Every edge of a tree walk is the edge discovered by some up step. -/
private theorem exists_up_edge {j : ℕ} (hj : j < 2 * k) :
    ∃ i < 2 * k, w (i + 1) = i + 1 ∧ s(w j, w (j + 1)) = s(w i, i + 1) := by
  set U := {j ∈ range (2 * k) | w (j + 1) = j + 1} with hU
  set e : ℕ → Sym2 ℕ := fun j => s(w j, w (j + 1)) with he
  set E := (range (2 * k)).image e with hE
  have hEcard : #E = k := by
    have h1 := card_eq_sum_card_image e (range (2 * k))
    have h2 : ∑ a ∈ E, #{x ∈ range (2 * k) | e x = a} = ∑ a ∈ E, 2 := by
      refine sum_congr rfl fun a ha => ?_
      obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
      exact hw.card_edge i (mem_range.mp hi)
    rw [← h1] at h2
    simp at h2
    omega
  have hinj : Set.InjOn e U := by
    intro i hi i' hi' h
    simp only [Finset.mem_coe, hU, mem_filter, mem_range] at hi hi'
    have a1 := hw.le_self i (by omega)
    have a2 := hw.le_self i' (by omega)
    simp only [he, hi.2, hi'.2, Sym2.eq_iff] at h
    omega
  have hsub : U.image e ⊆ E := image_subset_image (filter_subset _ _)
  have hcard : #(U.image e) = k := by rw [card_image_of_injOn hinj, hU, hw.card_up]
  have heq : U.image e = E := eq_of_subset_of_card_le hsub (by omega)
  have hmem : e j ∈ U.image e := by rw [heq]; exact mem_image_of_mem _ (mem_range.mpr hj)
  obtain ⟨i, hi, hie⟩ := mem_image.mp hmem
  simp only [hU, mem_filter, mem_range] at hi
  refine ⟨i, hi.1, hi.2, ?_⟩
  have h2 : e i = s(w i, i + 1) := by simp only [he, hi.2]
  exact hie.symm.trans h2

private theorem step_cases {j : ℕ} (hj : j < 2 * k) :
    depth w (w (j + 1)) = depth w (w j) + 1 ∨
      (1 ≤ w j ∧ w (j + 1) = w (w j - 1) ∧ depth w (w (j + 1)) + 1 = depth w (w j)) := by
  obtain ⟨i, hi, hiu, hji⟩ := hw.exists_up_edge hj
  have hd : depth w (i + 1) = depth w (w i) + 1 := depth_succ_of_le (hw.le_self i hi.le)
  rw [Sym2.eq_iff] at hji
  rcases hji with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    rw [h2, h1, hd]
  · right
    refine ⟨by omega, by rw [h1]; simpa using h2, ?_⟩
    rw [h2, h1, hd]

/-- Every step that does not discover a new vertex returns to the parent of the current vertex. -/
theorem step_down {j : ℕ} (hj : j < 2 * k) (hn : ¬ w (j + 1) = j + 1) :
    1 ≤ w j ∧ w (j + 1) = w (w j - 1) ∧ depth w (w (j + 1)) + 1 = depth w (w j) := by
  by_contra hcon
  set f : ℕ → ℤ := fun j => (depth w (w j) : ℤ) with hf
  have htel : ∑ j ∈ range (2 * k), (f (j + 1) - f j) = 0 := by
    rw [sum_range_sub]
    simp [hf, hw.closed, hw.root]
  have hU : ∑ j ∈ range (2 * k) with w (j + 1) = j + 1, (f (j + 1) - f j) = k := by
    have : ∀ j ∈ filter (fun j => w (j + 1) = j + 1) (range (2 * k)), f (j + 1) - f j = 1 := by
      intro j hj
      simp only [mem_filter, mem_range] at hj
      simp only [hf]
      rw [hj.2, depth_succ_of_le (hw.le_self j hj.1.le)]
      push_cast
      ring
    rw [sum_congr rfl this]
    simp [hw.card_up]
  have hcardN : #{j ∈ range (2 * k) | ¬ w (j + 1) = j + 1} = k := by
    have := card_filter_add_card_filter_not (s := range (2 * k))
      (fun j => w (j + 1) = j + 1)
    rw [hw.card_up] at this
    simp only [card_range] at this
    omega
  have hlow : ∀ j ∈ filter (fun j => ¬ w (j + 1) = j + 1) (range (2 * k)),
      (-1 : ℤ) ≤ f (j + 1) - f j := by
    intro j hj
    simp only [mem_filter, mem_range] at hj
    simp only [hf]
    rcases hw.step_cases hj.1 with h | h
    · omega
    · omega
  have hstrict : ∃ j ∈ filter (fun j => ¬ w (j + 1) = j + 1) (range (2 * k)),
      (-1 : ℤ) < f (j + 1) - f j := by
    refine ⟨j, by simp [hj, hn], ?_⟩
    simp only [hf]
    rcases hw.step_cases hj with h | h
    · omega
    · exact absurd h hcon
  have hlt := sum_lt_sum hlow hstrict
  rw [sum_const, hcardN] at hlt
  have hsplit := sum_filter_add_sum_filter_not (range (2 * k)) (fun j => w (j + 1) = j + 1)
    (fun j => f (j + 1) - f j)
  rw [htel, hU] at hsplit
  simp only [nsmul_eq_mul, mul_neg, mul_one] at hlt
  linarith

/-- Up steps reconstruct the original tree walk on its full interval of definition. -/
theorem walkOf_upSteps : ∀ j ≤ 2 * k, walkOf (upSteps k w) j = w j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    cases j with
    | zero => simp [walkOf_zero, hw.root]
    | succ j =>
      have hj' : j < 2 * k := by omega
      by_cases hup : w (j + 1) = j + 1
      · rw [walkOf_up _ (upSteps_eq_true_iff.mpr ⟨hj', hup⟩), hup]
      · have hs : upSteps k w j = false := by simp [upSteps, hup]
        obtain ⟨-, h2, -⟩ := hw.step_down hj' hup
        have hle := hw.le_self j hj'.le
        rw [walkOf_down _ hs, ih j (by omega) hj'.le, h2]
        exact ih (w j - 1) (by omega) (by omega)

/-- Every vertex label is fixed by the walk of its up-step pattern. -/
theorem idem {i : ℕ} (hi : i ≤ 2 * k) : w (w i) = w i := by
  have hwi : w i ≤ 2 * k := (hw.le_self i hi).trans hi
  rw [← hw.walkOf_upSteps (w i) hwi, ← hw.walkOf_upSteps i hi]
  exact walkOf_walkOf _ _

private theorem depth_eq_ups : ∀ n ≤ 2 * k,
    (depth w (w n) : ℤ) = 2 * ups (upSteps k w) n - n := by
  intro n
  induction n with
  | zero => intro _; simp [hw.root, ups]
  | succ n ih =>
    intro hn
    have ih := ih (by omega)
    have hn' : n < 2 * k := by omega
    have hup := ups_succ (upSteps k w) n
    by_cases h : w (n + 1) = n + 1
    · simp only [upSteps_eq_true_iff.mpr ⟨hn', h⟩, ite_true] at hup
      rw [hup, h, depth_succ_of_le (hw.le_self n hn'.le)]
      push_cast
      omega
    · have hs : upSteps k w n = false := by simp [upSteps, h]
      obtain ⟨-, -, h3⟩ := hw.step_down hn' h
      rw [hs] at hup
      simp only [Bool.false_eq_true, ite_false, add_zero] at hup
      rw [hup]
      push_cast
      omega

/-- The up-step pattern of a tree walk is a Dyck pattern. -/
theorem isDyckPattern_upSteps : IsDyckPattern k (upSteps k w) where
  ups_eq := by
    unfold ups
    refine Eq.trans ?_ hw.card_up
    refine congrArg card (filter_congr fun i hi => ?_)
    rw [upSteps_eq_true_iff]
    exact ⟨fun h => h.2, fun h => ⟨mem_range.mp hi, h⟩⟩
  le_two_mul_ups n hn := by
    have := hw.depth_eq_ups n hn
    omega
  eq_false j hj := by
    simp only [upSteps, decide_eq_false_iff_not]
    omega

end IsTreeWalk

/-! ### The bijection with Dyck words -/

/-- The pattern of up steps of a list of Dyck steps. -/
private def stepsOf (l : List DyckStep) (j : ℕ) : Bool :=
  decide (l[j]? = some DyckStep.U)

private theorem count_take_U (l : List DyckStep) (n : ℕ) :
    (l.take n).count DyckStep.U = ups (stepsOf l) n := by
  induction n with
  | zero => simp [ups]
  | succ n ih =>
    rw [ups_succ, ← ih, List.take_add_one]
    cases hl : l[n]? with
    | none => simp [stepsOf, hl]
    | some x => cases x <;> simp [stepsOf, hl, List.count_append]

private theorem isDyckPattern_stepsOf (p : DyckWord) :
    IsDyckPattern p.semilength (stepsOf p.toList) where
  ups_eq := by
    rw [← count_take_U, p.two_mul_semilength_eq_length, List.take_length]
    rfl
  le_two_mul_ups n hn := by
    have h1 := p.count_D_le_count_U n
    have h2 := TauCeti.DyckWord.count_U_add_count_D (p.toList.take n)
    have h3 := p.two_mul_semilength_eq_length
    rw [List.length_take] at h2
    rw [← count_take_U]
    omega
  eq_false j hj := by
    have := p.two_mul_semilength_eq_length
    have h := List.getElem?_eq_none (l := p.toList) (i := j) (by omega)
    simp [stepsOf, h]
private theorem stepsOf_ofFn {k : ℕ} {s : ℕ → Bool} (hs : IsDyckPattern k s) (j : ℕ) :
    stepsOf (List.ofFn fun i : Fin (2 * k) => if s i then DyckStep.U else DyckStep.D) j = s j := by
  by_cases h : j < 2 * k
  · cases hsj : s j <;> simp [stepsOf, h, hsj]
  · simp [stepsOf, h, hs.eq_false j (by omega)]

private theorem count_U_ofFn {k : ℕ} {s : ℕ → Bool} {n : ℕ} (hn : n ≤ 2 * k) :
    ((List.ofFn (fun i : Fin (2 * k) => if s i then DyckStep.U else DyckStep.D)).take n).count
      DyckStep.U = ups s n := by
  rw [List.count_take_ofFn]
  unfold ups
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    simp only [mem_filter, mem_range]
    refine ⟨hi.1, ?_⟩
    simpa using hi.2
  · intro i hi j hj hij
    exact Fin.ext hij
  · intro j hj
    simp only [mem_filter, mem_range] at hj
    let i : Fin (2 * k) := ⟨j, hj.1.trans_le hn⟩
    refine ⟨i, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨hj.1, by simpa [i] using hj.2⟩

/-- The Dyck word whose `U` steps are the up steps of a Dyck pattern. -/
private def dyckWordOf {k : ℕ} {s : ℕ → Bool} (hs : IsDyckPattern k s) : DyckWord where
  toList := List.ofFn fun i : Fin (2 * k) => if s i then DyckStep.U else DyckStep.D
  count_U_eq_count_D := by
    set l := List.ofFn fun i : Fin (2 * k) => if s i then DyckStep.U else DyckStep.D with hl
    have hlen : l.length = 2 * k := by simp [hl]
    have h1 := count_U_ofFn (k := k) (s := s) (n := 2 * k) (Nat.le_refl _)
    rw [← hl] at h1
    rw [hs.ups_eq] at h1
    rw [List.take_of_length_le (by omega)] at h1
    have h2 := TauCeti.DyckWord.count_U_add_count_D l
    omega
  count_D_le_count_U n := by
    set l := List.ofFn fun i : Fin (2 * k) => if s i then DyckStep.U else DyckStep.D with hl
    have hlen : l.length = 2 * k := by simp [hl]
    have h1 := count_U_ofFn (k := k) (s := s) (n := 2 * k) (Nat.le_refl _)
    rw [← hl] at h1
    rw [hs.ups_eq] at h1
    rw [List.take_of_length_le (by omega)] at h1
    have h2 := TauCeti.DyckWord.count_U_add_count_D l
    rcases le_total n (2 * k) with hn | hn
    · have h3 := TauCeti.DyckWord.count_U_add_count_D (l.take n)
      have h4 := count_U_ofFn (k := k) (s := s) (n := n) hn
      rw [← hl] at h4
      have h5 := hs.le_two_mul_ups n hn
      rw [List.length_take] at h3
      omega
    · rw [List.take_of_length_le (by omega)]
      omega

@[simp] private theorem stepsOf_dyckWordOf {k : ℕ} {s : ℕ → Bool} (hs : IsDyckPattern k s) :
    stepsOf (dyckWordOf hs).toList = s :=
  funext (stepsOf_ofFn hs)

@[simp] private theorem semilength_dyckWordOf {k : ℕ} {s : ℕ → Bool} (hs : IsDyckPattern k s) :
    (dyckWordOf hs).semilength = k := by
  have h1 := count_U_ofFn (k := k) (s := s) (n := 2 * k) (Nat.le_refl _)
  have hlen :
      (List.ofFn fun i : Fin (2 * k) => if s i then DyckStep.U else DyckStep.D).length = 2 * k :=
    by simp
  rw [List.take_of_length_le (by omega), hs.ups_eq] at h1
  simpa only [DyckWord.semilength, dyckWordOf] using h1

@[simp] private theorem dyckWordOf_stepsOf (p : DyckWord) :
    dyckWordOf (isDyckPattern_stepsOf p) = p := by
  ext1
  have hl := p.two_mul_semilength_eq_length
  refine List.ext_getElem (by simp [dyckWordOf, hl]) fun i h1 h2 => ?_
  simp only [dyckWordOf, List.getElem_ofFn]
  cases hp : p.toList[i] <;> simp [stepsOf, List.getElem?_eq_getElem h2, hp]

private theorem dyckWordOf_congr {k : ℕ} {s s' : ℕ → Bool} (e : s = s') (hs : IsDyckPattern k s)
    (hs' : IsDyckPattern k s') : dyckWordOf hs = dyckWordOf hs' := by
  subst e
  rfl

/-- Extracting the up steps of the walk of a Dyck pattern recovers the original Boolean sequence. -/
@[simp] theorem upSteps_walkOf {k : ℕ} {s : ℕ → Bool} (hs : IsDyckPattern k s) :
    upSteps k (walkOf s) = s := by
  funext j
  refine Bool.eq_iff_iff.mpr ?_
  rw [upSteps_eq_true_iff, walkOf_succ_eq_iff]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  by_contra hj
  simp [hs.eq_false j (by omega)] at h

/-- Closed walks of length `2 * k` in first-visit labelling that visit `k + 1` vertices and
traverse every edge exactly twice, padded by zeros after time `2 * k`. -/
abbrev ClosedTreeWalk (k : ℕ) : Type := {w : ℕ → ℕ // IsTreeWalk k w ∧ ∀ i, 2 * k < i → w i = 0}

/-- Closed tree walks traversing every edge twice correspond to Dyck words: the Dyck word
records which steps discover a new vertex. -/
def closedTreeWalkEquiv (k : ℕ) : ClosedTreeWalk k ≃ {p : DyckWord // p.semilength = k} where
  toFun w := ⟨dyckWordOf w.2.1.isDyckPattern_upSteps, semilength_dyckWordOf _⟩
  invFun p :=
    have hs : IsDyckPattern k (stepsOf p.1.toList) := by
      have h := isDyckPattern_stepsOf p.1
      rwa [p.2] at h
    ⟨walkOf (stepsOf p.1.toList), isTreeWalk_walkOf hs, fun _ hi => hs.walkOf_eq_zero hi.le⟩
  left_inv w := by
    refine Subtype.ext (funext fun i => ?_)
    have hs := w.2.1.isDyckPattern_upSteps
    -- Unfold the equivalence's function and subtype projections to expose the walk equality.
    change walkOf (stepsOf (dyckWordOf hs).toList) i = w.1 i
    rw [stepsOf_dyckWordOf hs]
    rcases le_or_gt i (2 * k) with hi | hi
    · exact w.2.1.walkOf_upSteps i hi
    · rw [hs.walkOf_eq_zero hi.le, w.2.2 i hi]
  right_inv := by
    rintro ⟨p, rfl⟩
    refine Subtype.ext ?_
    have hs := isDyckPattern_stepsOf p
    -- Unfold the inverse function and subtype projections to expose the Dyck-word equality.
    change dyckWordOf (isTreeWalk_walkOf hs).isDyckPattern_upSteps = p
    rw [dyckWordOf_congr (upSteps_walkOf hs) _ hs]
    exact dyckWordOf_stepsOf p

/-- The Dyck word corresponding to a closed tree walk is the word of its up-step pattern. -/
@[simp] theorem closedTreeWalkEquiv_apply_coe (k : ℕ) (w : ClosedTreeWalk k) :
    ((closedTreeWalkEquiv k w).1).toList =
      List.ofFn fun i : Fin (2 * k) => if upSteps k w.1 i then DyckStep.U else DyckStep.D := by
  simp [closedTreeWalkEquiv, dyckWordOf]

/-- The closed tree walk corresponding to a Dyck word is the walk of its step pattern. -/
@[simp] theorem closedTreeWalkEquiv_symm_apply_coe (k : ℕ)
    (p : {p : DyckWord // p.semilength = k}) :
    ((closedTreeWalkEquiv k).symm p).1 =
      walkOf (fun j => decide (p.1.toList[j]? = some DyckStep.U)) := by
  simp only [closedTreeWalkEquiv]
  apply congrArg walkOf
  funext j
  rfl

/-- There are `catalan k` closed walks of length `2 * k` in first-visit labelling that visit
`k + 1` vertices and traverse every edge exactly twice. -/
theorem card_closedTreeWalk (k : ℕ) : Nat.card (ClosedTreeWalk k) = catalan k := by
  rw [Nat.card_congr (closedTreeWalkEquiv k), Nat.card_eq_fintype_card,
    DyckWord.card_dyckWord_semilength_eq_catalan]

end TauCeti.TreeWalk
