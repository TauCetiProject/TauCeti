/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.Linarith

/-!
# Farthest-first sequences

A list `l` of points of a space with a distance `dist` is farthest-first when each entry after
the first is a point whose distance to the set of earlier entries is the largest possible. A
farthest-first list of length `k` is a choice of centres by the farthest-first traversal of
Gonzalez for the `k`-centre problem. The main result is the approximation guarantee of this
method: if at most `l.length` points cover the space with radius `r`, then the entries of a
farthest-first list `l` cover it with radius `2 * r`.

## Main definitions

* `List.IsFarthestFirst l`: for each position `i ≥ 1` of `l` and each point `x`, the distance
  from `x` to the entries before position `i` is at most the distance from `l[i]` to them.

## Main results

* `List.isFarthestFirst_iff`: the defining property.
* `List.isFarthestFirst_nil`, `List.isFarthestFirst_singleton`: the empty list and every list of
  one entry are farthest-first.
* `List.isFarthestFirst_append_singleton_iff`: `l ++ [z]` is farthest-first exactly when `l` is
  and, if `l` is nonempty, `z` is a point farthest from the entries of `l`.
* `List.IsFarthestFirst.take`: an initial segment of a farthest-first list is farthest-first.
* `List.IsFarthestFirst.exists_dist_le_two_mul`: if at most `l.length` points cover the space
  with radius `r`, the entries of a farthest-first list `l` cover it with radius `2 * r`.

## References

* T. F. Gonzalez, *Clustering to minimize the maximum intercluster distance*, Theoret. Comput.
  Sci. 38 (1985), 293-306.
* D. P. Williamson and D. B. Shmoys, *The Design of Approximation Algorithms*, Cambridge
  University Press, 2011, Theorem 2.3.
-/

public section

namespace List

variable {V : Type*}

section Dist

variable [Dist V]

/-- A list `l` is farthest-first when, for each position `i ≥ 1`, every point `x` has an entry
`c` before position `i` with `dist x c ≤ dist l[i] c'` for every entry `c'` before position `i`:
the distance from `l[i]` to the set of earlier entries is the largest possible. The first entry
is arbitrary. -/
def IsFarthestFirst (l : List V) : Prop :=
  ∀ (i : ℕ) (hi : i < l.length), 0 < i →
    ∀ x, ∃ c ∈ l.take i, ∀ c' ∈ l.take i, dist x c ≤ dist l[i] c'

/-- The defining property of a farthest-first list. -/
theorem isFarthestFirst_iff {l : List V} :
    l.IsFarthestFirst ↔ ∀ (i : ℕ) (hi : i < l.length), 0 < i →
      ∀ x, ∃ c ∈ l.take i, ∀ c' ∈ l.take i, dist x c ≤ dist l[i] c' :=
  Iff.rfl

/-- The empty list is farthest-first. -/
@[simp]
theorem isFarthestFirst_nil : ([] : List V).IsFarthestFirst := by
  simp [IsFarthestFirst]

/-- A list of one entry is farthest-first. -/
@[simp]
theorem isFarthestFirst_singleton (a : V) : [a].IsFarthestFirst := by
  intro i hi h0
  simp only [length_singleton] at hi
  omega

/-- `l ++ [z]` is farthest-first exactly when `l` is farthest-first and, if `l` is nonempty,
every point `x` has an entry `c` of `l` with `dist x c ≤ dist z c'` for every entry `c'` of
`l`. -/
theorem isFarthestFirst_append_singleton_iff {l : List V} {z : V} :
    (l ++ [z]).IsFarthestFirst ↔ l.IsFarthestFirst ∧
      (l ≠ [] → ∀ x, ∃ c ∈ l, ∀ c' ∈ l, dist x c ≤ dist z c') := by
  constructor
  · intro h
    refine ⟨fun i hi h0 x ↦ ?_, fun hl x ↦ ?_⟩
    · obtain ⟨c, hc, hc'⟩ := h i (by simp only [length_append, length_singleton]; omega) h0 x
      rw [List.take_append_of_le_length hi.le] at hc hc'
      refine ⟨c, hc, fun c' h' ↦ ?_⟩
      simpa [List.getElem_append_left hi] using hc' c' h'
    · obtain ⟨c, hc, hc'⟩ := h l.length (by simp) (List.length_pos_iff.2 hl) x
      simp only [List.take_left', List.getElem_concat_length] at hc hc'
      exact ⟨c, hc, hc'⟩
  · rintro ⟨hl, hz⟩ i hi h0 x
    simp only [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · obtain ⟨c, hc, hc'⟩ := hl i hi h0 x
      rw [List.take_append_of_le_length hi.le]
      refine ⟨c, hc, fun c' h' ↦ ?_⟩
      simpa [List.getElem_append_left hi] using hc' c' h'
    · simpa using hz (List.length_pos_iff.1 h0) x

/-- An initial segment of a farthest-first list is farthest-first. -/
theorem IsFarthestFirst.take {l : List V} (hl : l.IsFarthestFirst) (n : ℕ) :
    (l.take n).IsFarthestFirst := by
  intro i hi h0 x
  simp only [List.length_take, lt_min_iff] at hi
  obtain ⟨c, hc, hc'⟩ := hl i hi.2 h0 x
  simp only [List.take_take, min_eq_left hi.1.le, List.getElem_take]
  exact ⟨c, hc, hc'⟩

/-- If every entry of a farthest-first list `l` is at distance more than `s` from a point `x`,
then any two entries at different positions are at distance more than `s`. -/
private theorem IsFarthestFirst.lt_dist_getElem {l : List V} (hl : l.IsFarthestFirst) {x : V}
    {s : ℝ} (hx : ∀ c ∈ l, s < dist x c) {i j : ℕ} (hij : i < j) (hj : j < l.length) :
    s < dist l[j] l[i] := by
  obtain ⟨c, hc, hc'⟩ := hl j hj (by omega) x
  have hi : l[i] ∈ l.take j := List.mem_take_iff_getElem.2 ⟨i, by omega, by simp⟩
  exact (hx c (List.mem_of_mem_take hc)).trans_le (hc' _ hi)

end Dist

variable [PseudoMetricSpace V]

/-- The approximation guarantee of the farthest-first traversal (Gonzalez): if at most
`l.length` points `C` cover the space with radius `r`, then the entries of a farthest-first
list `l` cover it with radius `2 * r`. -/
theorem IsFarthestFirst.exists_dist_le_two_mul {l : List V} (hl : l.IsFarthestFirst)
    {C : Finset V} (hC : C.card ≤ l.length) {r : ℝ} (hr : ∀ x, ∃ c ∈ C, dist x c ≤ r) (x : V) :
    ∃ c ∈ l, dist x c ≤ 2 * r := by
  by_contra! hx
  -- The point `x` together with the entries of `l`, indexed by `Option (Fin l.length)`.
  let p : Option (Fin l.length) → V := fun a ↦ a.elim x fun i ↦ l[(i : ℕ)]
  choose g hgC hg using fun a ↦ hr (p a)
  obtain ⟨a, b, hab, he⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun a ↦ (⟨g a, hgC a⟩ : C))
    (by simpa using Nat.lt_succ_of_le hC)
  have hpq : dist (p a) (p b) ≤ 2 * r := by
    have ha := hg a
    rw [show g a = g b from congrArg Subtype.val he] at ha
    linarith [hg b, dist_triangle_right (p a) (p b) (g b)]
  -- Two different ones of these `l.length + 1` points are at distance more than `2 * r`:
  -- by `hx` when one of them is `x`, and by `lt_dist_getElem` when both are entries of `l`.
  rcases a with _ | i <;> rcases b with _ | j <;> simp only [p, Option.elim] at hpq
  · exact hab rfl
  · exact (hx _ (List.getElem_mem _)).not_ge hpq
  · exact (hx _ (List.getElem_mem _)).not_ge (by rwa [dist_comm] at hpq)
  · rcases lt_or_gt_of_ne (fun h ↦ hab (congrArg some h)) with hij | hij
    · exact (hl.lt_dist_getElem hx (Fin.lt_def.1 hij) j.isLt).not_ge (by rwa [dist_comm] at hpq)
    · exact (hl.lt_dist_getElem hx (Fin.lt_def.1 hij) i.isLt).not_ge hpq

end List
