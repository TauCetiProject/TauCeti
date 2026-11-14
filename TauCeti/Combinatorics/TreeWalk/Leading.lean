/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TreeWalk.Basic
public import TauCeti.Combinatorics.TreeWalk.Canonical
public import TauCeti.Combinatorics.TreeWalk.Relabeling
public import TauCeti.Combinatorics.TraceWord.Counting

/-!
# Leading trace words as canonical tree walks

A cyclic word of length `2 * m` with no singleton unordered edge and `m + 1` vertices is a
leading word in the Wigner moment expansion. Labeling each vertex by its first visit turns it
into a closed tree walk. Combining the Dyck-word bijection for canonical closed tree walks with
the relabeling equivalence counts double-traversal closed paths and leading cyclic trace words on
any finite vertex set as `(Fintype.card α).descFactorial (m + 1) * catalan m`.

`canonicalWalk` extends the first-visit canonical labeling of a finite path by zero after its
endpoint. Equality of vertices, and hence equality of unordered edges, is preserved and reflected.
`isTreeWalk_canonicalWalk_iff` and `isTreeWalk_canonicalWalk_cyclic_iff` characterize when a path
or cyclic word canonicalizes to a closed tree walk, while `IsTreeWalk.edge_ne_of_eq_zero` shows
that returning to the root partitions a tree walk into edge-disjoint excursions.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemma 2.1.6.
-/

public section

open Finset

namespace TauCeti.TreeWalk

private theorem walkOf_eq_zero_or_add_one_le {s : ℕ → Bool} {m : ℕ} (hm : walkOf s m = 0) :
    ∀ j, m ≤ j → walkOf s j = 0 ∨ m + 1 ≤ walkOf s j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hmj
    rcases eq_or_lt_of_le hmj with rfl | hlt
    · exact Or.inl hm
    · cases j with
      | zero => omega
      | succ t =>
        cases hst : s t
        · rw [walkOf_down s hst]
          rcases ih t (Nat.lt_succ_self t) (by omega) with ht0 | ht1
          · simp [ht0, walkOf_zero]
          · have hle := walkOf_le s t
            exact ih (walkOf s t - 1) (by omega) (by omega)
        · exact Or.inr (by rw [walkOf_up s hst]; omega)

/-- When a closed tree walk visits the root at time `m`, no unordered edge traversed before `m`
coincides with any unordered edge traversed from `m` onwards within the walk interval. -/
theorem IsTreeWalk.edge_ne_of_eq_zero {k m : ℕ} {w : ℕ → ℕ} (hw : IsTreeWalk k w)
    (hwm : w m = 0) {i j : ℕ} (hi : i < m) (hmj : m ≤ j) (hj : j < 2 * k) :
    s(w i, w (i + 1)) ≠ s(w j, w (j + 1)) := by
  intro heq
  have hs : walkOf (upSteps k w) m = 0 := (hw.walkOf_upSteps m (by omega)).trans hwm
  have _ : w i ≤ m := (hw.le_self i (by omega)).trans (by omega)
  have _ : w (i + 1) ≤ m := (hw.le_self (i + 1) (by omega)).trans (by omega)
  have _ : w j = 0 ∨ m + 1 ≤ w j := by
    simpa only [hw.walkOf_upSteps j (by omega)] using walkOf_eq_zero_or_add_one_le hs j hmj
  have _ : w (j + 1) = 0 ∨ m + 1 ≤ w (j + 1) := by
    simpa only [hw.walkOf_upSteps (j + 1) (by omega)] using
      walkOf_eq_zero_or_add_one_le hs (j + 1) (by omega)
  have hj0 : w j = 0 ∧ w (j + 1) = 0 := by
    rcases Sym2.eq_iff.mp heq with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  obtain ⟨t, -, -, hjt⟩ := hw.exists_up_edge hj
  rw [hj0.1, hj0.2, Sym2.eq_iff] at hjt
  omega

private theorem canonicalWalk_eq_of_le_of_idem {k : ℕ} (v : Fin (k + 1) → ℕ)
    (hle : ∀ i, v i ≤ i.val) (hidem : ∀ i (h : v i < k + 1), v ⟨v i, h⟩ = v i)
    (i : Fin (k + 1)) : canonicalWalk v i = v i := by
  have hc : canonicalWalk v i < k + 1 := (canonicalWalk_le v i).trans_lt i.isLt
  have h1 : v ⟨canonicalWalk v i, hc⟩ = v i :=
    (canonicalWalk_eq_iff v ⟨canonicalWalk v i, hc⟩ i).mp (canonicalWalk_idem v i)
  have hj : v i < k + 1 := (hle i).trans_lt i.isLt
  have h2 : canonicalWalk v (v i) = canonicalWalk v i :=
    (canonicalWalk_eq_iff v ⟨v i, hj⟩ i).mpr (hidem i hj)
  exact le_antisymm (h2.symm.trans_le (canonicalWalk_le v (v i))) (h1 ▸ hle ⟨_, hc⟩)

/-- Restricting a canonical closed tree walk to its path interval and taking first-visit labels
recovers the same padded walk. -/
@[simp] theorem canonicalWalk_closedTreeWalk {m : ℕ} (c : ClosedTreeWalk m) :
    canonicalWalk (fun i : Fin (2 * m + 1) ↦ c.1 i) = c.1 := by
  funext i
  by_cases hi : i < 2 * m + 1
  · exact canonicalWalk_eq_of_le_of_idem (fun j : Fin (2 * m + 1) ↦ c.1 j)
      (fun j ↦ c.2.1.le_self j (by omega))
      (fun j _ ↦ c.2.1.idem (by omega)) ⟨i, hi⟩
  · rw [canonicalWalk_eq_zero _ (by omega), c.2.2 i (by omega)]

/-- A canonical closed tree walk of semilength `m` visits `m + 1` distinct vertices on its path
interval. -/
@[simp] theorem card_image_closedTreeWalk {m : ℕ} (c : ClosedTreeWalk m) :
    #(univ.image fun i : Fin (2 * m + 1) ↦ c.1 i) = m + 1 := by
  rw [← card_fixed_canonicalWalk, canonicalWalk_closedTreeWalk]
  exact c.2.1.card_vertices

variable {α : Type*} {m : ℕ}

/-- A cyclic word viewed as a path, with its initial vertex repeated at the endpoint. -/
def cyclicPath {k : ℕ} [NeZero k] (w : Fin k → α) : Fin (k + 1) → α :=
  fun i ↦ w (Fin.ofNat k i.val)

/-- Evaluate the path extension by reducing the index modulo the cyclic word's length. -/
theorem cyclicPath_apply {k : ℕ} [NeZero k] (w : Fin k → α) (i : Fin (k + 1)) :
    cyclicPath w i = w (Fin.ofNat k i.val) := (rfl)

@[simp] theorem cyclicPath_castSucc {k : ℕ} [NeZero k] (w : Fin k → α) (i : Fin k) :
    cyclicPath w i.castSucc = w i := by
  simp [cyclicPath]

@[simp] theorem cyclicPath_succ {k : ℕ} [NeZero k] (w : Fin k → α) (i : Fin k) :
    cyclicPath w i.succ = w (finRotate k i) := by
  apply congrArg w
  simp [finRotate_apply, Fin.ext_iff, Fin.val_add, Fin.ofNat_eq_cast, Nat.add_mod]

@[simp] theorem cyclicPath_zero {k : ℕ} [NeZero k] (w : Fin k → α) :
    cyclicPath w 0 = w 0 := by
  simp [cyclicPath]

@[simp] theorem cyclicPath_last {k : ℕ} [NeZero k] (w : Fin k → α) :
    cyclicPath w (Fin.last k) = w 0 := by
  simp [cyclicPath]

/-- Repeating the initial vertex at the endpoint preserves the set of visited vertices. -/
@[simp] theorem range_cyclicPath {k : ℕ} [NeZero k] (w : Fin k → α) :
    Set.range (cyclicPath w) = Set.range w := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.ofNat k i.val, (cyclicPath_apply w i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.castSucc, cyclicPath_castSucc w i⟩

/-- Vertex relabeling commutes with extending a cyclic word to a path. -/
theorem comp_cyclicPath {β : Type*} {k : ℕ} [NeZero k] (f : α → β) (w : Fin k → α) :
    f ∘ cyclicPath w = cyclicPath (f ∘ w) := (rfl)

/-- The path extension determines the original cyclic word. -/
@[simp] theorem cyclicPath_inj {k : ℕ} [NeZero k] {w₁ w₂ : Fin k → α} :
    cyclicPath w₁ = cyclicPath w₂ ↔ w₁ = w₂ := by
  constructor
  · intro h
    funext i
    simpa only [cyclicPath_castSucc] using congrFun h i.castSucc
  · rintro rfl
    rfl

variable [DecidableEq α]

@[simp] theorem image_cyclicPath {k : ℕ} [NeZero k] (w : Fin k → α) :
    univ.image (cyclicPath w) = univ.image w := by
  ext x
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.ofNat k i.val, by simp [cyclicPath]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.castSucc, cyclicPath_castSucc w i⟩

/-- A leading cyclic word has two occurrences of every edge when viewed as a path. -/
theorem card_edge_fiber_cyclicPath [NeZero m] (w : Fin (2 * m) → α)
    (h : ∀ i, ∃ j ≠ i, s(w j, w (finRotate (2 * m) j)) = s(w i, w (finRotate (2 * m) i)))
    (hv : #(univ.image w) = m + 1) (i : Fin (2 * m)) :
    #{j : Fin (2 * m) |
      s(cyclicPath w j.castSucc, cyclicPath w j.succ) =
        s(cyclicPath w i.castSucc, cyclicPath w i.succ)} = 2 := by
  simpa only [cyclicPath_castSucc, cyclicPath_succ] using
    (ne_and_card_edge_fiber_eq_two_of_no_singleton_edge_of_card_image_eq w h hv).2 i

private theorem card_edge_canonicalWalk (w : Fin (2 * m + 1) → α) (i : Fin (2 * m)) :
    #{j ∈ range (2 * m) |
      s(canonicalWalk w j, canonicalWalk w (j + 1)) =
        s(canonicalWalk w i, canonicalWalk w (i + 1))} =
      #{j : Fin (2 * m) | s(w j.castSucc, w j.succ) = s(w i.castSucc, w i.succ)} := by
  have hedge (a b : Fin (2 * m)) :
      s(canonicalWalk w a.castSucc, canonicalWalk w a.succ) =
        s(canonicalWalk w b.castSucc, canonicalWalk w b.succ) ↔
      s(w a.castSucc, w a.succ) = s(w b.castSucc, w b.succ) := by
    simp only [Sym2.eq_iff, canonicalWalk_eq_iff]
  apply card_bij (fun j hj => (⟨j, mem_range.mp (mem_filter.mp hj).1⟩ : Fin (2 * m)))
  · intro j hj
    simp only [mem_filter, mem_univ, true_and]
    apply (hedge _ i).mp
    simpa only [Fin.val_castSucc, Fin.val_succ] using (mem_filter.mp hj).2
  · intro _ _ _ _ h
    exact Fin.mk.inj h
  · intro j hj
    refine ⟨j.val, mem_filter.mpr ⟨mem_range.mpr j.isLt, ?_⟩, rfl⟩
    have hh := (hedge j i).mpr (mem_filter.mp hj).2
    simpa only [Fin.val_castSucc, Fin.val_succ] using hh

/-- A closed path with `m + 1` vertices and each unordered edge traversed twice becomes a tree
walk after first-visit relabeling. No order on the original vertex type is needed. -/
theorem isTreeWalk_canonicalWalk (w : Fin (2 * m + 1) → α)
    (hclosed : w (Fin.last (2 * m)) = w 0)
    (hv : #(univ.image w) = m + 1)
    (he : ∀ i : Fin (2 * m),
      #{j : Fin (2 * m) | s(w j.castSucc, w j.succ) = s(w i.castSucc, w i.succ)} = 2) :
    IsTreeWalk m (canonicalWalk w) where
  root := canonicalWalk_zero w
  closed := by
    rw [← canonicalWalk_zero w]
    exact (canonicalWalk_eq_iff w (Fin.last _) 0).2 hclosed
  le_self i _ := canonicalWalk_le w i
  card_vertices := (card_fixed_canonicalWalk w).trans hv
  card_edge i hi := (card_edge_canonicalWalk w ⟨i, hi⟩).trans (he ⟨i, hi⟩)

/-- A path of length `2 * m` canonicalizes to a closed tree walk if and only if it is closed,
visits `m + 1` vertices, and traverses every unordered edge twice. -/
theorem isTreeWalk_canonicalWalk_iff (w : Fin (2 * m + 1) → α) :
    IsTreeWalk m (canonicalWalk w) ↔
      w (Fin.last (2 * m)) = w 0 ∧ #(univ.image w) = m + 1 ∧
        ∀ i : Fin (2 * m),
          #{j : Fin (2 * m) | s(w j.castSucc, w j.succ) = s(w i.castSucc, w i.succ)} = 2 := by
  constructor
  · intro hw
    refine ⟨?_, (card_fixed_canonicalWalk w).symm.trans hw.card_vertices, fun i => ?_⟩
    · exact (canonicalWalk_eq_iff w (Fin.last _) 0).mp (hw.closed.trans hw.root.symm)
    · exact (card_edge_canonicalWalk w i).symm.trans (hw.card_edge i i.isLt)
  · rintro ⟨hclosed, hv, he⟩
    exact isTreeWalk_canonicalWalk w hclosed hv he

/-- A leading cyclic trace word becomes a tree walk under first-visit labeling. The endpoint
is added by cycling back to the initial vertex. The no-singleton condition alone, together with
the maximal vertex count, forces the required double traversal of every edge. The cyclic word
has positive length; the path theorem also covers the zero-step walk. -/
theorem isTreeWalk_canonicalWalk_cyclic [NeZero m] (w : Fin (2 * m) → α)
    (h : ∀ i, ∃ j ≠ i, s(w j, w (finRotate (2 * m) j)) = s(w i, w (finRotate (2 * m) i)))
    (hv : #(univ.image w) = m + 1) :
    IsTreeWalk m (canonicalWalk (cyclicPath w)) :=
  isTreeWalk_canonicalWalk (cyclicPath w) (by simp) (by simpa using hv)
    (card_edge_fiber_cyclicPath w h hv)

/-- A cyclic word of positive length `2 * m` canonicalizes via `cyclicPath` to a closed tree walk
if and only if it has no singleton unordered edge and visits `m + 1` vertices. -/
theorem isTreeWalk_canonicalWalk_cyclic_iff [NeZero m] (w : Fin (2 * m) → α) :
    IsTreeWalk m (canonicalWalk (cyclicPath w)) ↔
      (∀ i, ∃ j ≠ i, s(w j, w (finRotate (2 * m) j)) = s(w i, w (finRotate (2 * m) i))) ∧
        #(univ.image w) = m + 1 := by
  constructor
  · intro hw
    obtain ⟨-, hv, he⟩ := (isTreeWalk_canonicalWalk_iff (cyclicPath w)).mp hw
    refine ⟨fun i => ?_, by simpa using hv⟩
    have hi2 : #{j : Fin (2 * m) |
        s(w j, w (finRotate (2 * m) j)) = s(w i, w (finRotate (2 * m) i))} = 2 := by
      simpa only [cyclicPath_castSucc, cyclicPath_succ] using he i
    obtain ⟨j, hj, hji⟩ := exists_mem_ne (s := {j : Fin (2 * m) |
        s(w j, w (finRotate (2 * m) j)) = s(w i, w (finRotate (2 * m) i))})
      (by omega) i
    exact ⟨j, hji, (mem_filter.mp hj).2⟩
  · rintro ⟨h, hv⟩
    exact isTreeWalk_canonicalWalk_cyclic w h hv

private noncomputable def closedTreePathSigmaEquiv (m : ℕ) :
    {v : Fin (2 * m + 1) → α // IsTreeWalk m (canonicalWalk v)} ≃
      Σ c : ClosedTreeWalk m, {v : Fin (2 * m + 1) → α // canonicalWalk v = c.1} where
  toFun v := ⟨⟨canonicalWalk v.1, v.2, fun _ hi => canonicalWalk_eq_zero v.1 hi⟩, ⟨v.1, rfl⟩⟩
  invFun cv := ⟨cv.2.1, cv.2.2.symm ▸ cv.1.2.1⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨w, hw⟩, ⟨v, hv⟩⟩
    dsimp only at hv ⊢
    subst hv
    rfl

/-- On a finite vertex type `α`, there are `(Nat.card α).descFactorial (m + 1) * catalan m` paths
of length `2 * m` whose first-visit canonical walk is a closed tree walk. -/
theorem card_subtype_isTreeWalk_canonicalWalk [Finite α] (m : ℕ) :
    Nat.card {v : Fin (2 * m + 1) → α // IsTreeWalk m (canonicalWalk v)} =
      (Nat.card α).descFactorial (m + 1) * catalan m := by
  let _ : Fintype (ClosedTreeWalk m) := Fintype.ofEquiv _ (closedTreeWalkEquiv m).symm
  rw [Nat.card_congr (closedTreePathSigmaEquiv (α := α) m), Nat.card_sigma]
  have hfiber (c : ClosedTreeWalk m) :
      Nat.card {v : Fin (2 * m + 1) → α // canonicalWalk v = c.1} =
        (Nat.card α).descFactorial (m + 1) := by
    simpa only [canonicalWalk_closedTreeWalk, card_image_closedTreeWalk] using
      card_canonicalWalk_eq (α := α) (fun i : Fin (2 * m + 1) ↦ c.1 i)
  simp_rw [hfiber, sum_const, card_univ, ← Nat.card_eq_fintype_card, card_closedTreeWalk,
    smul_eq_mul, Nat.mul_comm]

/-- On a finite vertex set `α`, there are `(Fintype.card α).descFactorial (m + 1) * catalan m`
closed paths of length `2 * m` visiting `m + 1` vertices and traversing every unordered edge
twice. This includes the zero-step path at `m = 0`. -/
theorem card_filter_closed_tree_path [Fintype α] (m : ℕ) :
    #{v : Fin (2 * m + 1) → α |
      v (Fin.last (2 * m)) = v 0 ∧ #(univ.image v) = m + 1 ∧
        ∀ i : Fin (2 * m),
          #{j : Fin (2 * m) | s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2} =
      (Fintype.card α).descFactorial (m + 1) * catalan m := by
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card (α := α),
    ← card_subtype_isTreeWalk_canonicalWalk (α := α) m]
  refine Nat.card_congr ⟨fun v => ⟨v.1, ?_⟩, fun v => ⟨v.1, ?_⟩, fun _ => rfl, fun _ => rfl⟩
  · exact (isTreeWalk_canonicalWalk_iff v.1).mpr (mem_filter.mp v.2).2
  · exact mem_filter.mpr ⟨mem_univ _, (isTreeWalk_canonicalWalk_iff v.1).mp v.2⟩

/-- On a finite vertex set `α`, there are `(Fintype.card α).descFactorial (m + 1) * catalan m`
leading cyclic trace words of positive length `2 * m`, namely words with no singleton unordered
edge that visit `m + 1` vertices. -/
theorem card_filter_no_singleton_edge_and_card_image_eq [Fintype α] [NeZero m] :
    #{w : Fin (2 * m) → α |
      (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
        #(univ.image w) = m + 1} =
      (Fintype.card α).descFactorial (m + 1) * catalan m := by
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  have hcyc_of_closed {v : Fin (2 * m + 1) → α} (hclosed : v (Fin.last (2 * m)) = v 0) :
      cyclicPath (fun i : Fin (2 * m) => v i.castSucc) = v := by
    funext j
    refine Fin.lastCases ?_ (fun i => cyclicPath_castSucc _ i) j
    exact (cyclicPath_last _).trans hclosed.symm
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card (α := α),
    ← card_subtype_isTreeWalk_canonicalWalk (α := α) m]
  refine Nat.card_congr
    ⟨fun w => ⟨cyclicPath w.1, (isTreeWalk_canonicalWalk_cyclic_iff w.1).mpr (mem_filter.mp w.2).2⟩,
     fun v => ⟨fun i => v.1 i.castSucc, mem_filter.mpr ⟨mem_univ _,
       (isTreeWalk_canonicalWalk_cyclic_iff _).mp
         ((hcyc_of_closed ((isTreeWalk_canonicalWalk_iff v.1).mp v.2).1).symm ▸ v.2)⟩⟩,
     fun w => Subtype.ext (funext fun i => cyclicPath_castSucc w.1 i),
     fun v => Subtype.ext (hcyc_of_closed ((isTreeWalk_canonicalWalk_iff v.1).mp v.2).1)⟩

end TauCeti.TreeWalk
