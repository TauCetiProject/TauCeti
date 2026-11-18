/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Sym.Sym2
public import TauCeti.Data.List.FindIdx
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# First-visit canonical labeling of walks

Relabeling the vertices of a finite walk does not change its combinatorial shape. The canonical
label of a vertex is the time at which it first appears. Thus isomorphic walks have the same
canonical labeling, and a walk already carrying these labels is the unique normalized
representative of its relabeling class.

## Main results

* `firstVisitCanonical`: replace each vertex by its first occurrence index.
* `firstVisitCanonical_map`: the canonical labeling is invariant under injective relabeling.
* `firstVisitCanonical_getElem_eq_iff`: canonical labels preserve and reflect equality of
  visited vertices.
* `firstVisitCanonical_closed_iff`: canonicalization preserves closedness of a nonempty walk.
* `firstVisitCanonical_idempotent`: canonicalization is already normalized.
* `eq_firstVisitCanonical_of_isFirstVisitLabeled`: the normalized representative is unique.
* `TauCeti.TreeWalk.canonicalWalk`: first-visit labels of a finite path, padded by zero.
* `TauCeti.TreeWalk.card_fixed_canonicalWalk`: fixed labels count the distinct visited vertices.

This is the finite combinatorial prerequisite used by the Wigner moment method to group closed
walks by their vertex-relabeled shapes.
-/

public section

namespace List

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Replace every vertex of a finite walk by the index of its first occurrence. -/
def firstVisitCanonical (w : List α) : List ℕ :=
  w.map fun x => w.idxOf x

@[simp]
theorem firstVisitCanonical_length (w : List α) :
    (firstVisitCanonical w).length = w.length := by
  simp [firstVisitCanonical]

theorem firstVisitCanonical_getElem (w : List α) {i : ℕ} (hi : i < w.length) :
    (firstVisitCanonical w)[i]'(by simpa [firstVisitCanonical] using hi) =
      w.idxOf w[i] := by
  simp [firstVisitCanonical]

/-- Injectively relabeling the vertices of a walk leaves its first-visit labels unchanged. -/
theorem firstVisitCanonical_map (w : List α) (f : α → β)
    (hf : ∀ ⦃x y⦄, x ∈ w → y ∈ w → f x = f y → x = y) :
    firstVisitCanonical (w.map f) = firstVisitCanonical w := by
  apply List.ext_getElem (by simp [firstVisitCanonical])
  intro i hi₁ hi₂
  have hi₂' : i < w.length := by simpa using hi₂
  have himap : i < (w.map f).length := by simpa using hi₁
  rw [firstVisitCanonical_getElem (w.map f) himap, firstVisitCanonical_getElem w hi₂']
  simp only [List.getElem_map]
  exact idxOf_map_eq_of_injectiveOn w f hf (List.getElem_mem hi₂')

/-- The first-visit labels distinguish exactly the distinct vertices of the walk. -/
theorem firstVisitCanonical_getElem_eq_iff (w : List α) {i j : ℕ}
    (hi : i < w.length) (hj : j < w.length) :
    (firstVisitCanonical w)[i]'(by simpa [firstVisitCanonical] using hi) =
      (firstVisitCanonical w)[j]'(by simpa [firstVisitCanonical] using hj) ↔
        w[i] = w[j] := by
  rw [firstVisitCanonical_getElem _ hi, firstVisitCanonical_getElem _ hj]
  exact List.idxOf_inj (List.getElem_mem hi)

/-- A nonempty walk is closed exactly when its first-visit labeling is closed. -/
theorem firstVisitCanonical_closed_iff (w : List α) (hne : w ≠ []) :
    w.head hne = w.getLast hne ↔
      (firstVisitCanonical w).head (by simpa [firstVisitCanonical] using hne) =
        (firstVisitCanonical w).getLast (by simpa [firstVisitCanonical] using hne) := by
  have hmem : w.head hne ∈ w := List.head_mem hne
  constructor
  · intro h
    simpa [firstVisitCanonical] using congrArg (fun x => w.idxOf x) h
  · intro h
    have h' : w.idxOf (w.head hne) = w.idxOf (w.getLast hne) := by
      simpa [firstVisitCanonical] using h
    exact (List.idxOf_inj hmem).1 h'

/-- A walk of natural-number labels is first-visit labeled when each label is its first time of
appearance. -/
def IsFirstVisitLabeled (w : List ℕ) : Prop :=
  ∀ i (hi : i < w.length), w[i] = w.idxOf w[i]

/-- A list is fixed by canonicalization exactly when it already uses first-visit labels. -/
theorem firstVisitCanonical_eq_self_iff_isFirstVisitLabeled (w : List ℕ) :
    firstVisitCanonical w = w ↔ IsFirstVisitLabeled w := by
  constructor
  · intro h i hi
    simpa [h] using firstVisitCanonical_getElem w hi
  · intro h
    apply List.ext_getElem (by simp [firstVisitCanonical])
    intro i hi₁ hi₂
    have hi₁' : i < w.length := by simpa using hi₁
    rw [firstVisitCanonical_getElem w hi₁']
    exact (h i hi₂).symm

/-- Canonicalizing a walk that is already canonically labeled has no further effect. -/
@[simp]
theorem firstVisitCanonical_idempotent (w : List α) :
    firstVisitCanonical (firstVisitCanonical w) = firstVisitCanonical w := by
  exact firstVisitCanonical_map w (fun x => w.idxOf x) (by
    intro x y hx _ hxy
    exact (List.idxOf_inj hx).1 hxy)

/-- Every first-visit canonical labeling is first-visit labeled. -/
@[simp]
theorem firstVisitCanonical_isFirstVisitLabeled (w : List α) :
    IsFirstVisitLabeled (firstVisitCanonical w) :=
  (firstVisitCanonical_eq_self_iff_isFirstVisitLabeled _).1
    (firstVisitCanonical_idempotent w)

/-- The normalized representative is unique: any injective relabeling of a walk that already
uses first-visit labels is its canonical form. -/
theorem eq_firstVisitCanonical_of_isFirstVisitLabeled (w : List α) (f : α → ℕ)
    (hf : ∀ ⦃x y⦄, x ∈ w → y ∈ w → f x = f y → x = y)
    {v : List ℕ} (hv : v = w.map f) (hvis : IsFirstVisitLabeled v) :
    v = firstVisitCanonical w := by
  calc
    v = firstVisitCanonical v :=
      (firstVisitCanonical_eq_self_iff_isFirstVisitLabeled v).2 hvis |>.symm
    _ = firstVisitCanonical (w.map f) := congrArg firstVisitCanonical hv
    _ = firstVisitCanonical w := firstVisitCanonical_map w f hf

end List

namespace TauCeti.TreeWalk

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β] {n : ℕ}

/-- First-visit labels of a finite path, extended by zero after its endpoint. -/
def canonicalWalk (w : Fin (n + 1) → α) (i : ℕ) : ℕ :=
  ((List.ofFn w).firstVisitCanonical)[i]?.getD 0

/-- At a time within the path, the canonical label is the first occurrence index. -/
theorem canonicalWalk_apply (w : Fin (n + 1) → α) {i : ℕ} (hi : i < n + 1) :
    canonicalWalk w i = (List.ofFn w).idxOf (w ⟨i, hi⟩) := by
  rw [canonicalWalk, List.getElem?_eq_getElem (by
    rw [List.firstVisitCanonical_length, List.length_ofFn]
    exact hi), Option.getD_some,
    List.firstVisitCanonical_getElem _ (by simpa only [List.length_ofFn] using hi),
    List.getElem_ofFn]

/-- The canonical path is padded by zeros after its endpoint. -/
@[simp] theorem canonicalWalk_eq_zero (w : Fin (n + 1) → α) {i : ℕ} (hi : n < i) :
    canonicalWalk w i = 0 := by
  rw [canonicalWalk, List.getElem?_eq_none (by
    rw [List.firstVisitCanonical_length, List.length_ofFn]
    omega)]
  rfl

/-- Canonical labels preserve and reflect equality of vertices. -/
@[simp] theorem canonicalWalk_eq_iff (w : Fin (n + 1) → α) (i j : Fin (n + 1)) :
    canonicalWalk w i = canonicalWalk w j ↔ w i = w j := by
  rw [canonicalWalk_apply w i.isLt, canonicalWalk_apply w j.isLt]
  exact List.idxOf_inj (List.mem_ofFn.mpr ⟨i, rfl⟩)

/-- Injective relabeling leaves the padded canonical walk unchanged. -/
@[simp] theorem canonicalWalk_comp (w : Fin (n + 1) → α) (f : α → β)
    (hf : Set.InjOn f (Set.range w)) :
    canonicalWalk (f ∘ w) = canonicalWalk w := by
  funext i
  simp only [canonicalWalk, ← List.map_ofFn]
  rw [List.firstVisitCanonical_map _ f (by
    intro x y hx hy hxy
    exact hf (List.mem_ofFn.mp hx) (List.mem_ofFn.mp hy) hxy)]

/-- A first occurrence cannot be later than the time of the current visit. -/
theorem canonicalWalk_le (w : Fin (n + 1) → α) (i : ℕ) : canonicalWalk w i ≤ i := by
  by_cases hi : i < n + 1
  · rw [canonicalWalk_apply w hi]
    by_contra h
    have hnot := List.not_of_lt_findIdx (xs := List.ofFn w)
      (p := fun x => x == w ⟨i, hi⟩) (i := i) (by simpa [List.idxOf] using h)
    simp only [List.getElem_ofFn, beq_self_eq_true, Bool.true_eq_false] at hnot
  · rw [canonicalWalk_eq_zero w (by omega)]
    exact Nat.zero_le _

/-- A step which discovers a new vertex cannot be a loop. -/
theorem ne_of_canonicalWalk_succ_eq (v : Fin (n + 1) → α) (i : Fin n)
    (hi : canonicalWalk v i.succ = i.succ) : v i.castSucc ≠ v i.succ := by
  have hle := canonicalWalk_le v i
  intro he
  have hc := (canonicalWalk_eq_iff v i.castSucc i.succ).mpr he
  simp only [Fin.val_castSucc, Fin.val_succ] at hc hi
  omega

/-- Distinct steps which discover new vertices traverse distinct unordered edges. -/
theorem injOn_edge_setOf_canonicalWalk_succ_eq (v : Fin (n + 1) → α) :
    Set.InjOn (fun i : Fin n ↦ s(v i.castSucc, v i.succ))
      {i | canonicalWalk v i.succ = i.succ} := by
  intro i hi j hj hij
  have hc : s(canonicalWalk v i.castSucc, canonicalWalk v i.succ) =
      s(canonicalWalk v j.castSucc, canonicalWalk v j.succ) := by
    simpa only [Sym2.eq_iff, canonicalWalk_eq_iff] using hij
  have hli := canonicalWalk_le v i
  have hlj := canonicalWalk_le v j
  simp only [Set.mem_ofPred_eq, Sym2.eq_iff, Fin.val_castSucc, Fin.val_succ] at hc hi hj
  apply Fin.ext
  omega

/-- The canonical walk starts at zero. -/
@[simp] theorem canonicalWalk_zero (w : Fin (n + 1) → α) : canonicalWalk w 0 = 0 :=
  Nat.eq_zero_of_le_zero (canonicalWalk_le w 0)

/-- First-visit labels are fixed points of the canonical walk. -/
@[simp] theorem canonicalWalk_idem (w : Fin (n + 1) → α) (i : ℕ) :
    canonicalWalk w (canonicalWalk w i) = canonicalWalk w i := by
  by_cases hi : i < n + 1
  · have hc : canonicalWalk w i < n + 1 := (canonicalWalk_le w i).trans_lt hi
    rw [canonicalWalk_apply w hc]
    have hget : w ⟨canonicalWalk w i, hc⟩ = w ⟨i, hi⟩ := by
      have := List.getElem_idxOf (xs := List.ofFn w) (x := w ⟨i, hi⟩)
        (by simpa only [List.length_ofFn, canonicalWalk_apply w hi] using hc)
      simpa only [canonicalWalk_apply w hi, List.getElem_ofFn] using this
    rw [hget, ← canonicalWalk_apply w hi]
  · have hz : canonicalWalk w i = 0 := canonicalWalk_eq_zero w (by omega)
    simp only [hz, canonicalWalk_zero]

/-- Fixed first-visit labels are in bijection with the distinct vertices of the original path. -/
theorem card_fixed_canonicalWalk (w : Fin (n + 1) → α) :
    #{i ∈ range (n + 1) | canonicalWalk w i = i} = #(univ.image w) := by
  let c : Fin (n + 1) → ℕ := fun i => canonicalWalk w i
  have hfix : {i ∈ range (n + 1) | canonicalWalk w i = i} = univ.image c := by
    ext i
    simp only [mem_filter, mem_range, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨hi, h⟩
      exact ⟨⟨i, hi⟩, h⟩
    · rintro ⟨j, rfl⟩
      exact ⟨(canonicalWalk_le w j).trans_lt j.isLt, canonicalWalk_idem w j⟩
  rw [hfix]
  have himage : univ.image c = (univ.image w).image (fun x => (List.ofFn w).idxOf x) := by
    simp only [image_image]
    congr 1
    funext i
    exact canonicalWalk_apply w i.isLt
  rw [himage]
  apply card_image_of_injOn
  intro x hx y _ hxy
  obtain ⟨i, -, rfl⟩ := mem_image.mp hx
  exact (List.idxOf_inj (List.mem_ofFn.mpr ⟨i, rfl⟩)).1 hxy

/-- The discovery steps of a path count its distinct vertices other than the initial vertex. -/
theorem card_filter_canonicalWalk_succ_eq (v : Fin (n + 1) → α) :
    #{i : Fin n | canonicalWalk v i.succ = i.succ} = #(univ.image v) - 1 := by
  have h := card_fixed_canonicalWalk v
  rw [card_filter, sum_range_succ', ← Fin.sum_univ_eq_sum_range] at h
  simp only [canonicalWalk_zero, ite_true] at h
  simp only [card_filter, Fin.val_succ]
  omega

end TauCeti.TreeWalk
