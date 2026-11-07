/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.List.FindIdx

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
  have hi₁' : i < w.length := by simpa using hi₁
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
    intro x y hx hy hxy
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
