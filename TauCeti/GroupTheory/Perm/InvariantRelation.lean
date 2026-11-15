/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Defs

/-!
# Invariants and rigidity of permutations preserving a binary relation

Let `g : Equiv.Perm α` preserve a binary valuation or relation `r` in the sense that
`∀ x y, r (g x) (g y) = r x y`, and suppose `g` fixes every anchor in a list `l : List α`. Two
finite invariants of a point `x : α` are then preserved by `g`:

* `TauCeti.relationProfile r l x`, the list of pairs `(decide (x = z), r z x)` for `z ∈ l`
  (`TauCeti.relationProfile_apply`). Recording `decide (x = z)` alongside `r z x` separates fixed
  anchors from other points with the same values of `r`.
* `TauCeti.commonNeighborCount r l x`, on a finite type `α` and for `Bool`-valued `r`, the number of
  points `y` with `r x y = true` and `r z y = true` for every `z ∈ l`
  (`TauCeti.commonNeighborCount_apply`). Using a `Bool`-valued relation avoids `DecidableRel`
  dictionary overhead during kernel evaluation.

Iterating profile uniqueness along a rank function `rank : α → ℕ` yields base-rigidity criteria for
automorphisms of `r`: if every non-seed point `x ∉ s` is uniquely determined by its profile relative
to anchors of strictly smaller rank, then fixing all seeds of rank `< n` fixes all points of rank
`< n` (`TauCeti.apply_eq_self_of_relationProfile_unique`), and fixing all seeds forces `g = 1`
(`TauCeti.eq_one_of_relationProfile_unique`).

## Main declarations

* `TauCeti.relationProfile`, `TauCeti.relationProfile_apply`: anchor profiles of a binary valuation
  and their invariance under relation-preserving permutations fixing the anchors.
* `TauCeti.apply_eq_self_of_relationProfile_unique`, `TauCeti.eq_one_of_relationProfile_unique`:
  ranked anchor-profile rigidity below a rank bound and on the whole carrier.
* `TauCeti.commonNeighborCount`, `TauCeti.commonNeighborCount_apply`: common-neighbor counts for a
  `Bool`-valued binary relation on a finite type and their invariance.
-/

public section

namespace TauCeti

/-- The profile of `x` relative to a binary valuation `r` and an ordered list `l` of anchor
points: for each `z ∈ l`, whether `x = z` together with `r z x`. Recording equality alongside
`r z x` distinguishes fixed anchors from other points sharing the same relation pattern. The body
is exposed so that `decide` can evaluate profiles in importing modules. -/
@[expose] def relationProfile {α β : Type*} [DecidableEq α] (r : α → α → β) (l : List α)
    (x : α) : List (Bool × β) :=
  l.map fun z ↦ (decide (x = z), r z x)

/-- Unfolding `relationProfile` as a map over the list of anchors. -/
theorem relationProfile_def {α β : Type*} [DecidableEq α] (r : α → α → β) (l : List α) (x : α) :
    relationProfile r l x = l.map fun z ↦ (decide (x = z), r z x) := (rfl)

/-- The profile relative to the empty anchor list is empty. -/
@[simp]
theorem relationProfile_nil {α β : Type*} [DecidableEq α] (r : α → α → β) (x : α) :
    relationProfile r [] x = [] := (rfl)

/-- Extending the anchor list by `z` prepends `(decide (x = z), r z x)` to the profile. -/
@[simp]
theorem relationProfile_cons {α β : Type*} [DecidableEq α] (r : α → α → β) (z : α) (l : List α)
    (x : α) :
    relationProfile r (z :: l) x = (decide (x = z), r z x) :: relationProfile r l x := (rfl)

/-- A permutation preserving `r` and fixing every anchor in `l` preserves `relationProfile r l`. -/
theorem relationProfile_apply {α β : Type*} [DecidableEq α] {r : α → α → β} {g : Equiv.Perm α}
    (hg : ∀ x y, r (g x) (g y) = r x y) {l : List α} (hl : ∀ z ∈ l, g z = z) (x : α) :
    relationProfile r l (g x) = relationProfile r l x := by
  apply List.map_congr_left
  intro z hz
  have hfix := hl z hz
  have heq : (g x = z) ↔ x = z :=
    ⟨fun h ↦ g.injective (h.trans hfix.symm), fun h ↦ h ▸ hfix⟩
  exact Prod.ext (Bool.decide_congr heq) (by simpa only [hfix] using hg z x)

/-- **Ranked anchor-profile rigidity below a rank bound.** Let `g` be a permutation preserving `r`.
Suppose every non-seed point `x ∉ s` is uniquely determined by its `r`-profile relative to a list
`anchors x` of points of strictly smaller rank. If `g` fixes every seed point in `s` of rank less
than `n`, then `g` fixes every point of rank less than `n`. -/
theorem apply_eq_self_of_relationProfile_unique {α β : Type*} [DecidableEq α] {r : α → α → β}
    {g : Equiv.Perm α} (hg : ∀ x y, r (g x) (g y) = r x y) {s : Set α} {rank : α → ℕ}
    {anchors : α → List α} (hrank : ∀ x ∉ s, ∀ z ∈ anchors x, rank z < rank x)
    (huniq : ∀ x ∉ s, ∀ y,
      relationProfile r (anchors x) y = relationProfile r (anchors x) x → y = x)
    {n : ℕ} (hseed : ∀ x ∈ s, rank x < n → g x = x) {x : α} (hx : rank x < n) :
    g x = x := by
  have h : ∀ m < n, ∀ y, rank y = m → g y = y := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro hmn y hym
      by_cases hys : y ∈ s
      · exact hseed y hys (hym ▸ hmn)
      · apply huniq y hys
        apply relationProfile_apply hg
        intro z hz
        have hlt := hrank y hys z hz
        rw [hym] at hlt
        exact ih _ hlt (hlt.trans hmn) z rfl
  exact h (rank x) hx x rfl

/-- **Ranked anchor-profile base rigidity.** Let `g` be a permutation preserving `r`. If every
non-seed point `x ∉ s` is uniquely determined by its `r`-profile relative to a list `anchors x` of
points of strictly smaller rank, and `g` fixes every seed point in `s`, then `g = 1`. -/
theorem eq_one_of_relationProfile_unique {α β : Type*} [DecidableEq α] {r : α → α → β}
    {g : Equiv.Perm α} (hg : ∀ x y, r (g x) (g y) = r x y) {s : Set α} {rank : α → ℕ}
    {anchors : α → List α} (hrank : ∀ x ∉ s, ∀ z ∈ anchors x, rank z < rank x)
    (huniq : ∀ x ∉ s, ∀ y,
      relationProfile r (anchors x) y = relationProfile r (anchors x) x → y = x)
    (hseed : ∀ x ∈ s, g x = x) :
    g = 1 := by
  ext x
  exact apply_eq_self_of_relationProfile_unique hg hrank huniq
    (fun y hy _ ↦ hseed y hy) (Nat.lt_succ_self _)

/-- The number of points `y` of a finite type `α` satisfying `r x y = true` together with
`r z y = true` for every anchor `z ∈ l`. In a directed or undirected graph encoded by `r`, this is
the number of common out-neighbors of `x` and the anchors in `l`. The body is exposed so that
`decide` can evaluate counts in importing modules. -/
@[expose] def commonNeighborCount {α : Type*} [Fintype α] (r : α → α → Bool) (l : List α)
    (x : α) : ℕ :=
  (Finset.univ.filter fun y ↦ r x y = true ∧ ∀ z ∈ l, r z y = true).card

/-- Unfolding `commonNeighborCount` as the cardinality of the filtered universe. -/
theorem commonNeighborCount_def {α : Type*} [Fintype α] (r : α → α → Bool) (l : List α) (x : α) :
    commonNeighborCount r l x =
      (Finset.univ.filter fun y ↦ r x y = true ∧ ∀ z ∈ l, r z y = true).card := (rfl)

/-- A permutation preserving `r` and fixing every anchor in `l` preserves
`commonNeighborCount r l`. -/
theorem commonNeighborCount_apply {α : Type*} [Fintype α] {r : α → α → Bool} {g : Equiv.Perm α}
    (hg : ∀ x y, r (g x) (g y) = r x y) {l : List α} (hl : ∀ z ∈ l, g z = z) (x : α) :
    commonNeighborCount r l (g x) = commonNeighborCount r l x := by
  symm
  apply Finset.card_equiv g
  intro y
  have h (z : α) (hz : z ∈ l) : r z (g y) = r z y := by
    simpa only [hl z hz] using hg z y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hg]
  exact and_congr_right fun _ ↦ forall_congr' fun z ↦ forall_congr' fun hz ↦ by rw [h z hz]

end TauCeti
