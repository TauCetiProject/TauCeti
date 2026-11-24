/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Pi

/-!
# Dependent functions on a disjoint union of finite sets

For disjoint finite sets `s` and `t`, Mathlib's `Equiv.piFinsetUnion` identifies pairs of
dependent functions on `s` and on `t` with dependent functions on `s ∪ t`. This file describes it
through the restrictions `Finset.restrict₂` to the two pieces: a function on `s ∪ t` is determined
by its two restrictions (`Finset.restrict₂_union_ext`), restricting twice is restricting once
(`Finset.restrict₂_restrict₂`), the restrictions of
`Equiv.piFinsetUnion π h (f, g)` are `f` and `g`, and the inverse equivalence takes the two
restrictions (`Equiv.piFinsetUnion_symm_apply`).

The identification is associative: gluing `f`, `g` and `k` on pairwise disjoint `s`, `t` and `u`
as `f` with the gluing of `g` and `k`, or as the gluing of `f` and `g` with `k`, gives the same
function once `s ∪ (t ∪ u)` is identified with `(s ∪ t) ∪ u`
(`Equiv.restrict₂_piFinsetUnion_assoc`).

## Main results

* `Finset.restrict₂_union_ext`: a function on `s ∪ t` is determined by its restrictions.
* `Equiv.restrict₂_piFinsetUnion_left` and `Equiv.restrict₂_piFinsetUnion_right`: the two
  restrictions of a glued function.
* `Equiv.piFinsetUnion_symm_apply`: the inverse of `Equiv.piFinsetUnion` takes restrictions.
* `Equiv.restrict₂_piFinsetUnion_assoc`: associativity of gluing.
-/

public section

namespace Finset

variable {ι : Type*} {π : ι → Type*} {s t u : Finset ι}

/-- Restricting to a finite set itself is the identity. -/
@[simp]
theorem restrict₂_refl : restrict₂ (π := π) (subset_refl s) = id :=
  (rfl)

/-- Restricting from `u` to `t` and then to `s` is restricting from `u` to `s`. -/
@[simp]
theorem restrict₂_restrict₂ (hst : s ⊆ t) (htu : t ⊆ u) (f : ∀ i : u, π i) :
    restrict₂ hst (restrict₂ htu f) = restrict₂ (hst.trans htu) f :=
  (rfl)

/-- A dependent function on `s ∪ t` is determined by its restrictions to `s` and to `t`. -/
theorem restrict₂_union_ext [DecidableEq ι] {f g : ∀ i : (s ∪ t : Finset ι), π i}
    (hs : restrict₂ subset_union_left f = restrict₂ subset_union_left g)
    (ht : restrict₂ subset_union_right f = restrict₂ subset_union_right g) : f = g := by
  funext ⟨i, hi⟩
  rcases mem_union.1 hi with h | h
  · exact congr_fun hs ⟨i, h⟩
  · exact congr_fun ht ⟨i, h⟩

end Finset

namespace Equiv

open _root_.Finset

variable {ι : Type*} [DecidableEq ι] (π : ι → Type*) {s t u : Finset ι}

/-- Restricting `Equiv.piFinsetUnion π h (f, g)` to `s` gives `f`. -/
@[simp]
theorem restrict₂_piFinsetUnion_left (h : Disjoint s t) (x : (∀ i : s, π i) × ∀ i : t, π i) :
    restrict₂ subset_union_left (piFinsetUnion π h x) = x.1 :=
  funext fun i ↦ piFinsetUnion_left π h i.property _

/-- Restricting `Equiv.piFinsetUnion π h (f, g)` to `t` gives `g`. -/
@[simp]
theorem restrict₂_piFinsetUnion_right (h : Disjoint s t) (x : (∀ i : s, π i) × ∀ i : t, π i) :
    restrict₂ subset_union_right (piFinsetUnion π h x) = x.2 :=
  funext fun i ↦ piFinsetUnion_right π h i.property _

/-- The inverse of `Equiv.piFinsetUnion` takes the restrictions to the two pieces. -/
@[simp]
theorem piFinsetUnion_symm_apply (h : Disjoint s t) (f : ∀ i : (s ∪ t : Finset ι), π i) :
    (piFinsetUnion π h).symm f = (restrict₂ subset_union_left f, restrict₂ subset_union_right f) :=
  (piFinsetUnion π h).symm_apply_eq.2 <| restrict₂_union_ext (by simp) (by simp)

/-- **Gluing is associative.** For pairwise disjoint `s`, `t` and `u`, gluing `f` with the gluing
of `g` and `k` and gluing the gluing of `f` and `g` with `k` give the same function, through the
identification of `s ∪ (t ∪ u)` with `(s ∪ t) ∪ u`. -/
theorem restrict₂_piFinsetUnion_assoc (hst : Disjoint s t) (hsu : Disjoint s u)
    (htu : Disjoint t u) (f : ∀ i : s, π i) (g : ∀ i : t, π i) (k : ∀ i : u, π i) :
    restrict₂ (union_assoc s t u).le
        (piFinsetUnion π (disjoint_union_right.2 ⟨hst, hsu⟩) (f, piFinsetUnion π htu (g, k))) =
      piFinsetUnion π (disjoint_union_left.2 ⟨hsu, htu⟩) (piFinsetUnion π hst (f, g), k) := by
  funext ⟨i, hi⟩
  rcases mem_union.1 hi with hi | hu
  · rcases mem_union.1 hi with hs | ht
    · simp only [restrict₂, piFinsetUnion_left π _ hs, piFinsetUnion_left π _ (mem_union_left t hs)]
    · simp only [restrict₂, piFinsetUnion_right π _ (mem_union_left u ht),
        piFinsetUnion_left π _ ht, piFinsetUnion_left π _ (mem_union_right s ht),
        piFinsetUnion_right π _ ht]
  · simp only [restrict₂, piFinsetUnion_right π _ (mem_union_right t hu),
      piFinsetUnion_right π _ hu]

end Equiv
