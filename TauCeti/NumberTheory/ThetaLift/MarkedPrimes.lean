/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Finset.Involution
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Full marks and collisions at an inert prime

A finite family of places induces a finite set of primes. If none is fixed by conjugation,
`Finset.exists_subset_disjoint_image_of_involutive` selects a full mark from that set: it meets
each conjugate pair exactly once. At an inert prime the partner at an odd exponent has conjugate
induced prime. Thus a collision between two places outside a full mark is impossible.

The marking and collision statements follow `New.Data.exists_isFullMark` and
`New.Data.IsFullMark.collisionSum_placesInducing_eq_zero` in
`New/UpperBound/Divisibility/MarkedPrimes` of grh-lean
(<https://github.com/lsernau/grh-lean>, revision `72fead1`).
-/

public section

open Finset

namespace TauCeti.OneSidedBound

/-- The weighted sum over odd partners outside a full mark vanishes. Here `A` is the set of
places being tested, `w` assigns each place its induced prime, and `step` acts on places by the
signed prime label. Only partners that are both in `A` need to induce conjugate primes, and only
coverage of the pairs is needed; the marks need not be disjoint from their conjugates. -/
theorem sum_tsum_collisions_eq_zero_of_fullMark {G α β : Type*} [Monoid G] [MulAction G α]
    [DecidableEq α] [DecidableEq β] {A : Finset α} {marks : Finset β}
    {w : α → β} {conj : β → β} (hconj : Function.Involutive conj)
    (hcover : A.image w ⊆ marks ∪ marks.image conj) (step : G)
    (hpartner : ∀ e : ℕ, Odd e → ∀ τ ∈ A, step ^ e • τ ∈ A →
      w (step ^ e • τ) = conj (w τ)) (weight : α → ℕ → ℝ) :
    (∑ τ ∈ A, ∑' e : ℕ, if Odd e ∧ step ^ e • τ ∈ A ∧
      w τ ∉ marks ∧ w (step ^ e • τ) ∉ marks then weight τ e else 0) = 0 := by
  refine sum_eq_zero fun τ hτ ↦ ?_
  have hzero (e : ℕ) : ¬ (Odd e ∧ step ^ e • τ ∈ A ∧
      w τ ∉ marks ∧ w (step ^ e • τ) ∉ marks) := by
    rintro ⟨he, hmem, hnot, hpartner_not⟩
    have hconj_mem : w τ ∈ marks.image conj :=
      (mem_union.mp (hcover (mem_image_of_mem w hτ))).resolve_left hnot
    obtain ⟨v, hv, hval⟩ := mem_image.mp hconj_mem
    rw [hpartner e he τ hτ hmem, ← hval, hconj v] at hpartner_not
    exact hpartner_not hv
  simp only [ite_eq_right (hzero _), tsum_zero]

end TauCeti.OneSidedBound
