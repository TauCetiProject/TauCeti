/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.FreeCancellation.Basic

/-!
# Crossing-free strands in a free-cancellation closure

When an inverse pair is appended to a braid word and neither of its two strand positions met an
old crossing, the pair is a closed Reidemeister-II clasp on two crossing-free circles.  The
characterisation here is the component-count input for the planned
`reidemeisterEquiv_closure_append_freeCancel_of_crossingless` theorem, which will identify this
branch with `OrientedPDCode.reidemeisterEquiv_adjoinTwoCircleClasp`.
-/

public section

namespace TauCeti
namespace BraidWord

open BraidGroup PDCode

variable {n : ℕ}

/-- An appended inverse pair creates crossings on exactly its two strand positions. -/
theorem crossingsAt_append_freeCancel_eq_nil_iff (v : BraidWord n)
    (i : Fin (n - 1)) (ε η : ℤˣ) (p : Fin n) :
    (v ++ [(i, ε), (i, η)]).crossingsAt p = [] ↔
      v.crossingsAt p = [] ∧ p ≠ strand i ∧ p ≠ strandSucc i := by
  rw [crossingsAt_append_eq_nil_iff, crossingsAt_cons_eq_nil_iff,
    crossingsAt_cons_eq_nil_iff]
  simp only [and_assoc]
  constructor
  · rintro ⟨hv, -, hi, hs, -, -⟩
    exact ⟨hv, hi, hs⟩
  · rintro ⟨hv, hi, hs⟩
    have hz : crossingsAt ([] : BraidWord n) p = [] := by
      rw [crossingsAt_def]
      simp
    exact ⟨hv, hz, hi, hs, hi, hs⟩

/-- The crossing-free circles lost by an appended inverse pair are exactly its two strand
positions. -/
theorem crossinglessComponentCount_append_freeCancel
    (v : BraidWord n) (i : Fin (n - 1)) (ε η : ℤˣ)
    (h₀ : v.crossingsAt (strand i) = []) (h₁ : v.crossingsAt (strandSucc i) = []) :
    (v ++ [(i, ε), (i, η)]).closure.crossinglessComponentCount + 2 =
      v.closure.crossinglessComponentCount := by
  rw [crossinglessComponentCount_closure, crossinglessComponentCount_closure]
  let S := Finset.univ.filter fun p : Fin n ↦ v.crossingsAt p = []
  have hfilter :
      Finset.univ.filter fun p : Fin n ↦
        (v ++ [(i, ε), (i, η)]).crossingsAt p = [] =
      (S.erase (strand i)).erase (strandSucc i) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    rw [crossingsAt_append_freeCancel_eq_nil_iff]
    simp [S, and_assoc, and_left_comm, and_comm]
  rw [hfilter]
  have hne : strand i ≠ strandSucc i := strand_ne_strandSucc i
  have hiS : strand i ∈ S := by simp [S, h₀]
  have hsuccS : strandSucc i ∈ S := by simp [S, h₁]
  change ((S.erase (strand i)).erase (strandSucc i)).card + 2 = S.card
  have hsuccErase : strandSucc i ∈ S.erase (strand i) :=
    Finset.mem_erase.mpr ⟨hne.symm, hsuccS⟩
  rw [Finset.card_erase_of_mem hsuccErase, Finset.card_erase_of_mem hiS]
  have hnontrivial : S.Nontrivial := by
    change Set.Nontrivial (↑S : Set (Fin n))
    exact Set.nontrivial_of_mem_mem_ne hiS hsuccS hne
  have hcard : 1 < S.card := Finset.one_lt_card_iff_nontrivial.mpr hnontrivial
  omega

end BraidWord
end TauCeti
