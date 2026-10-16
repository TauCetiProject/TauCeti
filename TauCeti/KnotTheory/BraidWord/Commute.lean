/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.Relabel
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Equivalence
public import TauCeti.Data.List.Swap

/-!
# Far commutation in braid-word closures

Two letters `σ i ^ ε` and `σ j ^ δ` with `i + 2 ≤ j` cross disjoint pairs of strands, so the
elementary braids they denote commute (`TauCeti.BraidGroup.sigma_mul_sigma_comm`). Exchanging two
such adjacent letters of a braid word slides one crossing past the other at a different height,
and the closure diagram does not change: only its crossing and half-edge names do. This file
proves that equality of oriented PD-codes, with the renaming exchanging the two crossings, and
concludes that the two closures are Reidemeister equivalent.

No strand position is involved in both crossings, so along every position the crossings are met
in the same order before and after the exchange, and
`TauCeti.BraidWord.closure_eq_relabel_of_isRotated` applies. Together with cyclic rotation
(`TauCeti.BraidWord.closure_rotate`), this is part of the diagram-level content of the defining
relations of the braid group and of the conjugation move in Markov equivalence.

## Main results

* `TauCeti.BraidWord.closure_append_cons_cons_comm`: exchanging two adjacent letters on
  disjoint strands changes the closure only by exchanging the names of their crossings.
* `TauCeti.BraidWord.reidemeisterEquiv_closure_append_cons_cons_comm`: the two closures are
  Reidemeister equivalent.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Chapters 1 and 2.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1.
-/

public section

namespace TauCeti

namespace BraidWord

open BraidGroup PDCode

variable {n : ℕ}

/-- Along every strand position, exchanging two adjacent letters on disjoint strands carries the
crossings of the new word, in order, to those of the old word. -/
private theorem map_crossingsAt_swapIndexEquiv (u v : BraidWord n) {a b : Fin (n - 1) × ℤˣ}
    (h : (a.1 : ℕ) + 2 ≤ b.1 ∨ (b.1 : ℕ) + 2 ≤ a.1) (p : Fin n) :
    (crossingsAt (u ++ b :: a :: v) p).map (List.swapIndexEquiv u v a b) =
      crossingsAt (u ++ a :: b :: v) p := by
  set e := List.swapIndexEquiv u v a b
  refine List.SortedLT.eq_of_mem_iff ?_ (sortedLT_crossingsAt _ p) fun i ↦ ?_
  · rw [List.sortedLT_iff_pairwise, List.pairwise_map]
    refine (List.sortedLT_iff_pairwise.1 (sortedLT_crossingsAt _ p)).imp_of_mem ?_
    intro x y hx hy hxy
    rw [mem_crossingsAt] at hx hy
    -- The only pair whose order is reversed is the pair of exchanged crossings, which involve
    -- disjoint strand positions, so they cannot both involve `p`.
    have hxy' : ¬((x : ℕ) = u.length ∧ (y : ℕ) = u.length + 1) := by
      rintro ⟨hx₁, hy₁⟩
      have hxb : (u ++ b :: a :: v)[(x : ℕ)] = b := by simp [hx₁]
      have hya : (u ++ b :: a :: v)[(y : ℕ)] = a := by simp [hy₁]
      rw [hxb] at hx
      rw [hya] at hy
      have hnd := nodup_strand_strandSucc_strand_strandSucc h
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or] at hnd
      rcases hx with rfl | rfl <;> rcases hy with hy | hy <;> simp_all
    rw [Fin.lt_def] at hxy ⊢
    simp only [e, List.val_swapIndexEquiv]
    split_ifs <;> omega
  · simp only [List.mem_map]
    constructor
    · rintro ⟨j, hj, rfl⟩
      rwa [mem_crossingsAt, ← List.getElem_swapIndexEquiv, ← mem_crossingsAt]
    · intro hi
      refine ⟨e.symm i, ?_, e.apply_symm_apply i⟩
      rw [mem_crossingsAt, List.getElem_swapIndexEquiv]
      simpa only [e, Equiv.apply_symm_apply, mem_crossingsAt] using hi

/-- Exchanging two adjacent letters `a = (i, ε)` and `b = (j, δ)` of a braid word with
`i + 2 ≤ j` or `j + 2 ≤ i` changes its oriented closure PD-code only by renaming crossings and
half-edges: the two crossings of `a` and `b` exchange their names, and
`PDCode.crossingBlockEquiv` applies the same renaming to all four crossing slots. -/
theorem closure_append_cons_cons_comm (u v : BraidWord n) {a b : Fin (n - 1) × ℤˣ}
    (h : (a.1 : ℕ) + 2 ≤ b.1 ∨ (b.1 : ℕ) + 2 ≤ a.1) :
    closure (u ++ b :: a :: v) =
      (closure (u ++ a :: b :: v)).relabel
        (crossingBlockEquiv (List.swapIndexEquiv u v b a)) (List.swapIndexEquiv u v b a) := by
  rw [← List.swapIndexEquiv_symm]
  exact closure_eq_relabel_of_isRotated _ (List.getElem_swapIndexEquiv u v a b)
    fun p ↦ (map_crossingsAt_swapIndexEquiv u v h p).symm ▸ List.IsRotated.refl _

/-- Exchanging two adjacent letters on disjoint strands of a braid word gives a Reidemeister
equivalent closure. -/
theorem reidemeisterEquiv_closure_append_cons_cons_comm (u v : BraidWord n)
    {a b : Fin (n - 1) × ℤˣ} (h : (a.1 : ℕ) + 2 ≤ b.1 ∨ (b.1 : ℕ) + 2 ≤ a.1) :
    OrientedPDCode.ReidemeisterEquiv (closure (u ++ a :: b :: v)) (closure (u ++ b :: a :: v)) := by
  rw [closure_append_cons_cons_comm u v h]
  exact OrientedPDCode.reidemeisterEquiv_relabel _ _ _

end BraidWord

end TauCeti
