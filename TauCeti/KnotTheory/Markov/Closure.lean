/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Markov.Basic
public import TauCeti.KnotTheory.BraidWord.PDCode
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Equivalence
import TauCeti.KnotTheory.BraidWord.Cyclic
import TauCeti.KnotTheory.BraidWord.FreeCancellation.Closure
import TauCeti.KnotTheory.BraidWord.Stabilization

/-!
# Markov-equivalent braids have Reidemeister-equivalent closures

The closure of a braid on `n + 1` strands is read from any braid word representing it, and by
`TauCeti.BraidWord.reidemeisterEquiv_closure_of_toBraid_eq` the choice of word only matters up to
Reidemeister moves. The Markov moves preserve the closure up to Reidemeister moves too:
conjugation `c * b * c⁻¹` becomes a cyclic rotation of a word, and stabilization adds a first
Reidemeister kink (`TauCeti.BraidWord.reidemeisterEquiv_closure_stabilize`). So the oriented
closures of Markov-equivalent braids, read from arbitrary words, are Reidemeister equivalent.

This is the elementary direction of Markov's theorem, from braids to diagrams; the converse, that
braids with isotopic closures are Markov equivalent, is not formalized here.

## Main results

* `TauCeti.MarkovEquiv.reidemeisterEquiv_closure`: the oriented closures of words representing
  Markov-equivalent braids are Reidemeister equivalent.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Chapter 2 (Markov's theorem, Theorem 2.3).
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1.
-/

public section

namespace TauCeti

open BraidGroup BraidWord

/-- A single Markov move between braids changes the oriented closures of words representing them
only by Reidemeister moves. -/
theorem IsMarkovMove.reidemeisterEquiv_closure {β γ : MarkovBraid} (h : IsMarkovMove β γ)
    {w : BraidWord (β.predStrands + 1)} {w' : BraidWord (γ.predStrands + 1)}
    (hw : w.toBraid = β.braid) (hw' : w'.toBraid = γ.braid) :
    OrientedPDCode.ReidemeisterEquiv w.closure w'.closure := by
  cases h with
  | conj b c =>
    -- Conjugation by a word `u` is undone by rotating `u` to the end of the word.
    obtain ⟨u, rfl⟩ := toBraid_surjective c
    let uInv : BraidWord _ := u.reverse.map fun x ↦ (x.1, -x.2)
    have huInv : uInv.toBraid = u.toBraid⁻¹ := toBraid_reverse_map_neg u
    have hconj : OrientedPDCode.ReidemeisterEquiv w.closure (closure (u ++ (w' ++ uInv))) :=
      reidemeisterEquiv_closure_of_toBraid_eq (by
        rw [hw, toBraid_append, toBraid_append, hw', huInv, mul_assoc])
    have hrot := reidemeisterEquiv_closure_rotate (u ++ (w' ++ uInv)) u.length
    rw [List.rotate_append_length_eq] at hrot
    have hcancel : OrientedPDCode.ReidemeisterEquiv (closure (w' ++ uInv ++ u)) w'.closure :=
      reidemeisterEquiv_closure_of_toBraid_eq (by
        rw [toBraid_append, toBraid_append, huInv, hw', inv_mul_cancel_right])
    exact hconj.trans (hrot.trans hcancel)
  | stabilize b =>
    have hstab : OrientedPDCode.ReidemeisterEquiv w.closure (w'.stabilize 1).closure :=
      reidemeisterEquiv_closure_of_toBraid_eq (by rw [hw, toBraid_stabilize, hw']; simp)
    exact hstab.trans (reidemeisterEquiv_closure_stabilize w' 1)
  | stabilizeInv b =>
    have hstab : OrientedPDCode.ReidemeisterEquiv w.closure (w'.stabilize (-1)).closure :=
      reidemeisterEquiv_closure_of_toBraid_eq (by rw [hw, toBraid_stabilize, hw']; simp)
    exact hstab.trans (reidemeisterEquiv_closure_stabilize w' (-1))

/-- **Markov-equivalent braids have Reidemeister-equivalent closures.** For any braid words
representing two Markov-equivalent braids, their oriented closures are Reidemeister
equivalent. -/
theorem MarkovEquiv.reidemeisterEquiv_closure {β γ : MarkovBraid} (h : MarkovEquiv β γ)
    {w : BraidWord (β.predStrands + 1)} {w' : BraidWord (γ.predStrands + 1)}
    (hw : w.toBraid = β.braid) (hw' : w'.toBraid = γ.braid) :
    OrientedPDCode.ReidemeisterEquiv w.closure w'.closure := by
  -- The representing words change along a chain of moves, so the motive quantifies over them.
  revert w w'
  refine h.induction (motive := fun β γ ↦ ∀ {w : BraidWord (β.predStrands + 1)}
      {w' : BraidWord (γ.predStrands + 1)}, w.toBraid = β.braid → w'.toBraid = γ.braid →
        OrientedPDCode.ReidemeisterEquiv w.closure w'.closure)
    (fun hmove _ _ hw hw' ↦ hmove.reidemeisterEquiv_closure hw hw')
    (fun _ _ _ hw hw' ↦ reidemeisterEquiv_closure_of_toBraid_eq (hw.trans hw'.symm))
    (fun _ ih _ _ hw hw' ↦ (ih hw' hw).symm) ?_
  -- Pass through any word representing the middle braid.
  intro _ γ _ _ _ ih₁ ih₂ _ _ hw hw'
  obtain ⟨u, hu⟩ := toBraid_surjective γ.braid
  exact (ih₁ hw hu).trans (ih₂ hu hw')

end TauCeti
