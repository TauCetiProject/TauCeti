/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.PDCode

/-!
# Crossing-free circles after inserting a pair of braid crossings

Inserting two crossings at the same generator positions turns each previously crossing-free
affected position into a crossing-bearing circle. All other crossing-free circles survive.
Thus the number of crossing-free components falls by zero, one, or two. This is the component
bookkeeping for identifying free cancellation in a braid closure with a Reidemeister-II clasp,
including clasps involving crossing-free circles.

The formulas allow insertion anywhere in a word and arbitrary signs on the two crossings.
They count crossing-free components, rather than all link components: for an inverse pair
the affected circles remain link components but acquire crossings.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, GTM 175 (1997), Chapter 1
  (braid closures and the second Reidemeister move).
* J. Birman, *Braids, Links, and Mapping Class Groups*, Chapter 2.
-/

public section

namespace TauCeti.BraidWord

open BraidGroup

variable {n : ℕ}

/-- After inserting two letters on generator `i`, a position is crossing-free exactly when
it was crossing-free before the insertion and differs from both positions of `i`.
The signs of the two letters are arbitrary. -/
theorem crossingsAt_insert_same_index_eq_nil_iff (u v : BraidWord n)
    (i : Fin (n - 1)) (ε η : ℤˣ) (p : Fin n) :
    (u ++ [(i, ε), (i, η)] ++ v).crossingsAt p = [] ↔
      (u ++ v).crossingsAt p = [] ∧ p ≠ strand i ∧ p ≠ strandSucc i := by
  simp only [crossingsAt_append_eq_nil_iff, crossingsAt_cons_eq_nil_iff,
    crossingsAt_nil]
  tauto

/-- Inserting two letters at the same generator positions removes exactly those positions
from the set of crossing-free positions. The signs do not affect this set. -/
private theorem filter_crossingsAt_insert_pair_eq_nil (u v : BraidWord n) (i : Fin (n - 1))
    (ε η : ℤˣ) :
    (Finset.univ.filter fun p => (u ++ [(i, ε), (i, η)] ++ v).crossingsAt p = []) =
      ((Finset.univ.filter fun p => (u ++ v).crossingsAt p = []).erase (strand i)).erase
        (strandSucc i) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
    crossingsAt_insert_same_index_eq_nil_iff]
  tauto

/-- **Crossing-free component bookkeeping for a pair insertion.** Each affected position
which had no crossing contributes one to the loss. This additive form avoids truncated
subtraction and supplies the circle counts for all three types of Reidemeister-II clasp. -/
theorem crossinglessComponentCount_closure_insert_pair (u v : BraidWord n)
    (i : Fin (n - 1)) (ε η : ℤˣ) :
    (u ++ [(i, ε), (i, η)] ++ v).closure.crossinglessComponentCount +
        (if (u ++ v).crossingsAt (strand i) = [] then 1 else 0) +
        (if (u ++ v).crossingsAt (strandSucc i) = [] then 1 else 0) =
      (u ++ v).closure.crossinglessComponentCount := by
  classical
  rw [crossinglessComponentCount_closure, crossinglessComponentCount_closure,
    filter_crossingsAt_insert_pair_eq_nil]
  let s := Finset.univ.filter fun p => (u ++ v).crossingsAt p = []
  have ha : strand i ∈ s ↔ (u ++ v).crossingsAt (strand i) = [] := by simp [s]
  have hb : strandSucc i ∈ s ↔ (u ++ v).crossingsAt (strandSucc i) = [] := by simp [s]
  have hab := strand_ne_strandSucc i
  by_cases h₁ : strand i ∈ s <;> by_cases h₂ : strandSucc i ∈ s
  · have h₂' : strandSucc i ∈ s.erase (strand i) := Finset.mem_erase.mpr ⟨hab.symm, h₂⟩
    have hcard₁ := Finset.card_erase_add_one h₁
    have hcard₂ := Finset.card_erase_add_one h₂'
    simp only [← ha, ← hb, h₁, h₂, ite_true]
    dsimp only [s] at hcard₁ hcard₂
    omega
  · have h₂' : strandSucc i ∉ s.erase (strand i) := by simp [h₂]
    have hcard₁ := Finset.card_erase_add_one h₁
    simp only [← ha, ← hb, h₁, h₂, ite_true, ite_false, add_zero]
    rw [Finset.erase_eq_of_notMem h₂']
    exact hcard₁
  · simp only [← ha, ← hb, h₁, h₂, ite_true, ite_false, add_zero]
    rw [Finset.erase_eq_of_notMem h₁]
    exact Finset.card_erase_add_one h₂
  · simp only [← ha, ← hb, h₁, h₂, ite_false, add_zero]
    rw [Finset.erase_eq_of_notMem h₁, Finset.erase_eq_of_notMem h₂]

/-- The surviving oriented crossing-free circles and the circles consumed at the two
affected positions recover exactly the original multiset. Every such circle has the braid
orientation `true`. This supplies oriented circle data as well as counts for clasp comparisons. -/
theorem crossinglessComponents_closure_insert_pair (u v : BraidWord n)
    (i : Fin (n - 1)) (ε η : ℤˣ) :
    (u ++ [(i, ε), (i, η)] ++ v).closure.crossinglessComponents +
        Multiset.replicate (if (u ++ v).crossingsAt (strand i) = [] then 1 else 0) true +
        Multiset.replicate (if (u ++ v).crossingsAt (strandSucc i) = [] then 1 else 0) true =
      (u ++ v).closure.crossinglessComponents := by
  rw [crossinglessComponents_closure, crossinglessComponents_closure,
    ← Multiset.replicate_add, ← Multiset.replicate_add]
  exact congrArg (fun k => Multiset.replicate k true)
    (by simpa only [crossinglessComponentCount_closure] using
      crossinglessComponentCount_closure_insert_pair u v i ε η)

end TauCeti.BraidWord
