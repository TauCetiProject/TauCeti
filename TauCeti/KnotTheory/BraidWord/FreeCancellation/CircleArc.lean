/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.FreeCancellation.Clasp
import TauCeti.KnotTheory.BraidWord.Cyclic

/-!
# Free cancellation beside a crossing-free circle

An inverse pair on adjacent braid positions gives a Reidemeister-II move when the higher
position is crossing-free in the original word. The lower position may already meet crossings:
then the move pushes the isolated circle across its closing arc. If neither position meets
crossings, the existing two-circle clasp applies.

Cyclic rotation places an insertion in an arbitrary word context at the cut of the closed braid.
This gives closure equivalence for inserting or removing an inverse pair between arbitrary
prefixes and suffixes when the higher participating position is crossing-free.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Chapter 2.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 1.
-/

public section

namespace TauCeti.BraidWord

open BraidGroup

/-- Inserting inverse letters anywhere in a braid word preserves its oriented closure up to
Reidemeister moves if the higher participating position was crossing-free. No condition is
imposed on the lower position. -/
theorem reidemeisterEquiv_closure_append_cons_cons_freeCancel_of_strandSucc_crossingsAt_eq_nil
    {n : ℕ} (u v : BraidWord n) (i : Fin (n - 1)) (ε : ℤˣ)
    (hq : (u ++ v).crossingsAt (strandSucc i) = []) :
    OrientedPDCode.ReidemeisterEquiv (closure (u ++ v))
      (closure (u ++ (i, ε) :: (i, -ε) :: v)) := by
  have hq' : (v ++ u).crossingsAt (strandSucc i) = [] := by
    simpa only [crossingsAt_append_eq_nil_iff, and_comm] using hq
  have hcancel :=
    reidemeisterEquiv_closure_cons_cons_freeCancel_of_strandSucc_crossingsAt_eq_nil
      (v ++ u) i ε hq'
  have hleft := reidemeisterEquiv_closure_rotate (u ++ v) u.length
  have hright := reidemeisterEquiv_closure_rotate (u ++ (i, ε) :: (i, -ε) :: v) u.length
  rw [List.rotate_append_length_eq] at hleft hright
  simp only [List.cons_append] at hright
  exact hleft.trans (hcancel.trans hright.symm)

end TauCeti.BraidWord
