/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.Equivalence
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Equivalence
import TauCeti.KnotTheory.BraidWord.Cyclic
import TauCeti.KnotTheory.BraidWord.FreeCancellation.Face

/-!
# Braid closures depend only on the braid

Inserting or deleting an adjacent inverse pair `σᵢ ^ ε σᵢ ^ (-ε)` anywhere in a braid word
changes its oriented closure only by Reidemeister moves. At the top of the word the pair is a
clasp: between the two closing arcs when both participating positions already meet crossings,
between a closing arc and an isolated circle when exactly one does, and between two isolated
circles when neither does. When only the higher position meets crossings, the isolated lower
circle is first reversed before the clasp is inserted. Cyclic rotation of the word moves an
arbitrary insertion to the top.

Together with the invariance under the Artin relations, and the completeness of Artin relations
and free cancellation as braid-word moves, this shows that two braid words representing the same
braid have Reidemeister-equivalent oriented closures.

## Main results

* `TauCeti.BraidWord.reidemeisterEquiv_closure_of_freeCancelStep` and
  `TauCeti.BraidWord.reidemeisterEquiv_closure_of_freeCancelEquiv`: free cancellation preserves
  the oriented closure up to Reidemeister moves.
* `TauCeti.BraidWord.reidemeisterEquiv_closure_of_toBraid_eq`: words representing the same braid
  have Reidemeister-equivalent oriented closures.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Chapter 2.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1.
-/

public section

namespace TauCeti.BraidWord

open BraidGroup

variable {n : ℕ}

/-- An inverse pair at the top of a braid word changes the closure only by Reidemeister moves,
in each of the three cases of which participating positions already meet crossings. -/
private theorem reidemeisterEquiv_closure_cons_cons (v : BraidWord n) (i : Fin (n - 1))
    (ε : ℤˣ) :
    OrientedPDCode.ReidemeisterEquiv v.closure (closure ((i, ε) :: (i, -ε) :: v)) := by
  by_cases hp : v.crossingsAt (strand i) = []
  · exact reidemeisterEquiv_closure_cons_cons_freeCancel_of_strand_crossingsAt_eq_nil v i ε hp
  by_cases hq : v.crossingsAt (strandSucc i) = []
  · exact reidemeisterEquiv_closure_cons_cons_freeCancel_of_strandSucc_crossingsAt_eq_nil v i ε hq
  exact (reidemeisterEquiv_closure_cons_cons_freeCancel v i ε hp hq).symm

/-- Inserting an inverse pair anywhere in a braid word gives a Reidemeister-equivalent closure:
rotate the word so that the pair is at the top. -/
private theorem reidemeisterEquiv_closure_append_freeCancel (u v : BraidWord n)
    (i : Fin (n - 1)) (ε : ℤˣ) :
    OrientedPDCode.ReidemeisterEquiv (closure (u ++ v))
      (closure (u ++ [(i, ε), (i, -ε)] ++ v)) := by
  have hleft := reidemeisterEquiv_closure_rotate (u ++ v) u.length
  have hright := reidemeisterEquiv_closure_rotate (u ++ ([(i, ε), (i, -ε)] ++ v)) u.length
  rw [List.rotate_append_length_eq] at hleft hright
  simp only [List.cons_append, List.nil_append] at hright
  rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
  exact hleft.trans ((reidemeisterEquiv_closure_cons_cons (v ++ u) i ε).trans hright.symm)

/-- A free-cancellation step changes the oriented closure of a braid word only by Reidemeister
moves. -/
theorem reidemeisterEquiv_closure_of_freeCancelStep {w w' : BraidWord n}
    (h : FreeCancelStep w w') : OrientedPDCode.ReidemeisterEquiv (closure w) (closure w') := by
  cases h with
  | insert u v i ε => exact reidemeisterEquiv_closure_append_freeCancel u v i ε
  | delete u v i ε => exact (reidemeisterEquiv_closure_append_freeCancel u v i ε).symm

/-- Free-cancellation-equivalent braid words have Reidemeister-equivalent oriented closures. -/
theorem reidemeisterEquiv_closure_of_freeCancelEquiv {w w' : BraidWord n}
    (h : FreeCancelEquiv w w') : OrientedPDCode.ReidemeisterEquiv (closure w) (closure w') :=
  FreeCancelEquiv.induction reidemeisterEquiv_closure_of_freeCancelStep
    (fun _ ↦ OrientedPDCode.ReidemeisterEquiv.refl _) (fun _ ih ↦ ih.symm)
    (fun _ _ ih ih' ↦ ih.trans ih') h

/-- Braid words connected by Artin relations and free cancellation have Reidemeister-equivalent
oriented closures. -/
theorem reidemeisterEquiv_closure_of_wordEquiv {w w' : BraidWord n} (h : WordEquiv w w') :
    OrientedPDCode.ReidemeisterEquiv (closure w) (closure w') :=
  WordEquiv.induction reidemeisterEquiv_closure_of_artinStep
    reidemeisterEquiv_closure_of_freeCancelStep
    (fun _ ↦ OrientedPDCode.ReidemeisterEquiv.refl _) (fun _ ih ↦ ih.symm)
    (fun _ _ ih ih' ↦ ih.trans ih') h

/-- **The closure of a braid is well defined up to Reidemeister moves.** Two braid words
representing the same braid have Reidemeister-equivalent oriented closures. -/
theorem reidemeisterEquiv_closure_of_toBraid_eq {w w' : BraidWord n}
    (h : toBraid w = toBraid w') : OrientedPDCode.ReidemeisterEquiv (closure w) (closure w') :=
  reidemeisterEquiv_closure_of_wordEquiv (toBraid_eq_iff_wordEquiv.mp h)

end TauCeti.BraidWord
