/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.Relabel
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Equivalence

/-!
# Cyclic rotation of braid-word closures

Cyclically rotating a braid word cuts its closed braid between two different levels. The closure
diagram therefore does not change: only its crossing and half-edge names do. This file describes
that renaming explicitly, proves equality of the resulting oriented PD-codes, and concludes that
the two closures are Reidemeister equivalent.

For a word `w` and a rotation distance `k`, `List.rotateIndexEquiv w k` sends an index in
`w.rotate k` to the index of the same letter in `w`. Its inverse renames the old crossings, and
the induced crossing-block equivalence renames their four half-edges. Along every strand position
the rotation carries the crossings of `w.rotate k` to a cyclic rotation of those of `w`, so by
`TauCeti.BraidWord.closure_eq_relabel_of_isRotated` these renamings account for the entire closure
construction, including arcs which cross the cut.

Taking `w = u ++ v` and `k = u.length` specializes the theorem to the familiar equality of the
closures of `u ++ v` and `v ++ u`. This is the diagram-level content of cyclic conjugation, the
word-level generator needed for the conjugation part of Markov equivalence.

## Main results

* `TauCeti.BraidWord.closure_rotate`: rotating a braid word changes its closure only by the
  explicit induced renaming.
* `TauCeti.BraidWord.reidemeisterEquiv_closure_rotate`: a braid word and its rotation have
  Reidemeister equivalent closures.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Chapter 2.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Proposition
  16.10.
-/

public section

namespace TauCeti

namespace BraidWord

open PDCode

private theorem crossingsAt_rotate_isRotated (w : BraidWord n) (k : ℕ) (p : Fin n) :
    (crossingsAt (w.rotate k) p).map (w.rotateIndexEquiv k) ~r w.crossingsAt p := by
  have hfin :
      (List.finRange (w.rotate k).length).map (w.rotateIndexEquiv k) ~r
        List.finRange w.length := by
    rw [List.map_finRange_rotateIndexEquiv]
    exact List.IsRotated.forall _ _
  have hfilter := hfin.filter
    (fun j : Fin w.length => p = BraidGroup.strand w[j.1].1 ∨
      p = BraidGroup.strandSucc w[j.1].1)
  rw [List.filter_map] at hfilter
  rw [crossingsAt_def, crossingsAt_def]
  simpa only [Function.comp_def, List.getElem_rotateIndexEquiv] using hfilter

/-- Rotating a braid word changes its oriented closure PD-code only by renaming crossings and
half-edges. The inverse of `rotateIndexEquiv` sends each old crossing name to its name in the
rotated word, and `PDCode.crossingBlockEquiv` applies the same renaming to all four crossing
slots. -/
theorem closure_rotate (w : BraidWord n) (k : ℕ) :
    closure (w.rotate k) =
      w.closure.relabel
        (PDCode.crossingBlockEquiv (w.rotateIndexEquiv k).symm)
        (w.rotateIndexEquiv k).symm :=
  closure_eq_relabel_of_isRotated _ (List.getElem_rotateIndexEquiv w k)
    (crossingsAt_rotate_isRotated w k)

/-- Rotating a braid word gives a Reidemeister equivalent closure. -/
theorem reidemeisterEquiv_closure_rotate (w : BraidWord n) (k : ℕ) :
    OrientedPDCode.ReidemeisterEquiv w.closure (closure (w.rotate k)) := by
  rw [closure_rotate]
  exact OrientedPDCode.reidemeisterEquiv_relabel _ _ _

end BraidWord

end TauCeti
