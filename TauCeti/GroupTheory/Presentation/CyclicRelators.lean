/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.Finiteness
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# Cyclic relators for finite coset certificates

`GroupPresentation.cyclicRelators` lists all cyclic rotations of the signed presentation
relators and their inverse words. Every listed word equals one in the exact presented group.
These words can therefore be supplied as `CosetCertificate.extraRelators`, allowing the
checker to deduce an edge at any position of a relator, in either orientation. Set
`extraRelators := ⟨P.cyclicRelators, P.cyclicRelators_eq_one⟩` in the certificate.

The list uses `List.cyclicPermutations` without removing duplicates; an empty relator contributes
the empty word in both orientations. This supplies scan words for CFSG basic properties P0.
-/

public section

namespace TauCeti.GroupPresentation

variable (P : GroupPresentation)

/-- All cyclic rotations of each signed relator and its inverse, in presentation order.

For each relator, its rotations come first, followed by the rotations of `FreeGroup.invRev`
of that relator. No free reduction or deduplication is performed. -/
@[expose]
def cyclicRelators : List (PresentationWord (Fin P.generatorCount)) :=
  P.relators.flatMap fun w ↦ w.cyclicPermutations ++ (FreeGroup.invRev w).cyclicPermutations

private theorem mk_rotate_eq_one {w : PresentationWord (Fin P.generatorCount)}
    (hw : PresentedGroup.mk P.relatorSet (FreeGroup.mk w) = 1) (n : ℕ) :
    PresentedGroup.mk P.relatorSet (FreeGroup.mk (w.rotate n)) = 1 := by
  rw [← P.prod_toTableWord]
  simpa only [PresentationWord.toTableWord, List.map_rotate] using
    List.prod_rotate_eq_one_of_prod_eq_one ((P.prod_toTableWord w).trans hw) n

/-- Every cyclic scan word is a consequence of the exact presentation relations. -/
theorem cyclicRelators_eq_one :
    ∀ w ∈ P.cyclicRelators, PresentedGroup.mk P.relatorSet (FreeGroup.mk w) = 1 := by
  intro w hw
  obtain ⟨r, hr, hw⟩ := List.mem_flatMap.mp hw
  have hr' : PresentedGroup.mk P.relatorSet (FreeGroup.mk r) = 1 := by
    rw [← P.prod_toTableWord]
    exact P.prod_tableRelators _ (List.mem_append_left _
      (List.mem_map.mpr ⟨r, hr, rfl⟩))
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨n, rfl⟩ := (List.mem_cyclicPermutations_iff.mp hw).symm
    exact P.mk_rotate_eq_one hr' n
  · obtain ⟨n, rfl⟩ := (List.mem_cyclicPermutations_iff.mp hw).symm
    apply P.mk_rotate_eq_one _ n
    rw [← FreeGroup.inv_mk, map_inv, hr', inv_one]

end TauCeti.GroupPresentation
