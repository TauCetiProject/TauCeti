/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Algebra.Polynomial.Lifts

/-!
# Monic polynomials over directed colimits of rings

Let `Ring.DirectLimit G f` be the directed colimit of commutative rings `G i`, indexed by a
nonempty directed preorder. Mathlib's `Ring.DirectLimit.Polynomial.exists_of` shows that every
polynomial over the colimit comes from a polynomial over some stage. This file shows that a monic
polynomial over the colimit comes from a monic polynomial of the same `natDegree` over some stage.

## Main results

* `TauCeti.Ring.DirectLimit.Polynomial.exists_monic_of`: a monic polynomial over the colimit is
  the image of a monic polynomial of the same `natDegree` over some stage.
-/

public section

open Polynomial

namespace TauCeti.Ring.DirectLimit

open _root_.Ring.DirectLimit

variable {ι : Type*} [Preorder ι] {G : ι → Type*} [∀ i, CommRing (G i)]
  {f : ∀ i j, i ≤ j → G i →+* G j}

/-- A monic polynomial over a directed colimit of rings is the image of a monic polynomial of the
same `natDegree` over some stage. -/
theorem Polynomial.exists_monic_of [Nonempty ι] [IsDirectedOrder ι]
    {P : (_root_.Ring.DirectLimit G (f · · ·))[X]} (hP : P.Monic) :
    ∃ i, ∃ p : (G i)[X], p.Monic ∧ p.natDegree = P.natDegree ∧ p.map (of G (f · · ·) i) = P := by
  obtain ⟨i, p, hp⟩ := _root_.Ring.DirectLimit.Polynomial.exists_of P
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic ((mem_lifts P).2 ⟨p, hp⟩) hP
  exact ⟨i, q, hqm, hqd, hq⟩

end TauCeti.Ring.DirectLimit
