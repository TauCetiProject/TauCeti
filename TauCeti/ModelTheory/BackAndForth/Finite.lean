/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Countable
public import TauCeti.ModelTheory.BackAndForth.Karp
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Potential isomorphism of finite structures

In a relational language, a structure potentially isomorphic to a finite structure `M` is
itself finite: potentially isomorphic structures are elementarily equivalent, and the
first-order sentence saying that there are not `Nat.card M + 1` distinct elements transfers.
Since finite structures are countable, potential isomorphism with a finite structure is
therefore isomorphism, with no cardinality assumption on the other structure. For infinite
structures this fails: `ℚ` and `ℝ` are potentially isomorphic dense linear orders but are not
isomorphic.

## Main results

* `TauCeti.PotentialIso.finite`: potential isomorphism transfers finiteness.
* `TauCeti.finite_potentialIso_iff_iso`: a structure is potentially isomorphic to a finite
  structure exactly when it is isomorphic to it.
-/

public section

universe u v w w'

namespace TauCeti

open FirstOrder FirstOrder.Language Cardinal

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- In a relational language, a structure potentially isomorphic to a finite structure is
finite. -/
theorem PotentialIso.finite [Finite M] (h : PotentialIso (L := L) M N) : Finite N := by
  have hM : M ⊨ (Sentence.cardGe L (Nat.card M + 1)).not := by
    simp [Sentence.realize_not, Sentence.realize_cardGe, ← Nat.cast_card]
  have hN := ((h.infEquivAt ℕ).elementarilyEquivalent.realize_sentence _).mp hM
  rw [Sentence.realize_not, Sentence.realize_cardGe, not_le] at hN
  exact lt_aleph0_iff_finite.mp (hN.trans natCast_lt_aleph0)

/-- In a relational language, a structure is potentially isomorphic to a finite structure
exactly when it is isomorphic to it. No cardinality assumption is made on `N`. -/
theorem finite_potentialIso_iff_iso [Finite M] :
    PotentialIso (L := L) M N ↔ Nonempty (M ≃[L] N) := by
  refine ⟨fun h => ?_, fun ⟨e⟩ => e.potentialIso⟩
  have := h.finite
  exact countable_potentialIso_iff_iso.mp h

end TauCeti
