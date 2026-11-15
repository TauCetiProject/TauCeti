/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Countable
public import TauCeti.ModelTheory.BackAndForth.Karp

/-!
# Potential isomorphism of finite structures

In a relational language, a structure potentially isomorphic to a finite structure `M` is
itself finite: potentially isomorphic structures are elementarily equivalent, and elementary
equivalence preserves finiteness (`FirstOrder.Language.ElementarilyEquivalent.infinite_iff`).
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

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- In a relational language, a structure potentially isomorphic to a finite structure is
finite. -/
theorem PotentialIso.finite [Finite M] (h : PotentialIso (L := L) M N) : Finite N :=
  not_infinite_iff_finite.mp fun hN =>
    not_infinite_iff_finite.mpr ‹Finite M›
      ((h.infEquivAt ℕ).elementarilyEquivalent.infinite_iff.mpr hN)

/-- In a relational language, a structure is potentially isomorphic to a finite structure
exactly when it is isomorphic to it. No cardinality assumption is made on `N`. -/
theorem finite_potentialIso_iff_iso [Finite M] :
    PotentialIso (L := L) M N ↔ Nonempty (M ≃[L] N) := by
  refine ⟨fun h => ?_, fun ⟨e⟩ => e.potentialIso⟩
  have := h.finite
  exact countable_potentialIso_iff_iso.mp h

end TauCeti
