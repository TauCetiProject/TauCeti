/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
# Length of a quotient of a discrete valuation ring

The length of `R/I` for a nonzero ideal of a discrete valuation ring is the exponent of its
maximal ideal in `I`. This is the local length calculation used for different ideals.
-/

public section

namespace Ideal

open IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The length of the quotient by a nonzero ideal of a discrete valuation ring is its
multiplicity at the maximal ideal. -/
theorem length_quotient_eq_multiplicity (I : Ideal R) (hI : I ≠ ⊥) :
    Module.length R (R ⧸ I) = multiplicity (maximalIdeal R) I := by
  have hgen : Submodule.IsPrincipal.generator I ≠ 0 := by
    intro hzero
    apply hI
    rw [← span_singleton_generator I, hzero, span_singleton_zero]
  rw [← span_singleton_generator I, ← Ring.ord]
  exact (Ring.ord_eq_addVal _).trans
    (TauCeti.IsDiscreteValuationRing.addVal_eq_multiplicity_span_singleton hgen)

end Ideal
