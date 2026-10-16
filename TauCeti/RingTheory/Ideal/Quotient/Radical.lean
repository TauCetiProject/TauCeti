/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Finiteness.Defs

import Mathlib.RingTheory.Finiteness.NilpotentKer
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Finiteness from a radical quotient

A quotient algebra is module-finite if its reduced quotient is module-finite and the radical
of the defining ideal is finitely generated. This is useful for passing from finite residue
fields to finite infinitesimal neighbourhoods, without assuming that the algebra itself is
finite over the coefficient ring.

The descent step is Mathlib's `Module.finite_of_surjective_of_ker_le_nilradical`.
-/

public section

namespace Ideal

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Finiteness of the quotient by the radical descends to the original quotient when the
radical is finitely generated. -/
theorem moduleFinite_quotient_of_radical (I : Ideal A) (hI : I.radical.FG)
    [Module.Finite R (A ⧸ I.radical)] : Module.Finite R (A ⧸ I) := by
  apply Module.finite_of_surjective_of_ker_le_nilradical
    (Ideal.Quotient.factorₐ R I.le_radical) (Ideal.Quotient.factor_surjective I.le_radical)
  · rw [← RingHom.ker_coe_toRingHom, Ideal.Quotient.coe_factorₐ, Ideal.Quotient.factor_ker]
    exact (Ideal.map_radical_le (f := Ideal.Quotient.mk I)).trans
      (by rw [Ideal.map_quotient_self]; rfl)
  · rw [← RingHom.ker_coe_toRingHom, Ideal.Quotient.coe_factorₐ, Ideal.Quotient.factor_ker]
    exact hI.map _

end Ideal
