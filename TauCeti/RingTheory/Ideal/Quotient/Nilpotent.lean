/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Reducedness of the quotient by the nilradical

The quotient of a commutative ring by its nilradical is reduced. This instance makes reduced
coordinate rings available to constructions such as tensor products of reduced algebras.
-/

public section

namespace TauCeti

/-- The quotient of a commutative ring by its nilradical is reduced. -/
instance instIsReducedQuotientNilradical {R : Type*} [CommRing R] :
    IsReduced (R ⧸ nilradical R) := by
  rw [← Ideal.isRadical_iff_quotient_reduced, nilradical]
  exact Ideal.radical_isRadical ⊥

end TauCeti
