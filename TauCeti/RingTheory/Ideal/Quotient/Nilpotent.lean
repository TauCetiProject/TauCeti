/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Reducedness of the quotient by the nilradical

The quotient of a commutative ring by its nilradical is reduced.

## Main declarations

* `TauCeti.isReduced_quotient_nilradical`: `A ⧸ nilradical A` is reduced.
-/

public section

namespace TauCeti

/-- The quotient of a commutative ring by its nilradical is reduced. -/
instance isReduced_quotient_nilradical (A : Type*) [CommRing A] :
    IsReduced (A ⧸ nilradical A) := by
  rw [← Ideal.isRadical_iff_quotient_reduced, nilradical]
  exact Ideal.radical_isRadical ⊥

end TauCeti
