/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import TauCeti.Algebra.Lie.Quotient

/-!
# Killing quotients of supplements

A Lie subalgebra `P` supplementing an ideal `I`, so that `I + P = L`, has quotient
`P ⧸ (I ∩ P)` isomorphic to `L ⧸ I` by the first isomorphism theorem. Consequently the
Killing property of `L ⧸ I` transfers to this quotient of `P`.

## Main results

* `LieIdeal.isKilling_quotient_comap_incl`: if `I + P = L` and `L ⧸ I` is Killing, so is
  `P ⧸ (I ∩ P)`.
-/

public section

namespace TauCeti

open LieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (I : LieIdeal R L) {P : LieSubalgebra R L}

/-- A Lie subalgebra `P` supplementing an ideal `I` with Killing quotient has Killing quotient by
`I ∩ P`, since `P ⧸ (I ∩ P)` is isomorphic to `L ⧸ I`. -/
theorem _root_.LieIdeal.isKilling_quotient_comap_incl [IsKilling R (L ⧸ I)]
    (hIP : Codisjoint I.toSubmodule P.toSubmodule) : IsKilling R (P ⧸ I.comap P.incl) := by
  rw [← I.ker_mkQ_comp_incl]
  exact isKilling_of_equiv
    ((I.mkQ.comp P.incl).quotKerEquivOfSurjective (I.mkQ_comp_incl_surjective hIP)).symm

end TauCeti
