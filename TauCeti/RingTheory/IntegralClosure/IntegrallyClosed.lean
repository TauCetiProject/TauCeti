/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Preimages of integrally closed subrings

If a subring `S` of `B` is integrally closed in `B`, then its preimage under a ring homomorphism
`f : A → B` is integrally closed in `A`: an element of `A` integral over the preimage is sent by
`f` to an element integral over `S`, which therefore lies in `S`.

## Main results

* `Subring.isIntegrallyClosedIn_comap`: the preimage of an integrally closed subring is integrally
  closed.
-/

public section

namespace Subring

variable {A B : Type*} [CommRing A] [CommRing B]

/-- **The preimage of an integrally closed subring is integrally closed**: if `S` is integrally
closed in `B`, then `S.comap f` is integrally closed in `A` for every ring homomorphism
`f : A →+* B`. -/
instance isIntegrallyClosedIn_comap (f : A →+* B) (S : Subring B) [IsIntegrallyClosedIn S B] :
    IsIntegrallyClosedIn (S.comap f) A :=
  Subring.isIntegrallyClosedIn_iff.mpr fun _ hx ↦ (Subring.isIntegrallyClosedIn_iff (S := S)).mp
    inferInstance (hx.map_of_comp_eq (f.restrict _ S fun _ hy ↦ hy) f rfl)

end Subring
