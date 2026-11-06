/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Localizations of principal ideal rings

Every ideal of a localization `S = M⁻¹R` is extended from its contraction to `R`
(`IsLocalization.map_under`), and the extension of a principal ideal is principal. So a
localization of a principal ideal ring is again a principal ideal ring. For instance the rings
`ℤ[1/m] = Localization.Away m` are principal ideal domains, so the structure theorem for finitely
generated modules over a principal ideal domain applies to modules over them.

## Main results

* `IsLocalization.isPrincipalIdealRing`: a localization of a principal ideal ring is a principal
  ideal ring.
-/

public section

namespace IsLocalization

variable {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*) [CommSemiring S]
  [Algebra R S] [IsLocalization M S]

include M in
/-- **A localization of a principal ideal ring is a principal ideal ring.** -/
theorem isPrincipalIdealRing [IsPrincipalIdealRing R] : IsPrincipalIdealRing S where
  principal J := by
    rw [← map_under M S J]
    exact (IsPrincipalIdealRing.principal _).map_ringHom _

instance [IsPrincipalIdealRing R] : IsPrincipalIdealRing (Localization M) :=
  isPrincipalIdealRing M _

end IsLocalization
