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

Every ideal of a localization `S` of `R` is extended from its contraction to `R`
(`IsLocalization.map_under`). So if every ideal of `R` is principal, so is every ideal of `S`:
a localization of a principal ideal ring is a principal ideal ring. For instance `ℤ[1/n]` is a
principal ideal domain, which makes the structure theorem for finitely generated modules over a
principal ideal domain available for its modules.

## Main results

* `IsLocalization.isPrincipalIdealRing`: a localization of a principal ideal ring is a principal
  ideal ring.
-/

public section

namespace IsLocalization

variable {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*) [CommSemiring S] [Algebra R S]
  [IsLocalization M S]

include M in
/-- **A localization of a principal ideal ring is a principal ideal ring.** -/
theorem isPrincipalIdealRing [IsPrincipalIdealRing R] : IsPrincipalIdealRing S where
  principal I := by
    obtain ⟨x, hx⟩ := (IsPrincipalIdealRing.principal (I.under R)).principal
    refine ⟨algebraMap R S x, ?_⟩
    rw [← map_under M S I, hx, ← Ideal.span, Ideal.map_span, Set.image_singleton]

end IsLocalization
