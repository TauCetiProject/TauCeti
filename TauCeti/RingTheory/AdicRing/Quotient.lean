/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicRing.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian

import TauCeti.RingTheory.AdicCompletion.Finite

/-!
# Quotients of noetherian complete adic rings

The instance `TauCeti.IsAdicRing.quotient` shows that the quotient of a noetherian complete
adic ring by any ideal is again a complete adic ring with its quotient topology. Thus imposing
ideal relations preserves the complete adic structure in the noetherian setting.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0,
  (7.3.5) and (7.3.6).
-/

public section

namespace TauCeti.IsAdicRing

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsAdicRing A] [IsNoetherianRing A]

/-- Every quotient of a noetherian complete adic ring is a complete adic ring for the
quotient topology. -/
instance (priority := 100) quotient (J : Ideal A) : IsAdicRing (A ⧸ J) := by
  obtain ⟨I, hfg, hI, hc⟩ := exists_isAdic (A := A)
  have : IsAdicComplete I A := hc
  have : IsAdicComplete I (A ⧸ J) := IsAdicComplete.of_finite I (A ⧸ J)
  refine ⟨I.map (Ideal.Quotient.mk J), hfg.map _,
    TauCeti.IsAdic.map_of_isOpenQuotientMap hI _ (QuotientRing.isOpenQuotientMap_mk J), ?_⟩
  exact (IsAdicComplete.map_algebraMap_iff I (A ⧸ J)).mpr inferInstance

end TauCeti.IsAdicRing
