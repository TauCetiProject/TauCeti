/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.OneVariable
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Ideal
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Noetherianity of the one-variable restricted power-series algebra

Over a complete nonarchimedean field, the completed one-variable Huber algebra is identified with
Mathlib's univariate restricted-series ring by
`TauCeti.Huber.restrictedMvPowerSeriesCompletionOneEquiv`. The latter is noetherian by
one-variable Weierstrass division, so the completed Huber algebra is noetherian as well.

## Main results

* `TauCeti.Huber.isNoetherianRing_restrictedMvPowerSeriesCompletion_one`: the completed
  one-variable Tate algebra over a complete nonarchimedean field is noetherian.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.6, for noetherianity of Tate algebras.
* T. Wedhorn, *Adic Spaces*, §5.6, for restricted power series and their topology.
-/

public section

namespace TauCeti.Huber

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]
  [CompleteSpace K]

/-- **The completed one-variable Tate algebra over a complete nonarchimedean field is
noetherian.** This is the one-variable case of noetherianity for the canonical Huber completion,
transported from the restricted univariate series ring where Weierstrass division proves the
stronger principal-ideal theorem. -/
theorem isNoetherianRing_restrictedMvPowerSeriesCompletion_one :
    IsNoetherianRing (restrictedMvPowerSeriesCompletion 1 K) := by
  let _ := TauCeti.PowerSeries.isNoetherianRing_isRestricted_subring (K := K) (c := 1) zero_lt_one
  exact isNoetherianRing_of_ringEquiv _
    (restrictedMvPowerSeriesCompletionOneEquiv (R := K)).symm

end TauCeti.Huber
