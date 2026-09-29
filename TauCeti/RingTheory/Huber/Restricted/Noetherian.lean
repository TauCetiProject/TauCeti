/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.OneVariable
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Ideal

/-!
# Noetherianity of the one-variable restricted power-series algebra

Over a complete nonarchimedean field, the completed one-variable Huber algebra is identified with
Mathlib's univariate restricted-series ring by
`TauCeti.Huber.restrictedMvPowerSeriesCompletionOneEquiv`. The latter is noetherian by
one-variable Weierstrass division; in fact it is a principal ideal ring. Both properties transfer
to the completed Huber algebra.

## Main results

* `TauCeti.Huber.isPrincipalIdealRing_restrictedMvPowerSeriesCompletion_one`: every ideal of the
  completed one-variable Tate algebra over a complete nonarchimedean field is principal.
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

/-- **The completed one-variable Tate algebra over a complete nonarchimedean field is a principal
ideal ring.** This is transported from the restricted univariate series ring, where Weierstrass
division shows that every ideal has a generator. -/
theorem isPrincipalIdealRing_restrictedMvPowerSeriesCompletion_one :
    IsPrincipalIdealRing (restrictedMvPowerSeriesCompletion 1 K) := by
  have := TauCeti.PowerSeries.isPrincipalIdealRing_isRestricted_subring (K := K) (c := 1)
    zero_lt_one
  exact IsPrincipalIdealRing.of_surjective _
    (restrictedMvPowerSeriesCompletionOneEquiv (R := K)).symm.surjective

/-- **The completed one-variable Tate algebra over a complete nonarchimedean field is
noetherian.** This is the one-variable case of noetherianity for the canonical Huber completion,
transported from the restricted univariate series ring where Weierstrass division proves the
stronger principal-ideal theorem. -/
theorem isNoetherianRing_restrictedMvPowerSeriesCompletion_one :
    IsNoetherianRing (restrictedMvPowerSeriesCompletion 1 K) := by
  have := isPrincipalIdealRing_restrictedMvPowerSeriesCompletion_one (K := K)
  exact PrincipalIdealRing.isNoetherianRing

end TauCeti.Huber
