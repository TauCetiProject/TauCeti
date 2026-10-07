/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.Restricted.OneVariable
public import TauCeti.RingTheory.Huber.StronglyNoetherian
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Noetherian
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Ideal

/-!
# Noetherianity of the completed Tate algebras

Over a complete nonarchimedean field, the completed Huber algebra in `n` variables is identified
with the Gauss-normed ring of unit-radius restricted series by
`TauCeti.Huber.restrictedMvPowerSeriesCompletionGaussEquiv`. The latter is noetherian by
Weierstrass division and induction on the number of variables, and this transfers to the
completed Huber algebra. In one variable it is moreover a principal ideal ring, transported from
Mathlib's univariate restricted-series ring along
`TauCeti.Huber.restrictedMvPowerSeriesCompletionOneEquiv`.

## Main results

* `TauCeti.Huber.isPrincipalIdealRing_restrictedMvPowerSeriesCompletion_one`: every ideal of the
  completed one-variable Tate algebra over a complete nonarchimedean field is principal.
* `TauCeti.Huber.isNoetherianRing_restrictedMvPowerSeriesCompletion`: the completed Tate algebra
  in `n` variables over a complete nonarchimedean field is noetherian.
* `TauCeti.Huber.IsStronglyNoetherian.of_normedField`: a complete nonarchimedean normed field is
  strongly noetherian.

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

/-- **The completed Tate algebra over a complete nonarchimedean field is noetherian.** This is
transported from the Gauss-normed ring of unit-radius restricted series in `n` variables. -/
theorem isNoetherianRing_restrictedMvPowerSeriesCompletion (n : ℕ) :
    IsNoetherianRing (restrictedMvPowerSeriesCompletion n K) := by
  have := TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring (K := K) (Fin n)
  exact isNoetherianRing_of_ringEquiv _ restrictedMvPowerSeriesCompletionGaussEquiv.symm

/-- **Complete nonarchimedean fields are strongly noetherian** (Bosch–Güntzer–Remmert §5.2.6):
every completed Tate algebra `K⟨X₁, …, Xₙ⟩` is noetherian. -/
instance IsStronglyNoetherian.of_normedField : IsStronglyNoetherian K :=
  ⟨isNoetherianRing_restrictedMvPowerSeriesCompletion⟩

end TauCeti.Huber
