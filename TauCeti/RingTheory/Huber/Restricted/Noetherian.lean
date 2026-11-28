/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.Gauss.Norm
public import TauCeti.RingTheory.Huber.Restricted.OneVariable
public import TauCeti.RingTheory.Huber.StronglyNoetherian
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Ideal

import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.RingTheory.Huber.Restricted.Adic

/-!
# Noetherianity of the completed Tate algebras

Over a complete nonarchimedean field, the completed Huber algebra in `n` variables is identified
with the Gauss-normed ring of unit-radius restricted series by
`TauCeti.Huber.restrictedMvPowerSeriesCompletionGaussEquiv`. The latter is noetherian by
Kedlaya's Gröbner-basis argument
(`TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring`), and this transfers to the
completed Huber algebra. In one variable it is moreover a principal ideal ring, transported from
Mathlib's univariate restricted-series ring along
`TauCeti.Huber.restrictedMvPowerSeriesCompletionOneEquiv`.

Conversely, over a complete nonarchimedean field, strong noetherianness of the completed
Huber algebras transfers back to the Gauss-normed ring `K⟨X₁, …, Xₙ⟩`, which is therefore a
complete strongly noetherian ring. When the norm of `K` is nontrivial it is moreover a Tate ring
(`TauCeti.Huber.IsTateRing.isRestricted_subring`); for instance `ℚ_p⟨T₁, …, Tₙ⟩`.

For the integral subrings `K° = Subring.unitClosedBall K` and `𝒪[K]`, no completeness of `K` is
needed: whenever `K°` is noetherian, its topology is either discrete or `ϖ`-adic for any
pseudouniformiser `ϖ`, so `K°` is strongly noetherian, and transporting along
`TauCeti.integerUnitClosedBallEquiv` yields the same for `𝒪[K]` when `K` is nontrivially normed.

## Main results

* `TauCeti.Huber.isPrincipalIdealRing_restrictedMvPowerSeriesCompletion_one`: every ideal of the
  completed one-variable Tate algebra over a complete nonarchimedean field is principal.
* `TauCeti.Huber.isNoetherianRing_restrictedMvPowerSeriesCompletion`: the completed Tate algebra
  in `n` variables over a complete nonarchimedean field is noetherian.
* `TauCeti.Huber.IsStronglyNoetherian.of_normedField`: a complete nonarchimedean normed field is
  strongly noetherian.
* `TauCeti.Huber.IsStronglyNoetherian.isRestricted_subring`: the Gauss-normed Tate algebra
  `K⟨X₁, …, Xₙ⟩` over a complete normed field with an ultrametric norm is strongly noetherian.
* `TauCeti.Huber.IsStronglyNoetherian.unitClosedBall` and
  `TauCeti.Huber.IsStronglyNoetherian.integer`: when `K°` or `𝒪[K]` is noetherian, it is strongly
  noetherian (without assuming `K` is complete).

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.6, for noetherianity of Tate algebras.
* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016, no. 8,
  2544–2567; arXiv:1410.5160v3, Theorem 3.2, for the Gröbner-basis argument.
* T. Wedhorn, *Adic Spaces*, §5.6, for restricted power series and their topology.
-/

public section

namespace TauCeti.Huber

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **The completed one-variable Tate algebra over a complete nonarchimedean field is a principal
ideal ring.** This is transported from the restricted univariate series ring, where Weierstrass
division shows that every ideal has a generator. -/
theorem isPrincipalIdealRing_restrictedMvPowerSeriesCompletion_one :
    IsPrincipalIdealRing (restrictedMvPowerSeriesCompletion 1 K) := by
  have := TauCeti.PowerSeries.isPrincipalIdealRing_isRestricted_subring (K := K) (c := 1)
  exact IsPrincipalIdealRing.of_surjective _
    (restrictedMvPowerSeriesCompletionOneEquiv (R := K)).symm.surjective

/-- **The completed Tate algebra over a complete nonarchimedean field is noetherian.** This is
transported from the Gauss-normed ring of unit-radius restricted series in `n` variables. -/
theorem isNoetherianRing_restrictedMvPowerSeriesCompletion (n : ℕ) :
    IsNoetherianRing (restrictedMvPowerSeriesCompletion n K) := by
  have := TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring (K := K)
    (c := fun _ : Fin n ↦ 1)
  exact isNoetherianRing_of_ringEquiv _ restrictedMvPowerSeriesCompletionGaussEquiv.symm

/-- **Complete nonarchimedean fields are strongly noetherian** (Bosch–Güntzer–Remmert §5.2.6):
every completed Tate algebra `K⟨X₁, …, Xₙ⟩` is noetherian. -/
instance IsStronglyNoetherian.of_normedField : IsStronglyNoetherian K :=
  ⟨isNoetherianRing_restrictedMvPowerSeriesCompletion⟩

section GaussNorm

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **The Gauss-normed Tate algebra over a complete nonarchimedean field is strongly noetherian.**
Over a complete normed field `K` with an ultrametric norm, every restricted power-series algebra
over the Banach algebra `K⟨X₁, …, Xₙ⟩` of unit-radius restricted series with its Gauss norm is
noetherian. -/
instance IsStronglyNoetherian.isRestricted_subring (n : ℕ) :
    IsStronglyNoetherian (MvPowerSeries.IsRestricted.subring (R := K) fun _ : Fin n ↦ (1 : ℝ)) := by
  -- `K` is Huber: discrete if its norm is trivial, and Tate if it is nontrivially normed
  have : IsHuberRing K := by
    rcases NormedField.discreteTopology_or_nontriviallyNormedField K with _ | ⟨_, rfl⟩
    · infer_instance
    · exact (IsTateRing.of_nontriviallyNormedField K).toIsHuberRing
  -- `K⟨X₁, …, Xₙ⟩` is the completed Huber algebra `restrictedMvPowerSeriesCompletion n K`, up to
  -- an isomorphism continuous in both directions, and that algebra is strongly noetherian
  exact (isStronglyNoetherian_congr restrictedMvPowerSeriesCompletionGaussEquiv
    continuous_restrictedMvPowerSeriesCompletionGaussEquiv
    continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm).mp inferInstance

end GaussNorm

section Integral

open scoped NormedField Valued

/-- **If the closed unit ball `K°` of an ultrametric normed field is noetherian, it is strongly
noetherian.** When `K` is trivially normed, `K°` is discrete; when `K` is nontrivially normed,
`K°` carries the `ϖ`-adic topology for any `0 < ‖ϖ‖ < 1`, so completed restricted series over
`K°` are noetherian without assuming `K` is complete. -/
instance IsStronglyNoetherian.unitClosedBall {K : Type*} [NormedField K] [IsUltrametricDist K]
    [IsNoetherianRing (Subring.unitClosedBall K)] :
    IsStronglyNoetherian (Subring.unitClosedBall K) := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField K with _ | ⟨_, rfl⟩
  · infer_instance
  · obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt_one K
    have hϖ : IsPseudoUniformizer ϖ :=
      isPseudoUniformizer_iff_norm_lt_one.mpr ⟨norm_pos_iff.mp hϖ0, hϖ1⟩
    have hadic : IsAdic
        (Ideal.span {(⟨ϖ, Subring.mem_unitClosedBall.mpr hϖ1.le⟩ : Subring.unitClosedBall K)}) :=
      (Subring.unitClosedBall K).isAdic_span_singleton_of_isOpen_of_isBounded
        (Subring.isOpen_unitClosedBall K)
        ((isBounded_closedBall_zero (R := K) 1).subset fun _ hx ↦
          mem_closedBall_zero_iff.mpr (Subring.mem_unitClosedBall.mp hx))
        hϖ (Subring.mem_unitClosedBall.mpr hϖ1.le)
    exact ⟨fun n ↦ isNoetherianRing_restrictedMvPowerSeriesCompletion_of_isAdic n hadic⟩

/-- **If the valuation ring `𝒪[K]` of a nontrivially normed ultrametric field is noetherian, it
is strongly noetherian.** Transported from `IsStronglyNoetherian.unitClosedBall` along
`TauCeti.integerUnitClosedBallEquiv`, without assuming `K` is complete. -/
instance IsStronglyNoetherian.integer {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [IsNoetherianRing 𝒪[K]] : IsStronglyNoetherian 𝒪[K] := by
  have : IsNoetherianRing (Subring.unitClosedBall K) :=
    isNoetherianRing_of_ringEquiv 𝒪[K] (TauCeti.integerUnitClosedBallEquiv (K := K))
  exact (isStronglyNoetherian_congr TauCeti.integerUnitClosedBallEquiv
    TauCeti.continuous_integerUnitClosedBallEquiv
    TauCeti.continuous_integerUnitClosedBallEquiv_symm).mpr inferInstance

end Integral

end TauCeti.Huber
