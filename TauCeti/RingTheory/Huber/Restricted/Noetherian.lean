/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
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
needed: whenever `K°` (respectively `𝒪[K]`) is noetherian, its topology is either discrete or
`ϖ`-adic for any pseudouniformiser `ϖ`, so `K°` and `𝒪[K]` are strongly noetherian and every
completed restricted-series ring `𝒪[K]⟨X₁, …, Xₙ⟩` and its quotients are noetherian.

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
* `TauCeti.Huber.isNoetherianRing_restrictedMvPowerSeriesCompletion_integer`:
  `restrictedMvPowerSeriesCompletion n 𝒪[K]` is noetherian whenever `𝒪[K]` is noetherian.
* `RingHom.isNoetherianRing_of_surjective_restrictedMvPowerSeriesCompletion_integer` and
  `RingHom.fg_of_surjective_restrictedMvPowerSeriesCompletion_integer`: quotients of
  `𝒪[K]⟨X₁, …, Xₙ⟩` are noetherian and submodules of finitely generated modules over them are
  finitely generated whenever `𝒪[K]` is noetherian.

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
is strongly noetherian.** Its subspace topology is `ϖ`-adic for any `0 < ‖ϖ‖ < 1`, so completed
restricted series over `𝒪[K]` are noetherian without assuming `K` is complete. -/
instance IsStronglyNoetherian.integer {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [IsNoetherianRing 𝒪[K]] : IsStronglyNoetherian 𝒪[K] := by
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt_one K
  have hϖ : IsPseudoUniformizer ϖ :=
    isPseudoUniformizer_iff_norm_lt_one.mpr ⟨norm_pos_iff.mp hϖ0, hϖ1⟩
  have hadic : IsAdic (Ideal.span {(⟨ϖ, Valued.integer.mem_iff.mpr hϖ1.le⟩ : 𝒪[K])}) :=
    (𝒪[K]).isAdic_span_singleton_of_isOpen_of_isBounded
      (by simpa [TauCeti.integer_eq_unitClosedBall] using Subring.isOpen_unitClosedBall K)
      ((isBounded_closedBall_zero (R := K) 1).subset fun _ hx ↦
        mem_closedBall_zero_iff.mpr (Valued.integer.mem_iff.mp hx))
      hϖ (Valued.integer.mem_iff.mpr hϖ1.le)
  exact ⟨fun n ↦ isNoetherianRing_restrictedMvPowerSeriesCompletion_of_isAdic n hadic⟩

/-- **Noetherianity of `𝒪[K]⟨X₁, …, Xₙ⟩` when `𝒪[K]` is noetherian.** Over a nontrivially normed
ultrametric field `K` (not necessarily complete) whose valuation ring `𝒪[K]` is noetherian
(equivalently, a discrete valuation ring), `restrictedMvPowerSeriesCompletion n 𝒪[K]` is
noetherian. -/
theorem isNoetherianRing_restrictedMvPowerSeriesCompletion_integer {K : Type*}
    [NontriviallyNormedField K] [IsUltrametricDist K] [IsNoetherianRing 𝒪[K]] (n : ℕ) :
    IsNoetherianRing (restrictedMvPowerSeriesCompletion n 𝒪[K]) :=
  inferInstance

/-- **Quotients of `𝒪[K]⟨X₁, …, Xₙ⟩` are noetherian when `𝒪[K]` is noetherian.** Over a
nontrivially normed ultrametric field `K` (not necessarily complete) with noetherian valuation
ring `𝒪[K]`, any ring receiving a surjective homomorphism from
`restrictedMvPowerSeriesCompletion n 𝒪[K]` is noetherian. -/
theorem _root_.RingHom.isNoetherianRing_of_surjective_restrictedMvPowerSeriesCompletion_integer
    {K A₀ : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [IsNoetherianRing 𝒪[K]]
    [CommRing A₀] {n : ℕ} (φ : restrictedMvPowerSeriesCompletion n 𝒪[K] →+* A₀)
    (hφ : Function.Surjective φ) : IsNoetherianRing A₀ :=
  isNoetherianRing_of_surjective _ _ φ hφ

/-- **Every submodule of a finitely generated module over a quotient of `𝒪[K]⟨X₁, …, Xₙ⟩` is
finitely generated when `𝒪[K]` is noetherian.** Over a nontrivially normed ultrametric field `K`
(not necessarily complete) with noetherian valuation ring `𝒪[K]`, any submodule of a finitely
generated module over a quotient `A₀` of `𝒪[K]⟨X₁, …, Xₙ⟩` is finitely generated. -/
theorem _root_.RingHom.fg_of_surjective_restrictedMvPowerSeriesCompletion_integer
    {K A₀ M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [IsNoetherianRing 𝒪[K]]
    [CommRing A₀] [AddCommGroup M] [Module A₀ M] [Module.Finite A₀ M] {n : ℕ}
    (φ : restrictedMvPowerSeriesCompletion n 𝒪[K] →+* A₀) (hφ : Function.Surjective φ)
    (N : Submodule A₀ M) : N.FG := by
  have : IsNoetherianRing A₀ :=
    φ.isNoetherianRing_of_surjective_restrictedMvPowerSeriesCompletion_integer hφ
  exact IsNoetherian.noetherian N

end Integral

end TauCeti.Huber
