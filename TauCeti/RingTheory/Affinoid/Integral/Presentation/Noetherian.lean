/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Integral.Presentation.Basic

import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.RingTheory.Huber.Restricted.Noetherian
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Noetherian

/-!
# Noetherianity of integral presentation rings

When the closed unit ball `K°` of a complete ultrametric normed field `K` is noetherian (for
instance when `K` has a strict norm gap below `1`, or when `K` is nontrivially normed with
noetherian valuation ring `𝒪[K]`, such as a complete discretely valued field), every integral
presentation subring `π(K⟨X⟩°)` in finitely many variables is noetherian, and every submodule of
a finitely generated module over an integral affinoid presentation `A₀` is finitely generated.

For the general case over an arbitrary complete ultrametric normed field `K`, where `A₀` need not
be noetherian, see `TauCeti.RingTheory.Affinoid.AlmostNoetherian` for Kiehl's almost
noetherianity theorem.

## Main results

* `AlgHom.isNoetherianRing_map_unitClosedBall` (registered as an instance),
  `AlgHom.isNoetherianRing_map_unitClosedBall_of_isNoetherianRing_integer`,
  `AlgHom.isNoetherianRing_map_unitClosedBall_of_forall_norm_le`: noetherianity of `π(K⟨X⟩°)` in
  finitely many variables when `K°` (or `𝒪[K]`) is noetherian or `K` has a strict norm gap
  below `1`.
* `TauCeti.Huber.IntegralAffinoidPresentation.isNoetherianRing_subring`: the open bounded subring
  `A₀` of an integral affinoid presentation is noetherian whenever `K°` is noetherian (without
  assuming completeness of `K`).
* `TauCeti.Huber.IntegralAffinoidPresentation.fg_of_isNoetherianRing`: every submodule of a
  finitely generated `A₀`-module is finitely generated whenever `K°` is noetherian.

## References

* S. Bosch, *Lectures on Formal and Rigid Geometry*, Lecture Notes in Mathematics 2105, Springer
  (2014), §6.4, Lemma 5 (pp. 137–138).
-/

public section

namespace AlgHom

open _root_.MvPowerSeries
open scoped NormedField Valued

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type*}
  {A : Type*} [CommRing A] [Algebra K A]

local notation "Tate " τ:max => IsRestricted.subring (R := K) (fun _ : τ ↦ 1)

/-- **Noetherianity of integral presentation rings.** Over a complete ultrametric normed field `K`
whose closed unit ball `K°` is noetherian (for instance a complete discretely valued field), every
integral presentation subring `π(K⟨X⟩°)` in finitely many variables is noetherian. -/
instance isNoetherianRing_map_unitClosedBall [CompleteSpace K] [_root_.Finite σ]
    [IsNoetherianRing (Subring.unitClosedBall K)] (π : Tate σ →ₐ[K] A) :
    IsNoetherianRing ((Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A)) := by
  let φ := (RingEquiv.subringCongr π.range_comp_subtype_unitClosedBall).toRingHom.comp
    ((π : Tate σ →+* A).comp (Subring.unitClosedBall (Tate σ)).subtype).rangeRestrict
  exact isNoetherianRing_of_surjective _ _ φ (by
    simpa only [φ, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] using
      (RingEquiv.surjective _).comp (RingHom.rangeRestrict_surjective _))

/-- Over a complete nontrivially normed ultrametric field `K` whose valuation ring `𝒪[K]` is
noetherian (for instance a complete discretely valued field), every integral presentation subring
`π(K⟨X⟩°)` in finitely many variables is noetherian. -/
theorem isNoetherianRing_map_unitClosedBall_of_isNoetherianRing_integer
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsNoetherianRing 𝒪[K]] {σ : Type*} [_root_.Finite σ]
    {A : Type*} [CommRing A] [Algebra K A]
    (π : IsRestricted.subring (R := K) (fun _ : σ ↦ 1) →ₐ[K] A) :
    IsNoetherianRing ((Subring.unitClosedBall
      (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))).map
        (π : IsRestricted.subring (R := K) (fun _ : σ ↦ 1) →+* A)) := by
  have : IsNoetherianRing (Subring.unitClosedBall K) :=
    isNoetherianRing_of_surjective _ _ TauCeti.integerUnitClosedBallEquiv.toRingHom
      TauCeti.integerUnitClosedBallEquiv.surjective
  infer_instance

/-- Over a complete ultrametric normed field `K` with a strict norm gap `ρ < 1` above
`{‖a‖ < 1}`, every integral presentation subring `π(K⟨X⟩°)` in finitely many variables is
noetherian. -/
theorem isNoetherianRing_map_unitClosedBall_of_forall_norm_le [CompleteSpace K] [_root_.Finite σ]
    (π : Tate σ →ₐ[K] A) {ρ : ℝ} (hρ1 : ρ < 1) (hρ : ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ) :
    IsNoetherianRing ((Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A)) := by
  have : IsNoetherianRing (Subring.unitClosedBall K) :=
    TauCeti.isNoetherianRing_unitClosedBall_iff_exists_forall_norm_le.mpr ⟨ρ, hρ1, hρ⟩
  infer_instance

end AlgHom

namespace TauCeti.Huber.IntegralAffinoidPresentation

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  {A : Type*} [CommRing A] [Algebra K A] [TopologicalSpace A]
  {n : ℕ} {A₀ : Subring A}

/-- **Noetherianity of an integral affinoid presentation subring.** When `K°` is noetherian (for
instance when `K°` is a discrete valuation ring), the presented open bounded subring `A₀` is
noetherian (without assuming completeness of `K`). -/
theorem isNoetherianRing_subring (P : IntegralAffinoidPresentation K A n A₀)
    [IsNoetherianRing (Subring.unitClosedBall K)] : IsNoetherianRing A₀ := by
  have : IsNoetherianRing (restrictedMvPowerSeriesCompletion n (Subring.unitClosedBall K)) :=
    (IsStronglyNoetherian.unitClosedBall (K := K)).isNoetherianRing n
  exact isNoetherianRing_of_surjective _ _ P.hom P.surjective_hom

/-- **Finite generation over a noetherian unit ball.** When `K°` is noetherian, every submodule `N`
of a finitely generated `A₀`-module `M` is finitely generated (without assuming completeness of
`K`). -/
theorem fg_of_isNoetherianRing (P : IntegralAffinoidPresentation K A n A₀)
    [IsNoetherianRing (Subring.unitClosedBall K)]
    {M : Type*} [AddCommGroup M] [Module A₀ M] [Module.Finite A₀ M]
    (N : Submodule A₀ M) : N.FG := by
  have := P.isNoetherianRing_subring
  exact IsNoetherian.noetherian N

end TauCeti.Huber.IntegralAffinoidPresentation
