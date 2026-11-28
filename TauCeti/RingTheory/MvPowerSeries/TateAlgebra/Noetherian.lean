/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall

import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.Analysis.Normed.Field.Basic
import TauCeti.Analysis.Normed.Group.Ultra

/-!
# Noetherianity of the Gauss unit ball when `K°` is noetherian

Let `K` be a complete ultrametric normed field with closed unit ball `K° = Subring.unitClosedBall K`
and let `T = K⟨X⟩` be the Tate algebra of unit-radius restricted power series in finitely many
variables `σ`, with Gauss unit ball `T° = Subring.unitClosedBall T`.

When `K°` is noetherian — equivalently when `K` has a strict norm gap below `1`, that is, when `K`
is either trivially normed or discretely valued — `K°` carries a Euclidean valuation degree
compatible with its ultrametric norm: an element of larger norm (smaller degree) divides one of
smaller norm in `K°`, while an element of strictly smaller degree (strictly larger norm) is left as
remainder. Kedlaya's Gröbner-basis theorem
(`TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring_of_division`) therefore makes
`K°{X/r}` and `T°` noetherian rings in finitely many variables for every positive polyradius `r`.
When `K` is moreover nontrivially normed, `𝒪[K]` is isomorphic to `K°`, so `𝒪[K]{X/r}` is
likewise noetherian whenever `𝒪[K]` is noetherian. Conversely, the constant-coefficient retraction
(`isNoetherianRing_unitClosedBall_of_isNoetherianRing_restrictedUnitClosedBall` in
`TauCeti.MvPowerSeries`) descends noetherianity from `T°` back to `K°`.

## Main results

* `TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring_unitClosedBall`: in finitely many
  variables at any positive polyradius `r`, `K°{X/r}` is noetherian whenever `K°` is noetherian
  and `K` is complete.
* `TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring_integer`: over a complete
  nontrivially normed ultrametric field `K`, `𝒪[K]{X/r}` in finitely many variables is noetherian
  at any positive polyradius `r` whenever `𝒪[K]` is noetherian.
* `TauCeti.MvPowerSeries.isNoetherianRing_unitClosedBall`: in finitely many variables, `T°` is
  noetherian when `K°` is.
* `TauCeti.MvPowerSeries.isNoetherianRing_unitClosedBall_iff`: in finitely many variables, `T°` is
  noetherian if and only if `K°` is.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §5.2.6.
* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, Int. Math. Res. Not. 2016
  (2016), no. 8, 2544–2567.
-/

public section

open _root_.MvPowerSeries
open scoped NormedField Valued

namespace TauCeti.MvPowerSeries

section Noetherian

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "Tate " τ:max => IsRestricted.subring (R := K) (fun _ : τ ↦ 1)

/-- **Restricted power series over `K°` are noetherian when `K°` is noetherian.** Over a complete
ultrametric normed field `K` with noetherian closed unit ball `K°`, `K°` carries a Euclidean
valuation degree compatible with its ultrametric norm, so `K°{X/r}` is noetherian for every finite
variable set `σ` and positive polyradius `r`. -/
instance isNoetherianRing_isRestricted_subring_unitClosedBall [CompleteSpace K] [Finite σ]
    {r : σ → ℝ} [∀ i, Fact (0 < r i)] [IsNoetherianRing (Subring.unitClosedBall K)] :
    IsNoetherianRing (IsRestricted.subring (R := Subring.unitClosedBall K) r) := by
  classical
  let O := Subring.unitClosedBall K
  have hclosed : IsClosed ((O : Subring K) : Set K) := by
    rw [Subring.coe_unitClosedBall]
    exact Metric.isClosed_closedBall
  have : CompleteSpace O := hclosed.completeSpace_coe
  obtain ⟨π, hπ1, hπ⟩ := exists_norm_lt_one_forall_norm_le_of_fg
    (IsNoetherian.noetherian (unitBallIdeal K))
  rcases eq_or_ne π 0 with rfl | hπ0
  · -- `K` is trivially normed, so every nonzero element of `K°` has norm `1` and divides every
    -- element of `K°`.
    refine isNoetherianRing_isRestricted_subring_of_division (fun _ ↦ 0) (fun _ _ _ ↦ rfl)
      fun x y hx ↦ ?_
    have hxK : (x : K) ≠ 0 := fun h ↦ hx (Subtype.ext h)
    have hx1 : ‖(x : K)‖ = 1 :=
      (Subring.mem_unitClosedBall.mp x.property).antisymm <| not_lt.mp fun hlt ↦
        hxK (norm_le_zero_iff.mp ((hπ _ hlt).trans (by simp)))
    obtain ⟨q, hq⟩ := Subring.unitClosedBall.dvd_iff_norm_le.mpr
      ((Subring.mem_unitClosedBall.mp y.property).trans_eq hx1.symm)
    exact ⟨q, 0, by rw [add_zero, mul_comm, hq], by simp, Or.inl rfl⟩
  · -- `0 < ‖π‖ < 1`, so nonzero elements of `K°` have norm `‖π‖ ^ n` for a unique `n : ℕ`.
    have hπpos : 0 < ‖π‖ := norm_pos_iff.mpr hπ0
    have hnat (x : O) (hx : x ≠ 0) : ∃ n : ℕ, ‖(x : K)‖ = ‖π‖ ^ n :=
      exists_norm_eq_pow_of_forall_norm_le_of_norm_le_one hπpos hπ1 hπ
        (fun h ↦ hx (Subtype.ext h)) (Subring.mem_unitClosedBall.mp x.property)
    let deg : O → ℕ := fun x ↦ if hx : x = 0 then 0 else Nat.find (hnat x hx)
    have hdeg_spec {x : O} (hx : x ≠ 0) : ‖(x : K)‖ = ‖π‖ ^ deg x := by
      simpa [deg, hx] using Nat.find_spec (hnat x hx)
    refine isNoetherianRing_isRestricted_subring_of_division deg (fun x y hxy ↦ ?_)
      fun x y hx ↦ ?_
    · have hx0 : x ≠ 0 := norm_pos_iff.mp ((norm_nonneg (x - y)).trans_lt hxy)
      have hnorm : ‖x‖ = ‖y‖ := IsUltrametricDist.norm_eq_of_norm_sub_lt_left hxy
      have hy0 : y ≠ 0 := norm_pos_iff.mp (hnorm ▸ norm_pos_iff.mpr hx0)
      have hpow : ‖π‖ ^ deg y = ‖π‖ ^ deg x := by
        rw [← hdeg_spec hy0, ← hdeg_spec hx0, ← AddSubgroupClass.coe_norm,
          ← AddSubgroupClass.coe_norm, hnorm]
      exact pow_right_injective₀ hπpos hπ1.ne hpow
    · rcases eq_or_ne y 0 with rfl | hy0
      · exact ⟨0, 0, by simp, by simp, Or.inl rfl⟩
      rcases le_or_gt (deg x) (deg y) with hle | hlt
      · have hnorm_le : ‖(y : K)‖ ≤ ‖(x : K)‖ := by
          rw [hdeg_spec hy0, hdeg_spec hx]
          exact pow_le_pow_of_le_one hπpos.le hπ1.le hle
        obtain ⟨q, hq⟩ := Subring.unitClosedBall.dvd_iff_norm_le.mpr hnorm_le
        exact ⟨q, 0, by rw [add_zero, mul_comm, hq], by simp, Or.inl rfl⟩
      · exact ⟨0, y, by simp, le_rfl, Or.inr hlt⟩

/-- **Restricted power series over `𝒪[K]` are noetherian when `𝒪[K]` is noetherian.** Over a
complete nontrivially normed ultrametric field `K` with noetherian valuation ring `𝒪[K]`
(equivalently, a discrete valuation ring), `𝒪[K]{X/r}` is noetherian for every finite variable set
`σ` and positive polyradius `r`. -/
instance isNoetherianRing_isRestricted_subring_integer {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [Finite σ] {r : σ → ℝ} [∀ i, Fact (0 < r i)]
    [IsNoetherianRing 𝒪[K]] :
    IsNoetherianRing (IsRestricted.subring (R := 𝒪[K]) r) := by
  have : IsNoetherianRing (Subring.unitClosedBall K) :=
    isNoetherianRing_of_ringEquiv 𝒪[K] (integerUnitClosedBallEquiv (K := K))
  exact isNoetherianRing_of_ringEquiv _
    (restrictedIntegerUnitClosedBallEquiv (σ := σ) (K := K) (r := r)).symm

/-- **The Gauss unit ball of a Tate algebra in finitely many variables over a complete field with
noetherian unit ball is noetherian.** This applies in particular when `K` is a complete discretely
valued field. -/
instance isNoetherianRing_unitClosedBall [CompleteSpace K] [Finite σ]
    [IsNoetherianRing (Subring.unitClosedBall K)] :
    IsNoetherianRing (Subring.unitClosedBall (Tate σ)) :=
  isNoetherianRing_of_ringEquiv _ restrictedUnitClosedBallEquiv

/-- **In finitely many variables, the Gauss unit ball `K⟨X⟩°` is noetherian if and only if `K°` is
noetherian.** -/
theorem isNoetherianRing_unitClosedBall_iff [CompleteSpace K] [Finite σ] :
    IsNoetherianRing (Subring.unitClosedBall (Tate σ)) ↔
      IsNoetherianRing (Subring.unitClosedBall K) :=
  ⟨fun _ ↦
      isNoetherianRing_unitClosedBall_of_isNoetherianRing_restrictedUnitClosedBall σ (fun _ ↦ 1),
    fun _ ↦ inferInstance⟩

end Noetherian

end TauCeti.MvPowerSeries
