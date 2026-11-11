/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Exchange
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.LeftCapping
import TauCeti.Geometry.Symplectic.Area.PuncturedDisc
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The energy of the input-exchange family capped at `0`

The left unit property of the pair-of-pants product is proved with the family
`K_c = TauCeti.Floer.cappedExchangePerturbation H L c`, `0 ≤ c ≤ 1`, of perturbation data on the
sphere `ℂ ∖ {1}` obtained by capping the input at `0` of the input-exchange family with a negative
plane along a neck of length `L`. Its member `c = 0` is the capping family at `0`, and its member
`c = 1` is a continuation datum on the standard cylinder. The chain homotopy given by the
one-parameter family of moduli spaces must be supported in the sense of
`TauCeti.NovikovModule.kernelMap`, and this support comes from an action bound that is uniform in
`c` and in the neck length. This file proves the energy identity of every member of the family and
the resulting energy and action bounds, for a symplectic vector space target.

Write `ℓ_1(R)(t) = u(φ_1(R + i t))` for the loop of a map `u` along the circle `s = R` of the
remaining input end, and `ℓ^c_∞(R)(t) = u(c + φ_∞(-R + i t))` for its loop along the circle
`s = -R` of the output end recentred at `c`. These circles bound the capped truncation
`TauCeti.ThricePuncturedSphere.cappedExchangeTruncation c R`, a compact subset of `ℂ ∖ {1}`
which contains the capped puncture `0`. For a map `u` which is `C²` on `ℂ ∖ {1}`, period-one `C¹`
Hamiltonians `H_q`, a neck length `L > 4` and `R ≥ L - 1`, the Floer energy of `u` for `K_c` over
this truncation is

`∫ E = A_{H_1}(ℓ_1(R)) - A_{H_∞}(ℓ^c_∞(R)) - ∫_S R_{K_c}(u)`

(`SymplecticForm.integral_floerEnergyDensity_cappedExchangePerturbation_cappedExchangeTruncation`),
where `A_H` is the Hamiltonian action `TauCeti.SymplecticForm.hamiltonianAction` and
`S = ℂ ∖ {0, 1}`. The Hamiltonian `H_0` of the capped input contributes to the curvature but to no
boundary term. If `|H_q| ≤ B_q`, the curvature bound
`TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_cappedExchangePerturbation_le` shows
that the energy differs from the change of action by at most `B_0 + B_0 + B_1 + B_∞`, uniformly in
`c`, `L` and `R` (in `SymplecticForm`,
`abs_integral_floerEnergyDensity_cappedExchangePerturbation_cappedExchangeTruncation_sub_le`).
For a solution of the Floer equation with tame almost complex structures the energy is
nonnegative, which gives the action bound
`A_{H_∞}(ℓ^c_∞(R)) ≤ A_{H_1}(ℓ_1(R)) + B_0 + B_0 + B_1 + B_∞`
(`SymplecticForm.hamiltonianAction_le_add_add_sum_of_cappedExchangePerturbation`) and its limit
`a_∞ ≤ a_1 + B_0 + B_0 + B_1 + B_∞` for the limiting actions of the two ends
(`SymplecticForm.le_add_add_sum_of_tendsto_hamiltonianAction_cappedExchangePerturbation`).

The identity is reduced to the energy identity of the input-exchange family
(`SymplecticForm.integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation`) for the
Hamiltonians with `H_0` replaced by `0`. Away from the annulus where the negative plane is plumbed
into the end at `0`, the two data agree: near the capped puncture both vanish, and elsewhere the
capped datum is the input-exchange datum, whose component on the end at `0` is switched off where
the signed longitudinal coordinate of that end is at most `1`. The annulus lies inside the
truncation with recentred output end once `R ≥ L - 1`, so the energy plus the integrated curvature
over that truncation is the same for both data
(`SymplecticForm.setIntegral_floerEnergyDensity_add_hamiltonianCurvature_eq_of_eqOn`). The capped
truncation adds to it the disc about `0` cut out by the circle `s = R` of the end at `0`, where the
capped datum vanishes and the energy is the symplectic area. By Stokes' formula
(`SymplecticForm.integral_fderiv_apply_preimage_closedBall`) this area cancels the loop area of the
boundary loop of the disc, which is the action of that loop for the zero Hamiltonian.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on capping inputs of the pair of pants and on their energy estimates.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology

namespace TauCeti

namespace Floer

variable {M : Type*} {H : Puncture → ℝ → M → ℝ} {L c : ℝ}

/-- Away from the disc of radius `1/2` about `0`, the capped datum is the input-exchange datum of
the Hamiltonians with `H_0` replaced by `0`: the component of the input-exchange datum on the end
at `0` is switched off there. -/
private theorem cappedExchangePerturbation_eq_of_le_norm (hL : 2 ≤ L) {w : ℂ} (hw : 1 / 2 ≤ ‖w‖)
    (x : M) :
    cappedExchangePerturbation H L c w x = exchangePerturbation (update H zero 0) c w x := by
  have hre : (zero.endCoord w).re ≤ 0 :=
    re_endCoord_nonpos_of_le_norm_sub_endCenter (by decide) (by rwa [endCenter_zero, sub_zero])
  have hcut : smoothTransition ((zero.endCoord w).re - 1) = 0 :=
    smoothTransition.zero_of_nonpos (by linarith)
  rw [cappedExchangePerturbation_of_re_endCoord_le (by linarith), exchangePerturbation_def,
    exchangePerturbation_def, update_of_ne (show inf ≠ zero by decide)]
  simp [pairOfPantsPerturbation_def, Puncture.sum_univ, hcut]

/-- Within distance `1/2` of `0`, the input-exchange datum of the Hamiltonians with `H_0` replaced
by `0` vanishes, for `0 ≤ c ≤ 1`. -/
private theorem exchangePerturbation_update_zero_eq_zero (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {w : ℂ}
    (hw : ‖w‖ ≤ 1 / 2) (x : M) : exchangePerturbation (update H zero 0) c w x = 0 := by
  have hw₁ : 1 / 2 ≤ ‖w - 1‖ := by
    have h := norm_sub_norm_le (1 : ℂ) w
    rw [norm_one, norm_sub_rev] at h
    linarith
  have hre : (one.endCoord w).re ≤ 0 :=
    re_endCoord_nonpos_of_le_norm_sub_endCenter (by decide) (by rwa [endCenter_one])
  have hcut : smoothTransition ((one.endCoord w).re - 1) = 0 :=
    smoothTransition.zero_of_nonpos (by linarith)
  have hwc : ‖w - c‖ ≤ 2 * Real.exp (2 * π) := by
    have h := norm_sub_le w (c : ℂ)
    rw [Complex.norm_real, Real.norm_of_nonneg hc₀] at h
    nlinarith [Real.one_le_exp (by positivity : (0 : ℝ) ≤ 2 * π)]
  rw [exchangePerturbation_def, negativePlanePerturbation_eq_zero_of_norm_le hwc, add_zero]
  simp [pairOfPantsPerturbation_def, Puncture.sum_univ, hcut]

/-- **Off the truncation the capped datum is an input-exchange datum.** For `L > 4`,
`0 ≤ c ≤ 1` and `R ≥ L - 1`, outside the truncation with recentred output end the capped datum is
the input-exchange datum of the Hamiltonians with `H_0` replaced by `0`: near the capped puncture
both vanish, and away from it the plumbed plane does not reach. -/
private theorem cappedExchangePerturbation_eq_of_notMem (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {R : ℝ} (hR : L - 1 ≤ R) {w : ℂ} (hw : w ∉ exchangeTruncation c R) (x : M) :
    cappedExchangePerturbation H L c w x = exchangePerturbation (update H zero 0) c w x := by
  have hρ : Real.exp (-(2 * π * R)) ≤ Real.exp (-(2 * π * (L - 1))) :=
    Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
  have hρ₁ : Real.exp (-(2 * π * (L - 1))) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
  have h₁ : 1 ≤ Real.exp (2 * π * R) := Real.one_le_exp (by nlinarith [Real.pi_pos])
  simp only [mem_exchangeTruncation, not_and_or, not_le] at hw
  by_cases hw₀ : ‖w‖ < Real.exp (-(2 * π * R)) / 2
  -- Near the capped puncture both data vanish.
  · rw [cappedExchangePerturbation_eq_zero (by linarith) hc₀ hc₁ (by linarith),
      exchangePerturbation_update_zero_eq_zero hc₀ hc₁ (by linarith)]
  -- Elsewhere off the truncation the point is at distance at least `1/2` from `0`.
  · refine cappedExchangePerturbation_eq_of_le_norm (by linarith) ?_ x
    rcases hw with hw | hw | hw
    · exact absurd hw hw₀
    · have h := norm_sub_norm_le (1 : ℂ) w
      rw [norm_one, norm_sub_rev] at h
      linarith
    · have h := norm_sub_le w (c : ℂ)
      rw [Complex.norm_real, Real.norm_of_nonneg hc₀] at h
      linarith

end Floer

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {L c : ℝ}

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Replacing `H_0` by `0` keeps the end Hamiltonians periodic. -/
private theorem periodic_update_zero (hH : ∀ q, Periodic (H q) 1) (q : Puncture) :
    Periodic (update H zero 0 q) 1 :=
  (forall_update_iff H fun _ f => Periodic f 1).2 ⟨fun _ => rfl, fun q _ => hH q⟩ q

omit [FiniteDimensional ℝ V] in
/-- Replacing `H_0` by `0` keeps the end Hamiltonians `C¹`. -/
private theorem contDiff_update_zero (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (q : Puncture) :
    ContDiff ℝ 1 (uncurry (update H zero 0 q)) :=
  (forall_update_iff H fun _ f => ContDiff ℝ 1 (uncurry f)).2 ⟨contDiff_const, fun q _ => hHs q⟩ q

/-- The curvature of the input-exchange datum of the Hamiltonians with `H_0` replaced by `0`
vanishes on `S = ℂ ∖ {0, 1}` outside the truncation with recentred output end, for `R ≥ 2`: near
`0` the datum vanishes, and on the other two ends it is cylindrical. -/
private theorem hamiltonianCurvature_exchangePerturbation_update_zero_eq_zero
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {R : ℝ} (hR : 2 ≤ R) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1)
    (hzT : Complex.equivRealProdCLM.symm z ∉ exchangeTruncation c R) (x : V) :
    ω.hamiltonianCurvature
      (fun z x ↦ exchangePerturbation (update H zero 0) c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦
        exchangePerturbation (update H zero 0) c (Complex.equivRealProdCLM.symm z) x Complex.I)
      z x = 0 := by
  set e := Complex.equivRealProdCLM
  have hρ : Real.exp (-(2 * π * R)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
  have h₁ : 1 ≤ Real.exp (2 * π * R) := Real.one_le_exp (by nlinarith [Real.pi_pos])
  -- Points near `z` satisfy any strict inequality on a distance that `z` satisfies.
  have hnear {a : ℂ} {r : ℝ} (h : ‖e.symm z - a‖ < r) : ∀ᶠ y in 𝓝 z, ‖e.symm y - a‖ < r :=
    ((continuous_norm.comp (e.symm.continuous.sub continuous_const)).continuousAt.eventually
      (gt_mem_nhds h))
  have hfar {a : ℂ} {r : ℝ} (h : r < ‖e.symm z - a‖) : ∀ᶠ y in 𝓝 z, r < ‖e.symm y - a‖ :=
    ((continuous_norm.comp (e.symm.continuous.sub continuous_const)).continuousAt.eventually
      (lt_mem_nhds h))
  simp only [mem_exchangeTruncation, not_and_or, not_le] at hzT
  rcases hzT with h₀ | h₁' | hc
  -- Near `0` the datum vanishes.
  · have hev := hnear (a := 0) (r := 1 / 2) (by rw [sub_zero]; linarith)
    refine ω.hamiltonianCurvature_eq_zero_of_eventuallyEq_zero ?_ ?_ x <;>
      exact hev.mono fun y hy ↦ funext fun x ↦ by
        rw [sub_zero] at hy
        simp [exchangePerturbation_update_zero_eq_zero hc₀ hc₁ hy.le x]
  -- Near `1` the output datum vanishes, and the input part is cylindrical on the end at `1`.
  · have hev := hnear (a := 1) (r := 1 / 2) (by linarith)
    have hK (v : ℂ) : (fun y x ↦ exchangePerturbation (update H zero 0) c (e.symm y) x v) =ᶠ[𝓝 z]
        fun y x ↦ pairOfPantsPerturbation (update (update H zero 0) inf 0) (e.symm y) x v :=
      hev.mono fun y hy ↦ funext fun x ↦ by
        have hyc : ‖e.symm y - c‖ ≤ 2 * Real.exp (2 * π) := by
          have h := norm_add_le (e.symm y - 1) (1 - (c : ℂ))
          have hc : ‖(1 : ℂ) - c‖ ≤ 1 := by
            rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
              Real.norm_of_nonneg (by linarith)]
            linarith
          rw [sub_add_sub_cancel] at h
          nlinarith [Real.one_le_exp (by positivity : (0 : ℝ) ≤ 2 * π)]
        beta_reduce
        rw [exchangePerturbation_def, negativePlanePerturbation_eq_zero_of_norm_le hyc, add_zero]
    have hre : R < (one.endCoord (e.symm z)).re := by
      rw [← not_le, re_endCoord_le_iff (by decide) (by rw [endCenter_one]; exact hz.2),
        endCenter_one, not_le]
      exact h₁'
    rw [ω.hamiltonianCurvature_congr_of_eventuallyEq (hK 1) (hK Complex.I)]
    exact ω.hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt
      (fun q ↦ (forall_update_iff _ fun _ f => Periodic f 1).2
        ⟨fun _ => rfl, fun q _ => periodic_update_zero hH q⟩ q)
      (fun q ↦ (forall_update_iff _ fun _ f => ContDiff ℝ 1 (uncurry f)).2
        ⟨contDiff_const, fun q _ => contDiff_update_zero hHs q⟩ q)
      hz (q := one) (by rw [endSign_one, one_mul]; linarith) x
  -- Far from `c` the input part vanishes, and the output datum is cylindrical on its end.
  · have hev := hfar (a := c) (r := 3 / 2) (by linarith)
    set z' : ℝ × ℝ := z + -(c, 0)
    have he (y : ℝ × ℝ) : e.symm (y + -(c, 0)) = e.symm y - c := by
      apply Complex.ext <;> simp [e, sub_eq_add_neg]
    have hK (v : ℂ) : (fun y x ↦ exchangePerturbation (update H zero 0) c (e.symm y) x v) =ᶠ[𝓝 z]
        fun y x ↦ pairOfPantsPerturbation (Pi.single inf (H inf)) (e.symm (y + -(c, 0))) x v :=
      hev.mono fun y hy ↦ funext fun x ↦ by
        beta_reduce
        rw [exchangePerturbation_def,
          pairOfPantsPerturbation_update_inf_eq_zero_of_le_norm_sub hc₀ hc₁ hy.le, zero_add,
          update_of_ne (show inf ≠ zero by decide), pairOfPantsPerturbation_single_inf, he]
    have hz' : e.symm z' ≠ 0 ∧ e.symm z' ≠ 1 := by
      rw [he]
      constructor <;> intro h <;> rw [h] at hc <;> simp at hc <;> linarith
    have hre : 2 < inf.endSign * (inf.endCoord (e.symm z')).re := by
      have hpos : 0 < ‖e.symm z - c‖ / 2 := by linarith
      have hlog : 2 * π * R < Real.log (‖e.symm z - c‖ / 2) := by
        rw [Real.lt_log_iff_exp_lt hpos]
        linarith
      rw [he, re_endCoord, endCenter_inf, endScale_inf, sub_zero, norm_div, Complex.norm_ofNat]
      simp only [endSign_inf]
      rw [neg_one_mul, neg_div, neg_neg, lt_div_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
    rw [ω.hamiltonianCurvature_congr_of_eventuallyEq (hK 1) (hK Complex.I),
      show z = z' + (c, 0) from (neg_add_cancel_right z (c, 0)).symm,
      ← ω.hamiltonianCurvature_comp_add_right]
    simp only [add_neg_cancel_right]
    have hsingle {P : (ℝ → V → ℝ) → Prop} (h₀ : P 0) (h : P (H inf)) (q : Puncture) :
        P ((Pi.single inf (H inf) : Puncture → ℝ → V → ℝ) q) := by
      rcases eq_or_ne q inf with rfl | hq
      · rwa [Pi.single_eq_same]
      · rwa [Pi.single_eq_of_ne hq]
    exact ω.hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt
      (hsingle (P := fun f => Periodic f 1) (fun _ => rfl) (hH inf))
      (hsingle (P := fun f => ContDiff ℝ 1 (uncurry f)) contDiff_const (hHs inf)) hz' hre x

/-- The symplectic area over the disc of radius `exp (-2πR) / 2` about `0`, cut out by the circle
`s = R` of the end at `0`, is minus the loop area of the boundary loop `t ↦ u(φ_0(R + i t))`: the
end coordinate `t` runs clockwise around the circle. -/
private theorem integral_preimage_ball_eq_neg_loopArea (ω : SymplecticForm V) {u : ℝ × ℝ → V}
    (R : ℝ) (hu : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹'
      Metric.closedBall 0 (Real.exp (-(2 * π * R)) / 2), ContDiffAt ℝ 2 u z) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.ball 0 (Real.exp (-(2 * π * R)) / 2),
        ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) =
      -ω.loopArea
        (fun t ↦ u (Complex.equivRealProdCLM (zero.cylindricalEndLift (R + t * Complex.I)))) := by
  set e := Complex.equivRealProdCLM
  set ρ := Real.exp (-(2 * π * R)) / 2
  -- The boundary circle is a null set, so the open and the closed disc have the same integrals.
  have hnull : volume (e.symm ⁻¹' Metric.sphere (0 : ℂ) ρ) = 0 := by
    have hsymm : (e.symm : ℝ × ℝ → ℂ) = Complex.measurableEquivRealProd.symm := rfl
    rw [hsymm, (Complex.volume_preserving_equiv_real_prod.symm _).measure_preimage
      Metric.isClosed_sphere.measurableSet.nullMeasurableSet]
    exact Measure.addHaar_sphere volume _ _
  have hae : e.symm ⁻¹' Metric.ball (0 : ℂ) ρ =ᵐ[volume] e.symm ⁻¹' Metric.closedBall 0 ρ := by
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · rw [← preimage_sdiff, sdiff_eq_empty.2 Metric.ball_subset_closedBall, preimage_empty,
        measure_empty]
    · rwa [← preimage_sdiff, Metric.closedBall_sdiff_ball]
  -- Stokes' formula on the closed disc.
  have hg : Periodic (fun θ ↦ u (e (circleMap 0 ρ θ))) (2 * π) := fun θ ↦ by
    simp only [periodic_circleMap 0 ρ θ]
  have hloop := ω.loopArea_comp_sub_mul hg 0
  have hℓ : (fun t : ℝ ↦ u (e (zero.cylindricalEndLift (R + t * Complex.I)))) =
      fun t ↦ u (e (circleMap 0 ρ (0 - 2 * π * t))) :=
    funext fun t ↦ by
      rw [cylindricalEndLift_ofReal_add_ofReal_mul_I, endCenter_zero, endScale_zero]
      congr 3
      · rw [norm_div, norm_one, Complex.norm_ofNat]
        ring
      · rw [show ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.arg_ofReal_of_nonneg
          (by norm_num)]
  rw [setIntegral_congr_set hae, integral_fderiv_apply_preimage_closedBall ω 0 (by positivity) hu,
    hℓ, hloop, neg_neg]

/-- **The energy identity along the input-exchange family capped at `0`.** Let `K_c` be the member
`c ∈ [0, 1]` of the input-exchange family capped at `0` along a neck of length `L > 4`, for
period-one `C¹` Hamiltonians `H_q`, with components `K_s(z) = K_c(z)(1)` and `K_t(z) = K_c(z)(i)` in
the global coordinate `z = s + i t` of `ℂ`, and let `u` be a map which is `C²` on the capped domain
`ℂ ∖ {1}`. For `R ≥ L - 1`, the Floer energy of `u` over the capped truncation with recentred output
end is the change of action between the loop `ℓ_1(t) = u(φ_1(R + i t))` along the boundary circle
of the remaining input end and the loop `ℓ^c_∞(t) = u(c + φ_∞(-R + i t))` along the boundary circle
of the recentred output end, minus the integrated curvature over `S = ℂ ∖ {0, 1}`:

`∫ E = A_{H_1}(ℓ_1) - A_{H_∞}(ℓ^c_∞) - ∫_S R_{K_c}(u)`. -/
theorem integral_floerEnergyDensity_cappedExchangePerturbation_cappedExchangeTruncation
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 1}) {R : ℝ}
    (hR : L - 1 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' cappedExchangeTruncation c R, ω.floerEnergyDensity
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
          (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) -
        ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
          (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) -
        ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
            Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  set e := Complex.equivRealProdCLM
  set S : Set (ℝ × ℝ) := {z | e.symm z ≠ 0 ∧ e.symm z ≠ 1}
  set U : Set (ℝ × ℝ) := {z | e.symm z ≠ 1}
  set T := e.symm ⁻¹' exchangeTruncation c R
  set B := e.symm ⁻¹' Metric.ball (0 : ℂ) (Real.exp (-(2 * π * R)) / 2)
  have hR₂ : 2 ≤ R := by linarith
  have hS : S = thricePuncturedSphereReal := Set.ext fun _ ↦ mem_thricePuncturedSphereReal_iff.symm
  have hSo : IsOpen S := hS ▸ isOpen_thricePuncturedSphereReal
  have hUo : IsOpen U := isOpen_ne_fun e.symm.continuous continuous_const
  have hSU : S ⊆ U := fun _ hz ↦ hz.2
  have hTS : T ⊆ S := fun _ hz ↦ exchangeTruncation_subset c R hz
  have hTc : IsCompact T := e.symm.toHomeomorph.isCompact_preimage.2
    (isCompact_exchangeTruncation c R)
  have hBm : MeasurableSet B := (Metric.isOpen_ball.preimage e.symm.continuous).measurableSet
  -- The capped datum and the input-exchange datum with `H_0` switched off are `C¹`.
  have hK (v : ℂ) : ContDiffOn ℝ 1
      (uncurry fun z x ↦ cappedExchangePerturbation H L c (e.symm z) x v) (U ×ˢ univ) :=
    fun p hp ↦ (contDiffAt_uncurry_cappedExchangePerturbation hH hHs hL c hp.1 p.2
      v).contDiffWithinAt
  have hK' (v : ℂ) : ContDiffOn ℝ 1
      (uncurry fun z x ↦ exchangePerturbation (update H zero 0) c (e.symm z) x v) (S ×ˢ univ) :=
    fun p hp ↦ (contDiffAt_uncurry_exchangePerturbation (periodic_update_zero hH)
      (contDiff_update_zero hHs) c (mem_thricePuncturedSphereReal_iff.2 hp.1) p.2
        v).contDiffWithinAt
  -- The two data agree on `S` outside the truncation `T`.
  have hagree (v : ℂ) : EqOn (fun z x ↦ cappedExchangePerturbation H L c (e.symm z) x v)
      (fun z x ↦ exchangePerturbation (update H zero 0) c (e.symm z) x v) (S \ T) :=
    fun z hz ↦ funext fun x ↦ by
      beta_reduce
      rw [cappedExchangePerturbation_eq_of_notMem hL hc₀ hc₁ hR hz.2 x]
  -- So the energy plus the curvature over `T` is the same for both data.
  have h₁ := ω.setIntegral_floerEnergyDensity_add_hamiltonianCurvature_eq_of_eqOn hSo
    ((hu.mono hSU).of_le one_le_two) ((hK 1).mono (prod_mono hSU subset_rfl))
    ((hK Complex.I).mono (prod_mono hSU subset_rfl)) (hK' 1) (hK' Complex.I) hTc hTS (hagree 1)
    (hagree Complex.I)
  -- The energy identity of the input-exchange family with `H_0` switched off.
  have h₂ := ω.integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation
    (periodic_update_zero hH) (contDiff_update_zero hHs) hc₀ hc₁ (hu.mono hSU) hR₂
  -- Both curvatures vanish on `S` outside `T`, so their integrals over `S` are those over `T`.
  have hR' (z : ℝ × ℝ) (hz : z ∈ S \ T) :=
    hamiltonianCurvature_exchangePerturbation_update_zero_eq_zero ω hH hHs hc₀ hc₁ hR₂ hz.1 hz.2
      (u z)
  have hRcap (z : ℝ × ℝ) (hz : z ∈ S \ T) :
      ω.hamiltonianCurvature
        (fun z x ↦ cappedExchangePerturbation H L c (e.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (e.symm z) x Complex.I) z (u z) = 0 := by
    have hn : S \ T ∈ 𝓝 z := (hSo.sdiff hTc.isClosed).mem_nhds hz
    rw [ω.hamiltonianCurvature_congr_of_eventuallyEq ((hagree 1).eventuallyEq_of_mem hn)
      ((hagree Complex.I).eventuallyEq_of_mem hn)]
    exact hR' z hz
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hSo.measurableSet hTS hR'] at h₂
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hSo.measurableSet hTS hRcap]
  -- The capped truncation is `T` together with the disc `B` about the capped puncture.
  have hcap : e.symm ⁻¹' cappedExchangeTruncation c R = T ∪ B := by
    rw [cappedExchangeTruncation_eq_union (abs_le.2 ⟨by linarith, hc₁⟩) (by linarith),
      preimage_union]
  have hcapc : IsCompact (e.symm ⁻¹' cappedExchangeTruncation c R) :=
    e.symm.toHomeomorph.isCompact_preimage.2 (isCompact_cappedExchangeTruncation c R)
  have hEint : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ cappedExchangePerturbation H L c (e.symm z) x 1)
      (fun z x ↦ cappedExchangePerturbation H L c (e.symm z) x Complex.I) u)
      (e.symm ⁻¹' cappedExchangeTruncation c R) :=
    ((ω.continuousOn_floerEnergyDensity hUo (hu.of_le one_le_two) (hK 1) (hK Complex.I)).mono
      fun _ hz ↦ cappedExchangeTruncation_subset c R hz).integrableOn_compact hcapc
  rw [hcap] at hEint ⊢
  rw [setIntegral_union ((disjoint_exchangeTruncation_ball c R).preimage _) hBm
    (hEint.mono_set subset_union_left) (hEint.mono_set subset_union_right)]
  -- On `B` the capped datum vanishes, so the energy density is the area density.
  have hB (z : ℝ × ℝ) (hz : z ∈ B) (v : ℂ) (x : V) :
      cappedExchangePerturbation H L c (e.symm z) x v = 0 := by
    have hρ : Real.exp (-(2 * π * R)) ≤ Real.exp (-(2 * π * (L - 1))) :=
      Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
    have hz' : ‖e.symm z‖ < Real.exp (-(2 * π * R)) / 2 := by
      simpa [B] using hz
    simp [cappedExchangePerturbation_eq_zero (H := H) (by linarith) hc₀ hc₁
      (show ‖e.symm z‖ ≤ Real.exp (-(2 * π * (L - 1))) / 2 by linarith) x]
  rw [setIntegral_congr_fun hBm fun z hz ↦ by
    rw [ω.floerEnergyDensity_congr_perturbation u (Ks' := fun _ _ ↦ 0) (Kt' := fun _ _ ↦ 0)
      (funext fun x ↦ hB z hz 1 x) (funext fun x ↦ hB z hz Complex.I x), floerEnergyDensity_zero]]
  -- By Stokes' formula the area over `B` cancels the action of its boundary loop for `H_0 = 0`.
  rw [integral_preimage_ball_eq_neg_loopArea ω R fun z hz ↦
    hu.contDiffAt (hUo.mem_nhds fun h ↦ by
      have h' : ‖e.symm z‖ ≤ Real.exp (-(2 * π * R)) / 2 := by simpa using hz
      rw [h, norm_one] at h'
      linarith [Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos] : -(2 * π * R) ≤ 0)])]
  simp only [update_self, update_of_ne (show one ≠ zero by decide),
    update_of_ne (show inf ≠ zero by decide), hamiltonianAction_def, Pi.zero_apply,
    intervalIntegral.integral_zero, add_zero] at h₂ ⊢
  linarith

/-- **The energy and the actions along the input-exchange family capped at `0`.** If the end
Hamiltonians are bounded, `|H_q| ≤ B_q`, then for every `c ∈ [0, 1]`, `L > 4` and `R ≥ L - 1` the
Floer energy of `u` for the member `c` of the family over the capped truncation differs from the
change of action `A_{H_1}(ℓ_1) - A_{H_∞}(ℓ^c_∞)` of its two boundary loops by at most
`B_0 + (B_0 + B_1 + B_∞)`, uniformly in `c`, `L` and `R`. -/
theorem abs_integral_floerEnergyDensity_cappedExchangePerturbation_cappedExchangeTruncation_sub_le
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 1})
    {R : ℝ} (hR : L - 1 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' cappedExchangeTruncation c R, ω.floerEnergyDensity
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      (ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
          (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) -
        ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
          (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))))| ≤ B zero + ∑ q, B q := by
  rw [integral_floerEnergyDensity_cappedExchangePerturbation_cappedExchangeTruncation ω hH hHs hL
    hc₀ hc₁ hu hR, sub_sub_cancel_left, abs_neg]
  have hB₀ (q : Puncture) : 0 ≤ B q := (abs_nonneg _).trans (hB q 0 0)
  have hsum₀ : 0 ≤ B zero + ∑ q, B q := add_nonneg (hB₀ _) (Finset.sum_nonneg fun q _ ↦ hB₀ q)
  have hsum : ENNReal.ofReal (B zero) + ∑ q, ENNReal.ofReal (B q) =
      ENNReal.ofReal (B zero + ∑ q, B q) := by
    rw [ENNReal.ofReal_add (hB₀ _) (Finset.sum_nonneg fun q _ ↦ hB₀ q),
      ENNReal.ofReal_sum_of_nonneg fun q _ ↦ hB₀ q]
  rw [← ENNReal.ofReal_le_ofReal_iff hsum₀, ← Real.enorm_eq_ofReal_abs, ← hsum]
  exact (enorm_integral_le_lintegral_enorm _).trans ((setLIntegral_le_lintegral _ _).trans
    (lintegral_enorm_hamiltonianCurvature_cappedExchangePerturbation_le ω hH hHs hL hB hc₀ hc₁ u))

/-- **The action bound along the input-exchange family capped at `0`.** Let `K_c` be the member
`c ∈ [0, 1]` of the input-exchange family capped at `0` along a neck of length `L > 4`, for
period-one `C¹` Hamiltonians `H_q` with `|H_q| ≤ B_q`, and let `u` be a map which is `C²` on the
capped domain `ℂ ∖ {1}` and solves the Floer equation `(du - X_K)^{0,1} = 0` for `K_c` on the capped
truncation, `R ≥ L - 1`, for almost complex structures `J(z)` tamed by `ω`. Then the action of the
output loop `ℓ^c_∞(t) = u(c + φ_∞(-R + i t))` is at most the action of the input loop
`ℓ_1(t) = u(φ_1(R + i t))` plus `B_0 + (B_0 + B_1 + B_∞)`:

`A_{H_∞}(ℓ^c_∞) ≤ A_{H_1}(ℓ_1) + B_0 + (B_0 + B_1 + B_∞)`,

uniformly in `c` and `L`. -/
theorem hamiltonianAction_le_add_add_sum_of_cappedExchangePerturbation (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {B : Puncture → ℝ}
    (hB : ∀ q t x, |H q t x| ≤ B q) (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 1}) {R : ℝ}
    (hR : L - 1 ≤ R) {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' cappedExchangeTruncation c R, ω.Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' cappedExchangeTruncation c R,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
        (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) ≤
      ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
        (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) + B zero + ∑ q, B q := by
  -- The energy over the capped truncation is nonnegative.
  have hE := setIntegral_nonneg (μ := volume)
    ((isCompact_cappedExchangeTruncation c R).isClosed.preimage
      Complex.equivRealProdCLM.symm.continuous).measurableSet fun z hz ↦
        ω.floerEnergyDensity_nonneg (hJ z hz) (hfloer z hz)
  have h := (abs_le.1
    (abs_integral_floerEnergyDensity_cappedExchangePerturbation_cappedExchangeTruncation_sub_le
      ω hH hHs hB hL hc₀ hc₁ hu hR)).2
  linarith

/-- **The action bound for the limiting actions along the input-exchange family capped at `0`.**
Let `u` be a map which is `C²` on the capped domain `ℂ ∖ {1}` and solves the Floer equation there
for the member `c ∈ [0, 1]` of the input-exchange family capped at `0` along a neck of length
`L > 4`, for bounded period-one `C¹` Hamiltonians `|H_q| ≤ B_q` and almost complex structures
`J(z)` tamed by `ω`. If the actions of the input loop `ℓ_1(t) = u(φ_1(R + i t))` and of the output
loop `ℓ^c_∞(t) = u(c + φ_∞(-R + i t))` converge to `a_1` and `a_∞` as `R → ∞`, then

`a_∞ ≤ a_1 + B_0 + (B_0 + B_1 + B_∞)`,

uniformly in `c` and `L`. -/
theorem le_add_add_sum_of_tendsto_hamiltonianAction_cappedExchangePerturbation
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 1})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 1}, ω.Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 1},
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    {a₁ a : ℝ}
    (ha₁ : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
      (one.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 a₁))
    (ha : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
      (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) atTop (𝓝 a)) :
    a ≤ a₁ + B zero + ∑ q, B q :=
  le_of_tendsto_of_tendsto ha ((ha₁.add_const _).add_const _) <| eventually_atTop.2
    ⟨L - 1, fun R hR ↦ hamiltonianAction_le_add_add_sum_of_cappedExchangePerturbation ω hH hHs hB
      hL hc₀ hc₁ hu hR (fun z hz ↦ hJ z (cappedExchangeTruncation_subset c R hz))
      fun z hz ↦ hfloer z (cappedExchangeTruncation_subset c R hz)⟩

end SymplecticForm

end TauCeti
