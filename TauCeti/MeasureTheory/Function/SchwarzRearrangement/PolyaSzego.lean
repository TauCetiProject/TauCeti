/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.MeasureTheory.Function.SchwarzRearrangement.Lipschitz
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import TauCeti.Analysis.BoundedVariation.LevelPerimeter
import TauCeti.Analysis.BoundedVariation.SchwarzRearrangement
import TauCeti.Analysis.Calculus.FDeriv.Basic
import TauCeti.Analysis.Convex.Continuous
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.MeasureTheory.Function.Coarea.DistributionFunction
import TauCeti.MeasureTheory.Function.Coarea.Integral
import TauCeti.MeasureTheory.Function.SchwarzRearrangement.CriticalValues
import TauCeti.MeasureTheory.Integral.ReciprocalWeight

/-!
# The Pólya–Szegő inequality for Lipschitz functions

Let `E` be a nontrivial finite-dimensional real inner product space, and let `Φ : ℝ → ℝ` be convex
and monotone on `[0, ∞)` with `Φ 0 = 0`. For a Lipschitz function `h : E → ℝ` whose positive
superlevel sets `{x | t < h x}` (`t > 0`) have finite Lebesgue volume, the real-valued Schwarz
rearrangement `h* x := (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) x).toReal`
is again Lipschitz with the same constant and decreases every convex gradient integral:

`∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h* x‖) ≤ ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖)`.

The same comparison holds for the signed rearrangement built from `‖u y‖`, for the corresponding
Bochner integrals when the right-hand side is integrable, and in particular for the `Lᵖ` gradient
energies `∫ ‖Du‖ ^ p` (`1 ≤ p`).

## Proof outline

Replacing `h` by `h⁺ := max h 0` leaves `h*` unchanged and can only zero out `fderiv ℝ h` where
`h ≤ 0`. For any nonnegative function `u`, `fderiv ℝ u` vanishes on `{u = 0}`, so weighted coarea on
the regular set `R_u := {x | fderiv ℝ u x ≠ 0}` expresses `∫⁻ x, ofReal (Φ ‖Du x‖)` as the integral
over `t ∈ (0, ∞)` of `∫_{R_u ∩ u⁻¹{t}} Φ(‖Du‖) / ‖Du‖ dHⁿ⁻¹`.

At almost every positive level `t`:
1. Both `Hⁿ⁻¹(R_{h*} ∩ (h*)⁻¹{t})` and `Hⁿ⁻¹(R_{h⁺} ∩ (h⁺)⁻¹{t})` coincide with the variational
   perimeters of `{h* > t}` and `{h⁺ > t}`, so Euclidean isoperimetry gives
   `Hⁿ⁻¹(R_{h*} ∩ (h*)⁻¹{t}) ≤ Hⁿ⁻¹(R_{h⁺} ∩ (h⁺)⁻¹{t})`.
2. Since `h*` and `h⁺` share the same distribution function `μ(t)` on `(0, ∞)` and `h*` has a null
   set of totalized critical values, the reciprocal-gradient level integrals satisfy
   `∫_{R_{h⁺} ∩ (h⁺)⁻¹{t}} ‖Dh⁺‖⁻¹ dHⁿ⁻¹ ≤ -μ'(t) = ∫_{R_{h*} ∩ (h*)⁻¹{t}} ‖Dh*‖⁻¹ dHⁿ⁻¹ < ∞`.
3. Every non-critical positive level of `h*` lies on a single centered sphere (an annulus between
   two radii would force `h*` to be locally constant there and produce a critical point), and
   orthogonal reflection equates `‖Dh*‖` across points of equal norm, so `‖Dh*‖` is constant on
   `(h*)⁻¹{t}`.

Applying the reciprocal-weighted Jensen comparison (`ConvexOn.mul_map_div_le_integral_div`) on each
regular fibre and integrating over `t > 0` yields the inequality.

## Main results

* `TauCeti.lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le` and
  `TauCeti.lintegral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le`: convex-integrand
  Pólya–Szegő inequalities in `ℝ≥0∞`.
* `TauCeti.integrable_map_norm_fderiv_toReal_schwarzRearrangement`,
  `TauCeti.integral_map_norm_fderiv_toReal_schwarzRearrangement_le`,
  `TauCeti.integrable_map_norm_fderiv_toReal_schwarzRearrangement_norm`, and
  `TauCeti.integral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le`: Bochner-integral forms.
* `TauCeti.lintegral_norm_fderiv_toReal_schwarzRearrangement_rpow_le`,
  `TauCeti.lintegral_norm_fderiv_toReal_schwarzRearrangement_norm_rpow_le`,
  `TauCeti.integrable_norm_fderiv_toReal_schwarzRearrangement_norm_rpow`, and
  `TauCeti.integral_norm_fderiv_toReal_schwarzRearrangement_norm_rpow_le`: power specializations
  for `1 ≤ p`.

## References

* G. Brothers, W. P. Ziemer, *Minimal rearrangements of Sobolev functions*, J. Reine Angew. Math.
  384 (1988), 153–179.
* G. Bianchi, R. J. Gardner, P. Gronchi, M. Kiderlen, *The Pólya–Szegő inequality for smoothing
  rearrangements*, J. Funct. Anal. 287 (2024), Theorem 5.8.
* E. H. Lieb, M. Loss, *Analysis*, 2nd edition, Chapter 3.
-/

public section

open Filter Function MeasureTheory Metric Module Set
open scoped ENNReal NNReal Topology

namespace TauCeti

section PrivateHelpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- A radial function on a real inner product space has equal totalized gradient norms at points of
equal norm, by reflection across the hyperplane orthogonal to their difference. -/
private theorem norm_fderiv_eq_of_norm_eq {v : E → ℝ}
    (hrad : ∀ x y, ‖x‖ = ‖y‖ → v x = v y) {x y : E} (hxy : ‖x‖ = ‖y‖) :
    ‖fderiv ℝ v x‖ = ‖fderiv ℝ v y‖ := by
  let R := (ℝ ∙ (x - y))ᗮ.reflection
  have hcomp : v ∘ R = v := funext fun z ↦ hrad (R z) z (R.norm_map z)
  have h := R.norm_iteratedFDeriv_comp_right v x 1
  rwa [hcomp, Submodule.reflection_sub hxy, norm_iteratedFDeriv_one, norm_iteratedFDeriv_one] at h

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- At a level `t` containing no totalized critical point of a radially antitone function `v`, any
two points of `v ⁻¹' {t}` have the same norm: otherwise `v` would be constant on the open annulus
between their radii and have zero derivative at the midpoint. -/
private theorem norm_eq_of_notMem_image_fderiv_eq_zero {v : E → ℝ}
    (hanti : ∀ x y, ‖x‖ ≤ ‖y‖ → v y ≤ v x) {t : ℝ}
    (ht : t ∉ v '' {z | fderiv ℝ v z = 0}) {x y : E} (hx : v x = t) (hy : v y = t) :
    ‖x‖ = ‖y‖ := by
  have hnot_lt {a b : E} (ha : v a = t) (hb : v b = t) (hab : ‖a‖ < ‖b‖) : False := by
    have hb0 : 0 < ‖b‖ := (norm_nonneg a).trans_lt hab
    let c : ℝ := (‖a‖ + ‖b‖) / (2 * ‖b‖)
    have hc0 : 0 ≤ c := div_nonneg (add_nonneg (norm_nonneg a) hb0.le) (by positivity)
    let z₀ : E := c • b
    have hz₀_norm : ‖z₀‖ = (‖a‖ + ‖b‖) / 2 := by
      rw [norm_smul, Real.norm_of_nonneg hc0]
      dsimp only [c]
      field_simp [hb0.ne']
    have hz₀_mem : z₀ ∈ {z : E | ‖a‖ < ‖z‖ ∧ ‖z‖ < ‖b‖} := by
      simp only [mem_ofPred_eq, hz₀_norm]
      exact ⟨by linarith, by linarith⟩
    have hU : {z : E | ‖a‖ < ‖z‖ ∧ ‖z‖ < ‖b‖} ∈ 𝓝 z₀ :=
      ((isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)).mem_nhds hz₀_mem
    have hconst : ∀ z ∈ {z : E | ‖a‖ < ‖z‖ ∧ ‖z‖ < ‖b‖}, v z = t := fun z hz ↦
      le_antisymm ((hanti a z hz.1.le).trans_eq ha) (hb.symm.trans_le (hanti z b hz.2.le))
    have hdz₀ : fderiv ℝ v z₀ = 0 :=
      (EventuallyEq.fderiv_eq (Filter.eventually_of_mem hU hconst)).trans (fderiv_const_apply t)
    exact ht ⟨z₀, hdz₀, hconst z₀ hz₀_mem⟩
  rcases lt_trichotomy ‖x‖ ‖y‖ with hlt | heq | hgt
  · exact (hnot_lt hx hy hlt).elim
  · exact heq
  · exact (hnot_lt hy hx hgt).elim

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- For a continuous function `h : E → ℝ`, taking `max h 0` does not increase `‖fderiv ℝ h x‖`. -/
private theorem norm_fderiv_max_zero_le {h : E → ℝ} (hh : Continuous h) (x : E) :
    ‖fderiv ℝ (fun y ↦ max (h y) 0) x‖ ≤ ‖fderiv ℝ h x‖ := by
  rcases lt_trichotomy (h x) 0 with hlt | heq | hgt
  · have h0 : fderiv ℝ (fun y ↦ max (h y) 0) x = 0 := by
      refine (EventuallyEq.fderiv_eq (f := fun _ ↦ (0 : ℝ)) ?_).trans (fderiv_const_apply 0)
      filter_upwards [hh.continuousAt.eventually (gt_mem_nhds hlt)] with y hy
      exact max_eq_right hy.le
    rw [h0, norm_zero]
    exact norm_nonneg _
  · have h0 : fderiv ℝ (fun y ↦ max (h y) 0) x = 0 := by
      refine IsLocalMin.fderiv_eq_zero (Eventually.of_forall fun y ↦ ?_)
      simp [heq]
    rw [h0, norm_zero]
    exact norm_nonneg _
  · have heq' : fderiv ℝ (fun y ↦ max (h y) 0) x = fderiv ℝ h x := by
      refine EventuallyEq.fderiv_eq ?_
      filter_upwards [hh.continuousAt.eventually (lt_mem_nhds hgt)] with y hy
      exact max_eq_left hy.le
    rw [heq']

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- For a continuous function `u : E → ℝ`, taking `‖u ·‖` does not increase `‖fderiv ℝ u x‖`. -/
private theorem norm_fderiv_norm_le {u : E → ℝ} (hu : Continuous u) (x : E) :
    ‖fderiv ℝ (fun y ↦ ‖u y‖) x‖ ≤ ‖fderiv ℝ u x‖ := by
  rcases lt_trichotomy (u x) 0 with hlt | heq | hgt
  · have hneg : fderiv ℝ (fun y ↦ ‖u y‖) x = -fderiv ℝ u x := by
      refine (EventuallyEq.fderiv_eq (f := fun y ↦ -u y) ?_).trans fderiv_neg
      filter_upwards [hu.continuousAt.eventually (gt_mem_nhds hlt)] with y hy
      exact Real.norm_of_nonpos hy.le
    rw [hneg, norm_neg]
  · have h0 : fderiv ℝ (fun y ↦ ‖u y‖) x = 0 := by
      refine IsLocalMin.fderiv_eq_zero (Eventually.of_forall fun y ↦ ?_)
      simp [heq]
    rw [h0, norm_zero]
    exact norm_nonneg _
  · have hpos : fderiv ℝ (fun y ↦ ‖u y‖) x = fderiv ℝ u x := by
      refine EventuallyEq.fderiv_eq ?_
      filter_upwards [hu.continuousAt.eventually (lt_mem_nhds hgt)] with y hy
      exact Real.norm_of_nonneg hy.le
    rw [hpos]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Measurability of `x ↦ Φ ‖fderiv ℝ u x‖` for convex monotone `Φ` on `[0, ∞)`. -/
private theorem measurable_map_norm_fderiv {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ)
    (hΦm : MonotoneOn Φ (Ici 0)) (u : E → ℝ) :
    Measurable fun x ↦ Φ ‖fderiv ℝ u x‖ := by
  have hcont : Continuous fun s : ℝ ↦ Φ (max s 0) :=
    (hΦ.continuousOn_Ici_of_monotoneOn hΦm).comp_continuous
      (continuous_id.max continuous_const) fun s ↦ le_max_right s 0
  have heq : (fun x ↦ Φ ‖fderiv ℝ u x‖) = fun x ↦ Φ (max ‖fderiv ℝ u x‖ 0) := by
    funext x
    rw [max_eq_left (norm_nonneg _)]
  rw [heq]
  exact hcont.measurable.comp (measurable_fderiv ℝ u).norm

omit [Nontrivial E] in
/-- Weighted regular-part coarea decomposition of `∫⁻ x, ofReal (Φ ‖Du x‖)` for a nonnegative
function `u : E → ℝ`: since `Du = 0` wherever `u = 0` and `Φ 0 = 0`, only positive regular levels
contribute. -/
private theorem lintegral_map_norm_fderiv_eq_setLIntegral_Ioi {Φ : ℝ → ℝ}
    (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    {u : E → ℝ} (hu0 : ∀ x, 0 ≤ u x) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ u x‖) =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x in {x | fderiv ℝ u x ≠ 0} ∩ u ⁻¹' {t},
        ENNReal.ofReal (Φ ‖fderiv ℝ u x‖ / ‖fderiv ℝ u x‖) ∂μHE[finrank ℝ E - 1] := by
  set R := {x : E | fderiv ℝ u x ≠ 0}
  have hR : MeasurableSet R := (measurableSet_singleton 0).compl.preimage (measurable_fderiv ℝ u)
  have hsurj (x : E) (hx : x ∈ R) : Surjective (fderiv ℝ u x) :=
    surjective_of_ne_zero_of_finrank_eq_one (finrank_self ℝ) (f := (fderiv ℝ u x).toLinearMap)
      ((ContinuousLinearMap.coe_injective.ne_iff' ContinuousLinearMap.toLinearMap_zero).2 hx)
  let g : E → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (Φ ‖fderiv ℝ u x‖ / ‖fderiv ℝ u x‖)
  have hg : Measurable g := ENNReal.measurable_ofReal.comp
    ((measurable_map_norm_fderiv hΦ hΦm u).div (measurable_fderiv ℝ u).norm)
  have hlhs : ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ u x‖) =
      ∫⁻ x in R, ENNReal.ofReal (fderiv ℝ u x).adjoint.normDet * g x := by
    rw [← lintegral_indicator hR]
    refine lintegral_congr fun x ↦ ?_
    by_cases hx : x ∈ R
    · rw [indicator_of_mem hx, ContinuousLinearMap.normDet_adjoint_eq_norm]
      dsimp only [g]
      rw [← ENNReal.ofReal_mul (norm_nonneg _),
        mul_div_cancel₀ _ (norm_ne_zero_iff.2 hx)]
    · simp only [R, mem_ofPred_eq, not_not] at hx
      rw [indicator_of_notMem (by simp [R, hx]), hx, norm_zero, hΦ0, ENNReal.ofReal_zero]
  rw [hlhs, lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber
    hR.nullMeasurableSet (fun _ hx ↦ differentiableAt_of_fderiv_ne_zero hx) hsurj hg, finrank_self,
    ← lintegral_indicator measurableSet_Ioi]
  refine lintegral_congr fun t ↦ ?_
  by_cases ht : 0 < t
  · rw [indicator_of_mem ht]
  · rw [indicator_of_notMem ht]
    have hemp : R ∩ u ⁻¹' {t} = ∅ := by
      refine eq_empty_of_forall_notMem fun x ⟨hxR, hxu⟩ ↦ hxR ?_
      have hux0 : u x = 0 := le_antisymm ((mem_preimage.1 hxu).trans_le (not_lt.1 ht)) (hu0 x)
      exact IsLocalMin.fderiv_eq_zero (Eventually.of_forall fun y ↦ hux0.symm ▸ hu0 y)
    simp [hemp]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- On a regular set `S` where `0 < ‖Dh‖ ≤ K`, finiteness of `∫_S ‖Dh‖⁻¹ dHⁿ⁻¹` forces `Hⁿ⁻¹(S)` to
be finite. -/
private theorem euclideanHausdorffMeasure_lt_top_of_lintegral_inv_lt_top
    {K : ℝ≥0} {h : E → ℝ} {S : Set E}
    (hS_pos : ∀ x ∈ S, 0 < ‖fderiv ℝ h x‖) (hS_le : ∀ x ∈ S, ‖fderiv ℝ h x‖ ≤ K)
    (hinv_fin : (∫⁻ x in S, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]) < ∞) :
    μHE[finrank ℝ E - 1] S < ∞ := by
  set μH : Measure E := μHE[finrank ℝ E - 1]
  have h1 : μH S ≤ (K : ℝ≥0∞) * ∫⁻ x in S, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μH := by
    rw [← setLIntegral_one,
      ← lintegral_const_mul (K : ℝ≥0∞) (f := fun x ↦ ‖fderiv ℝ h x‖ₑ⁻¹)
        (measurable_fderiv ℝ h).eNorm.inv]
    refine setLIntegral_mono ((measurable_fderiv ℝ h).eNorm.inv.const_mul (K : ℝ≥0∞)) fun x hx ↦ ?_
    have hne0 : ‖fderiv ℝ h x‖ₑ ≠ 0 := by
      rw [← ofReal_norm]
      exact (ENNReal.ofReal_pos.2 (hS_pos x hx)).ne'
    rw [← ENNReal.mul_inv_cancel hne0 (by simp [← ofReal_norm])]
    gcongr
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hS_le x hx)
  exact h1.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hinv_fin)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Single-level fibre inequality: when `‖Dv‖` is constant on `S_v`, `μ(S_v) ≤ μ(S_h)`, the
reciprocal-gradient integral on `S_h` is at most that on `S_v` (which is finite), and `‖Dh‖ ≤ K` on
`S_h`, the convex gradient fibre integral on `S_v` is at most that on `S_h`. -/
private theorem setLIntegral_fiber_le_of_const_norm_fderiv {Φ : ℝ → ℝ}
    (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    {K : ℝ≥0} {v h : E → ℝ} {S_v S_h : Set E}
    (hSv_m : MeasurableSet S_v) (hSh_m : MeasurableSet S_h)
    (hSv_pos : ∀ x ∈ S_v, 0 < ‖fderiv ℝ v x‖) (hSh_pos : ∀ x ∈ S_h, 0 < ‖fderiv ℝ h x‖)
    (hSh_le : ∀ x ∈ S_h, ‖fderiv ℝ h x‖ ≤ K)
    (hconst : ∀ x ∈ S_v, ∀ y ∈ S_v, ‖fderiv ℝ v x‖ = ‖fderiv ℝ v y‖)
    (hperim : μHE[finrank ℝ E - 1] S_v ≤ μHE[finrank ℝ E - 1] S_h)
    (hinv : (∫⁻ x in S_h, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]) ≤
      ∫⁻ x in S_v, ‖fderiv ℝ v x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1])
    (hinv_fin : (∫⁻ x in S_v, ‖fderiv ℝ v x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]) < ∞)
    (hΦ_fin : (∫⁻ x in S_h, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖)
      ∂μHE[finrank ℝ E - 1]) < ∞) :
    (∫⁻ x in S_v, ENNReal.ofReal (Φ ‖fderiv ℝ v x‖ / ‖fderiv ℝ v x‖) ∂μHE[finrank ℝ E - 1]) ≤
      ∫⁻ x in S_h, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖) ∂μHE[finrank ℝ E - 1] := by
  set μH : Measure E := μHE[finrank ℝ E - 1]
  have hΦ_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ Φ s := hΦ0 ▸ hΦm (mem_Ici.2 le_rfl) hs hs
  have hSh_fin : μH S_h < ∞ := euclideanHausdorffMeasure_lt_top_of_lintegral_inv_lt_top
    hSh_pos hSh_le (hinv.trans_lt hinv_fin)
  have hSv_fin : μH S_v < ∞ := hperim.trans_lt hSh_fin
  by_cases hSv0 : μH S_v = 0
  · simp [Measure.restrict_eq_zero.2 hSv0]
  obtain ⟨x₀, hx₀⟩ := nonempty_of_measure_ne_zero hSv0
  set γ := ‖fderiv ℝ v x₀‖
  have hγ : 0 < γ := hSv_pos x₀ hx₀
  set ν_h := μH.restrict S_h
  have : Fact (μH S_h < ∞) := ⟨hSh_fin⟩
  set P := (μH S_v).toReal
  set M := (∫⁻ x in S_v, ‖fderiv ℝ v x‖ₑ⁻¹ ∂μH).toReal
  have hP_pos : 0 < P := ENNReal.toReal_pos hSv0 hSv_fin.ne
  have hM_eq : M = P / γ := by
    have hm : (∫⁻ x in S_v, ‖fderiv ℝ v x‖ₑ⁻¹ ∂μH) = ENNReal.ofReal γ⁻¹ * μH S_v := by
      rw [← setLIntegral_const]
      exact setLIntegral_congr_fun hSv_m fun x hx ↦ by
        rw [← ofReal_norm, hconst x hx x₀ hx₀, ENNReal.ofReal_inv_of_pos hγ]
    dsimp only [M, P]
    rw [hm, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hγ.le), inv_mul_eq_div]
  have hPM : P / M = γ := by rw [hM_eq, div_div_cancel₀ hP_pos.ne']
  have hlhs_eq : (∫⁻ x in S_v, ENNReal.ofReal (Φ ‖fderiv ℝ v x‖ / ‖fderiv ℝ v x‖) ∂μH) =
      ENNReal.ofReal (M * Φ (P / M)) := by
    have hc : (∫⁻ x in S_v, ENNReal.ofReal (Φ ‖fderiv ℝ v x‖ / ‖fderiv ℝ v x‖) ∂μH) =
        ENNReal.ofReal (Φ γ / γ) * μH S_v := by
      rw [← setLIntegral_const]
      exact setLIntegral_congr_fun hSv_m fun x hx ↦ by rw [hconst x hx x₀ hx₀]
    rw [hc, hPM, hM_eq, ← ENNReal.ofReal_toReal hSv_fin.ne,
      ← ENNReal.ofReal_mul (div_nonneg (hΦ_nonneg γ hγ.le) hγ.le)]
    congr 1
    ring
  have hg_pos : ∀ᵐ x ∂ν_h, 0 < ‖fderiv ℝ h x‖ :=
    (ae_restrict_mem hSh_m).mono fun x hx ↦ hSh_pos x hx
  have hinv_int : Integrable (fun x ↦ ‖fderiv ℝ h x‖⁻¹) ν_h := by
    refine ⟨(measurable_fderiv ℝ h).norm.inv.aestronglyMeasurable, ?_⟩
    refine (lintegral_congr_ae ?_).trans_lt (hinv.trans_lt hinv_fin)
    filter_upwards [hg_pos] with x hx
    rw [← ofReal_norm, ← ofReal_norm, Real.norm_of_nonneg (inv_nonneg.2 hx.le),
      ENNReal.ofReal_inv_of_pos hx]
  have hΦ_int : Integrable (fun x ↦ Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖) ν_h := by
    refine ⟨((measurable_map_norm_fderiv hΦ hΦm h).div
      (measurable_fderiv ℝ h).norm).aestronglyMeasurable, (lintegral_congr_ae ?_).trans_lt hΦ_fin⟩
    filter_upwards [hg_pos] with x hx
    rw [← ofReal_norm, Real.norm_of_nonneg (div_nonneg (hΦ_nonneg _ hx.le) hx.le)]
  have hM_bound : (∫ x, ‖fderiv ℝ h x‖⁻¹ ∂ν_h) ≤ M := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hinv_fin.ne,
      ofReal_integral_eq_lintegral_ofReal hinv_int (hg_pos.mono fun _ hx ↦ inv_nonneg.2 hx.le)]
    refine (setLIntegral_congr_fun hSh_m fun x hx ↦ ?_).le.trans hinv
    rw [← ofReal_norm, ENNReal.ofReal_inv_of_pos (hSh_pos x hx)]
  have hPν : P ≤ ν_h.real univ := by
    rw [measureReal_def, Measure.restrict_apply_univ]
    exact ENNReal.toReal_mono hSh_fin.ne hperim
  rw [hlhs_eq, ← ofReal_integral_eq_lintegral_ofReal hΦ_int
    (hg_pos.mono fun _ hx ↦ div_nonneg (hΦ_nonneg _ hx.le) hx.le)]
  exact ENNReal.ofReal_le_ofReal
    (hΦ.mul_map_div_le_integral_div hΦm hΦ0 hg_pos hinv_int hΦ_int hP_pos.le hPν hM_bound)

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- For a scalar map `w : E → ℝ`, differentiability with surjective derivative is equivalent to
nonvanishing of the totalized derivative `fderiv ℝ w x`. -/
private theorem setOf_differentiableAt_and_surjective_eq_setOf_fderiv_ne_zero (w : E → ℝ) :
    {x : E | DifferentiableAt ℝ w x ∧ Surjective (fderiv ℝ w x)} = {x : E | fderiv ℝ w x ≠ 0} := by
  ext x
  simp only [mem_ofPred_eq]
  refine ⟨fun ⟨_, hs⟩ h0 ↦ ?_, fun hx ↦ ⟨differentiableAt_of_fderiv_ne_zero hx,
    surjective_of_ne_zero_of_finrank_eq_one (finrank_self ℝ) (f := (fderiv ℝ w x).toLinearMap)
      ((ContinuousLinearMap.coe_injective.ne_iff' ContinuousLinearMap.toLinearMap_zero).2 hx)⟩⟩
  obtain ⟨y, hy⟩ := hs 1
  simp [h0] at hy

/-- Almost-everywhere perimeter and reciprocal-gradient comparisons between a nonnegative Lipschitz
function `h` and its real-valued Schwarz rearrangement `v`. -/
private theorem ae_fiber_bounds_toReal_schwarzRearrangement
    {K : ℝ≥0} {h : E → ℝ} (hh : LipschitzWith K h)
    (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞) :
    let v : E → ℝ := fun x ↦
      (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) x).toReal
    ∀ᵐ t : ℝ, 0 < t →
      t ∉ v '' {z | fderiv ℝ v z = 0} ∧
      μHE[finrank ℝ E - 1] ({x | fderiv ℝ v x ≠ 0} ∩ v ⁻¹' {t}) ≤
        μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}) ∧
      (∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]) ≤
        (∫⁻ x in {x | fderiv ℝ v x ≠ 0} ∩ v ⁻¹' {t}, ‖fderiv ℝ v x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]) ∧
      (∫⁻ x in {x | fderiv ℝ v x ≠ 0} ∩ v ⁻¹' {t}, ‖fderiv ℝ v x‖ₑ⁻¹
        ∂μHE[finrank ℝ E - 1]) < ∞ := by
  set f : E → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (h y)
  set v : E → ℝ := fun x ↦ (schwarzRearrangement volume f x).toReal
  have hv_lip : LipschitzWith K v := lipschitzWith_toReal_schwarzRearrangement volume hh
  have hf_lip : ∀ x y, f x ≤ f y + K * edist x y := fun x y ↦ by
    calc ENNReal.ofReal (h x) ≤ ENNReal.ofReal (h y + K * dist x y) :=
          ENNReal.ofReal_le_ofReal (hh.le_add_mul x y)
      _ ≤ ENNReal.ofReal (h y) + K * edist x y := by
        rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg]
        exact ENNReal.ofReal_add_le
  have hv_ne_top (x : E) : schwarzRearrangement volume f x ≠ ∞ := by
    refine schwarzRearrangement_ne_top volume hf_lip (t := ENNReal.ofReal 1) (by simp) ?_ x
    have hset : {y | ENNReal.ofReal 1 < f y} = {y | 1 < h y} := by
      ext y; exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg zero_le_one
    exact hset ▸ hfin 1 zero_lt_one
  have hv_level {t : ℝ} (ht : 0 < t) :
      {x | t < v x} = {x | ENNReal.ofReal t < schwarzRearrangement volume f x} := by
    ext x; exact (ENNReal.ofReal_lt_iff_lt_toReal ht.le (hv_ne_top x)).symm
  have hh_level {t : ℝ} (ht : 0 < t) : {x | ENNReal.ofReal t < f x} = {x | t < h x} := by
    ext x; exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le
  have hv_vol {t : ℝ} (ht : 0 < t) : volume {x | t < v x} = volume {x | t < h x} := by
    rw [hv_level ht, addHaar_setOf_lt_schwarzRearrangement, hh_level ht]
  have hv_fin (t : ℝ) (ht : 0 < t) : volume {x | t < v x} ≠ ∞ := hv_vol ht ▸ hfin t ht
  have hcrit := hh.volume_image_setOf_fderiv_toReal_schwarzRearrangement_eq_zero volume
  filter_upwards [compl_mem_ae_iff.2 hcrit,
    hh.ae_restrict_inter_setOf_regular_preimage_eq univ,
    hv_lip.ae_restrict_inter_setOf_regular_preimage_eq univ,
    hh.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage,
    hv_lip.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage,
    ae_setLIntegral_inv_enorm_fderiv_le_ofReal_neg_deriv hfin,
    ae_setLIntegral_inv_enorm_fderiv_eq_ofReal_neg_deriv
      hv_lip.continuous.measurable.aemeasurable hv_fin hcrit]
    with t hcritt hregh hregv hperh hperv hdisth hdistv ht
  rw [finrank_self, univ_inter, univ_inter,
    setOf_differentiableAt_and_surjective_eq_setOf_fderiv_ne_zero h] at hregh
  rw [finrank_self, univ_inter, univ_inter,
    setOf_differentiableAt_and_surjective_eq_setOf_fderiv_ne_zero v] at hregv
  have h1 : μHE[finrank ℝ E - 1] ({x | fderiv ℝ v x ≠ 0} ∩ v ⁻¹' {t}) =
      μHE[finrank ℝ E - 1] (v ⁻¹' {t}) := by
    simpa using congrArg (fun ν : Measure E ↦ ν univ) hregv.symm
  have h2 : μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}) =
      μHE[finrank ℝ E - 1] (h ⁻¹' {t}) := by
    simpa using congrArg (fun ν : Measure E ↦ ν univ) hregh.symm
  have hmeas_lt : NullMeasurableSet {x | ENNReal.ofReal t < f x} volume :=
    (measurableSet_lt measurable_const hh.continuous.measurable.ennreal_ofReal).nullMeasurableSet
  have hderiv_eq : deriv (fun s ↦ volume.real {x | s < v x}) t =
      deriv (fun s ↦ volume.real {x | s < h x}) t := by
    refine EventuallyEq.deriv_eq ?_
    filter_upwards [Ioi_mem_nhds ht] with s hs
    simp only [measureReal_def, hv_vol hs]
  refine ⟨hcritt, ?_, ?_, (hdistv ht) ▸ ENNReal.ofReal_lt_top⟩
  · rw [h1, h2, ← hperv, ← hperh, hv_level ht, ← hh_level ht]
    exact hmeas_lt.perimeter_setOf_lt_schwarzRearrangement_le
  · rw [hdistv ht, hderiv_eq]
    exact hdisth ht

/-- Core nonnegative Lipschitz case of Pólya–Szegő. -/
private theorem lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le_of_nonneg
    {K : ℝ≥0} {h : E → ℝ} (hh : LipschitzWith K h) (hh0 : ∀ x, 0 ≤ h x)
    (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) := by
  by_cases htop : ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) = ∞
  · exact htop ▸ le_top
  set f : E → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (h y)
  set v : E → ℝ := fun x ↦ (schwarzRearrangement volume f x).toReal
  have hv_lip : LipschitzWith K v := lipschitzWith_toReal_schwarzRearrangement volume hh
  have hf_lip : ∀ x y, f x ≤ f y + K * edist x y := fun x y ↦ by
    calc ENNReal.ofReal (h x) ≤ ENNReal.ofReal (h y + K * dist x y) :=
          ENNReal.ofReal_le_ofReal (hh.le_add_mul x y)
      _ ≤ ENNReal.ofReal (h y) + K * edist x y := by
        rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg]
        exact ENNReal.ofReal_add_le
  have hv_ne_top (x : E) : schwarzRearrangement volume f x ≠ ∞ := by
    refine schwarzRearrangement_ne_top volume hf_lip (t := ENNReal.ofReal 1) (by simp) ?_ x
    have hset : {y | ENNReal.ofReal 1 < f y} = {y | 1 < h y} := by
      ext y; exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg zero_le_one
    exact hset ▸ hfin 1 zero_lt_one
  have hco_h := lintegral_map_norm_fderiv_eq_setLIntegral_Ioi hΦ hΦm hΦ0 hh0
  rw [lintegral_map_norm_fderiv_eq_setLIntegral_Ioi hΦ hΦm hΦ0 (fun _ ↦ ENNReal.toReal_nonneg),
    hco_h]
  set R_v := {x : E | fderiv ℝ v x ≠ 0}
  set R_h := {x : E | fderiv ℝ h x ≠ 0}
  have hRv_m : MeasurableSet R_v :=
    (measurableSet_singleton 0).compl.preimage (measurable_fderiv ℝ v)
  have hRh_m : MeasurableSet R_h :=
    (measurableSet_singleton 0).compl.preimage (measurable_fderiv ℝ h)
  have hΦ_ae_fin : ∀ᵐ t : ℝ, t ∈ Ioi (0 : ℝ) →
      (∫⁻ x in R_h ∩ h ⁻¹' {t}, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖)
        ∂μHE[finrank ℝ E - 1]) < ∞ := by
    have hmeas := aemeasurable_setLIntegral_fiber_of_hasFDerivWithinAt volume
      hRh_m.nullMeasurableSet
      (fun x hx ↦ (differentiableAt_of_fderiv_ne_zero hx).hasFDerivAt.hasFDerivWithinAt)
      (ENNReal.measurable_ofReal.comp
        ((measurable_map_norm_fderiv hΦ hΦm h).div (measurable_fderiv ℝ h).norm))
    rw [finrank_self] at hmeas
    exact (ae_restrict_iff' measurableSet_Ioi).1 (ae_lt_top' hmeas.restrict (hco_h ▸ htop))
  have hrad : ∀ x y, ‖x‖ = ‖y‖ → v x = v y := fun x y hxy ↦
    congrArg ENNReal.toReal (schwarzRearrangement_eq_of_norm_eq volume f hxy)
  have hanti : ∀ x y, ‖x‖ ≤ ‖y‖ → v y ≤ v x := fun x y hxy ↦
    ENNReal.toReal_mono (hv_ne_top x) (schwarzRearrangement_le_of_norm_le volume f hxy)
  refine setLIntegral_mono_ae' measurableSet_Ioi ?_
  filter_upwards [hΦ_ae_fin, ae_fiber_bounds_toReal_schwarzRearrangement hh hfin]
    with t hΦt hfib ht
  obtain ⟨hcritt, hperim_le, hinv_le, hinv_fin⟩ := hfib ht
  exact setLIntegral_fiber_le_of_const_norm_fderiv hΦ hΦm hΦ0
    (hRv_m.inter (isClosed_singleton.preimage hv_lip.continuous).measurableSet)
    (hRh_m.inter (isClosed_singleton.preimage hh.continuous).measurableSet)
    (fun _ hx ↦ norm_pos_iff.2 hx.1)
    (fun _ hx ↦ norm_pos_iff.2 hx.1)
    (fun _ _ ↦ norm_fderiv_le_of_lipschitz ℝ hh)
    (fun _ hx _ hy ↦ norm_fderiv_eq_of_norm_eq hrad
      (norm_eq_of_notMem_image_fderiv_eq_zero hanti hcritt hx.2 hy.2))
    hperim_le hinv_le hinv_fin (hΦt ht)

end PrivateHelpers

section PublicAPI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- **The convex-integrand Pólya–Szegő inequality for Lipschitz functions.** Let `Φ : ℝ → ℝ` be
convex and monotone on `[0, ∞)` with `Φ 0 = 0`, and let `h : E → ℝ` be Lipschitz with finite-volume
positive superlevel sets. Then the real-valued Schwarz rearrangement of the positive part of `h` has
convex gradient integral at most that of `h` (both sides valued in `ℝ≥0∞`). -/
theorem lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le
    {K : ℝ≥0} {h : E → ℝ} (hh : LipschitzWith K h)
    (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) := by
  let hpos : E → ℝ := fun x ↦ max (h x) 0
  have hhpos_lip : LipschitzWith K hpos := by
    simpa only [max_eq_left (zero_le : 0 ≤ K)] using hh.max (LipschitzWith.const (0 : ℝ))
  have hhpos_fin (t : ℝ) (ht : 0 < t) : volume {x | t < hpos x} ≠ ∞ := by
    have hset : {x | t < hpos x} = {x | t < h x} := by
      ext x; simp [hpos, lt_max_iff, ht.not_gt]
    exact hset ▸ hfin t ht
  have hofReal : (fun y ↦ ENNReal.ofReal (h y)) = fun y ↦ ENNReal.ofReal (hpos y) := by
    funext y
    rcases le_total 0 (h y) with hy | hy
    · simp [hpos, max_eq_left hy]
    · simp [hpos, max_eq_right hy, ENNReal.ofReal_of_nonpos hy]
  rw [hofReal]
  refine (lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le_of_nonneg hhpos_lip
    (fun x ↦ le_max_right (h x) 0) hhpos_fin hΦ hΦm hΦ0).trans (lintegral_mono fun x ↦ ?_)
  exact ENNReal.ofReal_le_ofReal
    (hΦm (norm_nonneg _) (norm_nonneg _) (norm_fderiv_max_zero_le hh.continuous x))

/-- **Signed convex-integrand Pólya–Szegő inequality for Lipschitz functions.** Rearranging `‖u ·‖`
does not increase `∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ u x‖)`. -/
theorem lintegral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le
    {K : ℝ≥0} {u : E → ℝ} (hu : LipschitzWith K u)
    (hfin : ∀ t, 0 < t → volume {x | t < ‖u x‖} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) z).toReal) x‖) ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ u x‖) := by
  have hu_norm : LipschitzWith K (fun x ↦ ‖u x‖) := by
    simpa only [one_mul, Function.comp_def] using
      (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)).comp hu
  refine (lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le hu_norm hfin hΦ hΦm hΦ0).trans
    (lintegral_mono fun x ↦ ?_)
  exact ENNReal.ofReal_le_ofReal
    (hΦm (norm_nonneg _) (norm_nonneg _) (norm_fderiv_norm_le hu.continuous x))

/-- Integrability of `Φ ‖Dh*‖` when `Φ ‖Dh‖` is integrable. -/
theorem integrable_map_norm_fderiv_toReal_schwarzRearrangement
    {K : ℝ≥0} {h : E → ℝ} (hh : LipschitzWith K h)
    (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ h x‖) volume) :
    Integrable (fun x ↦ Φ ‖fderiv ℝ
      (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖)
      volume := by
  have hΦ_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ Φ s := hΦ0 ▸ hΦm (mem_Ici.2 le_rfl) hs hs
  set v : E → ℝ := fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal
  refine ⟨(measurable_map_norm_fderiv hΦ hΦm v).aestronglyMeasurable, ?_⟩
  have heq (w : E → ℝ) : (∫⁻ x, ‖Φ ‖fderiv ℝ w x‖‖ₑ) =
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ w x‖) := by
    refine lintegral_congr fun x ↦ ?_
    rw [← ofReal_norm, Real.norm_of_nonneg (hΦ_nonneg _ (norm_nonneg _))]
  rw [HasFiniteIntegral, heq v]
  exact (lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le hh hfin hΦ hΦm hΦ0).trans_lt
    (heq h ▸ hint.hasFiniteIntegral)

/-- **Bochner-integral Pólya–Szegő inequality** for the positive-part Schwarz rearrangement. -/
theorem integral_map_norm_fderiv_toReal_schwarzRearrangement_le
    {K : ℝ≥0} {h : E → ℝ} (hh : LipschitzWith K h)
    (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ h x‖) volume) :
    ∫ x, Φ ‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖ ≤
      ∫ x, Φ ‖fderiv ℝ h x‖ := by
  have hΦ_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ Φ s := hΦ0 ▸ hΦm (mem_Ici.2 le_rfl) hs hs
  have hint_v := integrable_map_norm_fderiv_toReal_schwarzRearrangement hh hfin hΦ hΦm hΦ0 hint
  rw [← ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun x ↦ hΦ_nonneg _ (norm_nonneg _)),
    ofReal_integral_eq_lintegral_ofReal hint_v
      (Eventually.of_forall fun x ↦ hΦ_nonneg _ (norm_nonneg _)),
    ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun x ↦ hΦ_nonneg _ (norm_nonneg _))]
  exact lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le hh hfin hΦ hΦm hΦ0

/-- Integrability of `Φ ‖D(|u|*)‖` when `Φ ‖Du‖` is integrable. -/
theorem integrable_map_norm_fderiv_toReal_schwarzRearrangement_norm
    {K : ℝ≥0} {u : E → ℝ} (hu : LipschitzWith K u)
    (hfin : ∀ t, 0 < t → volume {x | t < ‖u x‖} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ u x‖) volume) :
    Integrable (fun x ↦ Φ ‖fderiv ℝ
      (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) z).toReal) x‖)
      volume := by
  have hΦ_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ Φ s := hΦ0 ▸ hΦm (mem_Ici.2 le_rfl) hs hs
  set v : E → ℝ := fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) z).toReal
  refine ⟨(measurable_map_norm_fderiv hΦ hΦm v).aestronglyMeasurable, ?_⟩
  have heq (w : E → ℝ) : (∫⁻ x, ‖Φ ‖fderiv ℝ w x‖‖ₑ) =
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ w x‖) := by
    refine lintegral_congr fun x ↦ ?_
    rw [← ofReal_norm, Real.norm_of_nonneg (hΦ_nonneg _ (norm_nonneg _))]
  rw [HasFiniteIntegral, heq v]
  exact (lintegral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le hu hfin hΦ hΦm hΦ0).trans_lt
    (heq u ▸ hint.hasFiniteIntegral)

/-- **Signed Bochner-integral Pólya–Szegő inequality** for `‖u ·‖`. -/
theorem integral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le
    {K : ℝ≥0} {u : E → ℝ} (hu : LipschitzWith K u)
    (hfin : ∀ t, 0 < t → volume {x | t < ‖u x‖} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ u x‖) volume) :
    ∫ x, Φ ‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) z).toReal) x‖ ≤
      ∫ x, Φ ‖fderiv ℝ u x‖ := by
  have hΦ_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ Φ s := hΦ0 ▸ hΦm (mem_Ici.2 le_rfl) hs hs
  have hint_v := integrable_map_norm_fderiv_toReal_schwarzRearrangement_norm hu hfin hΦ hΦm hΦ0 hint
  rw [← ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun x ↦ hΦ_nonneg _ (norm_nonneg _)),
    ofReal_integral_eq_lintegral_ofReal hint_v
      (Eventually.of_forall fun x ↦ hΦ_nonneg _ (norm_nonneg _)),
    ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun x ↦ hΦ_nonneg _ (norm_nonneg _))]
  exact lintegral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le hu hfin hΦ hΦm hΦ0

/-- **`Lᵖ` gradient Pólya–Szegő inequality (`1 ≤ p`, `lintegral` form)** for the positive part. -/
theorem lintegral_norm_fderiv_toReal_schwarzRearrangement_rpow_le
    {K : ℝ≥0} {h : E → ℝ} (hh : LipschitzWith K h)
    (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖ ^ p) ≤
      ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ h x‖ ^ p) :=
  lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le hh hfin (convexOn_rpow hp)
    (Real.monotoneOn_rpow_Ici_of_exponent_nonneg (zero_le_one.trans hp))
    (Real.zero_rpow (zero_lt_one.trans_le hp).ne')

/-- **Signed `Lᵖ` gradient Pólya–Szegő inequality (`1 ≤ p`, `lintegral` form)**. -/
theorem lintegral_norm_fderiv_toReal_schwarzRearrangement_norm_rpow_le
    {K : ℝ≥0} {u : E → ℝ} (hu : LipschitzWith K u)
    (hfin : ∀ t, 0 < t → volume {x | t < ‖u x‖} ≠ ∞) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) z).toReal) x‖ ^ p) ≤
      ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ u x‖ ^ p) :=
  lintegral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le hu hfin (convexOn_rpow hp)
    (Real.monotoneOn_rpow_Ici_of_exponent_nonneg (zero_le_one.trans hp))
    (Real.zero_rpow (zero_lt_one.trans_le hp).ne')

/-- Integrability of `‖D(|u|*)‖ ^ p` (`1 ≤ p`) when `‖Du‖ ^ p` is integrable. -/
theorem integrable_norm_fderiv_toReal_schwarzRearrangement_norm_rpow
    {K : ℝ≥0} {u : E → ℝ} (hu : LipschitzWith K u)
    (hfin : ∀ t, 0 < t → volume {x | t < ‖u x‖} ≠ ∞) {p : ℝ} (hp : 1 ≤ p)
    (hint : Integrable (fun x ↦ ‖fderiv ℝ u x‖ ^ p) volume) :
    Integrable (fun x ↦ ‖fderiv ℝ
      (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) z).toReal) x‖ ^ p)
      volume :=
  integrable_map_norm_fderiv_toReal_schwarzRearrangement_norm hu hfin (convexOn_rpow hp)
    (Real.monotoneOn_rpow_Ici_of_exponent_nonneg (zero_le_one.trans hp))
    (Real.zero_rpow (zero_lt_one.trans_le hp).ne') hint

/-- **Signed `Lᵖ` gradient Pólya–Szegő inequality (`1 ≤ p`, Bochner-integral form)**. -/
theorem integral_norm_fderiv_toReal_schwarzRearrangement_norm_rpow_le
    {K : ℝ≥0} {u : E → ℝ} (hu : LipschitzWith K u)
    (hfin : ∀ t, 0 < t → volume {x | t < ‖u x‖} ≠ ∞) {p : ℝ} (hp : 1 ≤ p)
    (hint : Integrable (fun x ↦ ‖fderiv ℝ u x‖ ^ p) volume) :
    ∫ x, ‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) z).toReal) x‖ ^ p ≤
      ∫ x, ‖fderiv ℝ u x‖ ^ p :=
  integral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le hu hfin (convexOn_rpow hp)
    (Real.monotoneOn_rpow_Ici_of_exponent_nonneg (zero_le_one.trans hp))
    (Real.zero_rpow (zero_lt_one.trans_le hp).ne') hint

end PublicAPI

end TauCeti
