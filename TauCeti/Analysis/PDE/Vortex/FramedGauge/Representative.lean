/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.WindingPhase
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.Distribution.SchwartzSpace.ExponentialDecay
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv
import TauCeti.Analysis.SpecialFunctions.Exp.Limits
import TauCeti.Analysis.SpecialFunctions.Exp.Shift

/-!
# Smooth framed vortices in the affine Sobolev field space

A plane vortex `x` whose section is normalized at its end — equal outside a compact set to `|α|`
times the winding phase `(z / |z|)^m` — has real positive section `|α| = exp ((1 / 2) log |α|²)` in
the winding-`m` end trivialization. Outside the cutoff disc of `referenceField f m`, the
holomorphicity equation `∂bar_a α = 0` expresses the connection of the end trivialization as
`(-∂₂ L, ∂₁ L)` where `L = (1 / 2) log |α|²` (`TauCeti.Vortex.fderiv_log_normSq_apply_one`,
`TauCeti.Vortex.fderiv_log_normSq_apply_I`), while the reference field becomes the vacuum. Hence
outside a ball the field defect `x - referenceField f m` has the exact coordinates

`(-∂₂ L, ∂₁ L, (exp L - 1) (x_ref)₂, (exp L - 1) (x_ref)₃)`.

Every iterated derivative of `log |α|²` is `O(exp (-c |z|))` at infinity for every `c < 1 / 2`
(`TauCeti.Vortex.isBigO_iteratedFDeriv_log_normSq`), and every iterated derivative of
`referenceField f m` is globally bounded
(`TauCeti.Vortex.exists_norm_iteratedFDeriv_referenceField_apply_le`). Differentiating the exterior
formula therefore upgrades the zeroth-order convergence of
`TauCeti.Vortex.exists_norm_sub_referenceField_le_mul_exp` to all derivative orders
(`TauCeti.Vortex.isBigO_iteratedFDeriv_sub_referenceField`,
`TauCeti.Vortex.exists_norm_iteratedFDeriv_sub_referenceField_le_mul_exp`).

When `x` is smooth, each coordinate of `x - referenceField f m` is a Schwartz function by
`SchwartzMap.ofIsBigOIteratedFDerivExp`, so `x` belongs to the affine Sobolev model
`framedFieldSpace f m s` at every real order `s`
(`TauCeti.Vortex.mem_framedFieldSpace_of_sectionValue_eq_mul_windingPhase`). Combining with the
end-phase normalization `TauCeti.Vortex.exists_framedGaugeGroup_sectionValue_smul_eq` shows that
every smooth degree-`m` framed plane vortex has a smooth framed gauge transform lying in
`framedFieldSpace f m s` for every `f` and `s`, with exponential decay of all iterated derivatives
(`TauCeti.Vortex.exists_framedGaugeGroup_norm_iteratedFDeriv_smul_sub_referenceField_le_mul_exp`,
`TauCeti.Vortex.exists_framedGaugeGroup_smul_mem_framedFieldSpace`). Note that the normalizing
smooth framed gauge need only tend to `1` at infinity (for instance with a `1 / |z|` tail) and need
not itself lie in a Sobolev gauge group; only the normalized representative lies in `A_m^s`.

## Main results

* `TauCeti.Vortex.isBigO_iteratedFDeriv_sub_referenceField_apply`,
  `TauCeti.Vortex.isBigO_iteratedFDeriv_sub_referenceField`: for a vortex with smooth section,
  `|α| → 1`, and end-normalized phase outside a compact set, every iterated derivative of
  `x - referenceField f m` is `O(exp (-c |z|))` at infinity for all `c < 1 / 2`.
* `TauCeti.Vortex.exists_norm_iteratedFDeriv_sub_referenceField_le_mul_exp`: when `x` is smooth,
  `‖Dⁿ(x - referenceField f m)(z)‖ ≤ K exp (-c |z|)` on the whole plane.
* `TauCeti.Vortex.mem_framedFieldSpace_of_sectionValue_eq_mul_windingPhase`: a smooth
  end-normalized vortex lies in `framedFieldSpace f m s` for every cutoff `f` and order `s : ℝ`.
* `TauCeti.Vortex.exists_framedGaugeGroup_norm_iteratedFDeriv_smul_sub_referenceField_le_mul_exp`:
  every smooth framed degree-`m` vortex has a smooth framed gauge representative whose difference
  from `referenceField f m` decays exponentially with all derivatives.
* `TauCeti.Vortex.exists_framedGaugeGroup_smul_mem_framedFieldSpace`: every smooth framed degree-`m`
  vortex has a smooth framed gauge representative lying in `framedFieldSpace f m s` for all `f` and
  `s`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Asymptotics Complex ComplexConjugate Filter Metric
open scoped ContDiff Topology

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {m : ℕ}

/-! ### Exterior coordinate formulas in the end trivialization -/

/-- Outside the cutoff disc of `referenceField f m`, at a nonzero point near which `x` solves the
vortex equations and its section is `|α|` times `windingPhase m`, the connection defect of
`x - referenceField f m` is `(-(1 / 2) ∂₂(log |α|²), (1 / 2) ∂₁(log |α|²))` and its section defect
is `(exp ((1 / 2) log |α|²) - 1)` times the reference section coordinates. -/
private theorem sub_referenceField_eq_of_sectionValue_eq_mul_windingPhase
    (f : ContDiffBump (0 : ℝ)) {z : ℂ} (hrOut : f.rOut ≤ ‖z‖ ^ 2)
    (hp : ContDiffAt ℝ 2 (fun w ↦ x w 2) z) (hq : ContDiffAt ℝ 2 (fun w ↦ x w 3) z)
    (hα : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0) (hsol : ∀ᶠ w in 𝓝 z, equation x w = 0)
    (hphase : ∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * windingPhase m w) :
    let ℓ : ℂ → ℝ := fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))
    (x z 0 - referenceField f m z 0 = -(1 / 2) * fderiv ℝ ℓ z I) ∧
      (x z 1 - referenceField f m z 1 = (1 / 2) * fderiv ℝ ℓ z 1) ∧
      (x z 2 - referenceField f m z 2 = (Real.exp (ℓ z / 2) - 1) * referenceField f m z 2) ∧
      (x z 3 - referenceField f m z 3 = (Real.exp (ℓ z / 2) - 1) * referenceField f m z 3) := by
  intro ℓ
  have hz : z ≠ 0 := ne_zero_of_rOut_le_norm_sq f hrOut
  set u : ℂ → Circle := (windingPhase m)⁻¹
  set y : ℂ → EuclideanSpace ℝ (Fin 4) := gaugeTransform u x
  have hu : ContDiffAt ℝ 2 (fun w ↦ (u w : ℂ)) z := by
    simpa only [u, Pi.inv_apply, Circle.coe_inv_eq_conj, Function.comp_def, conjCLE_apply] using
      conjCLE.contDiff.contDiffAt.comp z (contDiffAt_windingPhase m hz)
  have hu1 : DifferentiableAt ℝ (fun w ↦ (u w : ℂ)) z := hu.differentiableAt two_ne_zero
  -- Near `z`, the connection of `x` is differentiable because `α ≠ 0` and `∂bar_a α = 0`.
  obtain ⟨hb₀, hb₁⟩ := differentiableAt_connection_of_equation hp hq hα
    (hsol.mono fun w hw ↦ ⟨by simp [hw], by simp [hw]⟩)
  have hx_diff : ∀ i, DifferentiableAt ℝ (fun w ↦ x w i) z := fun i ↦ by
    fin_cases i
    exacts [hb₀, hb₁, hp.differentiableAt two_ne_zero, hq.differentiableAt two_ne_zero]
  have hysol : equation y z = 0 :=
    (equation_gaugeTransform_eq_zero_iff hu hx_diff).2 hsol.self_of_nhds
  -- In the end trivialization `y`, the section is real on `𝓝 z`, so `y · 3` vanishes near `z`.
  have hy_sec : ∀ᶠ w in 𝓝 z, sectionValue y w = ‖sectionValue x w‖ := by
    filter_upwards [hphase] with w hw
    have h1 : (u w : ℂ) * (windingPhase m w : ℂ) = 1 := by
      simp only [u, Pi.inv_apply, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
    rw [sectionValue_gaugeTransform]
    nth_rw 1 [hw]
    rw [mul_left_comm, h1, mul_one]
  have hy3_nhds : (fun w ↦ y w 3) =ᶠ[𝓝 z] fun _ ↦ (0 : ℝ) := by
    filter_upwards [hy_sec] with w hw
    have him := congrArg Complex.im (sectionValue_apply y w ▸ hw)
    simp only [mul_im, add_im, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat] at him
    linarith
  have hy3 : y z 3 = 0 := hy3_nhds.eq_of_nhds
  have hdy3 : fderiv ℝ (fun w ↦ y w 3) z = 0 := by simpa using hy3_nhds.fderiv_eq
  have hyp : DifferentiableAt ℝ (fun w ↦ y w 2) z := by
    simp only [y, gaugeTransform_apply, PiLp.toLp_apply, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    exact ((reCLM.differentiableAt.comp z hu1).mul (hx_diff 2)).sub
      ((imCLM.differentiableAt.comp z hu1).mul (hx_diff 3))
  have hyq : DifferentiableAt ℝ (fun w ↦ y w 3) z :=
    (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq hy3_nhds
  have hnorm_eq (w : ℂ) : y w 2 ^ 2 + y w 3 ^ 2 = x w 2 ^ 2 + x w 3 ^ 2 := by
    have h := congrArg (‖·‖ ^ 2) (sectionValue_gaugeTransform u x w)
    rw [norm_mul, Circle.norm_coe, one_mul, sq_norm_sectionValue, sq_norm_sectionValue] at h
    linarith
  have hℓy : (fun w ↦ Real.log (4 * (y w 2 ^ 2 + y w 3 ^ 2))) = ℓ := by
    funext w; simp only [ℓ, hnorm_eq w]
  have hyα : y z 2 ^ 2 + y z 3 ^ 2 ≠ 0 := by rwa [hnorm_eq z]
  have hf1 := fderiv_log_normSq_apply_one hyp hyq hyα (by simp [hysol]) (by simp [hysol])
  have hfI := fderiv_log_normSq_apply_I hyp hyq hyα (by simp [hysol]) (by simp [hysol])
  rw [hℓy, hy3, hdy3] at hf1 hfI
  simp only [zero_apply, mul_zero, zero_mul, sub_zero, zero_div, neg_zero, zero_sub] at hf1 hfI
  -- Subtract `vacuumField = gaugeTransform u (referenceField f m)` to read off connection defects.
  have hconn : y z 0 = x z 0 - referenceField f m z 0 ∧ y z 1 = x z 1 - referenceField f m z 1 := by
    have hsub := congrFun (gaugeTransform_sub_gaugeTransform u x (referenceField f m)) z
    rw [Pi.sub_apply, gaugeTransform_inv_windingPhase_referenceField f m hrOut] at hsub
    exact ⟨by simpa [y, vacuumField_apply, gaugeLinearAction_apply] using congrArg (· 0) hsub,
      by simpa [y, vacuumField_apply, gaugeLinearAction_apply] using congrArg (· 1) hsub⟩
  -- Outside the cutoff disc `referenceSection f m z = windingPhase m z` and `|α| = exp (ℓ / 2)`.
  have hexp : ‖sectionValue x z‖ = Real.exp (ℓ z / 2) := by
    have hpos : 0 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) :=
      lt_of_le_of_ne (by positivity) (mul_ne_zero four_ne_zero hα).symm
    dsimp only [ℓ]
    rw [Real.exp_half, Real.exp_log hpos, ← sq_norm_sectionValue, Real.sqrt_sq (norm_nonneg _)]
  have hsec_sub : sectionValue x z - sectionValue (referenceField f m) z =
      (Real.exp (ℓ z / 2) - 1 : ℝ) * sectionValue (referenceField f m) z := by
    rw [sectionValue_referenceField, hphase.self_of_nhds, hexp, referenceSection_eq_phase f m hrOut,
      ← coe_windingPhase m hz]
    push_cast
    ring
  have hsec_re := congrArg Complex.re hsec_sub
  have hsec_im := congrArg Complex.im hsec_sub
  simp only [sectionValue_apply, sub_re, sub_im, mul_re, mul_im, add_re, add_im, ofReal_re,
    ofReal_im, I_re, I_im, re_ofNat, im_ofNat] at hsec_re hsec_im
  exact ⟨by linarith [hconn.1, hfI], by linarith [hconn.2, hf1], by linarith, by linarith⟩

/-- If `L : ℂ → ℝ` is smooth, tends to `0` at infinity, has bounded iterated derivatives of every
order, and has `DʲL = O(exp (-c |z|))` for every `j`, then `Dⁿ(exp L - 1) = O(exp (-c |z|))` for
every `n`. -/
private theorem isBigO_iteratedFDeriv_exp_sub_one_of_isBigO {L : ℂ → ℝ} (hL : ContDiff ℝ ∞ L)
    (hL₀ : Tendsto L (cocompact ℂ) (𝓝 0))
    (hLbdd : ∀ j : ℕ, iteratedFDeriv ℝ j L =O[cocompact ℂ] fun _ ↦ (1 : ℝ))
    {c : ℝ} (hLc : ∀ j : ℕ, iteratedFDeriv ℝ j L =O[cocompact ℂ] fun z ↦ Real.exp (-(c * ‖z‖)))
    (n : ℕ) :
    iteratedFDeriv ℝ n (fun z ↦ Real.exp (L z) - 1) =O[cocompact ℂ]
      fun z ↦ Real.exp (-(c * ‖z‖)) := by
  -- First establish `Dⁱ(exp L) = O(1)` for all `i` so `c` may have any sign.
  have hexp_bdd : ∀ i : ℕ,
      iteratedFDeriv ℝ i (fun z ↦ Real.exp (L z)) =O[cocompact ℂ] fun _ ↦ (1 : ℝ) := by
    intro i
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      rcases i with _ | i
      · have hlim1 : Tendsto (fun z ↦ Real.exp (L z)) (cocompact ℂ) (𝓝 1) := by
          simpa [Function.comp_def] using (Real.continuous_exp.tendsto 0).comp hL₀
        refine (isBigO_of_le _ fun z ↦ ?_).trans (hlim1.isBigO_one ℝ)
        simp [iteratedFDeriv_zero_eq_comp]
      · exact (hL.of_le (mod_cast le_top)).isBigO_iteratedFDeriv_succ_exp
          (fun j _ _ ↦ hLbdd j) fun j hj ↦ ih j (Nat.lt_succ_of_le hj)
  rcases n with _ | n
  · have h0 := Real.isBigO_exp_comp_sub_one hL₀ (by
      refine (isBigO_of_le _ fun z ↦ ?_).trans (hLc 0)
      simp [iteratedFDeriv_zero_eq_comp])
    exact (isBigO_of_le _ fun z ↦ by simp [iteratedFDeriv_zero_eq_comp]).trans h0
  · have hsub : (fun z ↦ Real.exp (L z) - 1) = fun z ↦ Real.exp (L z) + (-1 : ℝ) := by
      funext z; ring
    rw [hsub, TauCeti.iteratedFDeriv_succ_add_const]
    exact (hL.of_le (mod_cast le_top)).isBigO_iteratedFDeriv_succ_exp
      (fun j _ _ ↦ hLc j) fun j _ ↦ hexp_bdd j

/-- Regularize `(1 / 2) log |α|²` inside a compact disc to obtain a globally smooth function `L` on
`ℂ` that agrees with `(1 / 2) log (4 (p² + q²))` outside a ball and inherits exponential derivative
decay at every rate `c' < 1 / 2`. -/
private theorem exists_contDiff_eq_half_log_normSq
    (hp : ContDiff ℝ ∞ (fun w ↦ x w 2)) (hq : ContDiff ℝ ∞ (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) (R : ℝ)
    (hR : ∀ z, R < ‖z‖ → 1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2)) :
    ∃ L : ℂ → ℝ, ContDiff ℝ ∞ L ∧ Tendsto L (cocompact ℂ) (𝓝 0) ∧
      (∀ z, max R 0 + 2 < ‖z‖ → L z = (1 / 2) * Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2))) ∧
      ∀ {c' : ℝ}, c' < 1 / 2 → ∀ j : ℕ,
        iteratedFDeriv ℝ j L =O[cocompact ℂ] fun z ↦ Real.exp (-(c' * ‖z‖)) := by
  set R' := max R 0
  let b : ContDiffBump (0 : ℂ) := ⟨R' + 1, R' + 2, by positivity, by linarith⟩
  set S : ℂ → ℝ := fun z ↦ b z + 4 * (x z 2 ^ 2 + x z 3 ^ 2)
  have hS_pos (z : ℂ) : 0 < S z := by
    rcases le_or_gt ‖z‖ R' with hz | hz
    · have hb1 : b z = 1 := b.one_of_mem_closedBall (mem_closedBall_zero_iff.2 (by linarith))
      have hsq : 0 ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2) := by positivity
      linarith
    · linarith [hR z ((le_max_left R 0).trans_lt hz), b.nonneg' z]
  have hS : ContDiff ℝ ∞ S := b.contDiff.add (contDiff_const.mul ((hp.pow 2).add (hq.pow 2)))
  set L : ℂ → ℝ := fun z ↦ (1 / 2) * Real.log (S z)
  have hL : ContDiff ℝ ∞ L := contDiff_const.mul (hS.log fun z ↦ (hS_pos z).ne')
  have hL_eq : ∀ z, R' + 2 < ‖z‖ → L z = (1 / 2) * Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) := by
    intro z hz
    have hb0 : b z = 0 := b.zero_of_le_dist (by rw [dist_zero_right]; exact hz.le)
    simp [L, S, hb0]
  have hL₀ : Tendsto L (cocompact ℂ) (𝓝 0) := by
    have hlog0 : Tendsto (fun z ↦ (1 / 2) * Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)))
        (cocompact ℂ) (𝓝 0) := by
      have h := ((Real.continuousAt_log one_ne_zero).tendsto.comp hlim).const_mul (1 / 2 : ℝ)
      rwa [Real.log_one, mul_zero] at h
    refine hlog0.congr' ?_
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop (R' + 2)] with z hz
    exact (hL_eq z hz).symm
  refine ⟨L, hL, hL₀, hL_eq, fun {c'} hc' j ↦ ?_⟩
  have hlog :=
    (isBigO_iteratedFDeriv_log_normSq hp hq hsol hlim hc' j).norm_left.const_mul_left (1 / 2)
  refine isBigO_norm_left.1 ((EventuallyEq.isBigO ?_).trans hlog)
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop (R' + 2)] with z hz
  have hnhds : L =ᶠ[𝓝 z] fun w ↦ (1 / 2 : ℝ) • Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)) :=
    Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hz) hL_eq
  have hgt : 1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) :=
    hR z ((le_max_left R 0).trans_lt (by linarith))
  have hcd_log : ContDiffAt ℝ j (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z :=
    ((contDiff_const.mul ((hp.pow 2).add (hq.pow 2))).contDiffAt.log (by positivity)).of_le
      (mod_cast le_top)
  rw [(hnhds.iteratedFDeriv ℝ j).eq_of_nhds, iteratedFDeriv_const_smul_apply' hcd_log, norm_smul,
    Real.norm_eq_abs, abs_of_pos one_half_pos]

/-- Construct globally smooth coordinate surrogates `g : Fin 4 → ℂ → ℝ` that agree with the
coordinates of `x - referenceField f m` outside a ball and have `O(exp (-c |z|))` iterated
derivatives at infinity for every `c < 1 / 2`. -/
private theorem exists_contDiff_sub_referenceField_eq_and_isBigO
    (hp : ContDiff ℝ ∞ (fun w ↦ x w 2)) (hq : ContDiff ℝ ∞ (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) :
    ∃ (R : ℝ) (g : Fin 4 → ℂ → ℝ), (∀ i, ContDiff ℝ ∞ (g i)) ∧
      (∀ z, R < ‖z‖ → ∀ i, x z i - referenceField f m z i = g i z) ∧
      ∀ {c : ℝ}, c < 1 / 2 → ∀ i n,
        iteratedFDeriv ℝ n (g i) =O[cocompact ℂ] fun z ↦ Real.exp (-(c * ‖z‖)) := by
  have hev := hphase.and (hlim.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1)))
  obtain ⟨R₀, -, hR₀⟩ :=
    hasBasis_cobounded_norm.eventually_iff.mp (cobounded_eq_cocompact (α := ℂ) ▸ hev)
  set R := max R₀ (max 1 f.rOut)
  have hR_pos : 0 ≤ R := (le_max_left 1 f.rOut).trans' zero_le_one |>.trans (le_max_right _ _)
  obtain ⟨L, hL, hL₀, hL_eq, hL_decay⟩ := exists_contDiff_eq_half_log_normSq hp hq hsol hlim R
    fun z hz ↦ (hR₀ ((le_max_left _ _).trans hz.le)).2
  rw [max_eq_left hR_pos] at hL_eq
  have hLf : ContDiff ℝ ∞ (fderiv ℝ L) := hL.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have href_cd := contDiff_euclidean.1 (contDiff_referenceField f m)
  let g : Fin 4 → ℂ → ℝ := ![fun z ↦ -fderiv ℝ L z I, fun z ↦ fderiv ℝ L z 1,
    fun z ↦ (Real.exp (L z) - 1) * referenceField f m z 2,
    fun z ↦ (Real.exp (L z) - 1) * referenceField f m z 3]
  have hg_cd (i : Fin 4) : ContDiff ℝ ∞ (g i) := by
    fin_cases i
    · exact ((ContinuousLinearMap.apply ℝ ℝ I).contDiff.comp hLf).neg
    · exact (ContinuousLinearMap.apply ℝ ℝ (1 : ℂ)).contDiff.comp hLf
    · exact ((Real.contDiff_exp.comp hL).sub contDiff_const).mul (href_cd 2)
    · exact ((Real.contDiff_exp.comp hL).sub contDiff_const).mul (href_cd 3)
  have hg_eq (z : ℂ) (hz : R + 2 < ‖z‖) (i : Fin 4) :
      x z i - referenceField f m z i = g i z := by
    have hzR : R < ‖z‖ := by linarith
    have hrOut : f.rOut ≤ ‖z‖ ^ 2 := rOut_le_norm_sq f ((le_max_right _ _).trans_lt hzR)
    have hnhds_phase : ∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * windingPhase m w :=
      Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hzR)
        fun w hw ↦ (hR₀ ((le_max_left _ _).trans hw.le)).1
    have hgt : 1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) := (hR₀ ((le_max_left _ _).trans hzR.le)).2
    have hα : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0 := by intro h0; rw [h0, mul_zero] at hgt; norm_num at hgt
    have hL_nhds : L =ᶠ[𝓝 z] fun w ↦ (1 / 2) * Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)) :=
      Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hz) hL_eq
    have hfderiv_L : fderiv ℝ L z =
        (1 / 2 : ℝ) • fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z := by
      rw [hL_nhds.fderiv_eq]
      exact fderiv_const_mul ((contDiff_const.mul ((hp.pow 2).add (hq.pow 2))).contDiffAt.log
        (mul_ne_zero four_ne_zero hα) |>.differentiableAt (by simp)) (1 / 2)
    obtain ⟨h0, h1, h2, h3⟩ := sub_referenceField_eq_of_sectionValue_eq_mul_windingPhase f hrOut
      (hp.contDiffAt.of_le (by simp)) (hq.contDiffAt.of_le (by simp)) hα
      (Eventually.of_forall hsol) hnhds_phase
    fin_cases i
    · dsimp [g]; rw [h0, hfderiv_L]; simp only [smul_apply, smul_eq_mul]; ring
    · dsimp [g]; rw [h1, hfderiv_L]; simp only [smul_apply, smul_eq_mul]
    · dsimp [g]; rw [h2, hL_nhds.eq_of_nhds]; ring_nf
    · dsimp [g]; rw [h3, hL_nhds.eq_of_nhds]; ring_nf
  refine ⟨R + 2, g, hg_cd, hg_eq, fun {c} hc i n ↦ ?_⟩
  have hexp := isBigO_iteratedFDeriv_exp_sub_one_of_isBigO hL hL₀
    (fun j ↦ by simpa using hL_decay (by norm_num : (0 : ℝ) < 1 / 2) j) (hL_decay hc)
  have href_bdd (k : Fin 4) (j : ℕ) :
      iteratedFDeriv ℝ j (fun z ↦ referenceField f m z k) =O[cocompact ℂ] fun _ ↦ (1 : ℝ) := by
    obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_referenceField_apply_le f m k j
    exact IsBigO.of_bound (max C 0) (Eventually.of_forall fun z ↦ by
      simpa using (hC z).trans (le_max_left C 0))
  have hmul (k : Fin 4) :
      iteratedFDeriv ℝ n (fun z ↦ (Real.exp (L z) - 1) * referenceField f m z k) =O[cocompact ℂ]
        fun z ↦ Real.exp (-(c * ‖z‖)) := by
    have hB := (ContinuousLinearMap.mul ℝ ℝ).isBigO_iteratedFDeriv_of_bilinear (n := n)
      ((Real.contDiff_exp.comp hL).sub contDiff_const) (href_cd k) (mod_cast le_top)
      (fun j _ ↦ hexp j) (fun j _ ↦ href_bdd k j)
    simpa only [ContinuousLinearMap.mul_apply', Function.comp_apply, mul_one] using hB
  have hfderiv (v : ℂ) :
      iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ L z v) =O[cocompact ℂ]
        fun z ↦ Real.exp (-(c * ‖z‖)) := by
    let ev : (ℂ →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
    refine isBigO_norm_left.1 ((isBigO_of_le _ fun z ↦ ?_).trans
      ((hL_decay hc (n + 1)).norm_left.const_mul_left ‖ev‖))
    rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg (by positivity)]
    calc ‖iteratedFDeriv ℝ n (fun w ↦ ev (fderiv ℝ L w)) z‖
        ≤ ‖ev‖ * ‖iteratedFDeriv ℝ n (fderiv ℝ L) z‖ :=
          ev.norm_iteratedFDeriv_comp_left hLf.contDiffAt (mod_cast le_top)
      _ = ‖ev‖ * ‖iteratedFDeriv ℝ (n + 1) L z‖ := by rw [norm_iteratedFDeriv_fderiv]
  fin_cases i
  · dsimp [g]
    have hneg : iteratedFDeriv ℝ n (fun z ↦ -fderiv ℝ L z I) =
        -iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ L z I) :=
      funext fun z ↦ iteratedFDeriv_neg_apply
    rw [hneg]
    exact (hfderiv I).neg_left
  · exact hfderiv 1
  · exact hmul 2
  · exact hmul 3

/-! ### Exponential decay of all derivatives of an end-normalized vortex -/

/-- **Coordinate derivative decay for an end-normalized vortex.** Let `x` be a plane vortex with
smooth section, `|α| → 1` at infinity, and section equal to `|α|` times `windingPhase m` outside a
compact set. Then for every cutoff `f`, every rate `c < 1 / 2`, every coordinate `i`, and every
order `n`, `Dⁿ(xᵢ - (x_ref)ᵢ) = O(exp (-c |z|))` at infinity. No global regularity assumption on
the connection components of `x` is needed. -/
theorem isBigO_iteratedFDeriv_sub_referenceField_apply
    (hp : ContDiff ℝ ∞ (fun w ↦ x w 2)) (hq : ContDiff ℝ ∞ (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) {c : ℝ} (hc : c < 1 / 2) (i : Fin 4) (n : ℕ) :
    iteratedFDeriv ℝ n (fun z ↦ x z i - referenceField f m z i) =O[cocompact ℂ]
      fun z ↦ Real.exp (-(c * ‖z‖)) := by
  obtain ⟨R, g, -, hg_eq, hg_decay⟩ :=
    exists_contDiff_sub_referenceField_eq_and_isBigO hp hq hsol hlim hphase f
  refine (EventuallyEq.isBigO ?_).trans (hg_decay hc i n)
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop R] with z hz
  have hnhds : (fun w ↦ x w i - referenceField f m w i) =ᶠ[𝓝 z] g i :=
    Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
      fun w hw ↦ hg_eq w hw i
  exact (hnhds.iteratedFDeriv ℝ n).eq_of_nhds

/-- **Derivative decay of an end-normalized vortex.** Let `x` be a plane vortex with smooth
section, `|α| → 1` at infinity, and section equal to `|α|` times `windingPhase m` outside a compact
set. Then for every cutoff `f`, every rate `c < 1 / 2`, and every order `n`,
`Dⁿ(x - referenceField f m) = O(exp (-c |z|))` at infinity. -/
theorem isBigO_iteratedFDeriv_sub_referenceField
    (hp : ContDiff ℝ ∞ (fun w ↦ x w 2)) (hq : ContDiff ℝ ∞ (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) {c : ℝ} (hc : c < 1 / 2) (n : ℕ) :
    iteratedFDeriv ℝ n (x - referenceField f m) =O[cocompact ℂ]
      fun z ↦ Real.exp (-(c * ‖z‖)) := by
  obtain ⟨R, g, hg_cd, hg_eq, hg_decay⟩ :=
    exists_contDiff_sub_referenceField_eq_and_isBigO hp hq hsol hlim hphase f
  let e (i : Fin 4) : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    (1 : ℝ →L[ℝ] ℝ).smulRight (EuclideanSpace.single i 1)
  let G : ℂ → EuclideanSpace ℝ (Fin 4) := fun z ↦ ∑ i : Fin 4, e i (g i z)
  have hG_decay : iteratedFDeriv ℝ n G =O[cocompact ℂ] fun z ↦ Real.exp (-(c * ‖z‖)) := by
    have hsum_eq : iteratedFDeriv ℝ n G =
        fun z ↦ ∑ i : Fin 4, iteratedFDeriv ℝ n (fun w ↦ e i (g i w)) z :=
      funext fun z ↦ iteratedFDeriv_fun_sum_apply fun i _ ↦
        ((e i).contDiff.comp (hg_cd i)).contDiffAt.of_le (mod_cast le_top)
    rw [hsum_eq]
    refine IsBigO.fun_sum fun i _ ↦ isBigO_norm_left.1 ((isBigO_of_le _ fun z ↦ ?_).trans
      ((hg_decay hc i n).norm_left.const_mul_left ‖e i‖))
    rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg (by positivity)]
    exact (e i).norm_iteratedFDeriv_comp_left (hg_cd i).contDiffAt (mod_cast le_top)
  refine (EventuallyEq.isBigO ?_).trans hG_decay
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop R] with z hz
  have hnhds : x - referenceField f m =ᶠ[𝓝 z] G := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    ext j
    simp [G, e, Finset.sum_apply, Pi.single_apply, hg_eq w hw j]
  exact (hnhds.iteratedFDeriv ℝ n).eq_of_nhds

/-- **Global exponential decay of all derivatives of a smooth end-normalized vortex.** For a smooth
plane vortex with `|α| → 1` at infinity whose section equals `|α|` times `windingPhase m` outside a
compact set, every iterated derivative of `x - referenceField f m` decays at every rate
`c < 1 / 2`: `‖Dⁿ(x - referenceField f m)(z)‖ ≤ K exp (-c |z|)`. -/
theorem exists_norm_iteratedFDeriv_sub_referenceField_le_mul_exp (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) {c : ℝ} (hc : c < 1 / 2) (n : ℕ) :
    ∃ K, ∀ z, ‖iteratedFDeriv ℝ n (x - referenceField f m) z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K, hK⟩ := (isBigO_iteratedFDeriv_sub_referenceField
    (contDiff_euclidean.1 hx 2) (contDiff_euclidean.1 hx 3) hsol hlim hphase f hc n).bound
  have hcont : Continuous fun z ↦ ‖iteratedFDeriv ℝ n (x - referenceField f m) z‖ :=
    ((hx.sub (contDiff_referenceField f m)).continuous_iteratedFDeriv (mod_cast le_top)).norm
  refine exists_forall_le_mul_exp_of_eventually_le hcont (K := K) ?_
  filter_upwards [hK] with z hz
  simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hz

/-- **Sobolev membership of a smooth end-normalized vortex.** A smooth plane vortex with `|α| → 1`
at infinity whose section equals `|α|` times `windingPhase m` outside a compact set lies in the
affine Sobolev field space `framedFieldSpace f m s` for every cutoff `f` and real order `s`. -/
theorem mem_framedFieldSpace_of_sectionValue_eq_mul_windingPhase (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) (s : ℝ) :
    x ∈ framedFieldSpace f m s := by
  rw [mem_framedFieldSpace, mem_sobolevFields]
  intro i
  have hcoord : ContDiff ℝ ∞ fun z ↦ (x - referenceField f m) z i :=
    (contDiff_euclidean.1 hx i).sub (contDiff_euclidean.1 (contDiff_referenceField f m) i)
  exact TemperedDistribution.mem_realSobolevFunctions_of_isBigO_iteratedFDeriv_exp hcoord
    (c := 1 / 4) (by norm_num)
    (isBigO_iteratedFDeriv_sub_referenceField_apply (contDiff_euclidean.1 hx 2)
      (contDiff_euclidean.1 hx 3) hsol hlim hphase f (by norm_num) i) s

/-! ### Smooth framed gauge representatives in `A_m^s` -/

private theorem exists_framedGaugeGroup_contDiff_equation_tendsto
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∃ u : framedGaugeGroup, ContDiff ℝ ∞ (u • x) ∧ (∀ z, equation (u • x) z = 0) ∧
      Tendsto (fun z ↦ 4 * ((u • x) z 2 ^ 2 + (u • x) z 3 ^ 2)) (cocompact ℂ) (𝓝 1) ∧
      ∀ᶠ z in cocompact ℂ,
        sectionValue (u • x) z = ‖sectionValue (u • x) z‖ * windingPhase m z := by
  obtain ⟨u, hu⟩ := exists_framedGaugeGroup_sectionValue_smul_eq hx hframe
  have huc := ((mem_framedGaugeGroup _).1 u.property).1
  have hy : ContDiff ℝ ∞ (u • x) := contDiff_gaugeTransform (by simpa using huc) hx
  have hsol' (z : ℂ) : equation (u • x) z = 0 :=
    (equation_gaugeTransform_eq_zero_iff ((huc.of_le (by norm_cast)).contDiffAt)
      fun i ↦ (contDiff_euclidean.1 hx i).differentiable (by simp) z).2 (hsol z)
  have hlim : Tendsto (fun z ↦ 4 * ((u • x) z 2 ^ 2 + (u • x) z 3 ^ 2)) (cocompact ℂ) (𝓝 1) := by
    refine (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe).congr fun z ↦ ?_
    rw [← sq_norm_sectionValue, ← sq_norm_sectionValue, framedGaugeGroup_smul,
      sectionValue_gaugeTransform, norm_mul, Circle.norm_coe, one_mul]
  exact ⟨u, hy, hsol', hlim, hu⟩

/-- **Smooth framed gauge representative with all-order exponential decay.** Every smooth plane
vortex with the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1` has a smooth framed gauge transform
`u • x` whose section is `|α|` times `windingPhase m` outside a compact set and whose difference
from `referenceField f m` has all iterated derivatives globally bounded by multiples of
`exp (-c |z|)` for every cutoff `f` and every rate `c < 1 / 2`. -/
theorem exists_framedGaugeGroup_norm_iteratedFDeriv_smul_sub_referenceField_le_mul_exp
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∃ u : framedGaugeGroup,
      (∀ᶠ z in cocompact ℂ,
        sectionValue (u • x) z = ‖sectionValue (u • x) z‖ * windingPhase m z) ∧
      ∀ (f : ContDiffBump (0 : ℝ)), ∀ c < 1 / 2, ∀ n : ℕ, ∃ K, ∀ z,
        ‖iteratedFDeriv ℝ n (u • x - referenceField f m) z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨u, hy, hsol', hlim, hu⟩ :=
    exists_framedGaugeGroup_contDiff_equation_tendsto hx hsol hframe
  exact ⟨u, hu, fun f _ hc n ↦
    exists_norm_iteratedFDeriv_sub_referenceField_le_mul_exp hy hsol' hlim hu f hc n⟩

/-- **Smooth framed gauge representative in the affine Sobolev field space.** Every smooth plane
vortex with the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1` has a smooth framed gauge transform
`u • x` whose section is `|α|` times `windingPhase m` outside a compact set and which belongs to
`framedFieldSpace f m s` for every cutoff `f` and every real order `s`. -/
theorem exists_framedGaugeGroup_smul_mem_framedFieldSpace
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∃ u : framedGaugeGroup,
      (∀ᶠ z in cocompact ℂ,
        sectionValue (u • x) z = ‖sectionValue (u • x) z‖ * windingPhase m z) ∧
      ∀ (f : ContDiffBump (0 : ℝ)) (s : ℝ), u • x ∈ framedFieldSpace f m s := by
  obtain ⟨u, hy, hsol', hlim, hu⟩ :=
    exists_framedGaugeGroup_contDiff_equation_tendsto hx hsol hframe
  exact ⟨u, hu, fun f s ↦
    mem_framedFieldSpace_of_sectionValue_eq_mul_windingPhase hy hsol' hlim hu f s⟩

end TauCeti.Vortex
