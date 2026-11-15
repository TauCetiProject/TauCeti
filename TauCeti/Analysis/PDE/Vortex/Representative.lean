/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.WindingPhase
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Sobolev.BesselPotential.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv
import TauCeti.Analysis.SpecialFunctions.Exp.Shift
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Smooth framed vortices in the affine Sobolev field space

The analytic theory of framed degree-`m` plane vortices takes place in the affine space
`A_m^s = x_ref + H^s` (`TauCeti.Vortex.framedFieldSpace`), centred at a smooth reference field
`x_ref` equal to `(-i m dθ, (z / |z|)^m)` outside a disc. This file shows that every smooth framed
vortex is represented there: its smooth framed gauge orbit meets `A_m^s` for every `s`
(`TauCeti.Vortex.exists_framedGaugeGroup_smul_mem_framedFieldSpace`). Since two fields of
`A_m^k` related by a smooth gauge are related by an element of the Sobolev gauge group `G_(k+1)`
(`TauCeti.Vortex.mem_sobolevGaugeGroup_of_mem_framedFieldSpace`), smooth framed vortex orbits and
vortex orbits of `G_(k+1)` in `A_m^k` correspond.

The representative is the one normalized at its end: a vortex whose section is `|α|` times the
winding phase `(z / |z|)^m` outside a compact set, which every smooth framed vortex is equivalent
to (`TauCeti.Vortex.exists_framedGaugeGroup_sectionValue_smul_eq`). For such a vortex `x`, every
derivative of every coordinate of `x - x_ref` decays like `exp (-c |z|)` for every `c < 1 / 2`
(`TauCeti.Vortex.isBigO_iteratedFDeriv_sub_referenceField_apply`). Outside a disc, with
`ℓ = log |α|²`,

* the connection coordinates of `x - x_ref` are `(-(1 / 2) ∂_t ℓ, (1 / 2) ∂_s ℓ)`
  (`TauCeti.Vortex.sub_referenceField_apply_zero_of_equation_eq_zero`), and
* its section is `(|α| - 1) (z / |z|)^m = (exp (ℓ / 2) - 1) α_ref`, with `α_ref` the reference
  section, whose derivatives are bounded.

Every derivative of `ℓ` decays at these rates (`TauCeti.Vortex.isBigO_iteratedFDeriv_log_normSq`),
hence so does every derivative of `exp (ℓ / 2) - 1`
(`ContDiff.isBigO_iteratedFDeriv_exp_sub_one`). The exponential `exp (-c |z|)` lies in `L²` for
`c > 0`, so a smooth end-normalized vortex lies in `A_m^s` for every `s`
(`TauCeti.Vortex.mem_framedFieldSpace_of_sectionValue_eq_norm_mul_windingPhase`), by
`TemperedDistribution.mem_realSobolevFunctions_natCast_of_contDiff`.

## Main results

* `TauCeti.Vortex.isBigO_iteratedFDeriv_sub_referenceField_apply`: the derivatives of
  `x - x_ref` decay exponentially at infinity, for a vortex normalized at its end.
* `TauCeti.Vortex.exists_norm_iteratedFDeriv_sub_referenceField_apply_le_mul_exp`: for a smooth
  such vortex, the bound `‖Dⁿ (x - x_ref)ᵢ (z)‖ ≤ K exp (-c |z|)` holds on the whole plane.
* `TauCeti.Vortex.mem_framedFieldSpace_of_sectionValue_eq_norm_mul_windingPhase`: a smooth such
  vortex lies in `A_m^s` for every `s`.
* `TauCeti.Vortex.exists_framedGaugeGroup_smul_mem_framedFieldSpace`: every smooth framed vortex
  has a smooth framed gauge representative, normalized at its end, lying in `A_m^s` for every `s`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Asymptotics Complex Filter Metric
open scoped Topology ContDiff

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {m : ℕ}

/-- **A global smooth half log-modulus.** For a vortex normalized at its end with `|α| → 1`, there
are a radius `R ≥ max 1 rOut`, beyond which the section is `|α|` times the winding phase and
`|α|² ≥ 1 / 4`, and a smooth function `ψ` on the plane equal to `(1 / 2) log |α|²` beyond `R`. -/
private theorem exists_contDiff_eq_half_log_normSq
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) :
    ∃ (ψ : ℂ → ℝ) (R : ℝ), ContDiff ℝ ∞ ψ ∧ max 1 f.rOut ≤ R ∧
      (∀ w : ℂ, R < ‖w‖ → sectionValue x w = ‖sectionValue x w‖ * windingPhase m w) ∧
      (∀ w : ℂ, R < ‖w‖ → 1 / 4 ≤ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) ∧
      ∀ w : ℂ, R < ‖w‖ → ψ w = Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)) / 2 := by
  set ℓ : ℂ → ℝ := fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))
  obtain ⟨R₁, -, hR₁⟩ :=
    hasBasis_cobounded_norm.eventually_iff.mp (cobounded_eq_cocompact (α := ℂ) ▸ hphase)
  obtain ⟨R₂, -, hR₂⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := ℂ) ▸
      hlim.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) / 4 < 1)))
  set R₀ := max (max R₁ R₂) 0
  have hR₀ : 0 ≤ R₀ := le_max_right _ _
  -- Beyond `R₀`, `ℓ` is smooth.
  have hℓ : ∀ w : ℂ, R₀ < ‖w‖ → ContDiffAt ℝ ∞ ℓ w := fun w hw ↦ by
    refine contDiffAt_log_normSq_of_equation_eq_zero hp.contDiffAt hq.contDiffAt (fun h ↦ ?_)
      (.of_forall hsol)
    have := hR₂ (((le_max_right R₁ R₂).trans (le_max_left _ _)).trans hw.le)
    simp only [h, mul_zero] at this
    norm_num at this
  -- A bump equal to one up to radius `R₀ + 1` cuts `ℓ` off near the origin.
  let β : ContDiffBump (0 : ℂ) := ⟨R₀ + 1, R₀ + 2, by linarith, by linarith⟩
  refine ⟨fun w ↦ (1 - β w) * ℓ w / 2, max (R₀ + 2) (max 1 f.rOut), ?_, le_max_right _ _,
    fun w hw ↦ hR₁ ?_, fun w hw ↦ (hR₂ ?_).le, fun w hw ↦ ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
    by_cases hz : R₀ < ‖z‖
    · exact ((contDiffAt_const.sub β.contDiff.contDiffAt).mul (hℓ z hz)).div_const 2
    · -- Near `z`, the bump is one and the function vanishes.
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds
        (show ‖z‖ < R₀ + 1 by linarith)] with w hw
      rw [β.one_of_mem_closedBall (by simpa using hw.le)]
      ring
  · exact ((le_max_left R₁ R₂).trans (le_max_left _ _)).trans
      ((by linarith : R₀ ≤ R₀ + 2).trans ((le_max_left _ _).trans hw.le))
  · exact ((le_max_right R₁ R₂).trans (le_max_left _ _)).trans
      ((by linarith : R₀ ≤ R₀ + 2).trans ((le_max_left _ _).trans hw.le))
  · dsimp only
    rw [β.zero_of_le_dist (by simpa using (le_max_left _ _).trans hw.le)]
    ring

/-- The derivatives of `w ↦ (exp ψ(w) - 1) L(α_ref(w))` are `O(ρ)` when `ρ → 0` and those of `ψ`
are `O(ρ)`, for a real-linear map `L : ℂ → ℝ`. -/
private theorem isBigO_iteratedFDeriv_exp_sub_one_mul_referenceSection {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) {ρ : ℂ → ℝ} (hρ : Tendsto ρ (cocompact ℂ) (𝓝 0))
    (hψn : ∀ n, iteratedFDeriv ℝ n ψ =O[cocompact ℂ] ρ) (f : ContDiffBump (0 : ℝ)) (m : ℕ)
    (L : ℂ →L[ℝ] ℝ) (n : ℕ) :
    iteratedFDeriv ℝ n (fun w ↦ (Real.exp (ψ w) - 1) * L (referenceSection f m w))
      =O[cocompact ℂ] ρ := by
  have hr := contDiff_referenceSection f m
  have hL : ∀ i ≤ n, iteratedFDeriv ℝ i (fun w ↦ L (referenceSection f m w)) =O[cocompact ℂ]
      fun _ ↦ (1 : ℝ) := fun i _ ↦ by
    obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_referenceSection_le f m i
    refine IsBigO.of_bound (‖L‖ * C) (.of_forall fun w ↦ ?_)
    rw [norm_one, mul_one]
    exact (L.norm_iteratedFDeriv_comp_left (hr.contDiffAt (x := w)) (n := i)
      (by exact_mod_cast le_top)).trans (mul_le_mul_of_nonneg_left (hC w) (norm_nonneg L))
  have h := (ContinuousLinearMap.mul ℝ ℝ).isBigO_iteratedFDeriv_of_bilinear
    ((Real.contDiff_exp.comp hψ).sub contDiff_const) (L.contDiff.comp hr) (n := n)
    (by exact_mod_cast le_top)
    (fun i _ ↦ (hψ.of_le (by exact_mod_cast le_top)).isBigO_iteratedFDeriv_exp_sub_one
      (hρ.isBigO_one ℝ)
      fun j _ ↦ hψn j) hL
  simpa only [ContinuousLinearMap.mul_apply', Function.comp_apply, mul_one] using h

/-- Beyond a radius `R` outside which `|α|² ≥ 1 / 4` and `ψ = (1 / 2) log |α|²`, the function `ψ`
agrees near each point with `(1 / 2) log |α|²`, which is smooth there. -/
private theorem eventuallyEq_half_log_normSq_and_contDiffAt
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0) {ψ : ℂ → ℝ} {R : ℝ}
    (hqR : ∀ w : ℂ, R < ‖w‖ → 1 / 4 ≤ 4 * (x w 2 ^ 2 + x w 3 ^ 2))
    (hψR : ∀ w : ℂ, R < ‖w‖ → ψ w = Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)) / 2) {z : ℂ}
    (hz : R < ‖z‖) :
    ψ =ᶠ[𝓝 z] (2⁻¹ : ℝ) • (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) ∧
      ContDiffAt ℝ ∞ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z :=
  ⟨eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hz) fun w hw ↦ by
      simp [hψR w hw, div_eq_inv_mul],
    contDiffAt_log_normSq_of_equation_eq_zero hp.contDiffAt hq.contDiffAt
      (fun h ↦ by linarith [hqR z hz, h]) (.of_forall hsol)⟩

/-- The section of `x - x_ref` is `(exp ψ - 1) α_ref` beyond a radius `R ≥ max 1 rOut` outside
which the section of `x` is `|α|` times the winding phase, `|α|² ≥ 1 / 4`, and
`ψ = (1 / 2) log |α|²`. -/
private theorem sectionValue_sub_referenceField_eq_exp_sub_one_mul (f : ContDiffBump (0 : ℝ))
    {ψ : ℂ → ℝ} {R : ℝ} (hR : max 1 f.rOut ≤ R)
    (hphR : ∀ w : ℂ, R < ‖w‖ → sectionValue x w = ‖sectionValue x w‖ * windingPhase m w)
    (hqR : ∀ w : ℂ, R < ‖w‖ → 1 / 4 ≤ 4 * (x w 2 ^ 2 + x w 3 ^ 2))
    (hψR : ∀ w : ℂ, R < ‖w‖ → ψ w = Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)) / 2) {w : ℂ}
    (hw : R < ‖w‖) :
    sectionValue (x - referenceField f m) w =
      ((Real.exp (ψ w) - 1 : ℝ) : ℂ) * referenceSection f m w := by
  have hw₀ : w ≠ 0 :=
    norm_pos_iff.mp ((zero_lt_one.trans_le ((le_max_left _ _).trans hR)).trans hw)
  -- The modulus `|α|` is `exp ψ`.
  have hnorm : ‖sectionValue x w‖ = Real.exp (ψ w) := by
    refine (sq_eq_sq₀ (norm_nonneg _) (Real.exp_pos _).le).1 ?_
    rw [sq_norm_sectionValue, pow_two (Real.exp (ψ w)), ← Real.exp_add, hψR w hw, add_halves,
      Real.exp_log (by linarith [hqR w hw])]
  rw [sectionValue_sub, sectionValue_referenceField, hphR w hw, hnorm, coe_windingPhase m hw₀,
    ← referenceSection_eq_phase f m (rOut_le_norm_sq f (hR.trans_lt hw))]
  push_cast
  ring

/-- **The coordinates of an end-normalized vortex near infinity.** Beyond a radius
`R ≥ max 1 rOut` outside which the section of `x` is `|α|` times the winding phase,
`|α|² ≥ 1 / 4`, and `ψ = (1 / 2) log |α|²`, the coordinates of `x - x_ref` are
`(-∂_t ψ, ∂_s ψ, (exp ψ - 1) Re α_ref / 2, (exp ψ - 1) Im α_ref / 2)`. -/
private theorem sub_referenceField_apply_eq_of_eq_half_log_normSq
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0) (f : ContDiffBump (0 : ℝ)) {ψ : ℂ → ℝ} {R : ℝ}
    (hR : max 1 f.rOut ≤ R)
    (hphR : ∀ w : ℂ, R < ‖w‖ → sectionValue x w = ‖sectionValue x w‖ * windingPhase m w)
    (hqR : ∀ w : ℂ, R < ‖w‖ → 1 / 4 ≤ 4 * (x w 2 ^ 2 + x w 3 ^ 2))
    (hψR : ∀ w : ℂ, R < ‖w‖ → ψ w = Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)) / 2) {w : ℂ}
    (hw : R < ‖w‖) :
    (x - referenceField f m) w 0 = fderiv ℝ ψ w (-I) ∧
      (x - referenceField f m) w 1 = fderiv ℝ ψ w 1 ∧
      (x - referenceField f m) w 2 =
        (Real.exp (ψ w) - 1) * ((2⁻¹ : ℝ) • reCLM) (referenceSection f m w) ∧
      (x - referenceField f m) w 3 =
        (Real.exp (ψ w) - 1) * ((2⁻¹ : ℝ) • imCLM) (referenceSection f m w) := by
  have hσ : sectionValue x w ≠ 0 := fun h ↦ by
    have := sq_norm_sectionValue x w
    rw [h, norm_zero] at this
    linarith [hqR w hw]
  have hphN : ∀ᶠ v in 𝓝 w, sectionValue x v = ‖sectionValue x v‖ * windingPhase m v :=
    eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hw) fun v hv ↦
      hphR v hv
  have hrOut : f.rOut ≤ ‖w‖ ^ 2 := rOut_le_norm_sq f (hR.trans_lt hw)
  have hpw := hp.differentiable (by norm_num) w
  have hqw := hq.differentiable (by norm_num) w
  -- The derivative of `ψ` is half that of `log |α|²`.
  obtain ⟨hψℓ, hℓ⟩ := eventuallyEq_half_log_normSq_and_contDiffAt hp hq hsol hqR hψR hw
  have hfd := hψℓ.fderiv_eq.trans (fderiv_const_smul (hℓ.differentiableAt (by simp)) _)
  have hsec := sectionValue_sub_referenceField_eq_exp_sub_one_mul f hR hphR hqR hψR hw
  have h₂ : sectionValue (x - referenceField f m) w = 2 * ((x - referenceField f m) w 2 : ℂ) +
      2 * ((x - referenceField f m) w 3 : ℂ) * I := by
    rw [sectionValue_apply]
    ring
  rw [hsec] at h₂
  have hre := congrArg re h₂
  have him := congrArg im h₂
  simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im,
    I_re, I_im, re_ofNat, im_ofNat] at hre him
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sub_referenceField_apply_zero_of_equation_eq_zero f hrOut hpw hqw (by simp [hsol w])
      (by simp [hsol w]) hphN hσ, hfd, map_neg]
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  · rw [sub_referenceField_apply_one_of_equation_eq_zero f hrOut hpw hqw (by simp [hsol w])
      (by simp [hsol w]) hphN hσ, hfd]
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [FunLike.coe_smul, Pi.smul_apply, reCLM_apply, smul_eq_mul]
    linarith
  · simp only [FunLike.coe_smul, Pi.smul_apply, imCLM_apply, smul_eq_mul]
    linarith

/-- **Exponential decay of all derivatives of an end-normalized vortex.** Let `x` be a plane
vortex with `C²` section and `|α| → 1` at infinity whose section is `|α|` times the winding phase
`(z / |z|)^m` outside a compact set. Then for every `c < 1 / 2`, every iterated derivative of
every coordinate of `x - x_ref` is `O(exp (-c |z|))` at infinity. -/
theorem isBigO_iteratedFDeriv_sub_referenceField_apply
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) {c : ℝ} (hc : c < 1 / 2) (i : Fin 4) (n : ℕ) :
    iteratedFDeriv ℝ n (fun z ↦ (x - referenceField f m) z i) =O[cocompact ℂ]
      fun z ↦ Real.exp (-(c * ‖z‖)) := by
  -- It suffices to treat a positive rate `c' ≥ c`.
  set c' := max c (1 / 4)
  have hc'pos : 0 < c' := lt_max_of_lt_right (by norm_num)
  refine IsBigO.trans ?_ (isBigO_exp_neg_mul_norm_of_le (le_max_left c (1 / 4)) _)
  set ρ : ℂ → ℝ := fun z ↦ Real.exp (-(c' * ‖z‖))
  have hρ : Tendsto ρ (cocompact ℂ) (𝓝 0) := tendsto_exp_neg_mul_norm_cocompact hc'pos
  obtain ⟨ψ, R, hψ, hR, hphR, hqR, hψR⟩ :=
    exists_contDiff_eq_half_log_normSq hp hq hsol hlim hphase f
  have hU (z : ℂ) (hz : R < ‖z‖) : ∀ᶠ w in 𝓝 z, R < ‖w‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hz
  -- Near infinity `ψ` is `(1 / 2) log |α|²`, so its derivatives decay.
  have hψn (n : ℕ) : iteratedFDeriv ℝ n ψ =O[cocompact ℂ] ρ := by
    have h := (isBigO_iteratedFDeriv_log_normSq hp hq hsol hlim (c := c')
      (max_lt hc (by norm_num)) n).const_smul_left (2⁻¹ : ℝ)
    refine h.congr' ?_ EventuallyEq.rfl
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop R] with z hz
    obtain ⟨hψℓ, hℓ⟩ := eventuallyEq_half_log_normSq_and_contDiffAt hp hq hsol hqR hψR hz
    rw [(hψℓ.iteratedFDeriv ℝ n).eq_of_nhds,
      iteratedFDeriv_const_smul_apply (hℓ.of_le (by exact_mod_cast le_top))]
    rfl
  -- Hence so do those of the directional derivatives `w ↦ Dψ(w) v`.
  have hψv (v : ℂ) (n : ℕ) : iteratedFDeriv ℝ n (fun w ↦ fderiv ℝ ψ w v) =O[cocompact ℂ] ρ := by
    refine (isBigO_of_le' (c := ‖ContinuousLinearMap.apply ℝ ℝ v‖) _ fun w ↦ ?_).trans
      (hψn (n + 1))
    rw [← norm_iteratedFDeriv_fderiv]
    exact (ContinuousLinearMap.apply ℝ ℝ v).norm_iteratedFDeriv_comp_left
      ((hψ.fderiv_right (m := ∞) le_rfl).contDiffAt (x := w)) (n := n) (by exact_mod_cast le_top)
  -- Near infinity each coordinate of `x - x_ref` is a function of `ψ` and the reference section
  -- whose derivatives decay.
  obtain ⟨g, hg, hgeq⟩ : ∃ g : ℂ → ℝ, (∀ n, iteratedFDeriv ℝ n g =O[cocompact ℂ] ρ) ∧
      ∀ w : ℂ, R < ‖w‖ → (x - referenceField f m) w i = g w := by
    have h := fun w (hw : R < ‖w‖) ↦
      sub_referenceField_apply_eq_of_eq_half_log_normSq hp hq hsol f hR hphR hqR hψR hw
    fin_cases i
    · exact ⟨_, hψv (-I), fun w hw ↦ (h w hw).1⟩
    · exact ⟨_, hψv 1, fun w hw ↦ (h w hw).2.1⟩
    · exact ⟨_, isBigO_iteratedFDeriv_exp_sub_one_mul_referenceSection hψ hρ hψn f m
        ((2⁻¹ : ℝ) • reCLM), fun w hw ↦ (h w hw).2.2.1⟩
    · exact ⟨_, isBigO_iteratedFDeriv_exp_sub_one_mul_referenceSection hψ hρ hψn f m
        ((2⁻¹ : ℝ) • imCLM), fun w hw ↦ (h w hw).2.2.2⟩
  refine (hg n).congr' ?_ EventuallyEq.rfl
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop R] with z hz
  refine (Filter.EventuallyEq.eq_of_nhds (Filter.EventuallyEq.iteratedFDeriv ℝ ?_ n)).symm
  exact (hU z hz).mono fun w hw ↦ hgeq w hw

/-- **Exponential decay of all derivatives of a smooth end-normalized vortex on the plane.** Let
`x` be a smooth plane vortex with `|α| → 1` at infinity whose section is `|α|` times the winding
phase `(z / |z|)^m` outside a compact set. Then for every `c < 1 / 2` and every order `n`, each
coordinate of `x - x_ref` satisfies `‖Dⁿ (x - x_ref)ᵢ (z)‖ ≤ K exp (-c |z|)` on the whole plane. -/
theorem exists_norm_iteratedFDeriv_sub_referenceField_apply_le_mul_exp (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) {c : ℝ} (hc : c < 1 / 2) (i : Fin 4) (n : ℕ) :
    ∃ K, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ (x - referenceField f m) z i) z‖ ≤
      K * Real.exp (-(c * ‖z‖)) := by
  have hcd (j : Fin 4) : ContDiff ℝ ∞ (fun z ↦ x z j) := contDiff_euclidean.1 hx j
  have hi : ContDiff ℝ ∞ (fun z ↦ (x - referenceField f m) z i) :=
    contDiff_euclidean.1 (hx.sub (contDiff_referenceField f m)) i
  obtain ⟨K, hK⟩ := (isBigO_iteratedFDeriv_sub_referenceField_apply ((hcd 2).of_le (by simp))
    ((hcd 3).of_le (by simp)) hsol hlim hphase f hc i n).bound
  exact exists_forall_le_mul_exp_of_eventually_le (K := K)
    (hi.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
    (hK.mono fun z hz ↦ by rwa [Real.norm_of_nonneg (Real.exp_pos _).le] at hz)

/-- **Smooth end-normalized vortices lie in every affine Sobolev space.** Let `x` be a smooth
plane vortex with `|α| → 1` at infinity whose section is `|α|` times the winding phase
`(z / |z|)^m` outside a compact set. Then `x` lies in `A_m^s = x_ref + H^s` for every `s`. -/
theorem mem_framedFieldSpace_of_sectionValue_eq_norm_mul_windingPhase (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) (s : ℝ) : x ∈ framedFieldSpace f m s := by
  refine mem_framedFieldSpace.2 (mem_sobolevFields.2 fun i ↦ ?_)
  have hi : ContDiff ℝ ∞ (fun z ↦ (x - referenceField f m) z i) :=
    contDiff_euclidean.1 (hx.sub (contDiff_referenceField f m)) i
  refine TemperedDistribution.realSobolevFunctions_mono (by norm_num) (by norm_num) (Nat.le_ceil s)
    (TemperedDistribution.mem_realSobolevFunctions_natCast_of_contDiff (by norm_num) (by norm_num)
      (hi.of_le (by exact_mod_cast le_top)) fun n _ ↦ ?_)
  -- Each derivative is bounded by a multiple of `exp (-|z| / 4)`, which lies in `L²`.
  obtain ⟨K, hK⟩ := exists_norm_iteratedFDeriv_sub_referenceField_apply_le_mul_exp hx hsol hlim
    hphase f (c := 1 / 4) (by norm_num) i n
  refine ((memLp_exp_neg_mul_norm MeasureTheory.volume (by norm_num : (0 : ℝ) < 1 / 4)
    2).const_mul K).of_le
    (hi.continuous_iteratedFDeriv (by exact_mod_cast le_top)).aestronglyMeasurable
    (.of_forall fun z ↦ (hK z).trans ?_)
  rw [Real.norm_eq_abs]
  exact le_abs_self _

/-- **Smooth framed vortices have representatives in every affine Sobolev space.** Every smooth
plane vortex with the degree-`m` end framing `α (z / |z|)^(-m) → 1` has a smooth framed gauge
transform whose section is `|α|` times the winding phase outside a compact set and which lies in
`A_m^s = x_ref + H^s` for every `s`. -/
theorem exists_framedGaugeGroup_smul_mem_framedFieldSpace (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (f : ContDiffBump (0 : ℝ)) :
    ∃ u : framedGaugeGroup,
      (∀ᶠ z in cocompact ℂ,
        sectionValue (u • x) z = ‖sectionValue (u • x) z‖ * windingPhase m z) ∧
      ∀ s : ℝ, u • x ∈ framedFieldSpace f m s := by
  obtain ⟨u, hu⟩ := exists_framedGaugeGroup_sectionValue_smul_eq hx hframe
  refine ⟨u, hu, fun s ↦ ?_⟩
  have huc := ((mem_framedGaugeGroup _).1 u.property).1
  have hy : ContDiff ℝ ∞ (u • x) := contDiff_gaugeTransform (by simpa using huc) hx
  have hsol' (z : ℂ) : equation (u • x) z = 0 :=
    (equation_gaugeTransform_eq_zero_iff ((huc.of_le (by norm_cast)).contDiffAt)
      fun i ↦ (contDiff_euclidean.1 hx i).differentiable (by simp) z).2 (hsol z)
  have hlim : Tendsto (fun z ↦ 4 * ((u • x) z 2 ^ 2 + (u • x) z 3 ^ 2)) (cocompact ℂ) (𝓝 1) := by
    refine (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe).congr fun z ↦ ?_
    rw [← sq_norm_sectionValue, ← sq_norm_sectionValue, framedGaugeGroup_smul,
      sectionValue_gaugeTransform, norm_mul, Circle.norm_coe, one_mul]
  exact mem_framedFieldSpace_of_sectionValue_eq_norm_mul_windingPhase hy hsol' hlim hu f s

end TauCeti.Vortex
