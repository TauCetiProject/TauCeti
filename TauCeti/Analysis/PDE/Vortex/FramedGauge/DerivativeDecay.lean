/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Basic
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.PDE.Vortex.DerivativeDecay
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv
import TauCeti.Analysis.SpecialFunctions.Exp.Shift

/-!
# Derivative decay of plane vortices in an end trivialization

Let `x` be a plane vortex with smooth section whose section satisfies `|α| → 1` at infinity and is
`|α|` times the winding phase `(z / |z|)^m` outside a compact set. Its winding-`m` end
trivialization `y = (z / |z|)^(-m) · x` then has the real section `|α| = exp (ℓ / 2)`, where
`ℓ = log |α|²`, and the holomorphicity rows of the vortex equation determine its connection:

`y = (-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, exp (ℓ / 2) / 2, 0)`

This holds for the gauge transformation by `u⁻¹` of any field whose section is `|α|` times a
gauge `u` (`TauCeti.Vortex.gaugeTransform_inv_apply_eq`). Every derivative of `ℓ` is
`O(exp (-c |z|))` for every rate `c < 1 / 2` (`TauCeti.Vortex.isBigO_iteratedFDeriv_log_normSq`),
and the derivatives of `exp (ℓ / 2) - 1` inherit this decay by the Leibniz rule
(`ContDiff.isBigO_iteratedFDeriv_exp_sub_one`). Hence the end-trivialized field tends to the vacuum
`(0, 1)` together with all its derivatives, at every rate `c < 1 / 2`. This upgrades the
zeroth-order convergence `TauCeti.Vortex.exists_norm_sub_referenceField_le_mul_exp`.

These are estimates for one smooth vortex; uniformity over compact families of divisors and decay
of derivatives in the divisor parameters are not treated here.

## Main results

* `TauCeti.Vortex.gaugeTransform_inv_apply_eq`: where the section is `|α|` times a gauge `u`
  and solves the holomorphicity rows, its gauge transformation by `u⁻¹` is
  `(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, exp (ℓ / 2) / 2, 0)` for `ℓ = log |α|²`.
* `TauCeti.Vortex.exists_contDiff_isBigO_eventuallyEq_gaugeTransform_inv_sub_vacuumField`: near
  infinity the end trivialization minus the vacuum agrees with a smooth field whose derivatives
  are all `O(exp (-c |z|))` for every rate `c < 1 / 2`.
* `TauCeti.Vortex.isBigO_iteratedFDeriv_gaugeTransform_inv_sub_vacuumField`: every derivative of
  the end trivialization minus the vacuum, in particular the winding end trivialization, is
  `O(exp (-c |z|))` for every rate `c < 1 / 2`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric Topology Asymptotics
open scoped ContDiff

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- **The end trivialization in terms of `ℓ = log |α|²`.** Let `x` satisfy the holomorphicity
rows of the vortex equation at a point `w` where `α ≠ 0` and its section coordinates are
differentiable. Suppose that near `w` the section of `x` is `|α|` times a gauge `u`, and
`ℓ = log |α|²`. Then the gauge transformation of `x` by `u⁻¹` has real section
`|α| = exp (ℓ / 2)`, and the holomorphicity rows determine its connection:
`(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, exp (ℓ / 2) / 2, 0)` at `w`. -/
theorem gaugeTransform_inv_apply_eq {u : ℂ → Circle} {w : ℂ}
    (hp : DifferentiableAt ℝ (fun v ↦ x v 2) w) (hq : DifferentiableAt ℝ (fun v ↦ x v 3) w)
    (hα : x w 2 ^ 2 + x w 3 ^ 2 ≠ 0) (h₁ : equation x w 1 = 0) (h₂ : equation x w 2 = 0)
    {ℓ : ℂ → ℝ} (hphase : ∀ᶠ v in 𝓝 w, sectionValue x v = ‖sectionValue x v‖ * u v)
    (hℓ : ℓ =ᶠ[𝓝 w] fun v ↦ Real.log (4 * (x v 2 ^ 2 + x v 3 ^ 2))) :
    gaugeTransform u⁻¹ x w =
      !₂[-(fderiv ℝ ℓ w I / 2), fderiv ℝ ℓ w 1 / 2, Real.exp (ℓ w / 2) / 2, 0] := by
  set y := gaugeTransform u⁻¹ x
  have hsd : DifferentiableAt ℝ (fun v ↦ 4 * (x v 2 ^ 2 + x v 3 ^ 2)) w := by fun_prop
  have hpos : ∀ᶠ v in 𝓝 w, 0 < 4 * (x v 2 ^ 2 + x v 3 ^ 2) :=
    continuousAt_const.eventually_lt hsd.continuousAt
      (mul_pos four_pos (lt_of_le_of_ne (by positivity) (Ne.symm hα)))
  have hℓd : DifferentiableAt ℝ ℓ w :=
    (hsd.log hpos.self_of_nhds.ne').congr_of_eventuallyEq hℓ
  -- Near `w` the modulus of the section is `|α| = exp (ℓ / 2)`.
  have hnorm : ∀ᶠ v in 𝓝 w, ‖sectionValue x v‖ = Real.exp (ℓ v / 2) := by
    filter_upwards [hℓ, hpos] with v hℓv hposv
    refine (pow_left_inj₀ (norm_nonneg _) (Real.exp_pos _).le two_ne_zero).1 ?_
    rw [sq_norm_sectionValue, ← Real.exp_natCast_mul, hℓv]
    push_cast
    rw [mul_div_cancel₀ _ two_ne_zero, Real.exp_log hposv]
  have hu := differentiableAt_coe_of_sectionValue_eq_norm_mul hp hq
    ((sectionValue_eq_zero_iff x w).not.2 hα) hphase
  -- Near `w` the section of `y` is the real `|α| = exp (ℓ / 2)`.
  have hsec : ∀ᶠ v in 𝓝 w, y v 2 = Real.exp (ℓ v / 2) / 2 ∧ y v 3 = 0 := by
    filter_upwards [hphase, hnorm] with v hv hnv
    simpa only [hnv, ofReal_re, ofReal_im, zero_div] using
      sectionValue_eq_iff.1 (sectionValue_gaugeTransform_inv_eq hv)
  have hy3 : (fun v ↦ y v 3) =ᶠ[𝓝 w] fun _ ↦ (0 : ℝ) := hsec.mono fun v hv ↦ hv.2
  have hpy : DifferentiableAt ℝ (fun v ↦ y v 2) w :=
    (by fun_prop : DifferentiableAt ℝ (fun v ↦ Real.exp (ℓ v / 2) / 2) w).congr_of_eventuallyEq
      (hsec.mono fun v hv ↦ hv.1)
  have hqy : DifferentiableAt ℝ (fun v ↦ y v 3) w :=
    (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq hy3
  have hαy : y w 2 ^ 2 + y w 3 ^ 2 ≠ 0 := by
    rw [hsec.self_of_nhds.1, hsec.self_of_nhds.2]
    positivity
  -- The holomorphicity rows are gauge covariant, so they also hold for `y`.
  have hrows : equation y w 1 = 0 ∧ equation y w 2 = 0 := by
    have h := equation_gaugeTransform_one_add_two_mul_I (Circle.differentiableAt_coe_inv hu) hp hq
    rw [h₁, h₂] at h
    simpa using Complex.ext_iff.1 h
  -- Since `|α|` is gauge invariant, `ℓ = log |α|²` for the section of `y` as well.
  have hℓy : ℓ =ᶠ[𝓝 w] fun v ↦ Real.log (4 * (y v 2 ^ 2 + y v 3 ^ 2)) := by
    filter_upwards [hℓ] with v hv
    rw [hv, ← sq_norm_sectionValue, ← sq_norm_sectionValue, sectionValue_gaugeTransform,
      norm_mul, Circle.norm_coe, one_mul]
  have h1 := fderiv_log_normSq_apply_one hpy hqy hαy hrows.1 hrows.2
  have hI := fderiv_log_normSq_apply_I hpy hqy hαy hrows.1 hrows.2
  rw [← hℓy.fderiv_eq, hy3.fderiv_eq, fderiv_const_apply, hsec.self_of_nhds.2] at h1 hI
  simp only [zero_apply, mul_zero, zero_mul, sub_zero, zero_div, zero_add, neg_zero] at h1 hI
  ext i
  fin_cases i <;> simp [hsec.self_of_nhds.1, hsec.self_of_nhds.2] <;> linarith

/-- Along a filter on which `ρ` is bounded, if every derivative of a smooth `ℓ` is `O(ρ)`, then so
is every derivative of `(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, (exp (ℓ / 2) - 1) / 2, 0)`: its connection
part is linear in `Dℓ` and its section part is linear in `exp (ℓ / 2) - 1`. -/
private theorem isBigO_iteratedFDeriv_endField {ℓ : ℂ → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) {l : Filter ℂ}
    {ρ : ℂ → ℝ} (hρ : ρ =O[l] fun _ ↦ (1 : ℝ)) (hdec : ∀ j, iteratedFDeriv ℝ j ℓ =O[l] ρ)
    (n : ℕ) :
    iteratedFDeriv ℝ n (fun w ↦ !₂[-(fderiv ℝ ℓ w I / 2), fderiv ℝ ℓ w 1 / 2,
      (Real.exp (ℓ w / 2) - 1) / 2, 0]) =O[l] ρ := by
  set L₁ : (ℂ →L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    (-(1 / 2 : ℝ)) • (ContinuousLinearMap.apply ℝ ℝ I).smulRight (EuclideanSpace.single 0 1) +
      (1 / 2 : ℝ) • (ContinuousLinearMap.apply ℝ ℝ 1).smulRight (EuclideanSpace.single 1 1)
  set L₂ : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single 2 (1 / 2))
  have hL : (fun w ↦ !₂[-(fderiv ℝ ℓ w I / 2), fderiv ℝ ℓ w 1 / 2,
      (Real.exp (ℓ w / 2) - 1) / 2, 0]) =
      fun w ↦ L₁ (fderiv ℝ ℓ w) + L₂ (Real.exp (ℓ w / 2) - 1) := by
    ext w i
    fin_cases i <;> simp [L₁, L₂] <;> ring
  -- The derivatives of `ℓ / 2` and hence of `exp (ℓ / 2) - 1` are `O(ρ)`.
  have hexp := ((hℓ.div_const 2).of_le (by simp)).isBigO_iteratedFDeriv_exp_sub_one (n := n) hρ
    fun j _ ↦ by simpa [div_eq_inv_mul] using ((2 : ℝ)⁻¹ • ContinuousLinearMap.id ℝ ℝ
      ).isBigO_iteratedFDeriv_comp_left hℓ (by simp) (hdec j)
  have hD : ContDiff ℝ ∞ (fderiv ℝ ℓ) := hℓ.fderiv_right (by norm_cast)
  have hE : ContDiff ℝ ∞ (fun w ↦ Real.exp (ℓ w / 2) - 1) :=
    (Real.contDiff_exp.comp (hℓ.div_const 2)).sub contDiff_const
  rw [hL]
  exact ((L₁.isBigO_iteratedFDeriv_comp_left hD (n := n) (by simp)
    ((isBigO_of_le _ fun z ↦ norm_iteratedFDeriv_fderiv.le).trans (hdec (n + 1)))).add
    (L₂.isBigO_iteratedFDeriv_comp_left hE (by simp) hexp)).congr_left fun z ↦
      (fun_iteratedFDeriv_add_apply ((L₁.contDiff.comp hD).contDiffAt.of_le (by simp))
        ((L₂.contDiff.comp hE).contDiffAt.of_le (by simp))).symm

/-- **A smooth decaying model of an end trivialization.** Let `x` be a plane vortex with smooth
section and `|α| → 1` at infinity whose section is `|α|` times a gauge `u` outside a compact set.
Then near every point outside a compact set, the end trivialization `u⁻¹ · x` minus the vacuum
agrees with one globally smooth field `g` all of whose derivatives are `O(exp (-c |z|))` for every
rate `c < 1 / 2`. Outside a compact set `g` is
`(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, (exp (ℓ / 2) - 1) / 2, 0)` for a smooth `ℓ` equal to `log |α|²`
there. -/
theorem exists_contDiff_isBigO_eventuallyEq_gaugeTransform_inv_sub_vacuumField {u : ℂ → Circle}
    (hp : ContDiff ℝ ∞ (fun z ↦ x z 2)) (hq : ContDiff ℝ ∞ (fun z ↦ x z 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * u z) :
    ∃ g : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ g ∧
      (∀ c < 1 / 2, ∀ n : ℕ, iteratedFDeriv ℝ n g =O[cocompact ℂ] fun z ↦ Real.exp (-(c * ‖z‖))) ∧
      ∀ᶠ z in cocompact ℂ, (fun w ↦ gaugeTransform u⁻¹ x w - vacuumField w) =ᶠ[𝓝 z] g := by
  have hs : ContDiff ℝ ∞ (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) :=
    contDiff_const.mul ((hp.pow 2).add (hq.pow 2))
  have hpos : ∀ᶠ z in cocompact ℂ, 1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) :=
    hlim.eventually (lt_mem_nhds (by norm_num))
  -- A smooth `ℓ` on the plane which is `log |α|²` near every point outside a compact set.
  obtain ⟨ℓ, hℓ, hagree⟩ := exists_contDiff_eventually_eventuallyEq
    (f := fun z ↦ Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)))
    (hpos.mono fun z hz ↦ hs.contDiffAt.log (by linarith))
  -- Outside a disc of radius `R` the end trivialization minus the vacuum is
  -- `(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, (exp (ℓ / 2) - 1) / 2, 0)`.
  obtain ⟨R, -, hR⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := ℂ) ▸ hagree.and (hphase.and hpos))
  have hopen : IsOpen {w : ℂ | R < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hDℓ : ContDiff ℝ ∞ (fderiv ℝ ℓ) := hℓ.fderiv_right (by norm_cast)
  refine ⟨fun w ↦ !₂[-(fderiv ℝ ℓ w I / 2), fderiv ℝ ℓ w 1 / 2, (Real.exp (ℓ w / 2) - 1) / 2, 0],
    contDiff_euclidean.2 fun i ↦ ?_, fun c hc n ↦ ?_, ?_⟩
  · fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val]
    · exact ((hDℓ.clm_apply contDiff_const).div_const 2).neg
    · exact (hDℓ.clm_apply contDiff_const).div_const 2
    · exact ((Real.contDiff_exp.comp (hℓ.div_const 2)).sub contDiff_const).div_const 2
    · exact contDiff_const
  · -- Every derivative of `ℓ` decays at the rate `max c 0`.
    set ρ : ℂ → ℝ := fun z ↦ Real.exp (-(max c 0 * ‖z‖))
    have hdec (j : ℕ) : iteratedFDeriv ℝ j ℓ =O[cocompact ℂ] ρ :=
      (isBigO_iteratedFDeriv_log_normSq (hp.of_le (by simp)) (hq.of_le (by simp)) hsol hlim
        (max_lt hc (by norm_num)) j).congr'
        (hagree.mono fun z hz ↦ (hz.iteratedFDeriv ℝ j).eq_of_nhds.symm) EventuallyEq.rfl
    have hρ : ρ =O[cocompact ℂ] fun _ ↦ (1 : ℝ) := by
      simpa only [zero_mul, neg_zero, Real.exp_zero] using
        isBigO_exp_neg_mul_norm_of_le (le_max_right c 0) (cocompact ℂ)
    exact (isBigO_iteratedFDeriv_endField hℓ hρ hdec n).trans
      (isBigO_exp_neg_mul_norm_of_le (le_max_left c 0) _)
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop R] with z hz
  filter_upwards [hopen.mem_nhds hz] with w (hw : R < ‖w‖)
  have hRw := hR hw.le
  rw [gaugeTransform_inv_apply_eq (hp.differentiable (by simp) w)
    (hq.differentiable (by simp) w) (fun h ↦ by linarith [hRw.2.2]) (by simp [hsol w])
    (by simp [hsol w])
    (eventually_of_mem (hopen.mem_nhds hw) fun v (hv : R < ‖v‖) ↦ (hR hv.le).2.1) hRw.1,
    vacuumField_apply]
  ext i
  fin_cases i
  · simp
  · simp
  · simp only [Fin.reduceFinMk, PiLp.sub_apply, Matrix.cons_val]
    ring
  · simp

/-- **Exponential decay of all derivatives in an end trivialization.** Let `x` be a plane vortex
with smooth section and `|α| → 1` at infinity whose section is `|α|` times a gauge `u` outside a
compact set; for instance `u` is the winding phase `(z / |z|)^m` (`TauCeti.Vortex.windingPhase`)
for a vortex normalized at its end. Then the end trivialization `y = u⁻¹ · x` tends to the vacuum
`(0, 1)` with all its derivatives: for every order `n` and every rate `c < 1 / 2`,
`Dⁿ (y - vacuum)` is `O(exp (-c |z|))` at infinity.

Outside a compact set the end trivialization is `(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, exp (ℓ / 2) / 2, 0)`
for `ℓ = log |α|²`, so this follows from the decay of all derivatives of `ℓ`
(`TauCeti.Vortex.exists_contDiff_isBigO_eventuallyEq_gaugeTransform_inv_sub_vacuumField`). -/
theorem isBigO_iteratedFDeriv_gaugeTransform_inv_sub_vacuumField {u : ℂ → Circle}
    (hp : ContDiff ℝ ∞ (fun z ↦ x z 2)) (hq : ContDiff ℝ ∞ (fun z ↦ x z 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * u z)
    {c : ℝ} (hc : c < 1 / 2) (n : ℕ) :
    iteratedFDeriv ℝ n (fun w ↦ gaugeTransform u⁻¹ x w - vacuumField w)
      =O[cocompact ℂ] fun z ↦ Real.exp (-(c * ‖z‖)) := by
  obtain ⟨g, -, hdec, hg⟩ :=
    exists_contDiff_isBigO_eventuallyEq_gaugeTransform_inv_sub_vacuumField hp hq hsol hlim hphase
  exact (hdec c hc n).congr' (hg.mono fun z hz ↦ (hz.iteratedFDeriv ℝ n).eq_of_nhds.symm)
    EventuallyEq.rfl

end TauCeti.Vortex
