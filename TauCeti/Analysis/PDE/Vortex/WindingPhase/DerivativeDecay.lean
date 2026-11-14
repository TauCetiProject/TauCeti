/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.WindingPhase.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv
import TauCeti.Analysis.SpecialFunctions.Exp.Shift

/-!
# Derivative decay of plane vortices in the winding end trivialization

Let `x` be a plane vortex with smooth section whose section satisfies `|α| → 1` at infinity and is
`|α|` times the winding phase `(z / |z|)^m` outside a compact set. Its winding-`m` end
trivialization `y = (z / |z|)^(-m) · x` then has the real section `|α| = exp (ℓ / 2)`, where
`ℓ = log |α|²`, and the holomorphicity rows of the vortex equation determine its connection:

`y = (-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, exp (ℓ / 2) / 2, 0)`

This holds for the gauge transformation by `u⁻¹` of any field whose section is `|α|` times a
differentiable gauge `u` (`TauCeti.Vortex.gaugeTransform_inv_apply_eq`). Every derivative of `ℓ` is
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
* `TauCeti.Vortex.isBigO_iteratedFDeriv_gaugeTransform_inv_windingPhase_sub_vacuumField`: every
  derivative of the winding end trivialization minus the vacuum is `O(exp (-c |z|))` for every
  rate `c < 1 / 2`.

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

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {m : ℕ}

/-- **The end trivialization in terms of `ℓ = log |α|²`.** Let `x` satisfy the holomorphicity
rows of the vortex equation at a point `w` where `α ≠ 0` and its section coordinates are
differentiable. Suppose that near `w` the section of `x` is `|α|` times a gauge `u` differentiable
at `w`, and `ℓ = log |α|²`. Then the gauge transformation of `x` by `u⁻¹` has real section
`|α| = exp (ℓ / 2)`, and the holomorphicity rows determine its connection:
`(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, exp (ℓ / 2) / 2, 0)` at `w`. -/
theorem gaugeTransform_inv_apply_eq {u : ℂ → Circle} {w : ℂ}
    (hu : DifferentiableAt ℝ (fun v ↦ (u v : ℂ)) w)
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
  -- Near `w` the section of `y` is `|α| = exp (ℓ / 2)`.
  have hsec : ∀ᶠ v in 𝓝 w, y v 2 = Real.exp (ℓ v / 2) / 2 ∧ y v 3 = 0 := by
    filter_upwards [hphase, hℓ, hpos] with v hv hℓv hposv
    have hs : sectionValue y v = ‖sectionValue x v‖ := sectionValue_gaugeTransform_inv_eq hv
    have hnorm : ‖sectionValue x v‖ = Real.exp (ℓ v / 2) := by
      have hsq := sq_norm_sectionValue x v
      refine (pow_left_inj₀ (norm_nonneg _) (Real.exp_pos _).le two_ne_zero).1 ?_
      rw [hsq, ← Real.exp_nat_mul, hℓv]
      push_cast
      rw [mul_div_cancel₀ _ two_ne_zero, Real.exp_log hposv]
    rw [sectionValue_apply, hnorm] at hs
    constructor
    · have := congrArg Complex.re hs
      simp only [mul_re, add_re, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat] at this
      linarith
    · have := congrArg Complex.im hs
      simp only [mul_im, add_im, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat] at this
      linarith
  have hℓd : DifferentiableAt ℝ ℓ w :=
    (hsd.log hpos.self_of_nhds.ne').congr_of_eventuallyEq hℓ
  have hy2 : (fun v ↦ y v 2) =ᶠ[𝓝 w] fun v ↦ Real.exp (ℓ v / 2) / 2 :=
    hsec.mono fun v hv ↦ hv.1
  have hy3 : (fun v ↦ y v 3) =ᶠ[𝓝 w] fun _ ↦ (0 : ℝ) := hsec.mono fun v hv ↦ hv.2
  have hpy : DifferentiableAt ℝ (fun v ↦ y v 2) w := by
    have h : DifferentiableAt ℝ (fun v ↦ Real.exp (ℓ v / 2) / 2) w := by fun_prop
    exact h.congr_of_eventuallyEq hy2
  have hqy : DifferentiableAt ℝ (fun v ↦ y v 3) w :=
    (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq hy3
  have hd3 : fderiv ℝ (fun v ↦ y v 3) w = 0 := by
    rw [hy3.fderiv_eq, fderiv_const_apply]
  have hαy : y w 2 ^ 2 + y w 3 ^ 2 ≠ 0 := by
    rw [hsec.self_of_nhds.1, hsec.self_of_nhds.2]
    positivity
  -- The holomorphicity rows say `∇_I α = i ∇_1 α`, which is preserved by the gauge `u⁻¹`.
  have hrows : equation y w 1 = 0 ∧ equation y w 2 = 0 := by
    have hu' := Circle.differentiableAt_coe_inv hu
    have hI : covariantDerivative y w I = I * covariantDerivative y w 1 := by
      rw [covariantDerivative_gaugeTransform hu' hp hq,
        covariantDerivative_gaugeTransform hu' hp hq,
        covariantDerivative_eq_mul_of_equation_eq_zero hp hq h₁ h₂ I]
      ring
    have hre := congrArg Complex.re hI
    have him := congrArg Complex.im hI
    simp only [mul_re, mul_im, I_re, I_im, zero_mul, one_mul, zero_sub, add_zero,
      covariantDerivative_re hpy hqy, covariantDerivative_im hpy hqy, one_re, one_im, mul_zero,
      mul_one, zero_add] at hre him
    rw [equation_apply_one, equation_apply_two]
    constructor <;> linarith
  -- Since `|α|` is gauge invariant, `ℓ = log |α|²` for the section of `y` as well.
  have hℓy : ℓ =ᶠ[𝓝 w] fun v ↦ Real.log (4 * (y v 2 ^ 2 + y v 3 ^ 2)) := by
    filter_upwards [hℓ] with v hv
    rw [hv, ← sq_norm_sectionValue, ← sq_norm_sectionValue, sectionValue_gaugeTransform,
      norm_mul, Circle.norm_coe, one_mul]
  have h1 := fderiv_log_normSq_apply_one hpy hqy hαy hrows.1 hrows.2
  have hI := fderiv_log_normSq_apply_I hpy hqy hαy hrows.1 hrows.2
  rw [← hℓy.fderiv_eq, hd3, hsec.self_of_nhds.2] at h1 hI
  simp only [zero_apply, mul_zero, zero_mul, sub_zero, zero_div,
    zero_add, neg_zero] at h1 hI
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    linarith
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith
  · simpa using hsec.self_of_nhds.1
  · simpa using hsec.self_of_nhds.2

/-- The `n`-th derivative of `(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, (exp (ℓ / 2) - 1) / 2, 0)` is bounded by
`‖Dⁿ⁺¹ ℓ‖ + ‖Dⁿ ((exp (ℓ / 2) - 1) / 2)‖`. -/
private theorem norm_iteratedFDeriv_endField_le {ℓ : ℂ → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) (n : ℕ)
    (z : ℂ) :
    ‖iteratedFDeriv ℝ n
        ((fun w ↦ (-(fderiv ℝ ℓ w I / 2)) • EuclideanSpace.single (0 : Fin 4) (1 : ℝ)) +
        (fun w ↦ (fderiv ℝ ℓ w 1 / 2) • EuclideanSpace.single (1 : Fin 4) (1 : ℝ)) +
        fun w ↦ ((Real.exp (ℓ w / 2) - 1) / 2) • EuclideanSpace.single (2 : Fin 4) (1 : ℝ)) z‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) ℓ z‖ +
        ‖iteratedFDeriv ℝ n (fun w ↦ (Real.exp (ℓ w / 2) - 1) / 2) z‖ := by
  have hℓ' : ContDiff ℝ ∞ (fderiv ℝ ℓ) := hℓ.fderiv_right (by norm_cast)
  -- A derivative component `a ∂_v ℓ` has `n`-th derivative at most `|a| |v| ‖Dⁿ⁺¹ ℓ‖`.
  have hcomp (v : ℂ) (a : ℝ) : ‖iteratedFDeriv ℝ n (fun w ↦ (a * fderiv ℝ ℓ w v)) z‖ ≤
      |a| * ‖v‖ * ‖iteratedFDeriv ℝ (n + 1) ℓ z‖ := by
    rw [show (fun w ↦ a * fderiv ℝ ℓ w v) = fun w ↦ a • fderiv ℝ ℓ w v from
        funext fun w ↦ (smul_eq_mul a _).symm,
      iteratedFDeriv_const_smul_apply' ((hℓ'.clm_apply contDiff_const).contDiffAt.of_le
        (by exact_mod_cast le_top)), norm_smul, Real.norm_eq_abs, mul_assoc,
      ← norm_iteratedFDeriv_fderiv]
    exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_clm_apply_const hℓ'.contDiffAt
      (by exact_mod_cast le_top)) (abs_nonneg a)
  -- The coordinate vectors have norm one.
  have hsingle (f : ℂ → ℝ) (hf : ContDiff ℝ ∞ f) (i : Fin 4) :
      ‖iteratedFDeriv ℝ n (fun w ↦ f w • EuclideanSpace.single i (1 : ℝ)) z‖ ≤
        ‖iteratedFDeriv ℝ n f z‖ := by
    refine (((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single i (1 : ℝ))
      ).norm_iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast le_top)).trans ?_
    rw [ContinuousLinearMap.norm_smulRight_apply, PiLp.norm_single, norm_one, mul_one]
    exact mul_le_of_le_one_left (norm_nonneg _) ContinuousLinearMap.norm_id_le
  have hcd₀ : ContDiff ℝ ∞ fun w ↦ -(fderiv ℝ ℓ w I / 2) :=
    ((hℓ'.clm_apply contDiff_const).div_const 2).neg
  have hcd₁ : ContDiff ℝ ∞ fun w ↦ fderiv ℝ ℓ w 1 / 2 :=
    (hℓ'.clm_apply contDiff_const).div_const 2
  have hcd₂ : ContDiff ℝ ∞ fun w ↦ (Real.exp (ℓ w / 2) - 1) / 2 :=
    ((Real.contDiff_exp.comp (hℓ.div_const 2)).sub contDiff_const).div_const 2
  set A : ℂ → EuclideanSpace ℝ (Fin 4) := fun w ↦ (-(fderiv ℝ ℓ w I / 2)) •
    EuclideanSpace.single 0 1
  set B : ℂ → EuclideanSpace ℝ (Fin 4) := fun w ↦ (fderiv ℝ ℓ w 1 / 2) •
    EuclideanSpace.single 1 1
  set C : ℂ → EuclideanSpace ℝ (Fin 4) := fun w ↦ ((Real.exp (ℓ w / 2) - 1) / 2) •
    EuclideanSpace.single 2 1
  have hA : ContDiff ℝ ∞ A := hcd₀.smul contDiff_const
  have hB : ContDiff ℝ ∞ B := hcd₁.smul contDiff_const
  have hC : ContDiff ℝ ∞ C := hcd₂.smul contDiff_const
  have hAB : ContDiff ℝ ∞ (A + B) := hA.add hB
  rw [iteratedFDeriv_add_apply (hAB.contDiffAt.of_le (by exact_mod_cast le_top))
      (hC.contDiffAt.of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_add_apply (hA.contDiffAt.of_le (by exact_mod_cast le_top))
      (hB.contDiffAt.of_le (by exact_mod_cast le_top))]
  have hA' : ‖iteratedFDeriv ℝ n A z‖ ≤ 1 / 2 * ‖iteratedFDeriv ℝ (n + 1) ℓ z‖ := by
    refine (hsingle _ hcd₀ 0).trans ?_
    rw [show (fun w ↦ -(fderiv ℝ ℓ w I / 2)) = fun w ↦ (-1 / 2) * fderiv ℝ ℓ w I from
      funext fun w ↦ by ring]
    refine (hcomp I (-1 / 2)).trans_eq ?_
    rw [norm_I]
    norm_num
  have hB' : ‖iteratedFDeriv ℝ n B z‖ ≤ 1 / 2 * ‖iteratedFDeriv ℝ (n + 1) ℓ z‖ := by
    refine (hsingle _ hcd₁ 1).trans ?_
    rw [show (fun w ↦ fderiv ℝ ℓ w 1 / 2) = fun w ↦ (1 / 2) * fderiv ℝ ℓ w 1 from
      funext fun w ↦ by ring]
    refine (hcomp 1 (1 / 2)).trans_eq ?_
    rw [norm_one]
    norm_num
  have hC' := hsingle _ hcd₂ 2
  calc _ ≤ _ := norm_add₃_le
    _ ≤ _ := by linarith


/-- **Exponential decay of all derivatives in the winding end trivialization.** Let `x` be a
plane vortex with smooth section and `|α| → 1` at infinity whose section is `|α|` times the
winding phase `(z / |z|)^m` outside a compact set. Then its winding-`m` end trivialization
`y = (z / |z|)^(-m) · x` tends to the vacuum `(0, 1)` with all its derivatives: for every order
`n` and every rate `c < 1 / 2`, `Dⁿ (y - vacuum)` is `O(exp (-c |z|))` at infinity.

Outside a compact set the end trivialization is `(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, exp (ℓ / 2) / 2, 0)`
for `ℓ = log |α|²`, so this follows from the decay of all derivatives of `ℓ`. -/
theorem isBigO_iteratedFDeriv_gaugeTransform_inv_windingPhase_sub_vacuumField
    (hp : ContDiff ℝ ∞ (fun z ↦ x z 2)) (hq : ContDiff ℝ ∞ (fun z ↦ x z 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    {c : ℝ} (hc : c < 1 / 2) (n : ℕ) :
    iteratedFDeriv ℝ n (fun w ↦ gaugeTransform (windingPhase m)⁻¹ x w - vacuumField w)
      =O[cocompact ℂ] fun z ↦ Real.exp (-(c * ‖z‖)) := by
  have hs : ContDiff ℝ ∞ (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) :=
    contDiff_const.mul ((hp.pow 2).add (hq.pow 2))
  have hpos : ∀ᶠ z in cocompact ℂ, 1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) :=
    hlim.eventually (lt_mem_nhds (by norm_num))
  -- A smooth `ℓ` on the plane which is `log |α|²` near every point outside a compact set.
  obtain ⟨ℓ, hℓ, hagree⟩ := exists_contDiff_eventually_eventuallyEq
    (f := fun z ↦ Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)))
    (hpos.mono fun z hz ↦ hs.contDiffAt.log (by linarith))
  have hℓlim : Tendsto ℓ (cocompact ℂ) (𝓝 0) := by
    have h := (Real.continuousAt_log one_ne_zero).tendsto.comp hlim
    rw [Real.log_one] at h
    exact h.congr' (hagree.mono fun z hz ↦ hz.eq_of_nhds.symm)
  -- Every derivative of `ℓ` decays at the rate `c' = max c 0`.
  set c' := max c 0
  set ρ : ℂ → ℝ := fun z ↦ Real.exp (-(c' * ‖z‖))
  have hρ : ρ =O[cocompact ℂ] fun _ ↦ (1 : ℝ) := by
    simpa only [zero_mul, neg_zero, Real.exp_zero] using
      isBigO_exp_neg_mul_norm_of_le (le_max_right c 0) (cocompact ℂ)
  have hdec (j : ℕ) : iteratedFDeriv ℝ j ℓ =O[cocompact ℂ] ρ :=
    (isBigO_iteratedFDeriv_log_normSq hp hq hsol hlim (max_lt hc (by norm_num))
      j).congr' (hagree.mono fun z hz ↦ (hz.iteratedFDeriv ℝ j).eq_of_nhds.symm)
      EventuallyEq.rfl
  -- Outside a disc of radius `R'` the end trivialization minus the vacuum is `Y`.
  obtain ⟨R, -, hR⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := ℂ) ▸ hagree.and (hphase.and hpos))
  set R' := max R 0
  set Y : ℂ → EuclideanSpace ℝ (Fin 4) :=
    (fun w ↦ (-(fderiv ℝ ℓ w I / 2)) • EuclideanSpace.single 0 1) +
      (fun w ↦ (fderiv ℝ ℓ w 1 / 2) • EuclideanSpace.single 1 1) +
      fun w ↦ ((Real.exp (ℓ w / 2) - 1) / 2) • EuclideanSpace.single 2 1
  have hopen : IsOpen {w : ℂ | R' < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hY (z : ℂ) (hz : R' < ‖z‖) :
      (fun w ↦ gaugeTransform (windingPhase m)⁻¹ x w - vacuumField w) =ᶠ[𝓝 z] Y := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    have hw' : R' < ‖w‖ := hw
    have hnhds : ∀ᶠ v in 𝓝 w, R ≤ ‖v‖ :=
      Filter.eventually_of_mem (hopen.mem_nhds hw') fun v (hv : R' < ‖v‖) ↦
        (le_max_left _ _).trans hv.le
    have hRw := hR (le_max_left R 0 |>.trans hw'.le)
    rw [gaugeTransform_inv_apply_eq
      (differentiableAt_windingPhase m (norm_pos_iff.mp ((le_max_right _ _).trans_lt hw')))
      (hp.differentiable (by simp) w) (hq.differentiable (by simp) w)
      (fun h ↦ by linarith [hRw.2.2]) (by simp [hsol w]) (by simp [hsol w])
      (hnhds.mono fun v hv ↦ (hR hv).2.1) hRw.1, vacuumField_apply]
    ext i
    fin_cases i <;> simp [Y]
    ring
  -- Halving a function halves its derivatives.
  have hhalf {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) {j : ℕ}
      (hfj : iteratedFDeriv ℝ j f =O[cocompact ℂ] ρ) :
      iteratedFDeriv ℝ j (fun w ↦ f w / 2) =O[cocompact ℂ] ρ := by
    have h2 : (fun w ↦ f w / 2) = fun w ↦ (1 / 2 : ℝ) • f w :=
      funext fun w ↦ by rw [smul_eq_mul]; ring
    rw [h2]
    exact (hfj.const_smul_left (1 / 2 : ℝ)).congr_left fun w ↦
      (iteratedFDeriv_const_smul_apply' (hf.contDiffAt.of_le (by simp))).symm
  -- The derivatives of `(exp (ℓ / 2) - 1) / 2` decay by the Leibniz rule.
  have hexp : iteratedFDeriv ℝ n (fun w ↦ (Real.exp (ℓ w / 2) - 1) / 2) =O[cocompact ℂ] ρ :=
    hhalf ((Real.contDiff_exp.comp (hℓ.div_const 2)).sub contDiff_const)
      (((hℓ.div_const 2).of_le (by simp)).isBigO_iteratedFDeriv_exp_sub_one
        (by simpa using hℓlim.div_const 2) hρ fun i _ ↦ hhalf hℓ (hdec i))
  have hYdec : iteratedFDeriv ℝ n Y =O[cocompact ℂ] ρ := by
    refine (IsBigO.of_bound 1 (Eventually.of_forall fun z ↦ ?_)).trans
      ((hdec (n + 1)).norm_left.add hexp.norm_left)
    rw [one_mul, Real.norm_of_nonneg (by positivity)]
    exact norm_iteratedFDeriv_endField_le hℓ n z
  refine (hYdec.congr' ?_ EventuallyEq.rfl).trans
    (isBigO_exp_neg_mul_norm_of_le (le_max_left c 0) _)
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop R'] with z hz
  exact ((hY z hz).iteratedFDeriv ℝ n).eq_of_nhds.symm

end TauCeti.Vortex
