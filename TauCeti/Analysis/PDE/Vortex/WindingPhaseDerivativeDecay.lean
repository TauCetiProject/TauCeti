/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.WindingPhase
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv
import TauCeti.Analysis.SpecialFunctions.Exp.Limits
import TauCeti.Analysis.SpecialFunctions.Exp.Shift

/-!
# Derivative decay of plane vortices in the winding end trivialization

Let `x` be a smooth plane vortex whose section satisfies `|α| → 1` at infinity and is `|α|` times
the winding phase `(z / |z|)^m` outside a compact set. Its winding-`m` end trivialization
`y = (z / |z|)^(-m) · x` then has the real section `|α| = exp (ℓ / 2)`, where `ℓ = log |α|²`, and
the holomorphicity rows of the vortex equation determine its connection:

`y = (-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, exp (ℓ / 2) / 2, 0)`

(`TauCeti.Vortex.gaugeTransform_inv_windingPhase_apply_eq`). Every derivative of `ℓ` is
`O(exp (-c |z|))` for every rate `c < 1 / 2` (`TauCeti.Vortex.isBigO_iteratedFDeriv_log_normSq`),
and the derivatives of `exp (ℓ / 2) - 1` inherit this decay by the Leibniz rule
(`ContDiff.isBigO_iteratedFDeriv_succ_exp`). Hence the end-trivialized field tends to the vacuum
`(0, 1)` together with all its derivatives, at every rate `c < 1 / 2`. This upgrades the
zeroth-order convergence `TauCeti.Vortex.exists_norm_sub_referenceField_le_mul_exp`.

These are estimates for one smooth vortex; uniformity over compact families of divisors and decay
of derivatives in the divisor parameters are not treated here.

## Main results

* `TauCeti.Vortex.gaugeTransform_inv_windingPhase_apply_eq`: where the section is `|α|` times the
  winding phase, the winding end trivialization is
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

/-- **The end trivialization in terms of `ℓ = log |α|²`.** Let `x` be differentiable at a point
`w ≠ 0` where it solves the vortex equation, and suppose that near `w` its section is `|α|` times
the winding phase, `|α| > 0`, and `ℓ = log |α|²`. Then its winding-`m` end trivialization has real
section `|α| = exp (ℓ / 2)`, and the holomorphicity rows determine its connection:
`y = (-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, exp (ℓ / 2) / 2, 0)` at `w`. -/
theorem gaugeTransform_inv_windingPhase_apply_eq {w : ℂ} (hx : DifferentiableAt ℝ x w)
    (hsol : equation x w = 0) {ℓ : ℂ → ℝ} (hw : w ≠ 0)
    (hphase : ∀ᶠ v in 𝓝 w, sectionValue x v = ‖sectionValue x v‖ * windingPhase m v)
    (hℓ : ℓ =ᶠ[𝓝 w] fun v ↦ Real.log (4 * (x v 2 ^ 2 + x v 3 ^ 2)))
    (hpos : ∀ᶠ v in 𝓝 w, 0 < 4 * (x v 2 ^ 2 + x v 3 ^ 2)) :
    gaugeTransform (windingPhase m)⁻¹ x w =
      !₂[-(fderiv ℝ ℓ w I / 2), fderiv ℝ ℓ w 1 / 2, Real.exp (ℓ w / 2) / 2, 0] := by
  set y := gaugeTransform (windingPhase m)⁻¹ x
  have hxi := differentiableAt_euclidean.1 hx
  -- Near `w` the section of `y` is `|α| = exp (ℓ / 2)`.
  have hsec : ∀ᶠ v in 𝓝 w, y v 2 = Real.exp (ℓ v / 2) / 2 ∧ y v 3 = 0 := by
    filter_upwards [hphase, hℓ, hpos] with v hv hℓv hposv
    have hs : sectionValue y v = ‖sectionValue x v‖ :=
      sectionValue_gaugeTransform_inv_windingPhase hv
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
  have hsd : DifferentiableAt ℝ (fun v ↦ 4 * (x v 2 ^ 2 + x v 3 ^ 2)) w :=
    (((hxi 2).pow 2).add ((hxi 3).pow 2)).const_mul 4
  have hℓd : DifferentiableAt ℝ ℓ w :=
    (hsd.log hpos.self_of_nhds.ne').congr_of_eventuallyEq hℓ
  have hd2 : fderiv ℝ (fun v ↦ y v 2) w = (Real.exp (ℓ w / 2) / 2 * (1 / 2)) • fderiv ℝ ℓ w := by
    rw [Filter.EventuallyEq.fderiv_eq (f₁ := fun v ↦ y v 2)
      (f := fun v ↦ Real.exp (ℓ v / 2) / 2) (hsec.mono fun v hv ↦ hv.1)]
    have hfun : (fun v ↦ Real.exp (ℓ v / 2) / 2) = fun v ↦ 1 / 2 * Real.exp (1 / 2 * ℓ v) := by
      funext v; ring_nf
    rw [hfun, (((hℓd.hasFDerivAt.const_mul (1 / 2 : ℝ)).exp).const_mul (1 / 2 : ℝ)).fderiv]
    ext v
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring_nf
  have hd3 : fderiv ℝ (fun v ↦ y v 3) w = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq (f₁ := fun v ↦ y v 3) (f := fun _ ↦ (0 : ℝ))
      (hsec.mono fun v hv ↦ hv.2), fderiv_const_apply]
  -- The holomorphicity rows of `equation y = 0` at `w`.
  have hu : ContDiffAt ℝ 2 (fun v ↦ (((windingPhase m)⁻¹ v : Circle) : ℂ)) w := by
    have h := (conjCLE.contDiff.contDiffAt (x := (windingPhase m w : ℂ))).comp w
      (contDiffAt_windingPhase m hw (n := 2))
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun v ↦ ?_)
    simp [-Circle.coe_inv, Circle.coe_inv_eq_conj]
  have heq : equation y w = 0 := (equation_gaugeTransform_eq_zero_iff hu hxi).2 hsol
  have h1 := congrArg (· 1) heq
  have h2 := congrArg (· 2) heq
  simp only [equation_apply_one, equation_apply_two, PiLp.zero_apply, hd2, hd3,
    hsec.self_of_nhds.1, hsec.self_of_nhds.2, smul_apply, smul_eq_mul, zero_apply] at h1 h2
  have he := Real.exp_pos (ℓ w / 2)
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    field_simp
    nlinarith
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    field_simp
    nlinarith
  · simpa using hsec.self_of_nhds.1
  · simpa using hsec.self_of_nhds.2


/-- Along a filter on which `ℓ → 0` and the weight `ρ` is bounded, if every derivative of `ℓ` is
`O(ρ)` then so is every derivative of `(exp (ℓ / 2) - 1) / 2`. -/
private theorem isBigO_iteratedFDeriv_exp_half_sub_one {ℓ : ℂ → ℝ} (hℓ : ContDiff ℝ ∞ ℓ)
    {l : Filter ℂ} {ρ : ℂ → ℝ} (hlim : Tendsto ℓ l (𝓝 0)) (hρ : ρ =O[l] fun _ ↦ (1 : ℝ))
    (hdec : ∀ j, iteratedFDeriv ℝ j ℓ =O[l] ρ) (n : ℕ) :
    iteratedFDeriv ℝ n (fun w ↦ (Real.exp (ℓ w / 2) - 1) / 2) =O[l] ρ := by
  have hh : ContDiff ℝ ∞ (fun w ↦ ℓ w / 2) := hℓ.div_const 2
  have hexp : ContDiff ℝ ∞ (fun w ↦ Real.exp (ℓ w / 2)) := Real.contDiff_exp.comp hh
  have he : ContDiff ℝ ∞ (fun w ↦ Real.exp (ℓ w / 2) - 1) := hexp.sub contDiff_const
  -- Halving a function halves its derivatives.
  have hhalf {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) {j : ℕ} (hfj : iteratedFDeriv ℝ j f =O[l] ρ) :
      iteratedFDeriv ℝ j (fun w ↦ f w / 2) =O[l] ρ := by
    have h2 : (fun w ↦ f w / 2) = fun w ↦ (1 / 2 : ℝ) • f w :=
      funext fun w ↦ by rw [smul_eq_mul]; ring
    rw [h2]
    exact (hfj.const_smul_left (1 / 2 : ℝ)).congr_left fun w ↦
      (iteratedFDeriv_const_smul_apply' (hf.contDiffAt.of_le (by simp))).symm
  have hhdec : ∀ j, iteratedFDeriv ℝ j (fun w ↦ ℓ w / 2) =O[l] ρ := fun j ↦ hhalf hℓ (hdec j)
  have he1 : (fun w ↦ Real.exp (ℓ w / 2) - 1) =O[l] ρ :=
    Real.isBigO_exp_comp_sub_one (by simpa using hlim.div_const 2)
      ((isBigO_of_le (g := iteratedFDeriv ℝ 0 fun w ↦ ℓ w / 2) _ fun w ↦
        norm_iteratedFDeriv_zero.ge).trans (hhdec 0))
  -- The derivatives of `exp (ℓ / 2)` are bounded.
  have hbdd (k : ℕ) : ∀ i ≤ k, iteratedFDeriv ℝ i (fun w ↦ Real.exp (ℓ w / 2)) =O[l]
      fun _ ↦ (1 : ℝ) := by
    induction k with
    | zero =>
      intro i hi
      obtain rfl : i = 0 := by omega
      refine (isBigO_of_le _ fun w ↦ norm_iteratedFDeriv_zero.le).trans ?_
      simpa using (he1.trans hρ).add (isBigO_refl (fun _ : ℂ ↦ (1 : ℝ)) l)
    | succ k ih =>
      intro i hi
      rcases Nat.lt_or_eq_of_le hi with hi | rfl
      · exact ih i (by omega)
      · exact ((hh.of_le (by simp)).isBigO_iteratedFDeriv_succ_exp (fun i _ _ ↦ hhdec i)
          ih).trans hρ
  refine hhalf he ?_
  rcases n with _ | n
  · exact (isBigO_of_le _ fun w ↦ norm_iteratedFDeriv_zero.le).trans he1
  · refine (isBigO_of_le _ fun w ↦ le_of_eq ?_).trans
      ((hh.of_le (by simp)).isBigO_iteratedFDeriv_succ_exp (fun i _ _ ↦ hhdec i) (hbdd n))
    rw [fun_iteratedFDeriv_sub_apply (hexp.contDiffAt.of_le (by simp)) contDiffAt_const,
      iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, sub_zero]

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
smooth plane vortex with `|α| → 1` at infinity whose section is `|α|` times the winding phase
`(z / |z|)^m` outside a compact set. Then its winding-`m` end trivialization
`y = (z / |z|)^(-m) · x` tends to the vacuum `(0, 1)` with all its derivatives: for every order
`n` and every rate `c < 1 / 2`, `Dⁿ (y - vacuum)` is `O(exp (-c |z|))` at infinity.

Outside a compact set the end trivialization is `(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, exp (ℓ / 2) / 2, 0)`
for `ℓ = log |α|²`, so this follows from the decay of all derivatives of `ℓ`. -/
theorem isBigO_iteratedFDeriv_gaugeTransform_inv_windingPhase_sub_vacuumField
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    {c : ℝ} (hc : c < 1 / 2) (n : ℕ) :
    iteratedFDeriv ℝ n (fun w ↦ gaugeTransform (windingPhase m)⁻¹ x w - vacuumField w)
      =O[cocompact ℂ] fun z ↦ Real.exp (-(c * ‖z‖)) := by
  have hcd (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ x z i) := contDiff_euclidean.1 hx i
  have hs : ContDiff ℝ ∞ (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) :=
    contDiff_const.mul (((hcd 2).pow 2).add ((hcd 3).pow 2))
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
  have hρ : ρ =O[cocompact ℂ] fun _ ↦ (1 : ℝ) :=
    isBigO_of_le _ fun z ↦ by
      simp only [ρ, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_one, Real.exp_le_one_iff,
        Left.neg_nonpos_iff]
      exact mul_nonneg (le_max_right _ _) (norm_nonneg _)
  have hdec (j : ℕ) : iteratedFDeriv ℝ j ℓ =O[cocompact ℂ] ρ :=
    (isBigO_iteratedFDeriv_log_normSq (hcd 2) (hcd 3) hsol hlim (max_lt hc (by norm_num))
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
    rw [gaugeTransform_inv_windingPhase_apply_eq (hx.differentiable (by simp) w) (hsol w)
      (norm_pos_iff.mp ((le_max_right _ _).trans_lt hw'))
      (hnhds.mono fun v hv ↦ (hR hv).2.1) (hR (le_max_left R 0 |>.trans hw'.le)).1
      (hnhds.mono fun v hv ↦ by linarith [(hR hv).2.2]), vacuumField_apply]
    ext i
    fin_cases i <;> simp [Y]
    ring
  have hYdec : iteratedFDeriv ℝ n Y =O[cocompact ℂ] ρ := by
    refine (IsBigO.of_bound 1 (Eventually.of_forall fun z ↦ ?_)).trans
      ((hdec (n + 1)).norm_left.add
        (isBigO_iteratedFDeriv_exp_half_sub_one hℓ hℓlim hρ hdec n).norm_left)
    rw [one_mul, Real.norm_of_nonneg (by positivity)]
    exact norm_iteratedFDeriv_endField_le hℓ n z
  refine (hYdec.congr' ?_ EventuallyEq.rfl).trans
    (isBigO_exp_neg_mul_norm_of_le (le_max_left c 0) _)
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop R'] with z hz
  exact ((hY z hz).iteratedFDeriv ℝ n).eq_of_nhds.symm

end TauCeti.Vortex
