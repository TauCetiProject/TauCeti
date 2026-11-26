/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Basic
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Complex.Circle.Basic
import TauCeti.Analysis.Normed.Lp.PiLp.Basic
import TauCeti.Analysis.Normed.Module.Basic
import TauCeti.Analysis.PDE.Vortex.DerivativeDecay
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
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

Since the end field is determined by `ℓ`, two vortices whose moduli exceed `2 c` outside a disc
and whose logarithmic moduli are within `M` of each other on its boundary circle have end
trivializations within `94 M exp (-c (|z| - (R + 3)))` of each other, by the comparison of their
logarithmic moduli and their gradients
(`TauCeti.Vortex.norm_gaugeTransform_inv_sub_gaugeTransform_inv_le_mul_exp`).

These are estimates for one or two smooth vortices. Their uniform version over the vortices whose
zeros lie in a fixed disc is `TauCeti.Analysis.PDE.Vortex.FramedGauge.UniformDerivativeDecay`, and
the decay of the derivatives of every order in the coefficients (symmetric coordinates) and the
point is `TauCeti.Analysis.PDE.Vortex.FramedGauge.CoefficientDecay`.

## Main results

* `TauCeti.Vortex.gaugeTransform_inv_apply_eq`: where the section is `|α|` times a gauge `u`
  and solves the holomorphicity rows, its gauge transformation by `u⁻¹` is
  `(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, exp (ℓ / 2) / 2, 0)` for `ℓ = log |α|²`.
* `TauCeti.Vortex.gaugeTransform_inv_apply_sub_vacuumField_eq`: the same gauge transformation
  minus the vacuum is the end field `(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, (exp (ℓ / 2) - 1) / 2, 0)`.
* `TauCeti.Vortex.exists_contDiff_isBigO_eventuallyEq_gaugeTransform_inv_sub_vacuumField`: near
  infinity the end trivialization minus the vacuum agrees with a smooth field whose derivatives
  are all `O(exp (-c |z|))` for every rate `c < 1 / 2`.
* `TauCeti.Vortex.isBigO_iteratedFDeriv_gaugeTransform_inv_sub_vacuumField`: every derivative of
  the end trivialization minus the vacuum, in particular the winding end trivialization, is
  `O(exp (-c |z|))` for every rate `c < 1 / 2`.
* `TauCeti.Vortex.exists_endField_eq_add`, `TauCeti.Vortex.norm_iteratedFDeriv_endField_le`: the
  end field `(-(∂_u ℓ) / 2, (∂_v ℓ) / 2, (exp (ℓ / 2) - 1) / 2, 0)` is linear in `Dℓ` and
  `exp (ℓ / 2) - 1`, so bounds on the derivatives of `ℓ ≤ 0` bound its derivatives.
* `TauCeti.Vortex.norm_gaugeTransform_inv_sub_gaugeTransform_inv_le_mul_exp`: the end
  trivializations of two vortices with moduli above `2 c` outside the disc of radius `R`, whose
  logarithmic moduli are within `M` of each other on its boundary, differ by at most
  `94 M exp (-c (|z| - (R + 3)))` for `|z| ≥ R + 3`.

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
    rw [hv, gaugeTransform_apply_two_sq_add_apply_three_sq]
  have h1 := fderiv_log_normSq_apply_one hpy hqy hαy hrows.1 hrows.2
  have hI := fderiv_log_normSq_apply_I hpy hqy hαy hrows.1 hrows.2
  rw [← hℓy.fderiv_eq, hy3.fderiv_eq, fderiv_const_apply, hsec.self_of_nhds.2] at h1 hI
  simp only [zero_apply, mul_zero, zero_mul, sub_zero, zero_div, zero_add, neg_zero] at h1 hI
  ext i
  fin_cases i <;> simp [hsec.self_of_nhds.1, hsec.self_of_nhds.2] <;> linarith

/-- **The end trivialization minus the vacuum in terms of `ℓ = log |α|²`.** Under the hypotheses
of `TauCeti.Vortex.gaugeTransform_inv_apply_eq`, the gauge transformation of `x` by `u⁻¹` minus
the vacuum `(0, 1)` is the end field `(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, (exp (ℓ / 2) - 1) / 2, 0)`
at `w`. -/
theorem gaugeTransform_inv_apply_sub_vacuumField_eq {u : ℂ → Circle} {w : ℂ}
    (hp : DifferentiableAt ℝ (fun v ↦ x v 2) w) (hq : DifferentiableAt ℝ (fun v ↦ x v 3) w)
    (hα : x w 2 ^ 2 + x w 3 ^ 2 ≠ 0) (h₁ : equation x w 1 = 0) (h₂ : equation x w 2 = 0)
    {ℓ : ℂ → ℝ} (hphase : ∀ᶠ v in 𝓝 w, sectionValue x v = ‖sectionValue x v‖ * u v)
    (hℓ : ℓ =ᶠ[𝓝 w] fun v ↦ Real.log (4 * (x v 2 ^ 2 + x v 3 ^ 2))) :
    gaugeTransform u⁻¹ x w - vacuumField w =
      !₂[-(fderiv ℝ ℓ w I / 2), fderiv ℝ ℓ w 1 / 2, (Real.exp (ℓ w / 2) - 1) / 2, 0] := by
  rw [gaugeTransform_inv_apply_eq hp hq hα h₁ h₂ hphase hℓ, vacuumField_apply]
  ext i
  fin_cases i
  · simp
  · simp
  · simp only [Fin.reduceFinMk, PiLp.sub_apply, Matrix.cons_val]
    ring
  · simp

/-- **The end field is linear in `Dℓ` and `exp (ℓ / 2) - 1`.** For vectors `u` and `v` of a real
normed space `W` there are continuous linear maps `L₁` and `L₂` with
`(-(φ u) / 2, φ v / 2, t / 2, 0) = L₁ φ + L₂ t` for every linear functional `φ` on `W` and every
real `t`. For `(u, v) = (I, 1)`, `φ = Dℓ (w)` and `t = exp (ℓ w / 2) - 1`, this writes the end field
`(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, (exp (ℓ / 2) - 1) / 2, 0)` of a function `ℓ` on the plane as
`L₁ (Dℓ) + L₂ (exp (ℓ / 2) - 1)`; other directions give the end field of a family of functions of
`z`, differentiated along the second factor. -/
theorem exists_endField_eq_add {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (u v : W) :
    ∃ (L₁ : (W →L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (L₂ : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 4)),
      ∀ (φ : W →L[ℝ] ℝ) (t : ℝ), !₂[-(φ u / 2), φ v / 2, t / 2, 0] = L₁ φ + L₂ t := by
  refine ⟨(-(1 / 2 : ℝ)) • (ContinuousLinearMap.apply ℝ ℝ u).smulRight (EuclideanSpace.single 0 1) +
      (1 / 2 : ℝ) • (ContinuousLinearMap.apply ℝ ℝ v).smulRight (EuclideanSpace.single 1 1),
    ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single 2 (1 / 2)), fun φ t ↦ ?_⟩
  ext i
  fin_cases i <;> simp <;> ring

/-- **Derivatives of an end field.** Let `ℓ` be smooth at `x` with `ℓ x ≤ 0`, and let its
derivatives of order at most `n + 1` at `x` be at most `C ε`, with `0 ≤ ε ≤ 1`. Then for continuous
linear maps `L₁` and `L₂` the `n`-th derivative of `L₁ (Dℓ) + L₂ (exp (ℓ / 2) - 1)` at `x` is at
most `(‖L₁‖ C + ‖L₂‖ n! max 1 C ^ (n + 1)) ε`. By `TauCeti.Vortex.exists_endField_eq_add` this
bounds the derivatives of the end field of `ℓ`. -/
theorem norm_iteratedFDeriv_endField_le {W F : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [NormedAddCommGroup F] [NormedSpace ℝ F] {ℓ : W → ℝ} {x : W}
    (L₁ : (W →L[ℝ] ℝ) →L[ℝ] F) (L₂ : ℝ →L[ℝ] F) (hℓ : ContDiffAt ℝ ∞ ℓ x) (hℓ₀ : ℓ x ≤ 0)
    {n : ℕ} {C ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hD : ∀ j ≤ n + 1, ‖iteratedFDeriv ℝ j ℓ x‖ ≤ C * ε) :
    ‖iteratedFDeriv ℝ n (fun y ↦ L₁ (fderiv ℝ ℓ y) + L₂ (Real.exp (ℓ y / 2) - 1)) x‖ ≤
      (‖L₁‖ * C + ‖L₂‖ * ((Nat.factorial n : ℝ) * max 1 C ^ (n + 1))) * ε := by
  have hDℓ : ContDiffAt ℝ ∞ (fderiv ℝ ℓ) x := hℓ.fderiv_right (by simp)
  have hE : ContDiffAt ℝ ∞ (fun y ↦ Real.exp (ℓ y / 2) - 1) x :=
    ((Real.contDiff_exp.contDiffAt).comp _ (hℓ.div_const 2)).sub contDiffAt_const
  have hL₁ : ContDiffAt ℝ ∞ (fun y ↦ L₁ (fderiv ℝ ℓ y)) x := L₁.contDiff.contDiffAt.comp x hDℓ
  have hL₂ : ContDiffAt ℝ ∞ (fun y ↦ L₂ (Real.exp (ℓ y / 2) - 1)) x :=
    L₂.contDiff.contDiffAt.comp x hE
  rw [fun_iteratedFDeriv_add_apply (hL₁.of_le (by simp)) (hL₂.of_le (by simp))]
  -- The connection part is linear in `Dℓ`.
  have h₁ : ‖iteratedFDeriv ℝ n (fun y ↦ L₁ (fderiv ℝ ℓ y)) x‖ ≤ ‖L₁‖ * (C * ε) := by
    refine (L₁.norm_iteratedFDeriv_comp_left hDℓ (by simp)).trans ?_
    rw [norm_iteratedFDeriv_fderiv]
    exact mul_le_mul_of_nonneg_left (hD (n + 1) le_rfl) (norm_nonneg _)
  -- The section part is linear in `exp (ℓ / 2) - 1`, bounded by the Faà di Bruno formula.
  have h₂ : ‖iteratedFDeriv ℝ n (fun y ↦ L₂ (Real.exp (ℓ y / 2) - 1)) x‖ ≤
      ‖L₂‖ * ((Nat.factorial n : ℝ) * max 1 C ^ (n + 1) * ε) := by
    refine (L₂.norm_iteratedFDeriv_comp_left hE (by simp)).trans
      (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    have hhalf : (fun y ↦ ℓ y / 2) = (2⁻¹ : ℝ) • ℓ := by
      funext y
      simp [div_eq_inv_mul]
    refine ((hℓ.div_const 2).of_le (by simp)).norm_iteratedFDeriv_exp_sub_one_le
      (div_nonpos_of_nonpos_of_nonneg hℓ₀ zero_le_two) hε₀ hε₁ fun j hj ↦ ?_
    rw [hhalf, iteratedFDeriv_const_smul_apply (hℓ.of_le (by simp))]
    refine (ContinuousMultilinearMap.opNorm_smul_le _ _).trans ?_
    have := hD j (by omega)
    rw [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
    nlinarith [norm_nonneg (iteratedFDeriv ℝ j ℓ x)]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ ‖L₁‖ * (C * ε) + ‖L₂‖ * ((Nat.factorial n : ℝ) * max 1 C ^ (n + 1) * ε) :=
        add_le_add h₁ h₂
    _ = _ := by ring

/-- Along a filter on which `ρ` is bounded, if every derivative of a smooth `ℓ` is `O(ρ)`, then so
is every derivative of `(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, (exp (ℓ / 2) - 1) / 2, 0)`: its connection
part is linear in `Dℓ` and its section part is linear in `exp (ℓ / 2) - 1`
(`TauCeti.Vortex.exists_endField_eq_add`). -/
private theorem isBigO_iteratedFDeriv_endField {ℓ : ℂ → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) {l : Filter ℂ}
    {ρ : ℂ → ℝ} (hρ : ρ =O[l] fun _ ↦ (1 : ℝ)) (hdec : ∀ j, iteratedFDeriv ℝ j ℓ =O[l] ρ)
    (n : ℕ) :
    iteratedFDeriv ℝ n (fun w ↦ !₂[-(fderiv ℝ ℓ w I / 2), fderiv ℝ ℓ w 1 / 2,
      (Real.exp (ℓ w / 2) - 1) / 2, 0]) =O[l] ρ := by
  obtain ⟨L₁, L₂, hL⟩ := exists_endField_eq_add I 1
  -- The derivatives of `ℓ / 2` and hence of `exp (ℓ / 2) - 1` are `O(ρ)`.
  have hexp := ((hℓ.div_const 2).of_le (by simp)).isBigO_iteratedFDeriv_exp_sub_one (n := n) hρ
    fun j _ ↦ by simpa [div_eq_inv_mul] using ((2 : ℝ)⁻¹ • ContinuousLinearMap.id ℝ ℝ
      ).isBigO_iteratedFDeriv_comp_left hℓ (by simp) (hdec j)
  have hD : ContDiff ℝ ∞ (fderiv ℝ ℓ) := hℓ.fderiv_right (by norm_cast)
  have hE : ContDiff ℝ ∞ (fun w ↦ Real.exp (ℓ w / 2) - 1) :=
    (Real.contDiff_exp.comp (hℓ.div_const 2)).sub contDiff_const
  simp only [hL]
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
  exact gaugeTransform_inv_apply_sub_vacuumField_eq (hp.differentiable (by simp) w)
    (hq.differentiable (by simp) w) (fun h ↦ by linarith [hRw.2.2]) (by simp [hsol w])
    (by simp [hsol w])
    (eventually_of_mem (hopen.mem_nhds hw) fun v (hv : R < ‖v‖) ↦ (hR hv.le).2.1) hRw.1

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

/-! ### Two vortices with nonvanishing sections outside a disc -/

section TwoVortices

variable {y : ℂ → EuclideanSpace ℝ (Fin 4)} {R c M : ℝ}

/-- The end fields `(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, (exp (ℓ / 2) - 1) / 2, 0)` of two functions
`ℓx, ℓy ≤ 0` differ by at most `‖D (ℓx - ℓy)‖ + |ℓx - ℓy|`. -/
private theorem norm_endField_sub_endField_le {ℓx ℓy : ℂ → ℝ} {z : ℂ}
    (hdx : DifferentiableAt ℝ ℓx z) (hdy : DifferentiableAt ℝ ℓy z) (hx : ℓx z ≤ 0)
    (hy : ℓy z ≤ 0) :
    ‖!₂[-(fderiv ℝ ℓx z I / 2), fderiv ℝ ℓx z 1 / 2, (Real.exp (ℓx z / 2) - 1) / 2, 0] -
      !₂[-(fderiv ℝ ℓy z I / 2), fderiv ℝ ℓy z 1 / 2, (Real.exp (ℓy z / 2) - 1) / 2, 0]‖ ≤
      ‖fderiv ℝ (fun w ↦ ℓx w - ℓy w) z‖ + |ℓx z - ℓy z| := by
  have hD : fderiv ℝ (fun w ↦ ℓx w - ℓy w) z = fderiv ℝ ℓx z - fderiv ℝ ℓy z := fderiv_sub hdx hdy
  have h₀ : |fderiv ℝ ℓx z I - fderiv ℝ ℓy z I| ≤ ‖fderiv ℝ (fun w ↦ ℓx w - ℓy w) z‖ := by
    rw [hD]
    simpa [Real.norm_eq_abs] using (fderiv ℝ ℓx z - fderiv ℝ ℓy z).le_opNorm I
  have h₁ : |fderiv ℝ ℓx z 1 - fderiv ℝ ℓy z 1| ≤ ‖fderiv ℝ (fun w ↦ ℓx w - ℓy w) z‖ := by
    rw [hD]
    simpa [Real.norm_eq_abs] using (fderiv ℝ ℓx z - fderiv ℝ ℓy z).le_opNorm 1
  have h₂ : |Real.exp (ℓx z / 2) - Real.exp (ℓy z / 2)| ≤ |ℓx z - ℓy z| / 2 := by
    refine (Real.abs_exp_sub_exp_le (div_nonpos_of_nonpos_of_nonneg hx zero_le_two)
      (div_nonpos_of_nonpos_of_nonneg hy zero_le_two)).trans (le_of_eq ?_)
    rw [Real.exp_zero, one_mul, ← sub_div, abs_div, abs_two]
  have hvec : !₂[-(fderiv ℝ ℓx z I / 2), fderiv ℝ ℓx z 1 / 2, (Real.exp (ℓx z / 2) - 1) / 2, 0] -
      !₂[-(fderiv ℝ ℓy z I / 2), fderiv ℝ ℓy z 1 / 2, (Real.exp (ℓy z / 2) - 1) / 2, 0] =
      !₂[-((fderiv ℝ ℓx z I - fderiv ℝ ℓy z I) / 2), (fderiv ℝ ℓx z 1 - fderiv ℝ ℓy z 1) / 2,
        (Real.exp (ℓx z / 2) - Real.exp (ℓy z / 2)) / 2, 0] := by
    ext i
    fin_cases i <;> simp <;> ring
  rw [hvec]
  refine (PiLp.norm_le_sum_norm _).trans ?_
  simp [Fin.sum_univ_four, abs_div]
  linarith [abs_nonneg (ℓx z - ℓy z)]

/-- **The end trivializations of two vortices converge to each other outside a disc.** Under the
hypotheses of `TauCeti.Vortex.norm_fderiv_log_normSq_sub_log_normSq_le_mul_exp`, let `u` be a gauge
such that the sections of both `x` and `y` are `|α|` times `u` near a point `z` at distance at least
`3` from the disc. Then the end trivializations `u⁻¹ · x` and `u⁻¹ · y` satisfy

`‖(u⁻¹ · x)(z) - (u⁻¹ · y)(z)‖ ≤ 94 M exp (-c (|z| - (R + 3)))`. -/
theorem norm_gaugeTransform_inv_sub_gaugeTransform_inv_le_mul_exp
    (hxp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hxq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hyp : ContDiff ℝ 2 (fun w ↦ y w 2)) (hyq : ContDiff ℝ 2 (fun w ↦ y w 3))
    (hxs : ∀ z, equation x z = 0) (hys : ∀ z, equation y z = 0)
    (hxl : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hyl : Tendsto (fun z ↦ 4 * (y z 2 ^ 2 + y z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hR : 0 < R) (hc : 0 ≤ c)
    (hxR : ∀ z, R ≤ ‖z‖ → 4 * c ^ 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2))
    (hyR : ∀ z, R ≤ ‖z‖ → 4 * c ^ 2 < 4 * (y z 2 ^ 2 + y z 3 ^ 2))
    (hbd : ∀ z, ‖z‖ = R → |Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) -
      Real.log (4 * (y z 2 ^ 2 + y z 3 ^ 2))| ≤ M) {u : ℂ → Circle} {z : ℂ} (hz : R + 3 ≤ ‖z‖)
    (hux : ∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * u w)
    (huy : ∀ᶠ w in 𝓝 z, sectionValue y w = ‖sectionValue y w‖ * u w) :
    ‖gaugeTransform u⁻¹ x z - gaugeTransform u⁻¹ y z‖ ≤
      94 * M * Real.exp (-(c * (‖z‖ - (R + 3)))) := by
  have hzR : R ≤ ‖z‖ := by linarith
  -- At `z` the sections do not vanish, and the logarithmic moduli are differentiable and `≤ 0`.
  have hc₄ : (0 : ℝ) ≤ 4 * c ^ 2 := by positivity
  have hαx := right_ne_zero_of_mul (hc₄.trans_lt (hxR z hzR)).ne'
  have hαy := right_ne_zero_of_mul (hc₄.trans_lt (hyR z hzR)).ne'
  have hdx := (contDiffAt_log_normSq_of_pos hxp hxq hxs
    (hc₄.trans_lt (hxR z hzR))).differentiableAt (by simp)
  have hdy := (contDiffAt_log_normSq_of_pos hyp hyq hys
    (hc₄.trans_lt (hyR z hzR))).differentiableAt (by simp)
  have hnx := log_normSq_nonpos hxp hxq hxs hxl z
  have hny := log_normSq_nonpos hyp hyq hys hyl z
  -- Near `z` the two end trivializations minus the vacuum are the end fields of the logarithmic
  -- moduli.
  have hex := gaugeTransform_inv_apply_sub_vacuumField_eq
    ((hxp.differentiable (by simp)) z) ((hxq.differentiable (by simp)) z) hαx (by simp [hxs z])
    (by simp [hxs z]) hux EventuallyEq.rfl
  have hey := gaugeTransform_inv_apply_sub_vacuumField_eq
    ((hyp.differentiable (by simp)) z) ((hyq.differentiable (by simp)) z) hαy (by simp [hys z])
    (by simp [hys z]) huy EventuallyEq.rfl
  rw [← sub_sub_sub_cancel_right _ _ (vacuumField z), hex, hey]
  refine (norm_endField_sub_endField_le hdx hdy hnx hny).trans ?_
  have hgrad := norm_fderiv_log_normSq_sub_log_normSq_le_mul_exp hxp hxq hyp hyq hxs hys hxl
    hyl hR hc hxR hyR hbd hz
  have hval := abs_log_normSq_sub_log_normSq_le_mul_exp hxp hxq hyp hyq hxs hys hxl hyl hR hc
    hxR hyR hbd hzR
  have hM := nonneg_of_forall_norm_eq_abs_le hR.le hbd
  have hexp : Real.exp (-(c * (‖z‖ - R))) ≤ Real.exp (-(c * (‖z‖ - (R + 3)))) :=
    Real.exp_le_exp.2 (by nlinarith)
  nlinarith [mul_le_mul_of_nonneg_left hexp hM]

end TwoVortices

end TauCeti.Vortex
