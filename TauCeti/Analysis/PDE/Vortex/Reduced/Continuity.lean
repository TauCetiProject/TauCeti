/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.EulerLagrange
public import TauCeti.Analysis.PDE.Vortex.Reduced.Regularity
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Algebra.Polynomial.BigOperators
import TauCeti.Analysis.Polynomial.SublevelVolume
import TauCeti.Analysis.SpecialFunctions.Exp.Modular
import TauCeti.Analysis.SpecialFunctions.Sqrt
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz
import TauCeti.Analysis.Sobolev.Poincare.Planar
import TauCeti.Analysis.Sobolev.W1p.Density
import TauCeti.Analysis.Sobolev.W1p.Exponential

/-!
# Uniqueness and continuous dependence of the minimizer of Taubes's functional

Let `P` be a complex polynomial of degree `m ≥ 1`, and put `h = ‖P‖² / (1 + ‖P‖²)` and
`g = 2 ‖P'‖² / (1 + ‖P‖²)²`. Taubes constructs the plane vortex with zero divisor `P` from a
minimizer `w ∈ H¹(ℂ)` of the functional

`I_P(w) = ‖∇w‖₂² / 2 + (1 / 16) ∫ h (exp (2w) - 1 - 2w) + ∫ (g - (1 + ‖P‖²)⁻¹ / 8) w`

(`TauCeti.Vortex.sobolevReducedFunctional`), which exists by
`TauCeti.Vortex.exists_forall_sobolevReducedFunctional_le`. This file proves that the minimizer is
unique and that it depends continuously on the zeros of `P` in `H¹(ℂ)`. This dependence is the
input for constructing continuous families of vortices over compact sets of divisors.

The functional is finite on all of `H¹(ℂ)` (`TauCeti.Vortex.sobolevReducedFunctional_ne_top`),
because `exp (2w) - 1 ∈ L²(ℂ)` for `w ∈ H¹(ℂ)`. By density of test functions the weak
Euler–Lagrange equation of a minimizer `w` then holds against every direction `v ∈ H¹(ℂ)`
(`TauCeti.Vortex.inner_gradient_add_integral_reducedSource_mul_eq_zero`):

`⟪∇w, ∇v⟫ + ∫ S_P(w) v = 0`,  `S_P(w) = (exp (2w) h - 1) / 8 + g`

(`TauCeti.Vortex.reducedSource`). The potential satisfies the exact expansion
`φ(w + d) = φ(w) + φ'(w) d + exp (2w) φ(d)` for `φ(t) = exp (2t) - 1 - 2t`. Expanding `I_Q(w + d)`
for a second polynomial `Q` and removing the first variation with the Euler–Lagrange equation of
`w` gives the stability inequality
(`TauCeti.Vortex.norm_gradient_sub_sq_div_two_add_integral_div_sixteen_le`): if
`I_Q(w + d) ≤ I_Q(w)`, then

`‖∇d‖₂² / 2 + (1 / 16) ∫ h_Q exp (2w) φ(d) ≤ -∫ (S_Q(w) - S_P(w)) d`.

For `Q = P` the right side vanishes, so two minimizers agree
(`TauCeti.Vortex.eq_of_forall_sobolevReducedFunctional_le`). For `Q` close to `P` the right side
is at most `‖S_Q(w) - S_P(w)‖₂ ‖d‖₂`. The left side controls `‖d‖₂` through the planar estimate
`TauCeti.W1p.exists_norm_value_sq_le_of_finrank_eq_two`, applied off the set where `‖Q‖` is small
or `|w|` is large; there the weight `h_Q exp (2w)` is bounded below. For
`P = ∏ i, (X - a i)` the sources converge in `L²` as the roots converge, and the sets where `‖P‖`
is small have small measure uniformly in the roots. Hence the minimizer is a continuous function of
the roots (`TauCeti.Vortex.continuous_of_forall_sobolevReducedFunctional_le`).

## Main results

All in the namespace `TauCeti.Vortex`:

* `inner_gradient_add_integral_reducedSource_mul_eq_zero`: the weak Euler–Lagrange equation of a
  minimizer, tested against `H¹(ℂ)`.
* `norm_gradient_sub_sq_div_two_add_integral_div_sixteen_le`: the stability inequality.
* `eq_of_forall_sobolevReducedFunctional_le`: the minimizer is unique.
* `tendsto_of_forall_sobolevReducedFunctional_le`: minimizers for polynomials `Q x` converge in
  `H¹(ℂ)` along a filter when the sources converge in `L²` and the small sublevel sets of `Q x`
  have uniformly small measure.
* `continuous_of_forall_sobolevReducedFunctional_le`: the minimizer for the zeros `a : ι → ℂ`
  depends continuously on `a` in `H¹(ℂ)`.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Filter MeasureTheory Metric Set Topology
open scoped ENNReal RealInnerProductSpace

variable {P : Polynomial ℂ}

/-- The source of the reduced equation in the form used by the Euler–Lagrange equation,
`(exp (2w) h - 1) / 8 + g`. -/
private theorem reducedSource_eq (w : ℂ → ℝ) (z : ℂ) :
    reducedSource P w z =
      (Real.exp (2 * w z) * (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2)) - 1) / 8 +
        2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 := by
  rw [reducedSource_def, backgroundSource_def, backgroundWeight_def, Polynomial.deriv]
  ring

/-- **The weak Euler–Lagrange equation tested against `H¹(ℂ)`.** Let `P` have degree at least one
and let `u ∈ H¹(ℂ)` minimize Taubes's functional `TauCeti.Vortex.sobolevReducedFunctional P`. Then
for every `v ∈ H¹(ℂ)`,

`⟪∇u, ∇v⟫ + ∫ ((exp (2u) h - 1) / 8 + g) v = 0`,

where `⟪∇u, ∇v⟫` is the `L²` pairing of the weak gradients and the source
`(exp (2u) h - 1) / 8 + g` is `TauCeti.Vortex.reducedSource P u`. Both terms are continuous in `v`
for the norm of `H¹(ℂ)`, because the source is square integrable
(`TauCeti.Vortex.memLp_reducedSource`), so this extends
`TauCeti.Vortex.integral_inner_gradient_add_integral_mul_value_eq_zero` from bounded `v` vanishing
outside a set of finite measure, by density of test functions. -/
theorem inner_gradient_add_integral_reducedSource_mul_eq_zero (hm : 0 < P.natDegree)
    {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ w, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P w)
    (v : W1p (volume : Measure ℂ) ⊤ 2) :
    ⟪W1p.gradient u, W1p.gradient v⟫ +
      ∫ z, reducedSource P (W1p.value u) z * W1p.value v z = 0 := by
  have hS := (memLp_reducedSource hm u).restrict ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ)
  set S := hS.toLp _
  have hint (v : W1p (volume : Measure ℂ) ⊤ 2) :
      ∫ z, reducedSource P (W1p.value u) z * W1p.value v z = ⟪S, W1p.value v⟫ := by
    rw [L2.inner_def]
    have h := hS.coeFn_toLp
    simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at h ⊢
    exact integral_congr_ae (h.mono fun z hz ↦ by
      simp only [S, hz, RCLike.inner_apply, conj_trivial, mul_comm])
  have hcont : Continuous fun v : W1p (volume : Measure ℂ) ⊤ 2 ↦
      ⟪W1p.gradient u, W1p.gradient v⟫ + ⟪S, W1p.value v⟫ := by
    have hg := (W1p.gradientL (mu := (volume : Measure ℂ)) (Omega := ⊤) (p := 2)).continuous.congr
      W1p.gradientL_apply
    have hv := (W1p.valueL (mu := (volume : Measure ℂ)) (Omega := ⊤) (p := 2)).continuous.congr
      W1p.valueL_apply
    exact (continuous_const.inner hg).add (continuous_const.inner hv)
  rw [hint]
  refine (W1p.denseRange_ofTestFunctionₗ_top (mu := (volume : Measure ℂ)) (p := 2)
    ENNReal.ofNat_ne_top).induction_on v (isClosed_eq hcont continuous_const) fun φ ↦ ?_
  have hvφ := W1p.value_ofTestFunctionₗ_top_ae (mu := (volume : Measure ℂ)) (p := 2) φ
  obtain ⟨M, hM⟩ := φ.contDiff.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have h := integral_inner_gradient_add_integral_mul_value_eq_zero hm hu
    (v := W1p.ofTestFunctionₗ volume ⊤ 2 φ) φ.hasCompactSupport.isCompact.measure_ne_top (M := M)
    (hvφ.mono fun z hz ↦ by rw [hz, ← Real.norm_eq_abs]; exact hM z)
    (hvφ.mono fun z hz hzK ↦ by rw [hz]; exact image_eq_zero_of_notMem_tsupport hzK)
  rw [← hint, ← h]
  congr 1
  · rw [L2.inner_def]
    simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ]
  · exact integral_congr_ae (ae_of_all _ fun z ↦ by simp only [reducedSource_eq])

/-- The integrand `h_Q exp (2w) (exp (2d) - 1 - 2d)` of the stability inequality is
nonnegative. -/
private theorem stability_integrand_nonneg (Q : Polynomial ℂ) (W D : ℂ → ℝ) (z : ℂ) :
    0 ≤ backgroundWeight (Q.eval ·) z * Real.exp (2 * W z) * (Real.exp (2 * D z) - 1 - 2 * D z) :=
  mul_nonneg (mul_nonneg (backgroundWeight_nonneg _ z) (Real.exp_pos _).le)
    (Real.exp_two_mul_sub_one_sub_two_mul_nonneg _)

/-- The stability inequality with the integrability of its potential term. -/
private theorem integrable_and_stability {Q : Polynomial ℂ} (hP : 0 < P.natDegree)
    (hQ : 0 < Q.natDegree) {w u : W1p (volume : Measure ℂ) ⊤ 2}
    (hw : ∀ v, sobolevReducedFunctional P w ≤ sobolevReducedFunctional P v)
    (hu : sobolevReducedFunctional Q u ≤ sobolevReducedFunctional Q w) :
    Integrable (fun z ↦ backgroundWeight (Q.eval ·) z * Real.exp (2 * W1p.value w z) *
      (Real.exp (2 * W1p.value (u - w) z) - 1 - 2 * W1p.value (u - w) z)) ∧
    ‖W1p.gradient (u - w)‖ ^ 2 / 2 +
        (∫ z, backgroundWeight (Q.eval ·) z * Real.exp (2 * W1p.value w z) *
          (Real.exp (2 * W1p.value (u - w) z) - 1 - 2 * W1p.value (u - w) z)) / 16 ≤
      -∫ z, (reducedSource Q (W1p.value w) z - reducedSource P (W1p.value w) z) *
        W1p.value (u - w) z := by
  set d := u - w
  set hQ' : ℂ → ℝ := backgroundWeight (Q.eval ·)
  set W : ℂ → ℝ := ⇑(W1p.value w)
  set D : ℂ → ℝ := ⇑(W1p.value d)
  set U : ℂ → ℝ := ⇑(W1p.value u)
  set c : ℂ → ℝ := fun z ↦
    2 * ‖Q.derivative.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2) ^ 2 - (1 + ‖Q.eval z‖ ^ 2)⁻¹ / 8
  have hc : MemLp c 2 := memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight hQ
  have hh0 (z : ℂ) : 0 ≤ hQ' z := backgroundWeight_nonneg _ z
  have hh1 (z : ℂ) : hQ' z ≤ 1 := (backgroundWeight_lt_one _ z).le
  have hhc : Continuous hQ' := continuous_backgroundWeight Q.continuous
  have hud : U =ᵐ[volume] fun z ↦ W z + D z := by
    have h := W1p.value_add_ae (mu := (volume : Measure ℂ)) (Omega := ⊤) (p := 2) w d
    simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at h
    have hwd : w + d = u := add_sub_cancel w u
    rwa [hwd] at h
  -- Integrability of the pieces of the expansion.
  have hA : Integrable fun z ↦ hQ' z * (Real.exp (2 * U z) - 1 - 2 * U z) := by
    simpa only [hQ', backgroundWeight_def] using
      sobolevReducedFunctional_ne_top_iff.1 (sobolevReducedFunctional_ne_top Q u)
  have hB : Integrable fun z ↦ hQ' z * (Real.exp (2 * W z) - 1 - 2 * W z) := by
    simpa only [hQ', backgroundWeight_def] using
      sobolevReducedFunctional_ne_top_iff.1 (sobolevReducedFunctional_ne_top Q w)
  have hC : Integrable fun z ↦ hQ' z * ((Real.exp (2 * W z) - 1) * D z) :=
    ((W1p.memLp_exp_two_mul_value_sub_one volume Complex.finrank_real_complex w).integrable_mul
      (W1p.memLp_value d)).bdd_mul
      hhc.aestronglyMeasurable (c := 1) (ae_of_all _ fun z ↦ by
        rw [Real.norm_of_nonneg (hh0 z)]; exact hh1 z)
  have hexpand : (fun z ↦ hQ' z * Real.exp (2 * W z) *
      (Real.exp (2 * D z) - 1 - 2 * D z)) =ᵐ[volume] fun z ↦
      hQ' z * (Real.exp (2 * U z) - 1 - 2 * U z) -
        hQ' z * (Real.exp (2 * W z) - 1 - 2 * W z) -
        2 * (hQ' z * ((Real.exp (2 * W z) - 1) * D z)) :=
    hud.mono fun z hz ↦ by
      simp only at hz ⊢
      rw [hz, mul_add, Real.exp_add]
      ring
  have hD : Integrable fun z ↦ hQ' z * Real.exp (2 * W z) *
      (Real.exp (2 * D z) - 1 - 2 * D z) :=
    ((hA.sub hB).sub (hC.const_mul 2)).congr hexpand.symm
  refine ⟨hD, ?_⟩
  -- The functional at `u` and at `w`.
  have hIu := sobolevReducedFunctional_eq_coe (P := Q) (u := u)
    (sobolevReducedFunctional_ne_top_iff.1 (sobolevReducedFunctional_ne_top Q u))
  have hIw := sobolevReducedFunctional_eq_coe (P := Q) (u := w)
    (sobolevReducedFunctional_ne_top_iff.1 (sobolevReducedFunctional_ne_top Q w))
  rw [hIu, hIw, EReal.coe_le_coe_iff] at hu
  simp only [← backgroundWeight_def (Q.eval ·)] at hu
  -- `rw` produced the unfolded integrands; restate `hu` through the local abbreviations, which are
  -- definitionally the same functions.
  change ‖W1p.gradient u‖ ^ 2 / 2 + (∫ z, hQ' z * (Real.exp (2 * U z) - 1 - 2 * U z)) / 16 +
      ∫ z, c z * U z ≤
    ‖W1p.gradient w‖ ^ 2 / 2 + (∫ z, hQ' z * (Real.exp (2 * W z) - 1 - 2 * W z)) / 16 +
      ∫ z, c z * W z at hu
  -- The gradient term.
  have hgrad : ‖W1p.gradient u‖ ^ 2 =
      ‖W1p.gradient w‖ ^ 2 + 2 * ⟪W1p.gradient w, W1p.gradient d⟫ + ‖W1p.gradient d‖ ^ 2 := by
    rw [← norm_add_sq_real, ← W1p.gradient_add, add_sub_cancel]
  -- The linear term.
  have hcW : Integrable fun z ↦ c z * W z := hc.integrable_mul (W1p.memLp_value w)
  have hcD : Integrable fun z ↦ c z * D z := hc.integrable_mul (W1p.memLp_value d)
  have hPD : Integrable fun z ↦ reducedSource P W z * D z :=
    (memLp_reducedSource hP w).integrable_mul (W1p.memLp_value d)
  have hlin : ∫ z, c z * U z = (∫ z, c z * W z) + ∫ z, c z * D z := by
    refine (integral_congr_ae (hud.mono fun z hz ↦ ?_)).trans (integral_add hcW hcD)
    simp only at hz ⊢
    rw [hz, mul_add]
  -- The potential term.
  have hpot : ∫ z, hQ' z * (Real.exp (2 * U z) - 1 - 2 * U z) =
      (∫ z, hQ' z * (Real.exp (2 * W z) - 1 - 2 * W z)) +
        2 * (∫ z, hQ' z * ((Real.exp (2 * W z) - 1) * D z)) +
        ∫ z, hQ' z * Real.exp (2 * W z) * (Real.exp (2 * D z) - 1 - 2 * D z) := by
    have hAB : Integrable fun z ↦ hQ' z * (Real.exp (2 * U z) - 1 - 2 * U z) -
        hQ' z * (Real.exp (2 * W z) - 1 - 2 * W z) := hA.sub hB
    have hC2 : Integrable fun z ↦ 2 * (hQ' z * ((Real.exp (2 * W z) - 1) * D z)) :=
      hC.const_mul 2
    rw [integral_congr_ae hexpand, integral_sub hAB hC2, integral_sub hA hB, integral_const_mul]
    ring
  -- The Euler–Lagrange equation of `w`, tested against `d`.
  have hEL := inner_gradient_add_integral_reducedSource_mul_eq_zero hP hw d
  -- The defect of `w` in the equation of `Q`.
  have hres : ∫ z, (reducedSource Q W z - reducedSource P W z) * D z =
      (∫ z, hQ' z * ((Real.exp (2 * W z) - 1) * D z)) / 8 + (∫ z, c z * D z) -
        ∫ z, reducedSource P W z * D z := by
    have hC8 : Integrable fun z ↦ hQ' z * ((Real.exp (2 * W z) - 1) * D z) / 8 + c z * D z :=
      (hC.div_const 8).add hcD
    rw [← integral_div, ← integral_add (hC.div_const 8) hcD, ← integral_sub hC8 hPD]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    simp only [reducedSource_eq_add (P := Q), hQ', c]
    ring
  rw [hres]
  nlinarith [hgrad, hlin, hpot, hEL, hu]

/-- **Stability of the minimizer of Taubes's functional.** Let `P` and `Q` have degree at least
one, let `w ∈ H¹(ℂ)` minimize Taubes's functional `I_P` and let `u ∈ H¹(ℂ)` satisfy
`I_Q(u) ≤ I_Q(w)`, for instance a minimizer of `I_Q`. Write `d = u - w`, `h_Q = ‖Q‖² / (1 + ‖Q‖²)`
and `S_P(w)`, `S_Q(w)` for the sources of the reduced equations of `P` and `Q` at `w`
(`TauCeti.Vortex.reducedSource`). Then

`‖∇d‖₂² / 2 + (1 / 16) ∫ h_Q exp (2w) (exp (2d) - 1 - 2d) ≤ -∫ (S_Q(w) - S_P(w)) d`.

The right side is controlled by the defect `S_Q(w) - S_P(w)` of `w` as a weak solution of the
equation of `Q`. The proof expands `I_Q(w + d)` exactly, using
`exp (2(w + d)) - 1 - 2(w + d) = (exp (2w) - 1 - 2w) + 2 (exp (2w) - 1) d +
exp (2w) (exp (2d) - 1 - 2d)`, and removes the first variation with the weak Euler–Lagrange
equation of `w` (`TauCeti.Vortex.inner_gradient_add_integral_reducedSource_mul_eq_zero`). -/
theorem norm_gradient_sub_sq_div_two_add_integral_div_sixteen_le {Q : Polynomial ℂ}
    (hP : 0 < P.natDegree) (hQ : 0 < Q.natDegree) {w u : W1p (volume : Measure ℂ) ⊤ 2}
    (hw : ∀ v, sobolevReducedFunctional P w ≤ sobolevReducedFunctional P v)
    (hu : sobolevReducedFunctional Q u ≤ sobolevReducedFunctional Q w) :
    ‖W1p.gradient (u - w)‖ ^ 2 / 2 +
        (∫ z, backgroundWeight (Q.eval ·) z * Real.exp (2 * W1p.value w z) *
          (Real.exp (2 * W1p.value (u - w) z) - 1 - 2 * W1p.value (u - w) z)) / 16 ≤
      -∫ z, (reducedSource Q (W1p.value w) z - reducedSource P (W1p.value w) z) *
        W1p.value (u - w) z :=
  (integrable_and_stability hP hQ hw hu).2

/-- **Uniqueness of the minimizer of Taubes's functional.** For a complex polynomial `P` of degree
at least one, Taubes's functional `TauCeti.Vortex.sobolevReducedFunctional P` has at most one
minimizer on `H¹(ℂ)`. Together with
`TauCeti.Vortex.exists_forall_sobolevReducedFunctional_le` it has exactly one.

By `TauCeti.Vortex.norm_gradient_sub_sq_div_two_add_integral_div_sixteen_le` with `Q = P`, the
difference `d` of two minimizers has `∇d = 0` and `h exp (2w) (exp (2d) - 1 - 2d) = 0` almost
everywhere. Since `h` vanishes only at the finitely many roots of `P` and `exp (2t) - 1 - 2t`
vanishes only at `t = 0`, `d = 0`. -/
theorem eq_of_forall_sobolevReducedFunctional_le (hm : 0 < P.natDegree)
    {u w : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ v, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v)
    (hw : ∀ v, sobolevReducedFunctional P w ≤ sobolevReducedFunctional P v) : u = w := by
  obtain ⟨hint, hle⟩ := integrable_and_stability hm hm hw (hu w)
  set d := u - w
  set F : ℂ → ℝ := fun z ↦ backgroundWeight (P.eval ·) z * Real.exp (2 * W1p.value w z) *
    (Real.exp (2 * W1p.value d z) - 1 - 2 * W1p.value d z)
  have hF0 (z : ℂ) : 0 ≤ F z := stability_integrand_nonneg _ _ _ z
  simp only [sub_self, zero_mul, integral_zero, neg_zero] at hle
  have hIF : 0 ≤ ∫ z, F z := integral_nonneg hF0
  have hgrad : ‖W1p.gradient d‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖W1p.gradient d‖]
  have hF : F =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z ↦ hF0 z) hint).1 (by nlinarith)
  -- The roots of `P` form a null set, off which `h > 0`.
  have hroots : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ {z | P.IsRoot z} :=
    measure_eq_zero_iff_ae_notMem.1
      ((Polynomial.finite_setOfPred_isRoot (Polynomial.ne_zero_of_natDegree_gt hm)).measure_zero
        volume)
  have hval : W1p.value d = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ]
    filter_upwards [hF, hroots] with z hz hzr
    simp only [Pi.zero_apply, F] at hz ⊢
    have hP0 : P.eval z ≠ 0 := hzr
    have hh : 0 < backgroundWeight (P.eval ·) z := by
      rw [backgroundWeight_def]
      have := norm_pos_iff.2 hP0
      positivity
    have hψ : Real.exp (2 * W1p.value d z) - 1 - 2 * W1p.value d z = 0 := by
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h (mul_pos hh (Real.exp_pos _)).ne'
      · exact h
    by_contra hne
    have := Real.add_one_lt_exp (x := 2 * W1p.value d z) (by simpa using hne)
    linarith
  have hd : d = 0 := by
    rw [← norm_eq_zero, ← sq_eq_zero_iff, W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq, hval,
      hgrad, norm_zero]
    norm_num
  exact sub_eq_zero.1 hd

/-! ### Polynomials with moving roots -/

section Roots

open Polynomial

variable {ι : Type*} [Fintype ι]

/-- **Uniform decay of the linear coefficient.** For roots in a fixed disc, the coefficient
`2 ‖P'‖² / (1 + ‖P‖²)² - (1 + ‖P‖²)⁻¹ / 8` of the linear term of Taubes's functional of
`P = ∏ i, (X - a i)` is bounded by `K (1 + ‖z‖)⁻²`, with `K` independent of the roots. -/
private theorem exists_abs_linearCoeff_le [Nonempty ι] (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : ι → ℂ, (∀ i, ‖a i‖ ≤ ρ) → ∀ z : ℂ,
      |2 * ‖(∏ i, (X - C (a i))).derivative.eval z‖ ^ 2 /
          (1 + ‖(∏ i, (X - C (a i))).eval z‖ ^ 2) ^ 2 -
        (1 + ‖(∏ i, (X - C (a i))).eval z‖ ^ 2)⁻¹ / 8| ≤ K / (1 + ‖z‖) ^ 2 := by
  classical
  set n := Fintype.card ι
  have hn : 1 ≤ n := Fintype.card_pos
  set R := 2 * ρ + 2
  set K₁ := 2 * ((n : ℝ) * (R + ρ) ^ (n - 1)) ^ 2 + 1
  refine ⟨4 * (8 * (n : ℝ) ^ 2 + 1) + K₁ * (1 + R) ^ 2, by positivity, fun a ha z ↦ ?_⟩
  set p := ∏ i, (z - a i)
  set q := ∑ i, ∏ j ∈ Finset.univ.erase i, (z - a j)
  simp only [derivative_prod_finset, derivative_sub, derivative_X, derivative_C, sub_zero,
    mul_one, eval_finsetSum, eval_prod, eval_sub, eval_X, eval_C]
  -- `simp only` produced the unfolded product and sum; restate the goal through `p` and `q`.
  change |2 * ‖q‖ ^ 2 / (1 + ‖p‖ ^ 2) ^ 2 - (1 + ‖p‖ ^ 2)⁻¹ / 8| ≤ _
  have habs : |2 * ‖q‖ ^ 2 / (1 + ‖p‖ ^ 2) ^ 2 - (1 + ‖p‖ ^ 2)⁻¹ / 8| ≤
      2 * ‖q‖ ^ 2 / (1 + ‖p‖ ^ 2) ^ 2 + (1 + ‖p‖ ^ 2)⁻¹ / 8 := by
    refine abs_sub_le_iff.2 ⟨?_, ?_⟩ <;>
    · have : 0 ≤ 2 * ‖q‖ ^ 2 / (1 + ‖p‖ ^ 2) ^ 2 := by positivity
      have : 0 ≤ (1 + ‖p‖ ^ 2)⁻¹ / 8 := by positivity
      linarith
  refine habs.trans ?_
  have hz1 : 0 < 1 + ‖z‖ := by positivity
  rcases lt_or_ge ‖z‖ R with hzR | hzR
  · -- Inside the disc of radius `R` everything is bounded.
    have hfac (j : ι) : ‖z - a j‖ ≤ R + ρ :=
      (norm_sub_le _ _).trans (add_le_add hzR.le (ha j))
    have hq : ‖q‖ ≤ n * (R + ρ) ^ (n - 1) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i, ‖∏ j ∈ Finset.univ.erase i, (z - a j)‖
          ≤ ∑ _i : ι, (R + ρ) ^ (n - 1) := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            rw [norm_prod]
            calc ∏ j ∈ Finset.univ.erase i, ‖z - a j‖
                ≤ ∏ _j ∈ Finset.univ.erase i, (R + ρ) :=
                  Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun j _ ↦ hfac j
              _ = (R + ρ) ^ (n - 1) := by
                rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
                  Finset.card_univ]
        _ = n * (R + ρ) ^ (n - 1) := by simp [n]
    have h1 : 2 * ‖q‖ ^ 2 / (1 + ‖p‖ ^ 2) ^ 2 ≤ 2 * ((n : ℝ) * (R + ρ) ^ (n - 1)) ^ 2 := by
      have hpp : 1 ≤ (1 + ‖p‖ ^ 2) ^ 2 := one_le_pow₀ (by nlinarith [sq_nonneg ‖p‖])
      rw [div_le_iff₀ (by positivity)]
      have : ‖q‖ ^ 2 ≤ ((n : ℝ) * (R + ρ) ^ (n - 1)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hq 2
      nlinarith [sq_nonneg ‖q‖]
    have h2 : (1 + ‖p‖ ^ 2)⁻¹ / 8 ≤ 1 := by
      have : (1 + ‖p‖ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ‖p‖])
      linarith
    have h3 : K₁ ≤ K₁ * (1 + R) ^ 2 / (1 + ‖z‖) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : (1 + ‖z‖) ^ 2 ≤ (1 + R) ^ 2 := pow_le_pow_left₀ hz1.le (by linarith) 2
      have : 0 ≤ K₁ := by positivity
      nlinarith
    calc 2 * ‖q‖ ^ 2 / (1 + ‖p‖ ^ 2) ^ 2 + (1 + ‖p‖ ^ 2)⁻¹ / 8 ≤ K₁ := by
          simp only [K₁]; linarith
      _ ≤ K₁ * (1 + R) ^ 2 / (1 + ‖z‖) ^ 2 := h3
      _ ≤ _ := by
          gcongr
          have : 0 ≤ 4 * (8 * (n : ℝ) ^ 2 + 1) := by positivity
          linarith
  · -- Outside it, `‖p‖ ≥ ‖z‖ / 2 ≥ 1` and `‖q‖ ≤ 2 n ‖p‖ / ‖z‖`.
    have hzpos : 0 < ‖z‖ := by linarith
    have hfac (j : ι) : ‖z‖ / 2 ≤ ‖z - a j‖ := by
      have := norm_sub_norm_le z (a j)
      linarith [ha j]
    have hp : ‖z‖ / 2 ≤ ‖p‖ := by
      rw [norm_prod]
      calc ‖z‖ / 2 ≤ (‖z‖ / 2) ^ n := le_self_pow₀ (by linarith) (by omega)
        _ = ∏ _j : ι, ‖z‖ / 2 := by rw [Finset.prod_const, Finset.card_univ]
        _ ≤ ∏ j, ‖z - a j‖ :=
          Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun j _ ↦ hfac j
    have hppos : 0 < ‖p‖ := lt_of_lt_of_le (by positivity) hp
    have hq : ‖q‖ ≤ n * (2 * ‖p‖ / ‖z‖) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i, ‖∏ j ∈ Finset.univ.erase i, (z - a j)‖ ≤ ∑ _i : ι, 2 * ‖p‖ / ‖z‖ := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            have hmul : ‖z - a i‖ * ‖∏ j ∈ Finset.univ.erase i, (z - a j)‖ = ‖p‖ := by
              rw [← norm_mul, Finset.mul_prod_erase _ (fun j ↦ z - a j) (Finset.mem_univ i)]
            rw [le_div_iff₀ hzpos]
            nlinarith [hfac i, norm_nonneg (∏ j ∈ Finset.univ.erase i, (z - a j))]
        _ = n * (2 * ‖p‖ / ‖z‖) := by simp [n]
    have hz2 : (1 + ‖z‖) ^ 2 ≤ 4 * ‖z‖ ^ 2 := by nlinarith
    have h1 : 2 * ‖q‖ ^ 2 / (1 + ‖p‖ ^ 2) ^ 2 ≤ 8 * (n : ℝ) ^ 2 / ‖z‖ ^ 2 := by
      have hq2 : ‖q‖ ^ 2 ≤ 4 * (n : ℝ) ^ 2 * ‖p‖ ^ 2 / ‖z‖ ^ 2 := by
        calc ‖q‖ ^ 2 ≤ (n * (2 * ‖p‖ / ‖z‖)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hq 2
          _ = 4 * (n : ℝ) ^ 2 * ‖p‖ ^ 2 / ‖z‖ ^ 2 := by field_simp; ring
      have hpp : ‖p‖ ^ 2 ≤ (1 + ‖p‖ ^ 2) ^ 2 := by nlinarith [sq_nonneg ‖p‖]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      rw [le_div_iff₀ (by positivity)] at hq2
      nlinarith [sq_nonneg (n : ℝ), sq_nonneg ‖z‖]
    have h2 : (1 + ‖p‖ ^ 2)⁻¹ / 8 ≤ 1 / ‖z‖ ^ 2 := by
      have : ‖z‖ ^ 2 ≤ 8 * (1 + ‖p‖ ^ 2) := by nlinarith
      rw [inv_div_left, ← one_div]
      exact one_div_le_one_div_of_le (by positivity) this
    calc 2 * ‖q‖ ^ 2 / (1 + ‖p‖ ^ 2) ^ 2 + (1 + ‖p‖ ^ 2)⁻¹ / 8
        ≤ (8 * (n : ℝ) ^ 2 + 1) / ‖z‖ ^ 2 := by rw [add_div]; linarith
      _ ≤ 4 * (8 * (n : ℝ) ^ 2 + 1) / (1 + ‖z‖) ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [sq_nonneg (n : ℝ)]
      _ ≤ _ := by
          gcongr
          have : 0 ≤ K₁ * (1 + R) ^ 2 := by positivity
          linarith

/-- The elementary bound behind the domination of the difference of two sources:
`|(x e / 8 + c) - (y e / 8 + c')| ≤ |e| / 8 + 2B` for `x, y ∈ [0, 1]` and `|c|, |c'| ≤ B`. -/
private theorem abs_sub_add_sub_le {x y e c c' B : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) (hc : |c| ≤ B) (hc' : |c'| ≤ B) :
    |x * e / 8 + c - (y * e / 8 + c')| ≤ |e| / 8 + 2 * B := by
  have hxy : |x - y| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have h1 : |(x - y) * e / 8| ≤ |e| / 8 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) hxy) (by norm_num)
  calc |x * e / 8 + c - (y * e / 8 + c')| = |(x - y) * e / 8 + c - c'| := by ring_nf
    _ ≤ |(x - y) * e / 8 + c| + |c'| := abs_sub _ _
    _ ≤ |(x - y) * e / 8| + |c| + |c'| := by gcongr; exact abs_add_le _ _
    _ ≤ |e| / 8 + 2 * B := by linarith

/-- **Convergence of the sources.** For a fixed `w ∈ H¹(ℂ)`, the source of the reduced equation of
`∏ i, (X - a i)` at `w` converges in `L²` as the roots `a` converge: the coefficients converge
pointwise, and they are dominated uniformly by `TauCeti.Vortex.exists_abs_linearCoeff_le`. -/
private theorem tendsto_integral_reducedSource_sub_sq [Nonempty ι]
    (w : W1p (volume : Measure ℂ) ⊤ 2) (a₀ : ι → ℂ) :
    Tendsto (fun a : ι → ℂ ↦ ∫ z, (reducedSource (∏ i, (X - C (a i))) (W1p.value w) z -
      reducedSource (∏ i, (X - C (a₀ i))) (W1p.value w) z) ^ 2) (𝓝 a₀) (𝓝 0) := by
  classical
  set W : ℂ → ℝ := ⇑(W1p.value w)
  obtain ⟨K, -, hKb⟩ := exists_abs_linearCoeff_le (ι := ι) (‖a₀‖ + 1) (by positivity)
  have hexp := W1p.memLp_exp_two_mul_value_sub_one volume Complex.finrank_real_complex w
  set bound : ℂ → ℝ := fun z ↦
    2 * ((Real.exp (2 * W z) - 1) ^ 2 / 64) + 2 * (4 * K ^ 2 * (1 + ‖z‖) ^ (-4 : ℝ))
  have hbound : Integrable bound := by
    have hsq := (memLp_two_iff_integrable_sq hexp.aestronglyMeasurable).1 hexp
    refine ((hsq.div_const 64).const_mul 2).add
      (((integrable_one_add_norm ?_).const_mul (4 * K ^ 2)).const_mul 2)
    simp [Complex.finrank_real_complex]
    norm_num
  suffices h : Tendsto (fun a : ι → ℂ ↦ ∫ z, (reducedSource (∏ i, (X - C (a i))) W z -
      reducedSource (∏ i, (X - C (a₀ i))) W z) ^ 2) (𝓝 a₀) (𝓝 (∫ _z : ℂ, (0 : ℝ))) by
    simpa only [integral_zero] using h
  refine tendsto_integral_filter_of_dominated_convergence bound
    (Eventually.of_forall fun a ↦ (((memLp_reducedSource (natDegree_prod_X_sub_C_pos a) w).sub
      (memLp_reducedSource (natDegree_prod_X_sub_C_pos a₀) w)).aestronglyMeasurable.pow 2))
    ?_ hbound (ae_of_all _ fun z ↦ ?_)
  · -- The uniform bound, for roots within distance one of `a₀`.
    filter_upwards [Metric.ball_mem_nhds a₀ one_pos] with a ha
    refine ae_of_all _ fun z ↦ ?_
    have hroots (b : ι → ℂ) (hb : dist b a₀ < 1) (i : ι) : ‖b i‖ ≤ ‖a₀‖ + 1 := by
      have h1 : ‖b i - a₀ i‖ ≤ ‖b - a₀‖ := norm_le_pi_norm (b - a₀) i
      have h2 : ‖a₀ i‖ ≤ ‖a₀‖ := norm_le_pi_norm a₀ i
      rw [dist_eq_norm] at hb
      have := norm_le_insert' (b i) (a₀ i)
      linarith
    have hb := hKb a (hroots a ha) z
    have hb₀ := hKb a₀ (hroots a₀ (dist_self a₀ ▸ one_pos)) z
    have hdiff : |reducedSource (∏ i, (X - C (a i))) W z -
        reducedSource (∏ i, (X - C (a₀ i))) W z| ≤
        |Real.exp (2 * W z) - 1| / 8 + 2 * (K / (1 + ‖z‖) ^ 2) := by
      rw [reducedSource_eq_add, reducedSource_eq_add]
      exact abs_sub_add_sub_le (backgroundWeight_nonneg _ z) (backgroundWeight_lt_one _ z).le
        (backgroundWeight_nonneg _ z) (backgroundWeight_lt_one _ z).le hb hb₀
    have hz4 : (1 + ‖z‖) ^ (-4 : ℝ) = ((1 + ‖z‖) ^ 2)⁻¹ ^ 2 := by
      rw [Real.rpow_neg (by positivity), ← inv_pow, ← pow_mul]
      norm_num
    rw [Real.norm_eq_abs, abs_pow, sq_abs]
    calc (reducedSource (∏ i, (X - C (a i))) W z - reducedSource (∏ i, (X - C (a₀ i))) W z) ^ 2
        ≤ (|Real.exp (2 * W z) - 1| / 8 + 2 * (K / (1 + ‖z‖) ^ 2)) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hdiff 2
      _ ≤ bound z := by
          simp only [bound, hz4]
          rw [div_eq_mul_inv K]
          nlinarith [sq_nonneg (|Real.exp (2 * W z) - 1| / 8 - 2 * (K * ((1 + ‖z‖) ^ 2)⁻¹)),
            sq_abs (Real.exp (2 * W z) - 1)]
  · -- Pointwise convergence: the coefficients depend continuously on the roots.
    have hcont : Continuous fun a : ι → ℂ ↦ reducedSource (∏ i, (X - C (a i))) W z := by
      simp only [reducedSource_eq_add, backgroundWeight_def, derivative_prod_finset,
        derivative_sub, derivative_X, derivative_C, sub_zero, mul_one, eval_finsetSum, eval_prod,
        eval_sub, eval_X, eval_C]
      fun_prop (disch := intro; positivity)
    have h := ((hcont.tendsto a₀).sub
      (tendsto_const_nhds (x := reducedSource (∏ i, (X - C (a₀ i))) W z))).pow 2
    simpa using h

end Roots

/-! ### Convergence of minimizers -/

/-- The algebra of the uniform `L²` bound: if `G² / 2 + E / 16 ≤ X` and
`X² ≤ 2 (2 + C G) (E / κ) + (2 + C G)² S`, then `X` is bounded in terms of `C`, `κ` and `S`. -/
private theorem le_of_le_of_sq_le {X G E C κ S : ℝ} (hX : 0 ≤ X) (hG : 0 ≤ G) (hE : 0 ≤ E)
    (hC : 0 ≤ C) (hκ : 0 < κ) (hS : 0 ≤ S) (h1 : G ^ 2 / 2 + E / 16 ≤ X)
    (h2 : X ^ 2 ≤ 2 * (2 + C * G) * (E / κ) + (2 + C * G) ^ 2 * S) :
    X ≤ 1 + 2 * (64 / κ + 2048 * C ^ 2 / κ ^ 2 + 4 * C ^ 2 * S) + 16 * S := by
  have hG0 := sq_nonneg G
  have hE16 : E / κ ≤ 16 * X / κ := div_le_div_of_nonneg_right (by linarith) hκ.le
  have hG2 : G ^ 2 ≤ 2 * X := by linarith
  -- `32 C G X / κ ≤ X² / 4 + (32 C G / κ)²`.
  have hamgm : 32 * C * G * X / κ ≤ X ^ 2 / 4 + 2048 * C ^ 2 / κ ^ 2 * X := by
    have := sq_nonneg (X / 2 - 32 * C * G / κ)
    have hb : (32 * C * G / κ) ^ 2 ≤ 2048 * C ^ 2 / κ ^ 2 * X := by
      rw [div_pow, mul_pow, mul_pow, div_mul_eq_mul_div,
        div_le_div_iff_of_pos_right (by positivity)]
      nlinarith [sq_nonneg C]
    have : 32 * C * G * X / κ = 2 * (X / 2) * (32 * C * G / κ) := by ring
    nlinarith
  have hT1 : 2 * (2 + C * G) * (E / κ) ≤ 64 / κ * X + (X ^ 2 / 4 + 2048 * C ^ 2 / κ ^ 2 * X) := by
    calc 2 * (2 + C * G) * (E / κ) ≤ 2 * (2 + C * G) * (16 * X / κ) := by gcongr
      _ = 64 / κ * X + 32 * C * G * X / κ := by ring
      _ ≤ _ := by linarith
  have hT2 : (2 + C * G) ^ 2 * S ≤ 8 * S + 4 * C ^ 2 * S * X := by
    have : (2 + C * G) ^ 2 ≤ 8 + 2 * C ^ 2 * G ^ 2 := by nlinarith [sq_nonneg (2 - C * G)]
    have : C ^ 2 * G ^ 2 ≤ C ^ 2 * (2 * X) := mul_le_mul_of_nonneg_left hG2 (sq_nonneg C)
    nlinarith
  set a := 64 / κ + 2048 * C ^ 2 / κ ^ 2 + 4 * C ^ 2 * S
  have ha : 0 ≤ a := by positivity
  have : 3 * X ^ 2 / 4 ≤ a * X + 8 * S := by simp only [a]; nlinarith
  rcases le_total X 1 with hX1 | hX1
  · linarith
  · nlinarith

/-- The algebra of the smallness: if `X ≤ B`, `G² / 2 + E / 16 ≤ τ X`, `2 τ B C² ≤ 1` and
`X² ≤ 2 (2 + C G) (E / κ) + (2 + C G)² S`, then `X² + G² ≤ 96 τ B / κ + 9 S + 2 τ B`. -/
private theorem sq_add_sq_le {X G E C κ S τ B : ℝ} (hG : 0 ≤ G) (hE : 0 ≤ E)
    (hC : 0 ≤ C) (hκ : 0 < κ) (hS : 0 ≤ S) (hτ : 0 ≤ τ) (hXB : X ≤ B)
    (h1 : G ^ 2 / 2 + E / 16 ≤ τ * X) (hτB : 2 * τ * B * C ^ 2 ≤ 1)
    (h2 : X ^ 2 ≤ 2 * (2 + C * G) * (E / κ) + (2 + C * G) ^ 2 * S) :
    X ^ 2 + G ^ 2 ≤ 96 * τ * B / κ + 9 * S + 2 * τ * B := by
  have hτX : τ * X ≤ τ * B := mul_le_mul_of_nonneg_left hXB hτ
  have hG0 := sq_nonneg G
  have hG2 : G ^ 2 ≤ 2 * τ * B := by linarith
  have hE16 : E ≤ 16 * τ * B := by linarith
  have hCG : C * G ≤ 1 := by
    have : (C * G) ^ 2 ≤ 1 := by
      rw [mul_pow]
      calc C ^ 2 * G ^ 2 ≤ C ^ 2 * (2 * τ * B) := mul_le_mul_of_nonneg_left hG2 (sq_nonneg C)
        _ ≤ 1 := by linarith
    nlinarith [mul_nonneg hC hG]
  have hk : 2 + C * G ≤ 3 := by linarith
  have : 0 ≤ 2 + C * G := by positivity
  have hEκ : E / κ ≤ 16 * τ * B / κ := div_le_div_of_nonneg_right hE16 hκ.le
  have : 2 * (2 + C * G) * (E / κ) ≤ 2 * 3 * (16 * τ * B / κ) := by
    gcongr
  have : (2 + C * G) ^ 2 * S ≤ 3 ^ 2 * S := by gcongr
  have : 2 * 3 * (16 * τ * B / κ) = 96 * τ * B / κ := by ring
  nlinarith

/-- The choice of the tolerance `τ` in the convergence of minimizers. -/
private theorem exists_pos_mul_le {B C a η : ℝ} (hB : 0 ≤ B) (ha : 0 ≤ a) (hη : 0 < η) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ 2 * τ * B * C ^ 2 ≤ 1 ∧ τ * a ≤ η ^ 2 / 4 := by
  set τ := min (min 1 (1 / (2 * B * C ^ 2 + 1))) (η ^ 2 / (4 * a + 1))
  have hτ : 0 < τ := by positivity
  refine ⟨τ, hτ, (min_le_left _ _).trans (min_le_left _ _), ?_, ?_⟩
  · have h : τ ≤ 1 / (2 * B * C ^ 2 + 1) := (min_le_left _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith [mul_nonneg (mul_nonneg hτ.le hB) (sq_nonneg C)]
  · have h : τ ≤ η ^ 2 / (4 * a + 1) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith

/-- The stability inequality with the `L²` distance of the sources bounded by `τ`: by the
Cauchy–Schwarz inequality, `‖∇d‖₂² / 2 + E / 16 ≤ τ ‖d‖₂` for `d = u - w`. -/
private theorem stability_le_mul_norm {Q : Polynomial ℂ} (hP : 0 < P.natDegree)
    (hQ : 0 < Q.natDegree) {w u : W1p (volume : Measure ℂ) ⊤ 2}
    (hw : ∀ v, sobolevReducedFunctional P w ≤ sobolevReducedFunctional P v)
    (hu : sobolevReducedFunctional Q u ≤ sobolevReducedFunctional Q w) {τ : ℝ} (hτ : 0 ≤ τ)
    (hR : ∫ z, (reducedSource Q (W1p.value w) z - reducedSource P (W1p.value w) z) ^ 2 ≤ τ ^ 2) :
    ‖W1p.gradient (u - w)‖ ^ 2 / 2 +
        (∫ z, backgroundWeight (Q.eval ·) z * Real.exp (2 * W1p.value w z) *
          (Real.exp (2 * W1p.value (u - w) z) - 1 - 2 * W1p.value (u - w) z)) / 16 ≤
      τ * ‖W1p.value (u - w)‖ := by
  set W : ℂ → ℝ := ⇑(W1p.value w)
  set F : ℂ → ℝ := fun z ↦ backgroundWeight (Q.eval ·) z * Real.exp (2 * W z) *
    (Real.exp (2 * W1p.value (u - w) z) - 1 - 2 * W1p.value (u - w) z)
  have hF0 (z : ℂ) : 0 ≤ F z := stability_integrand_nonneg _ _ _ z
  have hE0 : 0 ≤ ∫ z, F z := integral_nonneg hF0
  have hle := (integrable_and_stability hP hQ hw hu).2
  have hr : MemLp (fun z ↦ reducedSource Q W z - reducedSource P W z) 2 :=
    (memLp_reducedSource hQ w).sub (memLp_reducedSource hP w)
  have hcs := sq_integral_mul_le_integral_sq_mul_integral_sq hr (W1p.memLp_value (u - w))
  have hd : ∫ z, W1p.value (u - w) z ^ 2 = ‖W1p.value (u - w)‖ ^ 2 := by
    rw [← W1p.integral_value_sq_eq_norm_value_sq]
    simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ]
  rw [hd] at hcs
  set L := ‖W1p.gradient (u - w)‖ ^ 2 / 2 + (∫ z, F z) / 16
  set I := ∫ z, (reducedSource Q W z - reducedSource P W z) * W1p.value (u - w) z
  have hL : 0 ≤ L := by have := hE0; positivity
  have hI2 : I ^ 2 ≤ (τ * ‖W1p.value (u - w)‖) ^ 2 := by
    rw [mul_pow]
    exact hcs.trans (mul_le_mul_of_nonneg_right hR (sq_nonneg _))
  have hτX : 0 ≤ τ * ‖W1p.value (u - w)‖ := by positivity
  nlinarith

/-- The planar estimate for `d = u - w`, off the set where `‖Q‖ < δ` or `w² ≥ M²`. There the weight
`h_Q exp (2w)` is at least `κ = δ² / (1 + δ²) exp (-2M)`, so the modular `√(1 + d²) - 1` is at most
`h_Q exp (2w) (exp (2d) - 1 - 2d) / κ`, and the measure of the exceptional set is at most
`η + ‖w‖₂² / M²` by Chebyshev's inequality. -/
private theorem norm_value_sub_sq_le {Q : Polynomial ℂ} (hP : 0 < P.natDegree)
    (hQ : 0 < Q.natDegree) {w u : W1p (volume : Measure ℂ) ⊤ 2}
    (hw : ∀ v, sobolevReducedFunctional P w ≤ sobolevReducedFunctional P v)
    (hu : sobolevReducedFunctional Q u ≤ sobolevReducedFunctional Q w) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hpl : ∀ v : W1p (volume : Measure ℂ) ⊤ 2, ∀ s : Set ℂ, MeasurableSet s → volume s ≠ ∞ →
      ‖W1p.value v‖ ^ 2 ≤
        2 * (2 + C₀ * ‖W1p.gradient v‖) * (∫ z in sᶜ, (√(1 + W1p.value v z ^ 2) - 1)) +
          (2 + C₀ * ‖W1p.gradient v‖) ^ 2 * volume.real s)
    {δ M η : ℝ} (hδ : 0 < δ) (hM : 0 < M)
    (hη : volume {z | ‖Q.eval z‖ < δ} ≤ ENNReal.ofReal η) (hη0 : 0 ≤ η) :
    ‖W1p.value (u - w)‖ ^ 2 ≤
      2 * (2 + C₀ * ‖W1p.gradient (u - w)‖) *
          ((∫ z, backgroundWeight (Q.eval ·) z * Real.exp (2 * W1p.value w z) *
          (Real.exp (2 * W1p.value (u - w) z) - 1 - 2 * W1p.value (u - w) z)) /
            (δ ^ 2 / (1 + δ ^ 2) * Real.exp (-(2 * M)))) +
        (2 + C₀ * ‖W1p.gradient (u - w)‖) ^ 2 * (η + ‖W1p.value w‖ ^ 2 / M ^ 2) := by
  set W : ℂ → ℝ := ⇑(W1p.value w)
  set F : ℂ → ℝ := fun z ↦ backgroundWeight (Q.eval ·) z * Real.exp (2 * W z) *
    (Real.exp (2 * W1p.value (u - w) z) - 1 - 2 * W1p.value (u - w) z)
  have hF0 (z : ℂ) : 0 ≤ F z := stability_integrand_nonneg _ _ _ z
  have hWsq : ∫ z, W z ^ 2 = ‖W1p.value w‖ ^ 2 := by
    rw [← W1p.integral_value_sq_eq_norm_value_sq]
    simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ, W]
  have hWint : Integrable fun z ↦ W z ^ 2 :=
    (memLp_two_iff_integrable_sq (W1p.memLp_value w).aestronglyMeasurable).1 (W1p.memLp_value w)
  set κ := δ ^ 2 / (1 + δ ^ 2) * Real.exp (-(2 * M))
  have hκ : 0 < κ := by positivity
  set s₁ := {z | ‖Q.eval z‖ < δ}
  set s₂ := {z | M ^ 2 ≤ W z ^ 2}
  have hs₁ : MeasurableSet s₁ :=
    (isOpen_lt Q.continuous.norm continuous_const).measurableSet
  have hWm : Measurable W := (Lp.stronglyMeasurable (W1p.value w)).measurable
  have hs₂ : MeasurableSet s₂ := measurableSet_le measurable_const (hWm.pow_const 2)
  have hs₂fin : volume s₂ < ∞ := by
    have h := hWint.measure_norm_ge_lt_top (ε := M ^ 2) (by positivity)
    simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using h
  have hs₂real : volume.real s₂ ≤ ‖W1p.value w‖ ^ 2 / M ^ 2 := by
    have h := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun z ↦ sq_nonneg (W z)) hWint
      (M ^ 2)
    rw [hWsq] at h
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hs₁fin : volume s₁ < ∞ := hη.trans_lt ENNReal.ofReal_lt_top
  have hs₁real : volume.real s₁ ≤ η := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hη0 hη
  have hs : MeasurableSet (s₁ ∪ s₂) := hs₁.union hs₂
  have hsfin : volume (s₁ ∪ s₂) ≠ ∞ :=
    (measure_union_le s₁ s₂).trans_lt (ENNReal.add_lt_top.2 ⟨hs₁fin, hs₂fin⟩) |>.ne
  have hsreal : volume.real (s₁ ∪ s₂) ≤ η + ‖W1p.value w‖ ^ 2 / M ^ 2 :=
    (measureReal_union_le s₁ s₂).trans (add_le_add hs₁real hs₂real)
  have h := hpl (u - w) (s₁ ∪ s₂) hs hsfin
  simp only [TopologicalSpace.Opens.coe_top] at h
  -- Off `s₁ ∪ s₂`, the modular is at most `F / κ`.
  have hFint : Integrable F := (integrable_and_stability hP hQ hw hu).1
  have hmod : ∫ z in (s₁ ∪ s₂)ᶜ, (√(1 + W1p.value (u - w) z ^ 2) - 1) ≤
      (∫ z, F z) / κ := by
    calc ∫ z in (s₁ ∪ s₂)ᶜ, (√(1 + W1p.value (u - w) z ^ 2) - 1)
        ≤ ∫ z in (s₁ ∪ s₂)ᶜ, F z / κ := by
          refine integral_mono_of_nonneg (ae_of_all _ fun z ↦
            sub_nonneg.2 (Real.one_le_sqrt_one_add_sq _)) (hFint.div_const κ).restrict ?_
          filter_upwards [ae_restrict_mem hs.compl] with z hz
          simp only [mem_compl_iff, mem_union, not_or, mem_ofPred_eq, not_lt, not_le, s₁,
            s₂] at hz
          have hh : δ ^ 2 / (1 + δ ^ 2) ≤ backgroundWeight (Q.eval ·) z := by
            rw [backgroundWeight_def, div_le_div_iff₀ (by positivity) (by positivity)]
            have : δ ^ 2 ≤ ‖Q.eval z‖ ^ 2 := pow_le_pow_left₀ hδ.le hz.1 2
            nlinarith
          have hWM : -M < W z := (abs_lt.1 (abs_lt_of_sq_lt_sq hz.2 hM.le)).1
          have he : Real.exp (-(2 * M)) ≤ Real.exp (2 * W z) := Real.exp_le_exp.2 (by linarith)
          have hκF : κ * (Real.exp (2 * W1p.value (u - w) z) - 1 - 2 * W1p.value (u - w) z)
              ≤ F z := by
            simp only [F, κ]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul hh he (by positivity) (backgroundWeight_nonneg _ z))
              (Real.exp_two_mul_sub_one_sub_two_mul_nonneg _)
          rw [le_div_iff₀ hκ]
          have := Real.sqrt_one_add_sq_sub_one_le_exp_two_mul_sub_one_sub_two_mul
            (W1p.value (u - w) z)
          nlinarith
      _ ≤ ∫ z, F z / κ :=
          setIntegral_le_integral (hFint.div_const κ) (ae_of_all _ fun z ↦
            div_nonneg (hF0 z) hκ.le)
      _ = (∫ z, F z) / κ := integral_div κ _
  calc ‖W1p.value (u - w)‖ ^ 2
      ≤ 2 * (2 + C₀ * ‖W1p.gradient (u - w)‖) *
          (∫ z in (s₁ ∪ s₂)ᶜ, (√(1 + W1p.value (u - w) z ^ 2) - 1)) +
        (2 + C₀ * ‖W1p.gradient (u - w)‖) ^ 2 * volume.real (s₁ ∪ s₂) := h
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hmod (by positivity))
        (mul_le_mul_of_nonneg_left hsreal (by positivity))

/-- **Convergence of minimizers.** Let `w` minimize Taubes's functional `I_P`, and let `u x`
satisfy `I_(Q x)(u x) ≤ I_(Q x)(w)` along a filter. If the sources `S_(Q x)(w)` converge to
`S_P(w)` in `L²` and the sublevel sets `{‖Q x‖ < δ}` have measure tending to zero with `δ`,
uniformly in `x`, then `u x → w` in `H¹(ℂ)`.

By `TauCeti.Vortex.norm_gradient_sub_sq_div_two_add_integral_div_sixteen_le` and the
Cauchy–Schwarz inequality, `d = u x - w` satisfies `‖∇d‖₂² / 2 + E / 16 ≤ τ ‖d‖₂`, where `τ` is
the `L²` distance of the sources and `E = ∫ h exp (2w) (exp (2d) - 1 - 2d)`. Off the set `s` where
`‖Q x‖ < δ` or `|w| ≥ M`, the weight `h exp (2w)` is at least `κ > 0`, so the planar estimate
`TauCeti.W1p.exists_norm_value_sq_le_of_finrank_eq_two` bounds `‖d‖₂²` by `E / κ` and the
measure of `s`. This first bounds `‖d‖₂`, and then makes it small. -/
theorem tendsto_of_forall_sobolevReducedFunctional_le {X : Type*} {l : Filter X}
    (hP : 0 < P.natDegree) {w : W1p (volume : Measure ℂ) ⊤ 2}
    (hw : ∀ v, sobolevReducedFunctional P w ≤ sobolevReducedFunctional P v)
    {Q : X → Polynomial ℂ} {u : X → W1p (volume : Measure ℂ) ⊤ 2}
    (hQ : ∀ x, 0 < (Q x).natDegree)
    (hu : ∀ x, sobolevReducedFunctional (Q x) (u x) ≤ sobolevReducedFunctional (Q x) w)
    (hres : Tendsto (fun x ↦ ∫ z, (reducedSource (Q x) (W1p.value w) z -
      reducedSource P (W1p.value w) z) ^ 2) l (𝓝 0))
    (hlev : ∀ η > 0, ∃ δ > 0, ∀ x, volume {z | ‖(Q x).eval z‖ < δ} ≤ ENNReal.ofReal η) :
    Tendsto u l (𝓝 w) := by
  obtain ⟨C₀, hC₀, hpl⟩ :=
    W1p.exists_norm_value_sq_le_of_finrank_eq_two (volume : Measure ℂ) Complex.finrank_real_complex
  set W : ℂ → ℝ := ⇑(W1p.value w)
  set F : X → ℂ → ℝ := fun x z ↦ backgroundWeight ((Q x).eval ·) z * Real.exp (2 * W z) *
    (Real.exp (2 * W1p.value (u x - w) z) - 1 - 2 * W1p.value (u x - w) z)
  have hF0 (x : X) (z : ℂ) : 0 ≤ F x z := stability_integrand_nonneg _ _ _ z
  have hE0 (x : X) : 0 ≤ ∫ z, F x z := integral_nonneg (hF0 x)
  -- Stage one: `‖u x - w‖` is eventually bounded.
  obtain ⟨δ₁, hδ₁, hδ₁b⟩ := hlev 1 one_pos
  set κ₁ := δ₁ ^ 2 / (1 + δ₁ ^ 2) * Real.exp (-(2 * 1))
  have hκ₁ : 0 < κ₁ := by positivity
  set S₁ := 1 + ‖W1p.value w‖ ^ 2 / 1 ^ 2
  set B := 1 + 2 * (64 / κ₁ + 2048 * C₀ ^ 2 / κ₁ ^ 2 + 4 * C₀ ^ 2 * S₁) + 16 * S₁
  have hB : 0 ≤ B := by positivity
  have hbound (x : X)
      (hR : ∫ z, (reducedSource (Q x) W z - reducedSource P W z) ^ 2 ≤ 1) :
      ‖W1p.value (u x - w)‖ ≤ B :=
    le_of_le_of_sq_le (norm_nonneg _) (norm_nonneg _) (hE0 x) hC₀ hκ₁ (by positivity)
      (by simpa using stability_le_mul_norm hP (hQ x) hw (hu x) zero_le_one (by simpa using hR))
      (norm_value_sub_sq_le hP (hQ x) hw (hu x) hC₀ hpl hδ₁ one_pos (hδ₁b x) zero_le_one)
  -- Stage two: `‖u x - w‖` is eventually small.
  rw [Metric.tendsto_nhds]
  intro η hη
  set θ := η ^ 2 / 40
  have hθ : 0 < θ := by positivity
  obtain ⟨δ, hδ, hδb⟩ := hlev (θ / 2) (by positivity)
  have hMlim : Tendsto (fun M : ℝ ↦ ‖W1p.value w‖ ^ 2 / M ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  obtain ⟨M, hM, hMθ⟩ :=
    ((eventually_ge_atTop 1).and (hMlim.eventually (eventually_le_nhds (half_pos hθ)))).exists
  set κ := δ ^ 2 / (1 + δ ^ 2) * Real.exp (-(2 * M))
  have hκ : 0 < κ := by positivity
  obtain ⟨τ, hτ, hτ1, hτC, hτη⟩ := exists_pos_mul_le hB (C := C₀)
    (by positivity : 0 ≤ 96 * B / κ + 2 * B) hη
  filter_upwards [(tendsto_order.1 hres).2 (τ ^ 2) (by positivity)] with x hx
  have hXB := hbound x (hx.le.trans (pow_le_one₀ hτ.le hτ1))
  have hsq := sq_add_sq_le (norm_nonneg _) (hE0 x) hC₀ hκ (by positivity) hτ.le hXB
    (stability_le_mul_norm hP (hQ x) hw (hu x) hτ.le hx.le) hτC
    (norm_value_sub_sq_le hP (hQ x) hw (hu x) hC₀ hpl hδ (by linarith) (hδb x) (by positivity))
  rw [dist_eq_norm, ← sq_lt_sq₀ (norm_nonneg _) hη.le,
    W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq]
  have h96 : 96 * τ * B / κ + 2 * τ * B = τ * (96 * B / κ + 2 * B) := by ring
  have : 0 < η ^ 2 := by positivity
  have hθη : θ = η ^ 2 / 40 := rfl
  linarith

/-- **The minimizer of Taubes's functional depends continuously on the zeros.** Let `ι` be a
nonempty finite type, and for every family of roots `a : ι → ℂ` let `u a ∈ H¹(ℂ)` minimize Taubes's
functional of `∏ i, (X - a i)` (`TauCeti.Vortex.sobolevReducedFunctional`). Then `a ↦ u a` is
continuous into `H¹(ℂ)`. By `TauCeti.Vortex.eq_of_forall_sobolevReducedFunctional_le` the minimizer
is unique, so this is the continuity of the correction of the background amplitude of the vortex
with zeros `a`, as a function of the zeros, in `H¹(ℂ)`.

The sources of the reduced equations converge in `L²` as the roots converge, by dominated
convergence: the coefficients `g` and `(1 + ‖P‖²)⁻¹` decay like `(1 + ‖z‖)⁻²` uniformly for roots
in a disc. The set where `‖∏ i, (z - a i)‖ < δ` has small measure for small `δ`, uniformly in the
roots, as it lies in the union of small discs about the roots. -/
theorem continuous_of_forall_sobolevReducedFunctional_le {ι : Type*} [Fintype ι] [Nonempty ι]
    {u : (ι → ℂ) → W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ a v, sobolevReducedFunctional (∏ i, (Polynomial.X - Polynomial.C (a i))) (u a) ≤
      sobolevReducedFunctional (∏ i, (Polynomial.X - Polynomial.C (a i))) v) :
    Continuous u := by
  classical
  refine continuous_iff_continuousAt.2 fun a₀ ↦ ?_
  exact tendsto_of_forall_sobolevReducedFunctional_le
    (Polynomial.natDegree_prod_X_sub_C_pos a₀) (hu a₀) Polynomial.natDegree_prod_X_sub_C_pos
    (fun a ↦ hu a (u a₀)) (tendsto_integral_reducedSource_sub_sq (u a₀) a₀)
    fun _ hη ↦ exists_volume_setOf_norm_eval_prod_lt_le hη

end TauCeti.Vortex
