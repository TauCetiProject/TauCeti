/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Reduced.Functional
import TauCeti.Analysis.PDE.Vortex.Existence
import TauCeti.Analysis.Polynomial.Monic.ProdXSubC
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.SpecialFunctions.Exp.Modular
import TauCeti.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Sobolev.Poincare.Planar
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# Continuity of the minimizer of Taubes's functional in the zeros

A plane vortex with zeros `b₁, …, bₘ` (repeated points allowed) is obtained from the minimizer
`u_b ∈ H¹(ℂ)` of Taubes's functional `TauCeti.Vortex.sobolevReducedFunctional` for the polynomial
`P_b = ∏ i, (X - bᵢ)` (`TauCeti.Vortex.exists_forall_sobolevReducedFunctional_le`), which is unique
(`TauCeti.Vortex.eq_of_forall_sobolevReducedFunctional_le`). This file proves that `u_b` depends
continuously on the roots `b` in `H¹(ℂ)`, including where roots collide
(`TauCeti.Vortex.tendsto_of_forall_sobolevReducedFunctional_le`). In particular the minimizers
form a continuous map `(ι → ℂ) → H¹(ℂ)`
(`TauCeti.Vortex.exists_continuous_forall_sobolevReducedFunctional_le`). This is the first step
from the existence of a vortex with each prescribed zero divisor towards families of vortices over
compact windows of divisors.

Write `h_b = ‖P_b‖² / (1 + ‖P_b‖²)` for the weight of the potential `φ(t) = exp (2t) - 1 - 2t`
of the functional and `q_b(v)` for the coefficient
`(exp (2v) h_b - 1) / 8 + 2 ‖P_b'‖² / (1 + ‖P_b‖²)²` of the reduced equation at `v`. Let `u`
minimize the functional for `P_b` and `u₀` for `P_a`, and put `w = u - u₀`. The proof has three
steps.

1. **Energy estimate.** The minimizer `u₀` is bounded, since it agrees with a smooth solution of
   the reduced equation tending to zero at infinity. Expanding the functional for `P_b` around
   `u₀` by `φ(s + r) = φ(s) + φ'(s) r + exp (2s) φ(r)`, minimality of `u` and the Euler–Lagrange
   equation `⟪∇u₀, ∇w⟫ + ∫ q_a(u₀) w = 0` of `u₀`, valid for every `w ∈ H¹(ℂ)` by density, give

   `‖∇w‖₂² / 2 + (1 / 16) ∫ h_b exp (2u₀) φ(w) ≤ ‖q_b(u₀) - q_a(u₀)‖₂ ‖w‖₂`.
2. **Convergence of the coefficients.** `‖q_b(u₀) - q_a(u₀)‖₂ → 0` as `b → a`, by dominated
   convergence: when the roots lie in a fixed disc, the coefficient of the linear term of the
   functional is at most a constant times `(1 + |z|)⁻²`, uniformly in the roots
   (`Polynomial.norm_eval_derivative_prod_X_sub_C_mul_le`).
3. **`L²` convergence.** Away from a set `S` of small measure around the roots of `P_a`, the
   weights `h_b` are bounded below uniformly for `b` near `a`, so the potential term of step 1
   controls the modular `∫_{Sᶜ} (√(1 + w²) - 1)`. The planar estimate
   `TauCeti.W1p.exists_norm_value_sq_le_of_finrank_eq_two`,
   `‖w‖₂² ≤ 2 (2 + C ‖∇w‖₂) ∫_{Sᶜ} (√(1 + w²) - 1) + (2 + C ‖∇w‖₂)² |S|`, then makes `‖w‖₂²` at
   most a multiple of `|S|` in the limit, and `|S|` is arbitrarily small.

## Main results

* `TauCeti.Vortex.tendsto_of_forall_sobolevReducedFunctional_le`: if the roots `a x` converge to
  `a₀`, minimizers for `∏ i, (X - a x i)` converge in `H¹(ℂ)` to the minimizer for
  `∏ i, (X - a₀ i)`.
* `TauCeti.Vortex.continuous_of_forall_sobolevReducedFunctional_le`: minimizers for roots
  depending continuously on a parameter in a first-countable space depend continuously on it.
* `TauCeti.Vortex.exists_continuous_forall_sobolevReducedFunctional_le`: the minimizer is a
  continuous function of the roots.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open _root_.MeasureTheory Set Filter Topology Polynomial
open scoped ENNReal RealInnerProductSpace

variable {P : Polynomial ℂ}

/-- The coefficient `(exp (2v) h - 1) / 8 + 2 ‖P'‖² / (1 + ‖P‖²)²` of the reduced vortex equation
at `v`, written as the coefficient `c = 2 ‖P'‖² / (1 + ‖P‖²)² - (1 + ‖P‖²)⁻¹ / 8` of the linear
term of Taubes's functional plus the derivative `h (exp (2v) - 1) / 8` of its potential, where
`h = ‖P‖² / (1 + ‖P‖²)`. -/
private def eulerCoeff (P : Polynomial ℂ) (v : ℂ → ℝ) (z : ℂ) : ℝ :=
  2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 - (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8 +
    ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * v z) - 1) / 8

private theorem eulerCoeff_eq (P : Polynomial ℂ) (v : ℂ → ℝ) (z : ℂ) :
    eulerCoeff P v z = (Real.exp (2 * v z) * (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2)) - 1) / 8 +
      2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 := by
  have : (1 : ℝ) + ‖P.eval z‖ ^ 2 ≠ 0 := by positivity
  rw [eulerCoeff]
  field_simp
  ring

/-- The weight `h = ‖P‖² / (1 + ‖P‖²)` of the potential of Taubes's functional is continuous
with values in `[0, 1]`. -/
private theorem continuous_and_nonneg_and_le_one (P : Polynomial ℂ) :
    Continuous (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2)) ∧
      (∀ z, 0 ≤ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2)) ∧
      ∀ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ≤ 1 :=
  ⟨by fun_prop (disch := intro z; positivity), fun z ↦ by positivity,
    fun z ↦ by rw [div_le_one (by positivity)]; linarith⟩

/-- **Minimality as an inequality of real numbers.** If `u` minimizes Taubes's functional and its
potential is finite at `u₀`, then the potential is finite at `u`, and the real forms of the
functional (`TauCeti.Vortex.sobolevReducedFunctional_eq_coe`) satisfy `I(u) ≤ I(u₀)`. -/
private theorem integrable_and_le_of_forall_le {u₀ u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ v, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v)
    (hpot₀ : Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u₀ z) - 1 - 2 * W1p.value u₀ z)) :
    (Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) ∧
    ‖W1p.gradient u‖ ^ 2 / 2 + (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) / 16 +
      ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z ≤
    ‖W1p.gradient u₀‖ ^ 2 / 2 + (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u₀ z) - 1 - 2 * W1p.value u₀ z)) / 16 +
      ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u₀ z := by
  have hI₀ := sobolevReducedFunctional_eq_coe hpot₀
  have hpot := sobolevReducedFunctional_ne_top_iff.mp
    ((hu u₀).trans_lt (hI₀ ▸ EReal.coe_lt_top _)).ne
  have hle := hu u₀
  rw [sobolevReducedFunctional_eq_coe hpot, hI₀, EReal.coe_le_coe_iff] at hle
  exact ⟨hpot, hle⟩

/-! ### The Euler–Lagrange equation against all of `H¹(ℂ)` -/

/-- **The weak Euler–Lagrange equation in every direction of `H¹(ℂ)`.** If `u` minimizes Taubes's
functional and the coefficient `q = eulerCoeff P u` of the reduced equation is square integrable,
then `⟪∇u, ∇w⟫ + ∫ q w = 0` for every `w ∈ H¹(ℂ)`. Both sides are continuous in `w`, and test
functions are dense in `H¹(ℂ)`. -/
private theorem inner_gradient_add_integral_mul_value_eq_zero (hm : 0 < P.natDegree)
    {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ v, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v)
    (hq : MemLp (eulerCoeff P (W1p.value u)) 2) (w : W1p (volume : Measure ℂ) ⊤ 2) :
    ⟪W1p.gradient u, W1p.gradient w⟫ + ∫ z, eulerCoeff P (W1p.value u) z * W1p.value w z = 0 := by
  set q : ℂ → ℝ := eulerCoeff P (W1p.value u)
  -- The left side is a continuous function of `w`.
  have hqr := hq.restrict ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ)
  have hlin (v : Lp ℝ 2 ((volume : Measure ℂ).restrict ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ))) :
      innerSL ℝ (hqr.toLp q) v = ∫ z, q z * v z := by
    have h := integral_congr_ae (hqr.coeFn_toLp.mono fun z hz ↦ congrArg (· * v z) hz)
    simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at h
    rw [← h, innerSL_apply_apply, L2.inner_def]
    simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ, RCLike.inner_apply,
      conj_trivial]
    exact integral_congr_ae (ae_of_all _ fun z ↦ mul_comm _ _)
  have hcont : Continuous fun v : W1p (volume : Measure ℂ) ⊤ 2 ↦
      ⟪W1p.gradient u, W1p.gradient v⟫ + ∫ z, q z * W1p.value v z := by
    simp only [← hlin, ← W1p.gradientL_apply, ← W1p.valueL_apply]
    exact (continuous_const.inner (W1p.gradientL (mu := (volume : Measure ℂ))).continuous).add
      ((innerSL ℝ (hqr.toLp q)).continuous.comp
        (W1p.valueL (mu := (volume : Measure ℂ))).continuous)
  refine (W1p.denseRange_ofTestFunctionₗ_top (mu := (volume : Measure ℂ)) (p := 2)
    ENNReal.ofNat_ne_top).induction_on w (isClosed_eq hcont continuous_const) fun φ ↦ ?_
  -- On a test function this is the Euler–Lagrange equation of `TauCeti.Vortex.EulerLagrange`.
  have hv := W1p.value_ofTestFunctionₗ_top_ae (mu := (volume : Measure ℂ)) (p := 2) φ
  have hg := W1p.gradient_ofTestFunctionₗ_top_ae (mu := (volume : Measure ℂ)) (p := 2) φ
  have hEL := integral_inner_gradient_add_integral_mul_eq_zero hm hu
    (φ.contDiff.of_le (by exact_mod_cast le_top)) φ.hasCompactSupport
  rw [L2.inner_def]
  simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ]
  rw [← hEL]
  congr 1
  · exact integral_congr_ae (hg.mono fun z hz ↦ by dsimp only; rw [hz])
  · exact integral_congr_ae (hv.mono fun z hz ↦ by
      dsimp only; rw [hz]; simp only [q, eulerCoeff_eq])

/-! ### The minimizer is bounded -/

/-- A minimizer of Taubes's functional is essentially bounded: it agrees almost everywhere with a
smooth solution of the reduced equation, which tends to zero at infinity. -/
private theorem exists_ae_abs_value_le (hm : 0 < P.natDegree) {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ v, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v) :
    ∃ B, ∀ᵐ z, |W1p.value u z| ≤ B := by
  obtain ⟨w, hw, huw, hΔ⟩ :=
    exists_contDiff_ae_eq_and_laplacian_eq_of_forall_sobolevReducedFunctional_le hm hu
  have hwp : MemLp w 2 := (W1p.memLp_value u).ae_eq huw
  have ht := tendsto_cocompact_of_memLp_of_laplacian_eq
    (.of_forall fun _ ↦ (hw.of_le (by simp)).contDiffAt) hwp one_le_two ENNReal.ofNat_ne_top
    (.of_forall hΔ)
  obtain ⟨K, hK, hKc⟩ := mem_cocompact.mp (ht.eventually (Metric.closedBall_mem_nhds 0 one_pos))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hw.continuous.continuousOn
  refine ⟨max C 1, huw.mono fun z hz ↦ ?_⟩
  rw [hz]
  by_cases hzK : z ∈ K
  · exact (hC z hzK).trans (le_max_left _ _)
  · have h := hKc hzK
    simp only [Real.dist_eq, sub_zero] at h
    exact h.trans (le_max_right _ _)

/-- On a set where `|a| ≤ B`, the function `h (exp (2a) - 1)` with `0 ≤ h ≤ 1` continuous is
square integrable when `a` is. This is the derivative of the potential of Taubes's functional at a
bounded `a`. -/
private theorem memLp_mul_exp_two_mul_sub_one {h a : ℂ → ℝ} {B : ℝ} (hhc : Continuous h)
    (h0 : ∀ z, 0 ≤ h z) (h1 : ∀ z, h z ≤ 1) (haL : MemLp a 2) (hB : ∀ᵐ z, |a z| ≤ B) :
    MemLp (fun z ↦ h z * (Real.exp (2 * a z) - 1)) 2 := by
  refine (haL.const_mul (2 * Real.exp (2 * B))).of_le ?_ ?_
  · exact hhc.aestronglyMeasurable.mul
      ((Real.continuous_exp.comp_aestronglyMeasurable (haL.aestronglyMeasurable.const_mul 2)).sub
        aestronglyMeasurable_const)
  · filter_upwards [hB] with z hz
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    calc |h z * (Real.exp (2 * a z) - 1)| = h z * |Real.exp (2 * a z) - 1| := by
          rw [abs_mul, abs_of_nonneg (h0 z)]
      _ ≤ 1 * |Real.exp (2 * a z) - 1| := mul_le_mul_of_nonneg_right (h1 z) (abs_nonneg _)
      _ ≤ 2 * Real.exp (2 * B) * |a z| := by rw [one_mul]; exact Real.abs_exp_two_mul_sub_one_le hz
      _ = |2 * Real.exp (2 * B) * a z| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.exp (2 * B))]

/-- The coefficient of the reduced equation at a bounded square-integrable `v` is square
integrable. -/
private theorem memLp_eulerCoeff (hm : 0 < P.natDegree) {v : ℂ → ℝ} (hv : MemLp v 2) {B : ℝ}
    (hB : ∀ᵐ z, |v z| ≤ B) : MemLp (eulerCoeff P v) 2 := by
  obtain ⟨hhc, h0, h1⟩ := continuous_and_nonneg_and_le_one P
  have hf := memLp_mul_exp_two_mul_sub_one hhc h0 h1 hv hB
  refine ((memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight hm).add
    (hf.const_mul 8⁻¹)).ae_eq (ae_of_all _ fun z ↦ ?_)
  simp only [eulerCoeff, Pi.add_apply]
  ring

/-- The weighted potential `h φ(a)`, `φ(t) = exp (2t) - 1 - 2t`, of a bounded square-integrable
`a` is integrable when `0 ≤ h ≤ 1`, since `φ(a) ≤ 4 exp (2B) a²` where `|a| ≤ B`. -/
private theorem integrable_mul_exp_two_mul_sub_one_sub {h a : ℂ → ℝ} {B : ℝ} (hhc : Continuous h)
    (h0 : ∀ z, 0 ≤ h z) (h1 : ∀ z, h z ≤ 1) (haL : MemLp a 2) (hB : ∀ᵐ z, |a z| ≤ B) :
    Integrable fun z ↦ h z * (Real.exp (2 * a z) - 1 - 2 * a z) := by
  refine (haL.integrable_sq.const_mul (4 * Real.exp (2 * B))).mono' ?_ ?_
  · exact hhc.aestronglyMeasurable.mul
      (((Real.continuous_exp.comp_aestronglyMeasurable (haL.aestronglyMeasurable.const_mul 2)).sub
        aestronglyMeasurable_const).sub (haL.aestronglyMeasurable.const_mul 2))
  · filter_upwards [hB] with z hz
    have hφ := Real.exp_two_mul_sub_one_sub_two_mul_nonneg (a z)
    rw [Real.norm_of_nonneg (mul_nonneg (h0 z) hφ)]
    calc h z * (Real.exp (2 * a z) - 1 - 2 * a z) ≤ 1 * (Real.exp (2 * a z) - 1 - 2 * a z) :=
          mul_le_mul_of_nonneg_right (h1 z) hφ
      _ ≤ 4 * Real.exp (2 * B) * a z ^ 2 := by
        rw [one_mul]; exact Real.exp_two_mul_sub_one_sub_two_mul_le hz

/-- **The weighted potential expanded around a bounded function.** If `a` is bounded and square
integrable, `x` is square integrable, `0 ≤ h ≤ 1` and `h φ(a + x)` is integrable, then so is
`h exp (2a) φ(x)`, and
`∫ h φ(a + x) = ∫ h φ(a) + 2 ∫ h (exp (2a) - 1) x + ∫ h exp (2a) φ(x)`. -/
private theorem integrable_and_integral_mul_exp_two_mul_add {h a x : ℂ → ℝ} {B : ℝ}
    (hhc : Continuous h) (h0 : ∀ z, 0 ≤ h z) (h1 : ∀ z, h z ≤ 1) (haL : MemLp a 2)
    (hB : ∀ᵐ z, |a z| ≤ B) (hxL : MemLp x 2)
    (hpot : Integrable fun z ↦ h z * (Real.exp (2 * (a z + x z)) - 1 - 2 * (a z + x z))) :
    Integrable (fun z ↦ h z * Real.exp (2 * a z) * (Real.exp (2 * x z) - 1 - 2 * x z)) ∧
      ∫ z, h z * (Real.exp (2 * (a z + x z)) - 1 - 2 * (a z + x z)) =
        (∫ z, h z * (Real.exp (2 * a z) - 1 - 2 * a z)) +
          2 * (∫ z, h z * (Real.exp (2 * a z) - 1) * x z) +
          ∫ z, h z * Real.exp (2 * a z) * (Real.exp (2 * x z) - 1 - 2 * x z) := by
  have hpot₀ := integrable_mul_exp_two_mul_sub_one_sub hhc h0 h1 haL hB
  have hmid : Integrable fun z ↦ 2 * (h z * (Real.exp (2 * a z) - 1) * x z) :=
    ((memLp_mul_exp_two_mul_sub_one hhc h0 h1 haL hB).integrable_mul hxL).const_mul 2
  have hexp (z : ℂ) : h z * (Real.exp (2 * (a z + x z)) - 1 - 2 * (a z + x z)) =
      h z * (Real.exp (2 * a z) - 1 - 2 * a z) + 2 * (h z * (Real.exp (2 * a z) - 1) * x z) +
        h z * Real.exp (2 * a z) * (Real.exp (2 * x z) - 1 - 2 * x z) := by
    rw [Real.exp_two_mul_add_sub_one_sub_two_mul]; ring
  have hlast : Integrable fun z ↦ h z * Real.exp (2 * a z) * (Real.exp (2 * x z) - 1 - 2 * x z) :=
    ((hpot.sub hpot₀).sub hmid).congr (ae_of_all _ fun z ↦ by simp only [Pi.sub_apply, hexp]; ring)
  refine ⟨hlast, ?_⟩
  have h2 : Integrable fun z ↦ h z * (Real.exp (2 * a z) - 1 - 2 * a z) +
      2 * (h z * (Real.exp (2 * a z) - 1) * x z) := hpot₀.add hmid
  simp_rw [hexp]
  rw [integral_add h2 hlast, integral_add hpot₀ hmid, integral_const_mul]

/-! ### The energy estimate -/

/-- **The energy estimate.** Let `u₀ ∈ H¹(ℂ)` have bounded value and satisfy the linear equation
`⟪∇u₀, ∇w⟫ + ∫ q w = 0` for every `w ∈ H¹(ℂ)`, and let `u` minimize Taubes's functional for `P`.
Then `w = u - u₀` satisfies

`‖∇w‖₂² / 2 + (1 / 16) ∫ h exp (2u₀) φ(w) ≤ -∫ (eulerCoeff P u₀ - q) w`,

where `h = ‖P‖² / (1 + ‖P‖²)` and `φ(t) = exp (2t) - 1 - 2t`. The left side is what minimality
of `u` leaves after expanding the functional around `u₀` by
`φ(a + x) = φ(a) + 2 (exp (2a) - 1) x + exp (2a) φ(x)`. When `q` is the Euler–Lagrange
coefficient of a minimizer for another polynomial, the right side only sees the difference of the
coefficients of the two reduced equations at `u₀`. -/
private theorem integrable_and_le_of_forall_sobolevReducedFunctional_le (hm : 0 < P.natDegree)
    {u₀ u : W1p (volume : Measure ℂ) ⊤ 2} {B : ℝ} (hB : ∀ᵐ z, |W1p.value u₀ z| ≤ B)
    {q : ℂ → ℝ} (hq : MemLp q 2)
    (hEL : ∀ w : W1p (volume : Measure ℂ) ⊤ 2,
      ⟪W1p.gradient u₀, W1p.gradient w⟫ + ∫ z, q z * W1p.value w z = 0)
    (hu : ∀ v, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v) :
    Integrable (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * Real.exp (2 * W1p.value u₀ z) *
        (Real.exp (2 * W1p.value (u - u₀) z) - 1 - 2 * W1p.value (u - u₀) z)) ∧
    ‖W1p.gradient (u - u₀)‖ ^ 2 / 2 +
        (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * Real.exp (2 * W1p.value u₀ z) *
          (Real.exp (2 * W1p.value (u - u₀) z) - 1 - 2 * W1p.value (u - u₀) z)) / 16 ≤
      -∫ z, (eulerCoeff P (W1p.value u₀) z - q z) * W1p.value (u - u₀) z := by
  set w := u - u₀ with hw
  have huw : u = u₀ + w := by rw [hw, add_sub_cancel]
  set h : ℂ → ℝ := fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) with hh
  set c : ℂ → ℝ := fun z ↦ 2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
    (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8 with hc
  set a : ℂ → ℝ := ⇑(W1p.value u₀)
  set x : ℂ → ℝ := ⇑(W1p.value w)
  obtain ⟨hhc, h0, h1⟩ := continuous_and_nonneg_and_le_one P
  have hcL : MemLp c 2 := memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight hm
  have haL : MemLp a 2 := W1p.memLp_value u₀
  have hxL : MemLp x 2 := W1p.memLp_value w
  have hval : (W1p.value u : ℂ → ℝ) =ᵐ[volume] fun z ↦ a z + x z := by
    have h := W1p.value_add_ae u₀ w
    simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at h
    rw [huw]; exact h
  -- The derivative `f = h (exp (2u₀) - 1)` of the potential at `u₀` is square integrable.
  set f : ℂ → ℝ := fun z ↦ h z * (Real.exp (2 * a z) - 1) with hf
  have hfL : MemLp f 2 := memLp_mul_exp_two_mul_sub_one hhc h0 h1 haL hB
  -- The potential is finite at `u₀`, so `I(u₀)` and hence `I(u)` are real numbers.
  obtain ⟨hpot, hle⟩ := integrable_and_le_of_forall_le hu
    (integrable_mul_exp_two_mul_sub_one_sub hhc h0 h1 haL hB)
  -- Expand the three terms of `I(u₀ + w)` around `u₀`.
  have hgrad : ‖W1p.gradient u‖ ^ 2 = ‖W1p.gradient u₀‖ ^ 2 +
      2 * ⟪W1p.gradient u₀, W1p.gradient w⟫ + ‖W1p.gradient w‖ ^ 2 := by
    rw [huw, W1p.gradient_add, norm_add_sq_real]
  have hca : Integrable fun z ↦ c z * a z := hcL.integrable_mul haL
  have hcx : Integrable fun z ↦ c z * x z := hcL.integrable_mul hxL
  have hfx : Integrable fun z ↦ f z * x z := hfL.integrable_mul hxL
  have hqx : Integrable fun z ↦ q z * x z := hq.integrable_mul hxL
  have hlin : ∫ z, c z * W1p.value u z = (∫ z, c z * a z) + ∫ z, c z * x z := by
    rw [← integral_add hca hcx]
    exact integral_congr_ae (hval.mono fun z hz ↦ by simp only [hz, mul_add])
  have hpotu : (fun z ↦ h z * (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) =ᵐ[volume]
      fun z ↦ h z * (Real.exp (2 * (a z + x z)) - 1 - 2 * (a z + x z)) :=
    hval.mono fun z hz ↦ by dsimp only; rw [hz]
  obtain ⟨hlast, hpotI⟩ := integrable_and_integral_mul_exp_two_mul_add hhc h0 h1 haL hB hxL
    (hpot.congr hpotu)
  rw [← integral_congr_ae hpotu] at hpotI
  refine ⟨hlast, ?_⟩
  -- The right side, split into its three integrals.
  have hR : ∫ z, (eulerCoeff P a z - q z) * x z =
      (∫ z, c z * x z) + (∫ z, f z * x z) / 8 - ∫ z, q z * x z := by
    have h2 : Integrable fun z ↦ c z * x z + f z * x z / 8 := hcx.add (hfx.div_const 8)
    rw [← integral_div, ← integral_add hcx (hfx.div_const 8), ← integral_sub h2 hqx]
    exact integral_congr_ae (ae_of_all _ fun z ↦ by simp only [eulerCoeff, hf, hh, hc]; ring)
  have hEL' := hEL w
  rw [hR]
  rw [hgrad, hlin, hpotI] at hle
  linarith

/-- The energy estimate with its right side bounded by the Cauchy–Schwarz inequality:
`‖∇w‖₂² / 2 + (1 / 16) ∫ h exp (2u₀) φ(w) ≤ ‖eulerCoeff P u₀ - q‖₂ ‖w‖₂` for `w = u - u₀`. -/
private theorem integrable_and_le_sqrt_mul_of_forall_sobolevReducedFunctional_le
    (hm : 0 < P.natDegree) {u₀ u : W1p (volume : Measure ℂ) ⊤ 2} {B : ℝ}
    (hB : ∀ᵐ z, |W1p.value u₀ z| ≤ B) {q : ℂ → ℝ} (hq : MemLp q 2)
    (hEL : ∀ w : W1p (volume : Measure ℂ) ⊤ 2,
      ⟪W1p.gradient u₀, W1p.gradient w⟫ + ∫ z, q z * W1p.value w z = 0)
    (hu : ∀ v, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v) :
    Integrable (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * Real.exp (2 * W1p.value u₀ z) *
        (Real.exp (2 * W1p.value (u - u₀) z) - 1 - 2 * W1p.value (u - u₀) z)) ∧
    ‖W1p.gradient (u - u₀)‖ ^ 2 / 2 +
        (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * Real.exp (2 * W1p.value u₀ z) *
          (Real.exp (2 * W1p.value (u - u₀) z) - 1 - 2 * W1p.value (u - u₀) z)) / 16 ≤
      √(∫ z, (eulerCoeff P (W1p.value u₀) z - q z) ^ 2) * ‖W1p.value (u - u₀)‖ := by
  obtain ⟨hH, hle⟩ := integrable_and_le_of_forall_sobolevReducedFunctional_le hm hB hq hEL hu
  refine ⟨hH, hle.trans ?_⟩
  have hCS := sq_integral_mul_le_integral_sq_mul_integral_sq
    ((memLp_eulerCoeff hm (W1p.memLp_value u₀) hB).sub hq) (W1p.memLp_value (u - u₀))
  have hw2 : ∫ z, W1p.value (u - u₀) z ^ 2 = ‖W1p.value (u - u₀)‖ ^ 2 := by
    simpa using W1p.integral_value_sq_eq_norm_value_sq (u - u₀)
  simp only [Pi.sub_apply] at hCS
  rw [hw2] at hCS
  refine (neg_le_abs _).trans ((Real.abs_le_sqrt hCS).trans_eq ?_)
  rw [Real.sqrt_mul (integral_nonneg fun z ↦ sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- The weight `t² / (1 + t²)` is monotone on `[0, ∞)`. -/
private theorem sq_div_one_add_sq_le_sq_div_one_add_sq {s p : ℝ} (hs : 0 ≤ s) (h : s ≤ p) :
    s ^ 2 / (1 + s ^ 2) ≤ p ^ 2 / (1 + p ^ 2) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul h h hs (hs.trans h)]

/-! ### Polynomials with prescribed roots -/

section Roots

variable {ι : Type*} [Fintype ι]

/-- The two terms `2 d² / (1 + p²)²` and `(1 + p²)⁻¹ / 8` of the linear coefficient of Taubes's
functional, with `d = |P'(z)|` and `p = |P(z)|`, are at most `(2 D² + 1) T²` after multiplication
by `t² ≤ T²` when `d ≤ D`. This is the bound near the roots. -/
private theorem sq_div_sq_add_inv_div_mul_sq_le_of_le {d p D t T : ℝ} (hd : 0 ≤ d) (hdD : d ≤ D)
    (ht : 0 ≤ t) (htT : t ≤ T) :
    (2 * d ^ 2 / (1 + p ^ 2) ^ 2 + (1 + p ^ 2)⁻¹ / 8) * t ^ 2 ≤ (2 * D ^ 2 + 1) * T ^ 2 := by
  have h1 : 2 * d ^ 2 / (1 + p ^ 2) ^ 2 ≤ 2 * D ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ (1 + p ^ 2) ^ 2 := one_le_pow₀ (by nlinarith)
    nlinarith [mul_le_mul hdD hdD hd (hd.trans hdD)]
  have h2 : (1 + p ^ 2)⁻¹ / 8 ≤ 1 := by
    rw [div_le_one (by norm_num)]
    exact (inv_le_one_of_one_le₀ (by nlinarith)).trans (by norm_num)
  exact mul_le_mul (by linarith) (pow_le_pow_left₀ ht htT 2) (by positivity) (by positivity)

/-- The same two terms are at most `8 m² + 1` after multiplication by `t²`, when
`d t ≤ 2 m p` and `t / 2 ≤ p`. This is the bound far from the roots, with `t = 1 + |z|`. -/
private theorem sq_div_sq_add_inv_div_mul_sq_le_of_mul_le {d p t m : ℝ} (hd : 0 ≤ d)
    (ht : 0 ≤ t) (hdt : d * t ≤ 2 * m * p) (hpt : t / 2 ≤ p) :
    (2 * d ^ 2 / (1 + p ^ 2) ^ 2 + (1 + p ^ 2)⁻¹ / 8) * t ^ 2 ≤ 8 * m ^ 2 + 1 := by
  have h1 : 2 * d ^ 2 / (1 + p ^ 2) ^ 2 * t ^ 2 ≤ 8 * m ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have h5 : (d * t) ^ 2 ≤ (2 * m * p) ^ 2 := pow_le_pow_left₀ (by positivity) hdt 2
    have h6 : p ^ 2 ≤ (1 + p ^ 2) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h6 (by positivity : (0 : ℝ) ≤ 8 * m ^ 2)]
  have h2 : (1 + p ^ 2)⁻¹ / 8 * t ^ 2 ≤ 1 := by
    have h7 : (1 + p ^ 2)⁻¹ / 8 * t ^ 2 = t ^ 2 / (8 * (1 + p ^ 2)) := by field_simp
    rw [h7, div_le_one (by positivity)]
    nlinarith
  linarith

/-- **Uniform decay of the linear coefficient.** If the roots of `P` lie in the disc of radius `ρ`,
the coefficient `c = 2 ‖P'‖² / (1 + ‖P‖²)² - (1 + ‖P‖²)⁻¹ / 8` of the linear term of Taubes's
functional satisfies `|c(z)| (1 + |z|)² ≤ K` with `K` depending only on `ρ` and the degree. -/
private theorem exists_abs_mul_one_add_norm_sq_le [Nonempty ι] {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ K, ∀ b : ι → ℂ, (∀ i, ‖b i‖ ≤ ρ) → ∀ z : ℂ,
      |2 * ‖(∏ i, (X - C (b i))).derivative.eval z‖ ^ 2 /
          (1 + ‖(∏ i, (X - C (b i))).eval z‖ ^ 2) ^ 2 -
        (1 + ‖(∏ i, (X - C (b i))).eval z‖ ^ 2)⁻¹ / 8| * (1 + ‖z‖) ^ 2 ≤ K := by
  set m := Fintype.card ι
  have hm : 1 ≤ m := Fintype.card_pos
  set R := 2 * ρ + 2
  set D := (m : ℝ) * (R + ρ) ^ (m - 1)
  refine ⟨(8 * m ^ 2 + 1) + (2 * D ^ 2 + 1) * (1 + R) ^ 2, fun b hb z ↦ ?_⟩
  set p := ‖(∏ i, (X - C (b i))).eval z‖
  set d := ‖(∏ i, (X - C (b i))).derivative.eval z‖
  have hd : 0 ≤ d := norm_nonneg _
  -- Both terms of `c` are nonnegative, so `|c|` is at most their sum.
  have habs : |2 * d ^ 2 / (1 + p ^ 2) ^ 2 - (1 + p ^ 2)⁻¹ / 8| ≤
      2 * d ^ 2 / (1 + p ^ 2) ^ 2 + (1 + p ^ 2)⁻¹ / 8 := by
    have hT1 : 0 ≤ 2 * d ^ 2 / (1 + p ^ 2) ^ 2 := by positivity
    have hT2 : 0 ≤ (1 + p ^ 2)⁻¹ / 8 := by positivity
    rw [abs_le]; constructor <;> linarith
  refine (mul_le_mul_of_nonneg_right habs (by positivity)).trans ?_
  have hK₁ : 0 ≤ 8 * (m : ℝ) ^ 2 + 1 := by positivity
  have hK₂ : 0 ≤ (2 * D ^ 2 + 1) * (1 + R) ^ 2 := by positivity
  rcases le_total ‖z‖ R with hzR | hzR
  · -- Near the roots: `d ≤ D` and `1 + |z| ≤ 1 + R`.
    have hdD : d ≤ D := (norm_eval_derivative_prod_X_sub_C_le hb z).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _)
        (Nat.cast_nonneg _))
    linarith [sq_div_sq_add_inv_div_mul_sq_le_of_le (p := p) hd hdD (by positivity)
      (by linarith : 1 + ‖z‖ ≤ 1 + R)]
  · -- Away from the roots: `|z| - ρ ≥ (1 + |z|) / 2`, so `d (1 + |z|) ≤ 2 m p` and
    -- `p ≥ (1 + |z|) / 2`.
    have hzρ : ρ ≤ ‖z‖ := by linarith
    have ht : (1 + ‖z‖) / 2 ≤ ‖z‖ - ρ := by linarith
    have hdt : d * (1 + ‖z‖) ≤ 2 * m * p := by
      have := norm_eval_derivative_prod_X_sub_C_mul_le hb hzρ
      nlinarith
    have hpt : (1 + ‖z‖) / 2 ≤ p :=
      calc (1 + ‖z‖) / 2 ≤ ((1 + ‖z‖) / 2) ^ m := le_self_pow₀ (by linarith) (by omega)
        _ ≤ (‖z‖ - ρ) ^ m := pow_le_pow_left₀ (by linarith) ht m
        _ ≤ p := pow_le_norm_eval_prod_X_sub_C hb hzρ
    linarith [sq_div_sq_add_inv_div_mul_sq_le_of_mul_le hd (by positivity) hdt hpt]

/-- **Lower bounds pass to nearby roots.** If `|P_a(z)| ≥ η` with `0 < η ≤ 1`, then
`|P_b(z)| ≥ η / 2` for all `z` once `b` is close to `a`. Far from the roots both polynomials are
at least `1`, and on a disc `P_b → P_a` uniformly. -/
private theorem eventually_forall_div_two_le_norm_eval (a : ι → ℂ) {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1) :
    ∀ᶠ b in 𝓝 a, ∀ z, η ≤ ‖(∏ i, (X - C (a i))).eval z‖ →
      η / 2 ≤ ‖(∏ i, (X - C (b i))).eval z‖ := by
  set ρ := ‖a‖ + 1
  set R := ρ + 1
  have hρ : ∀ᶠ b in 𝓝 a, ∀ i, ‖b i‖ ≤ ρ := by
    filter_upwards [(continuous_norm.tendsto a).eventually (gt_mem_nhds (lt_add_one ‖a‖))]
      with b hb i using (norm_le_pi_norm b i).trans hb.le
  have hunif := (isCompact_closedBall (0 : ℂ) R).mem_uniformity_of_prod
    (f := fun b : ι → ℂ ↦ fun z : ℂ ↦ ∏ i, (z - b i)) (s := univ) (q := a)
    (by fun_prop) (mem_univ a) (Metric.dist_mem_uniformity (half_pos hη))
  obtain ⟨v, hv, hvu⟩ := hunif
  rw [nhdsWithin_univ] at hv
  filter_upwards [hρ, hv] with b hb hbv z hz
  by_cases hzR : z ∈ Metric.closedBall (0 : ℂ) R
  · have h := hvu b hbv z hzR
    simp only [mem_ofPred_eq, dist_eq_norm] at h
    simp only [eval_prod, eval_sub, eval_X, eval_C] at hz ⊢
    have := norm_sub_norm_le (∏ i, (z - a i)) (∏ i, (z - b i))
    rw [norm_sub_rev] at h
    linarith
  · simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hzR
    have h := pow_le_norm_eval_prod_X_sub_C hb (by linarith : ρ ≤ ‖z‖)
    have h1 : 1 ≤ (‖z‖ - ρ) ^ Fintype.card ι := one_le_pow₀ (by linarith)
    linarith

/-- **The sublevel sets of `|P|` have small measure.** For a polynomial with prescribed roots, the
measure of `{z | |P(z)| < 1 / (k + 1)}` tends to zero: these sets decrease to the finite set of
roots. -/
private theorem tendsto_volume_setOf_norm_eval_lt (a : ι → ℂ) :
    Tendsto (fun k : ℕ ↦ volume {z : ℂ | ‖(∏ i, (X - C (a i))).eval z‖ < 1 / ((k : ℝ) + 1)})
      atTop (𝓝 0) := by
  set S : ℕ → Set ℂ := fun k ↦ {z | ‖(∏ i, (X - C (a i))).eval z‖ < 1 / ((k : ℝ) + 1)}
  have hcont : Continuous fun z : ℂ ↦ ‖(∏ i, (X - C (a i))).eval z‖ :=
    (Polynomial.continuous _).norm
  have hmeas (k : ℕ) : NullMeasurableSet (S k) :=
    (isOpen_lt hcont continuous_const).measurableSet.nullMeasurableSet
  have hanti : Antitone S := fun j k hjk z hz ↦ by
    simp only [S, mem_ofPred_eq] at hz ⊢
    refine hz.trans_le (one_div_le_one_div_of_le (by positivity) ?_)
    exact_mod_cast Nat.add_le_add_right hjk 1
  -- The first set lies in a disc, since `|P| ≥ 1` outside the disc of radius `|a| + 1`.
  have hfin : volume (S 0) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_closedBall_lt_top (x := (0 : ℂ)) (r := ‖a‖ + 1)).ne
      (measure_mono fun z hz ↦ ?_)
    simp only [S, mem_ofPred_eq, CharP.cast_eq_zero, zero_add, ne_eq, one_ne_zero,
      not_false_eq_true, div_self] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    have h1 := pow_le_norm_eval_prod_X_sub_C (fun i ↦ norm_le_pi_norm a i)
      (by linarith : ‖a‖ ≤ ‖z‖)
    have h2 : 1 ≤ (‖z‖ - ‖a‖) ^ Fintype.card ι := one_le_pow₀ (by linarith)
    linarith
  -- The intersection is the set of roots.
  have hinter : volume (⋂ k, S k) = 0 := by
    refine measure_mono_null (fun z hz ↦ ?_) ((finite_range a).measure_zero volume)
    simp only [mem_iInter, S, mem_ofPred_eq] at hz
    have h0 : ‖(∏ i, (X - C (a i))).eval z‖ = 0 :=
      le_antisymm (ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat fun k ↦ (hz k).le)
        (norm_nonneg _)
    simp only [norm_eq_zero, eval_prod, eval_sub, eval_X, eval_C, Finset.prod_eq_zero_iff] at h0
    obtain ⟨i, -, hi⟩ := h0
    exact ⟨i, (sub_eq_zero.mp hi).symm⟩
  have h := tendsto_measure_iInter_atTop hmeas hanti ⟨0, hfin⟩
  rwa [hinter] at h

/-- **An exceptional set around the roots.** For every `ε > 0` there are a measurable set `S`
of measure at most `ε` around the roots of `∏ i, (X - aᵢ)` and a constant `lam > 0` such that, for
all roots `b` close to `a`, the weight `h_b = ‖P_b‖² / (1 + ‖P_b‖²)` is at least `lam` off `S`. -/
private theorem exists_measurableSet_eventually_le (a : ι → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Set ℂ, MeasurableSet S ∧ volume S ≠ ⊤ ∧ volume.real S ≤ ε ∧ ∃ lam > 0,
      ∀ᶠ b in 𝓝 a, ∀ z ∉ S, lam ≤ ‖(∏ i, (X - C (b i))).eval z‖ ^ 2 /
        (1 + ‖(∏ i, (X - C (b i))).eval z‖ ^ 2) := by
  obtain ⟨k, hk⟩ := ((tendsto_volume_setOf_norm_eval_lt a).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
  set η : ℝ := 1 / ((k : ℝ) + 1)
  have hη : 0 < η := by positivity
  have hη1 : η ≤ 1 := by rw [div_le_one (by positivity)]; linarith [k.cast_nonneg (α := ℝ)]
  refine ⟨_, (isOpen_lt (Polynomial.continuous _).norm continuous_const).measurableSet,
    ne_top_of_lt hk, ENNReal.toReal_le_of_le_ofReal hε.le hk.le, (η / 2) ^ 2 / (1 + (η / 2) ^ 2),
    by positivity, ?_⟩
  filter_upwards [eventually_forall_div_two_le_norm_eval a hη hη1] with b hb z hz
  exact sq_div_one_add_sq_le_sq_div_one_add_sq (by positivity) (hb z (not_lt.mp hz))

end Roots

/-! ### Convergence of the coefficients -/

/-- The pointwise domination behind `tendsto_integral_eulerCoeff_sub_sq`: if `|c| t² ≤ K`,
`0 ≤ h ≤ 1` and `|v| ≤ B`, then `(c + h (exp (2v) - 1) / 8 - E)² ≤
3 (K² t⁻⁴ + (exp (2B) / 4)² v² + E²)`. -/
private theorem sq_sub_le_of_abs_mul_sq_le {c h v t K B E : ℝ} (hk : |c| * t ^ 2 ≤ K) (ht : 0 < t)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hv : |v| ≤ B) :
    (c + h * (Real.exp (2 * v) - 1) / 8 - E) ^ 2 ≤
      3 * (K ^ 2 * t ^ (-4 : ℝ) + (Real.exp (2 * B) / 4) ^ 2 * v ^ 2 + E ^ 2) := by
  set y := h * (Real.exp (2 * v) - 1) / 8
  have hc : c ^ 2 ≤ K ^ 2 * t ^ (-4 : ℝ) := by
    have h4 : t ^ (-4 : ℝ) = (t ^ 4)⁻¹ := by rw [Real.rpow_neg ht.le]; norm_cast
    have hk0 : 0 ≤ |c| * t ^ 2 := by positivity
    rw [h4, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have h5 := mul_le_mul hk hk hk0 (hk0.trans hk)
    have h6 : |c| * t ^ 2 * (|c| * t ^ 2) = c ^ 2 * t ^ 4 := by rw [← sq_abs c]; ring
    nlinarith
  have hy : |y| ≤ Real.exp (2 * B) / 4 * |v| := by
    have he := Real.abs_exp_two_mul_sub_one_le hv
    rw [abs_div, abs_mul, abs_of_nonneg hh0, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    nlinarith [abs_nonneg (Real.exp (2 * v) - 1)]
  have hy2 : y ^ 2 ≤ (Real.exp (2 * B) / 4) ^ 2 * v ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg y) hy 2
    rwa [sq_abs, mul_pow, sq_abs] at this
  nlinarith [sq_nonneg (c - y), sq_nonneg (c + E), sq_nonneg (y + E)]

/-- **The coefficients of the reduced equation converge in `L²`.** As the roots `a x` converge to
`a₀`, the coefficient `eulerCoeff P_(a x) v` of the reduced equation at a fixed bounded
square-integrable `v` converges to `eulerCoeff P_(a₀) v` in `L²`. The uniform decay
`|c(z)| ≤ K (1 + |z|)⁻²` of the linear coefficient dominates the difference. -/
private theorem tendsto_integral_eulerCoeff_sub_sq {ι : Type*} [Fintype ι] [Nonempty ι]
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated] {a : α → ι → ℂ} {a₀ : ι → ℂ}
    (ha : Tendsto a l (𝓝 a₀)) {v : ℂ → ℝ} (hv : MemLp v 2) {B : ℝ} (hB : ∀ᵐ z, |v z| ≤ B) :
    Tendsto (fun x ↦ ∫ z, (eulerCoeff (∏ i, (X - C (a x i))) v z -
      eulerCoeff (∏ i, (X - C (a₀ i))) v z) ^ 2) l (𝓝 0) := by
  have hm (b : ι → ℂ) : 0 < (∏ i, (X - C (b i))).natDegree := by
    rw [natDegree_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (b i)]
    simpa using Fintype.card_pos
  set E₀ := eulerCoeff (∏ i, (X - C (a₀ i))) v
  have hE₀ : MemLp E₀ 2 := memLp_eulerCoeff (hm a₀) hv hB
  have hρ : ∀ᶠ x in l, ∀ i, ‖a x i‖ ≤ ‖a₀‖ + 1 :=
    ha.eventually ((continuous_norm.tendsto a₀).eventually (gt_mem_nhds (lt_add_one ‖a₀‖)) |>.mono
      fun b hb i ↦ (norm_le_pi_norm b i).trans hb.le)
  obtain ⟨K, hK⟩ := exists_abs_mul_one_add_norm_sq_le (ι := ι) (by positivity : 0 ≤ ‖a₀‖ + 1)
  have hint : Integrable fun z : ℂ ↦ 3 * (K ^ 2 * (1 + ‖z‖) ^ (-4 : ℝ) +
      (Real.exp (2 * B) / 4) ^ 2 * v z ^ 2 + E₀ z ^ 2) :=
    ((((integrable_one_add_norm (μ := (volume : Measure ℂ)) (r := 4)
      (by rw [Complex.finrank_real_complex]; norm_num)).const_mul (K ^ 2)).add
        (hv.integrable_sq.const_mul _)).add hE₀.integrable_sq).const_mul 3
  have hlim (z : ℂ) : Tendsto (fun x ↦ (eulerCoeff (∏ i, (X - C (a x i))) v z - E₀ z) ^ 2) l
      (𝓝 0) := by
    have hP := continuous_eval_prod_X_sub_C (ι := ι) z
    have hP' := continuous_eval_derivative_prod_X_sub_C (ι := ι) z
    have hc : Continuous fun b : ι → ℂ ↦ eulerCoeff (∏ i, (X - C (b i))) v z := by
      simp only [eulerCoeff]
      fun_prop (disch := intro b; positivity)
    have h := ((hc.tendsto a₀).comp ha).sub_const (E₀ z)
    simpa [E₀] using h.pow 2
  have hconv := tendsto_integral_filter_of_dominated_convergence
    (F := fun x z ↦ (eulerCoeff (∏ i, (X - C (a x i))) v z - E₀ z) ^ 2) _ (.of_forall fun x ↦
      (((memLp_eulerCoeff (hm (a x)) hv hB).aestronglyMeasurable.sub
        hE₀.aestronglyMeasurable).pow 2)) ?_ hint (.of_forall hlim)
  · simpa using hconv
  filter_upwards [hρ] with x hx
  filter_upwards [hB] with z hz
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact sq_sub_le_of_abs_mul_sq_le (hK (a x) hx z) (by positivity) (by positivity)
    (by rw [div_le_one (by positivity)]; linarith) hz

/-! ### The final estimate -/

/-- **The modular is controlled by the weighted potential off a set.** If `h ≥ λ > 0` off `S`
and `|a| ≤ B`, then `∫_{Sᶜ} (√(1 + x²) - 1) ≤ (exp (2B) / λ) ∫ h exp (2a) φ(x)`, where
`φ(t) = exp (2t) - 1 - 2t`. -/
private theorem setIntegral_compl_sqrt_one_add_sq_sub_one_le {S : Set ℂ} (hS : MeasurableSet S)
    {h a x : ℂ → ℝ} {B lam : ℝ} (hlam : 0 < lam) (h0 : ∀ z, 0 ≤ h z)
    (hhS : ∀ z ∉ S, lam ≤ h z) (hB : ∀ᵐ z, |a z| ≤ B) (hx : AEStronglyMeasurable x)
    (hH : Integrable fun z ↦ h z * Real.exp (2 * a z) * (Real.exp (2 * x z) - 1 - 2 * x z)) :
    ∫ z in Sᶜ, (√(1 + x z ^ 2) - 1) ≤
      Real.exp (2 * B) / lam *
        ∫ z, h z * Real.exp (2 * a z) * (Real.exp (2 * x z) - 1 - 2 * x z) := by
  set k := Real.exp (2 * B) / lam
  have hpt : ∀ᵐ z ∂volume.restrict Sᶜ, √(1 + x z ^ 2) - 1 ≤
      k * (h z * Real.exp (2 * a z) * (Real.exp (2 * x z) - 1 - 2 * x z)) := by
    filter_upwards [ae_restrict_mem hS.compl, ae_restrict_of_ae hB] with z hzS hzB
    have hφ := Real.exp_two_mul_sub_one_sub_two_mul_nonneg (x z)
    have hmod := Real.sqrt_one_add_sq_sub_one_le_exp_two_mul_sub_one_sub_two_mul (x z)
    -- `k h exp (2a) ≥ (exp (2B) / λ) λ exp (-2B) = 1`.
    have hk : 1 ≤ k * (h z * Real.exp (2 * a z)) := by
      have h1 : 1 ≤ Real.exp (2 * B) * Real.exp (2 * a z) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by linarith [neg_abs_le (a z)])
      have h2 : lam * (Real.exp (2 * B) * Real.exp (2 * a z)) ≤
          h z * (Real.exp (2 * B) * Real.exp (2 * a z)) :=
        mul_le_mul_of_nonneg_right (hhS z hzS) (by positivity)
      rw [show k * (h z * Real.exp (2 * a z)) =
        h z * (Real.exp (2 * B) * Real.exp (2 * a z)) / lam by simp only [k]; ring,
        le_div_iff₀ hlam]
      nlinarith
    nlinarith
  have hmeas : AEStronglyMeasurable (fun z ↦ √(1 + x z ^ 2) - 1) (volume.restrict Sᶜ) :=
    ((by fun_prop : Continuous fun t : ℝ ↦ √(1 + t ^ 2) - 1).comp_aestronglyMeasurable hx).restrict
  have hmodint : IntegrableOn (fun z ↦ √(1 + x z ^ 2) - 1) Sᶜ :=
    (hH.const_mul k).integrableOn.mono' hmeas (hpt.mono fun z hz ↦ by
      rwa [Real.norm_of_nonneg (sub_nonneg.mpr (Real.one_le_sqrt_one_add_sq _))])
  calc ∫ z in Sᶜ, (√(1 + x z ^ 2) - 1)
      ≤ ∫ z in Sᶜ, k * (h z * Real.exp (2 * a z) * (Real.exp (2 * x z) - 1 - 2 * x z)) :=
        integral_mono_ae hmodint (hH.const_mul k).integrableOn hpt
    _ ≤ ∫ z, k * (h z * Real.exp (2 * a z) * (Real.exp (2 * x z) - 1 - 2 * x z)) :=
        setIntegral_le_integral (hH.const_mul k) (.of_forall fun z ↦ mul_nonneg (by positivity)
          (mul_nonneg (mul_nonneg (h0 z) (Real.exp_pos _).le)
            (Real.exp_two_mul_sub_one_sub_two_mul_nonneg _)))
    _ = k * ∫ z, h z * Real.exp (2 * a z) * (Real.exp (2 * x z) - 1 - 2 * x z) :=
        integral_const_mul k _

/-- **The final arithmetic.** If `g² ≤ 2 ε X` and
`X² ≤ 2 (2 + C₀ g) (A ε X) + (2 + C₀ g)² V`, the planar estimate with an exceptional set of
measure `V`, then `X² ≤ 2 (θ + 8 V)` as soon as `θ ≤ 1 / 2` bounds the explicit quantity
`(4 A + 2 C₀² (1 + 2 V)) ε / 2 + A² ε²`, which tends to zero with `ε`. -/
private theorem sq_le_two_mul_add_of_sq_le {X g ε A C₀ V θ : ℝ} (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hV : 0 ≤ V) (hgε : g ^ 2 ≤ 2 * ε * X)
    (hXi : X ^ 2 ≤ 2 * (2 + C₀ * g) * (A * ε * X) + (2 + C₀ * g) ^ 2 * V)
    (hθ : (4 * A + 2 * C₀ ^ 2 * (1 + 2 * V)) * ε / 2 + A ^ 2 * ε ^ 2 ≤ θ) (hθ1 : θ ≤ 1 / 2) :
    X ^ 2 ≤ 2 * (θ + 8 * V) := by
  set y := C₀ * g
  have hy : y ^ 2 ≤ 2 * C₀ ^ 2 * ε * X := by
    rw [mul_pow]; nlinarith [sq_nonneg C₀]
  -- `(2 + y)² ≤ 8 + 2 y²` and `2 (2 + y) A ε X ≤ 4 A ε X + y² + (A ε X)²`.
  have h1 : (2 + y) ^ 2 ≤ 8 + 2 * y ^ 2 := by nlinarith [sq_nonneg (y - 2)]
  have h2 : 2 * (2 + y) * (A * ε * X) ≤ 4 * (A * ε * X) + y ^ 2 + (A * ε * X) ^ 2 := by
    nlinarith [sq_nonneg (y - A * ε * X)]
  have h3 : X ^ 2 ≤ 4 * (A * ε * X) + (A * ε * X) ^ 2 + 8 * V + (1 + 2 * V) * y ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right h1 hV]
  have h4 : (1 + 2 * V) * y ^ 2 ≤ (1 + 2 * V) * (2 * C₀ ^ 2 * ε * X) :=
    mul_le_mul_of_nonneg_left hy (by positivity)
  -- `β ε X ≤ β ε (1 + X²) / 2` with `β = 4 A + 2 C₀² (1 + 2 V)`.
  have h5 : (4 * A + 2 * C₀ ^ 2 * (1 + 2 * V)) * ε * X ≤
      (4 * A + 2 * C₀ ^ 2 * (1 + 2 * V)) * ε * (1 + X ^ 2) / 2 := by
    have : 0 ≤ (4 * A + 2 * C₀ ^ 2 * (1 + 2 * V)) * ε := by positivity
    nlinarith [sq_nonneg (X - 1)]
  have h6 : X ^ 2 ≤ θ + θ * X ^ 2 + 8 * V := by
    have hθ' : (4 * A + 2 * C₀ ^ 2 * (1 + 2 * V)) * ε / 2 ≤ θ := by
      nlinarith [sq_nonneg (A * ε)]
    nlinarith [mul_le_mul_of_nonneg_right hθ (sq_nonneg X)]
  nlinarith

/-- **The final estimate.** Combine the energy estimate `g² / 2 + I / 16 ≤ ε N`, the bound
`T ≤ k I` on the modular off the exceptional set and the planar estimate
`N² ≤ 2 (2 + C₀ g) T + (2 + C₀ g)² V`: when `V ≤ δ / 32` and `ε` is small, `N² + g² < δ`. Here
`N` and `g` are the `L²` norms of the value and gradient of the difference of two minimizers. -/
private theorem sq_add_sq_lt_of_le {N g ε k C₀ V θ δ I T : ℝ} (hε : 0 ≤ ε)
    (hk : 0 ≤ k) (hV : 0 ≤ V) (hδ : 0 < δ) (hI : 0 ≤ I)
    (hle : g ^ 2 / 2 + I / 16 ≤ ε * N) (hT : T ≤ k * I)
    (hpl : N ^ 2 ≤ 2 * (2 + C₀ * g) * T + (2 + C₀ * g) ^ 2 * V) (hg : 0 ≤ 2 + C₀ * g)
    (hθ : (4 * (16 * k) + 2 * C₀ ^ 2 * (1 + 2 * V)) * ε / 2 + (16 * k) ^ 2 * ε ^ 2 ≤ θ)
    (hθ1 : θ ≤ 1 / 2) (hθδ : θ ≤ δ / 16) (hVδ : V ≤ δ / 32) (hεδ : ε * (1 + δ) ≤ δ / 4) :
    N ^ 2 + g ^ 2 < δ := by
  have hgε : g ^ 2 ≤ 2 * ε * N := by linarith
  have hIε : I ≤ 16 * (ε * N) := by nlinarith [sq_nonneg g]
  have hTA : T ≤ 16 * k * ε * N := by nlinarith [mul_le_mul_of_nonneg_left hIε hk]
  have hpl' : N ^ 2 ≤ 2 * (2 + C₀ * g) * (16 * k * ε * N) + (2 + C₀ * g) ^ 2 * V :=
    hpl.trans (by nlinarith [mul_le_mul_of_nonneg_left hTA hg])
  have hN2 := sq_le_two_mul_add_of_sq_le hε (by positivity) hV hgε hpl' hθ hθ1
  have hN1 : N ≤ (1 + N ^ 2) / 2 := by nlinarith [sq_nonneg (N - 1)]
  have hg2 : g ^ 2 ≤ ε * (1 + δ) := by nlinarith [mul_le_mul_of_nonneg_left hN1 hε]
  linarith

/-! ### Continuity of the minimizer -/

/-- **Taubes's minimizer depends continuously on the zeros.** Let `u x` minimize Taubes's
functional `TauCeti.Vortex.sobolevReducedFunctional` for the polynomial `∏ i, (X - a x i)` with
roots `a x`, and let `u₀` minimize it for `∏ i, (X - a₀ i)`. If the roots `a x` converge to `a₀`,
then `u x → u₀` in `H¹(ℂ)`. Repeated roots and collisions of roots are allowed, and `u x` only
needs to be a minimizer eventually along the filter. -/
theorem tendsto_of_forall_sobolevReducedFunctional_le {ι : Type*} [Fintype ι] [Nonempty ι]
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated] {a : α → ι → ℂ} {a₀ : ι → ℂ}
    (ha : Tendsto a l (𝓝 a₀)) {u : α → W1p (volume : Measure ℂ) ⊤ 2}
    {u₀ : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ᶠ x in l, ∀ v, sobolevReducedFunctional (∏ i, (X - C (a x i))) (u x) ≤
      sobolevReducedFunctional (∏ i, (X - C (a x i))) v)
    (hu₀ : ∀ v, sobolevReducedFunctional (∏ i, (X - C (a₀ i))) u₀ ≤
      sobolevReducedFunctional (∏ i, (X - C (a₀ i))) v) :
    Tendsto u l (𝓝 u₀) := by
  have hm (b : ι → ℂ) : 0 < (∏ i, (X - C (b i))).natDegree := by
    rw [natDegree_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (b i)]
    simpa using Fintype.card_pos
  set P₀ := ∏ i, (X - C (a₀ i))
  obtain ⟨B, hB⟩ := exists_ae_abs_value_le (hm a₀) hu₀
  have hq : MemLp (eulerCoeff P₀ (W1p.value u₀)) 2 :=
    memLp_eulerCoeff (hm a₀) (W1p.memLp_value u₀) hB
  have hEL := inner_gradient_add_integral_mul_value_eq_zero (hm a₀) hu₀ hq
  -- `ε x` is the `L²` distance between the coefficients of the reduced equations at `u₀`.
  set ε : α → ℝ := fun x ↦ √(∫ z, (eulerCoeff (∏ i, (X - C (a x i))) (W1p.value u₀) z -
    eulerCoeff P₀ (W1p.value u₀) z) ^ 2)
  have hε : Tendsto ε l (𝓝 0) := by
    simpa using (tendsto_integral_eulerCoeff_sub_sq ha (W1p.memLp_value u₀) hB).sqrt
  obtain ⟨C₀, hC₀, hpl⟩ :=
    W1p.exists_norm_value_sq_le_of_finrank_eq_two (volume : Measure ℂ) Complex.finrank_real_complex
  rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_nhds]
  intro δ hδ
  set δ' := δ ^ 2 / 2
  -- An exceptional set `S` of measure `V ≤ δ' / 32` around the roots of `P₀`, off which the
  -- weights of the nearby functionals are at least `lam`.
  obtain ⟨S, hSm, hSfin, hV, lam, hlam, hlow⟩ := exists_measurableSet_eventually_le a₀
    (by positivity : 0 < δ' / 32)
  set V := volume.real S
  set k := Real.exp (2 * B) / lam
  set θ := min (1 / 2) (δ' / 16)
  -- Eventually `ε x` is small enough for the final estimate.
  have hθε : Tendsto (fun x ↦ (4 * (16 * k) + 2 * C₀ ^ 2 * (1 + 2 * V)) * ε x / 2 +
      (16 * k) ^ 2 * ε x ^ 2) l (𝓝 0) := by
    simpa using ((hε.const_mul (4 * (16 * k) + 2 * C₀ ^ 2 * (1 + 2 * V))).div_const 2).add
      ((hε.pow 2).const_mul ((16 * k) ^ 2))
  have hεδ : Tendsto (fun x ↦ ε x * (1 + δ')) l (𝓝 0) := by simpa using hε.mul_const (1 + δ')
  filter_upwards [hu, hθε.eventually (eventually_le_nhds (show (0 : ℝ) < θ from
    lt_min (by norm_num) (by positivity))), hεδ.eventually (eventually_le_nhds
    (show (0 : ℝ) < δ' / 4 by positivity)), ha.eventually hlow]
    with x hx hθx hεx hlowx
  -- The energy estimate, the bound on the modular off `S` and the planar estimate.
  obtain ⟨hH, hle⟩ := integrable_and_le_sqrt_mul_of_forall_sobolevReducedFunctional_le (hm (a x))
    hB hq hEL hx
  have hH0 := integral_nonneg (μ := volume) fun z ↦ mul_nonneg (mul_nonneg
    (by positivity : 0 ≤ ‖(∏ i, (X - C (a x i))).eval z‖ ^ 2 /
      (1 + ‖(∏ i, (X - C (a x i))).eval z‖ ^ 2)) (Real.exp_pos (2 * W1p.value u₀ z)).le)
    (Real.exp_two_mul_sub_one_sub_two_mul_nonneg (W1p.value (u x - u₀) z))
  have hT := setIntegral_compl_sqrt_one_add_sq_sub_one_le hSm hlam (fun z ↦ by positivity) hlowx
    hB (W1p.memLp_value (u x - u₀)).aestronglyMeasurable hH
  have hlt := sq_add_sq_lt_of_le (Real.sqrt_nonneg _) (by positivity) measureReal_nonneg
    (by positivity) hH0 hle hT (hpl (u x - u₀) S hSm hSfin) (by positivity) hθx
    (min_le_left _ _) (min_le_right _ _) hV hεx
  rw [← W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq] at hlt
  rw [Real.dist_eq, sub_zero, abs_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hδ.le (hlt.trans (by simp only [δ']; linarith [pow_pos hδ 2]))

/-- **Continuous families of minimizers.** For roots `a y` depending continuously on a parameter
`y` in a first-countable space, minimizers `u y` of Taubes's functional for `∏ i, (X - a y i)`
depend continuously on `y` in `H¹(ℂ)`. -/
theorem continuous_of_forall_sobolevReducedFunctional_le {ι : Type*} [Fintype ι] [Nonempty ι]
    {Y : Type*} [TopologicalSpace Y] [FirstCountableTopology Y] {a : Y → ι → ℂ}
    (ha : Continuous a) {u : Y → W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ y v, sobolevReducedFunctional (∏ i, (X - C (a y i))) (u y) ≤
      sobolevReducedFunctional (∏ i, (X - C (a y i))) v) :
    Continuous u :=
  continuous_iff_continuousAt.2 fun y ↦
    tendsto_of_forall_sobolevReducedFunctional_le (ha.tendsto y) (.of_forall hu) (hu y)

/-- **Taubes's minimizer as a continuous function of the zeros.** There is a continuous map
`b ↦ u b` from the roots `b : ι → ℂ` to `H¹(ℂ)` such that each `u b` minimizes Taubes's
functional for `∏ i, (X - b i)`. By uniqueness of the minimizer
(`TauCeti.Vortex.eq_of_forall_sobolevReducedFunctional_le`), `u b` depends only on the zero divisor
of `∏ i, (X - b i)`. -/
theorem exists_continuous_forall_sobolevReducedFunctional_le (ι : Type*) [Fintype ι]
    [Nonempty ι] :
    ∃ u : (ι → ℂ) → W1p (volume : Measure ℂ) ⊤ 2, Continuous u ∧
      ∀ b v, sobolevReducedFunctional (∏ i, (X - C (b i))) (u b) ≤
        sobolevReducedFunctional (∏ i, (X - C (b i))) v := by
  choose u hu using fun b : ι → ℂ ↦ exists_forall_sobolevReducedFunctional_le
    (P := ∏ i, (X - C (b i))) (by
      rw [natDegree_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (b i)]
      simpa using Fintype.card_pos)
  exact ⟨u, continuous_of_forall_sobolevReducedFunctional_le continuous_id hu, hu⟩

end TauCeti.Vortex
