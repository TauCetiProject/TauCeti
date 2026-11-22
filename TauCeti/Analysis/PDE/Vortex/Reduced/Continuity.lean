/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Minimizer
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.InnerProductSpace.Laplacian.LpDecay
import TauCeti.Analysis.PDE.Regularity.PlanarGradientEstimate
public import TauCeti.Analysis.PDE.Vortex.Existence
import TauCeti.Analysis.Polynomial.AtInfinity
import TauCeti.Analysis.Sobolev.Poincare.Planar
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Exp.Modular
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Continuity of the minimizer of Taubes's functional in the polynomial

For a complex polynomial `P` of degree `m ≥ 1`, the plane vortex with zero divisor `P` is built
from the minimizer `w_P = TauCeti.Vortex.reducedMinimizer P` of Taubes's functional

`I_P(w) = ‖∇w‖₂² / 2 + (1 / 16) ∫ h_P (exp (2w) - 1 - 2w) + ∫ c_P w`

on `H¹(ℂ)`, where `h_P = ‖P‖² / (1 + ‖P‖²)` and `c_P = 2 ‖P'‖² / (1 + ‖P‖²)² - (1 + ‖P‖²)⁻¹ / 8`
(`TauCeti.Vortex.sobolevReducedFunctional`). This file proves that `w_P` depends continuously on
`P`: if the coefficients of `P i` converge to those of `Q`, of positive degree, with eventually
`deg P i ≤ deg Q`, then `w_(P i) → w_Q` in `H¹(ℂ)` (`TauCeti.Vortex.tendsto_reducedMinimizer`).
In particular the minimizer is continuous on every family of polynomials of a fixed positive degree
with continuous coefficients (`TauCeti.Vortex.continuous_reducedMinimizer`), such as the monic
polynomials `∏ (X - aⱼ)` written in the elementary symmetric functions of their roots, collisions
of roots included.

The proof compares the two functionals at the two minimizers, with every constant uniform in `i`.

1. **Coefficients.** The coefficients of `P i - Q` and of its derivative tend to zero, so
   `‖P i - Q‖ ≤ δᵢ (1 + ‖Q‖)` and `‖P i' - Q'‖ ≤ δᵢ (1 + ‖Q'‖)` on the whole plane with `δᵢ → 0`
   (`Polynomial.exists_tendsto_eventually_forall_norm_eval_le`). Hence `|h_(P i) - h_Q| ≤ C δᵢ`
   and `|c_(P i) - c_Q| ≤ C δᵢ β` for a fixed square-integrable, bounded weight `β`. Eventually
   `‖P i‖ ≥ 1` outside a fixed disc and `∫ c_(P i)²` is bounded, so the uniform coercivity of
   Taubes's functional
   (`TauCeti.Vortex.exists_norm_le_of_sobolevReducedFunctional_le_of_forall_one_le_norm_eval`)
   bounds `‖w_(P i)‖_(H¹)` uniformly.
2. **Sup bounds.** The smooth representative of a minimizer solves
   `Δw = (exp (2w) h - 1) / 8 + 2 ‖P'‖² / (1 + ‖P‖²)²`. So `Δw ≥ -1 / 8`, and the mean-value
   inequality bounds `w` above by its `L²` norm
   (`TauCeti.le_sqrt_integral_sq_div_add_of_neg_le_laplacian`); then `Δw` is bounded above too,
   which bounds `-w`. This gives `|w_(P i)|, |w_Q| ≤ M` almost everywhere, uniformly in `i`
   (`TauCeti.Vortex.exists_forall_ae_abs_value_le_of_forall_sobolevReducedFunctional_le`).
3. **Comparison.** For `u ≤ M` the potentials are dominated by `2 exp (2M) u²`
   (`Real.exp_two_mul_sub_one_sub_two_mul_le_mul_sq`), so `|I_(P i)(u) - I_Q(u)| ≤ C δᵢ` on the
   uniform bounds. Since `w_(P i)` minimizes `I_(P i)`, `I_Q(w_(P i)) - I_Q(w_Q) ≤ C δᵢ`.
4. **Growth.** At the midpoint the potential has the exact convexity defect
   `Φ(a) + Φ(b) - 2 Φ((a + b) / 2) = (exp a - exp b)²`, `Φ(t) = exp (2t) - 1 - 2t`
   (`Real.exp_two_mul_sub_one_sub_two_mul_midpoint_defect_eq_sq`), which carries over to
   Taubes's functional
   (`TauCeti.Vortex.sobolevReducedFunctional_midpoint_add_add_exp_sub_exp_sq_le`), so at the
   minimizer `w_Q`
   `I_Q(v) - I_Q(w_Q) ≥ ‖∇(v - w_Q)‖₂² / 4 + (1 / 16) ∫ h_Q (exp v - exp w_Q)²`.
   For `v = w_(P i)` this bounds the gradient of `w_(P i) - w_Q`, and, since `h_Q ≥ 1 / 2`
   outside a disc and `exp (-M) |a - b| ≤ |exp a - exp b|` for `a, b ≥ -M`
   (`TauCeti.exp_neg_mul_abs_sub_le_abs_exp_sub_exp`), its `L²` mass outside that disc, by
   `C δᵢ`.
5. **`L²` convergence.** In the plane, a small gradient and a small `L²` mass outside a disc force
   a small `L²` norm (`TauCeti.W1p.tendsto_of_tendsto_norm_gradient_sub`), so
   `w_(P i) - w_Q → 0` in `H¹(ℂ)`.

The smooth representatives `TauCeti.Vortex.reducedSolution P` then converge uniformly on the
whole plane, together with their first derivatives
(`TauCeti.Vortex.tendstoUniformly_reducedSolution`,
`TauCeti.Vortex.tendstoUniformly_fderiv_reducedSolution`), hence depend continuously on
families of polynomials of a fixed positive degree with continuous coefficients
(`TauCeti.Vortex.continuous_ofFun_reducedSolution`,
`TauCeti.Vortex.continuous_ofFun_fderiv_reducedSolution`). The sup bounds of step 2 bound the
right-hand sides of the reduced equations, hence the Laplacians of the differences
`w_(P i) - w_Q`, uniformly in `i`. A square-integrable function with a bounded Laplacian is bounded
by its `L²` norm through the mean-value inequality, so the `L²` convergence of step 5 becomes
uniform convergence (`TauCeti.tendstoUniformly_zero_of_tendsto_integral_sq_of_abs_laplacian_le`),
and the interior gradient estimate for Poisson's equation upgrades it to uniform convergence of
the derivatives (`TendstoUniformly.fderiv_of_abs_laplacian_sub_le`). Smoothness in the divisor and
the corresponding statements for the background amplitude and the reconstructed vortex fields are
not treated here.

## Main results

* `TauCeti.Vortex.tendsto_reducedMinimizer`: the minimizer of Taubes's functional converges along
  polynomials whose coefficients converge, with eventually `deg P i ≤ deg Q` and `Q` of positive
  degree.
* `TauCeti.Vortex.continuous_reducedMinimizer`: the minimizer is continuous on families of
  polynomials of a fixed positive degree with continuous coefficients.
* `TauCeti.Vortex.tendstoUniformly_reducedSolution`,
  `TauCeti.Vortex.tendstoUniformly_fderiv_reducedSolution`: under the hypotheses of
  `TauCeti.Vortex.tendsto_reducedMinimizer`, the smooth reduced solutions and their derivatives
  converge uniformly on the plane.
* `TauCeti.Vortex.continuous_ofFun_reducedSolution`,
  `TauCeti.Vortex.continuous_ofFun_fderiv_reducedSolution`: the smooth reduced solutions and their
  derivatives are continuous, for the topology of uniform convergence on the plane, on families of
  polynomials of a fixed positive degree with continuous coefficients.
* `TauCeti.Vortex.exists_forall_ae_abs_value_le_of_forall_sobolevReducedFunctional_le`: minimizers
  of Taubes's functional are bounded in `L∞`, uniformly over polynomials with a common bound on
  `2 ‖P'‖² / (1 + ‖P‖²)²` and minimizers with a common `L²` bound.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set Topology InnerProductSpace Laplacian
open scoped ENNReal

namespace TauCeti.Vortex

/-! ### Comparison of the coefficients of Taubes's functional -/

/-- If `|a - b| ≤ δ (1 + b)` with `δ ≤ 1 / 2`, then `1 + b² ≤ 8 (1 + a²)` and
`|a² - b²| ≤ 6 δ (1 + b²)`. -/
private theorem one_add_sq_le_and_abs_sq_sub_sq_le {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hab : |a - b| ≤ δ * (1 + b)) :
    1 + b ^ 2 ≤ 8 * (1 + a ^ 2) ∧ |a ^ 2 - b ^ 2| ≤ 6 * δ * (1 + b ^ 2) := by
  obtain ⟨h1, h2⟩ := abs_le.1 hab
  have hδb : δ * (1 + b) ≤ (1 + b) / 2 := by nlinarith
  refine ⟨by nlinarith [sq_nonneg (a - b), sq_nonneg (1 + b - 2 * (1 + a))], ?_⟩
  have hsum : a + b ≤ 3 * (1 + b) := by linarith
  rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring, abs_mul,
    abs_of_nonneg (by linarith : 0 ≤ a + b)]
  calc |a - b| * (a + b) ≤ δ * (1 + b) * (3 * (1 + b)) :=
        mul_le_mul hab hsum (by linarith) (by positivity)
    _ = 3 * δ * (1 + b) ^ 2 := by ring
    _ ≤ 6 * δ * (1 + b ^ 2) := by nlinarith [sq_nonneg (1 - b)]

/-- If `|a - b| ≤ δ (1 + b)` with `δ ≤ 1 / 2`, then `x = (1 + a²)⁻¹` and `y = (1 + b²)⁻¹` satisfy
`x ≤ 8 y` and `|x - y| ≤ 48 δ y`. -/
private theorem inv_one_add_sq_le_and_abs_sub_le {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hab : |a - b| ≤ δ * (1 + b)) :
    (1 + a ^ 2)⁻¹ ≤ 8 * (1 + b ^ 2)⁻¹ ∧
      |(1 + a ^ 2)⁻¹ - (1 + b ^ 2)⁻¹| ≤ 48 * δ * (1 + b ^ 2)⁻¹ := by
  obtain ⟨hA, hD⟩ := one_add_sq_le_and_abs_sq_sub_sq_le ha hb hδ0 hδ hab
  have hA0 : 0 < 1 + a ^ 2 := by positivity
  have hB0 : 0 < 1 + b ^ 2 := by positivity
  have hxy : (1 + a ^ 2)⁻¹ ≤ 8 * (1 + b ^ 2)⁻¹ := by
    rw [inv_le_iff_one_le_mul₀ hA0]
    calc (1 : ℝ) = (1 + b ^ 2) * (1 + b ^ 2)⁻¹ := (mul_inv_cancel₀ hB0.ne').symm
      _ ≤ (8 * (1 + a ^ 2)) * (1 + b ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hA (by positivity)
      _ = 8 * (1 + b ^ 2)⁻¹ * (1 + a ^ 2) := by ring
  refine ⟨hxy, ?_⟩
  -- `x - y = (b² - a²) x y`, and `(1 + b²) y = 1`.
  have hsub : (1 + a ^ 2)⁻¹ - (1 + b ^ 2)⁻¹ = (b ^ 2 - a ^ 2) * (1 + a ^ 2)⁻¹ * (1 + b ^ 2)⁻¹ := by
    field_simp
    ring
  rw [hsub, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hA0), abs_of_pos (inv_pos.2 hB0),
    abs_sub_comm]
  calc |a ^ 2 - b ^ 2| * (1 + a ^ 2)⁻¹ * (1 + b ^ 2)⁻¹
      ≤ 6 * δ * (1 + b ^ 2) * (1 + a ^ 2)⁻¹ * (1 + b ^ 2)⁻¹ := by gcongr
    _ = 6 * δ * (1 + a ^ 2)⁻¹ * ((1 + b ^ 2) * (1 + b ^ 2)⁻¹) := by ring
    _ ≤ 6 * δ * (8 * (1 + b ^ 2)⁻¹) * 1 := by rw [mul_inv_cancel₀ hB0.ne']; gcongr
    _ = 48 * δ * (1 + b ^ 2)⁻¹ := by ring

/-- The comparison of the source terms `2 a'² x² - x / 8` and `2 b'² y² - y / 8`, given
`x ≤ 8 y`, `|x - y| ≤ 48 δ y`, `y ≤ 1`, `|a'² - b'²| ≤ 6 δ (1 + b'²)` and
`a'² ≤ 8 (1 + b'²)`. -/
private theorem abs_source_sub_le {x y a' b' δ : ℝ} (hδ0 : 0 ≤ δ) (hx0 : 0 < x) (hy0 : 0 < y)
    (hy1 : y ≤ 1) (hxy : x ≤ 8 * y) (hxy' : |x - y| ≤ 48 * δ * y)
    (hD' : |a' ^ 2 - b' ^ 2| ≤ 6 * δ * (1 + b' ^ 2)) (ha'2 : a' ^ 2 ≤ 8 * (1 + b' ^ 2)) :
    |(2 * a' ^ 2 * x ^ 2 - x / 8) - (2 * b' ^ 2 * y ^ 2 - y / 8)| ≤
        1632 * δ * (b' ^ 2 * y ^ 2 + 2 * y) ∧
      2 * a' ^ 2 * x ^ 2 ≤ 1024 * (b' ^ 2 * y ^ 2 + 2 * y) := by
  have hy2 : y ^ 2 ≤ y := by nlinarith
  have hx2 : x ^ 2 ≤ 64 * y ^ 2 := by nlinarith
  refine ⟨?_, ?_⟩
  · -- `2 a'² x² - 2 b'² y² = 2 (a'² - b'²) x² + 2 b'² (x - y) (x + y)`.
    have hsplit : (2 * a' ^ 2 * x ^ 2 - x / 8) - (2 * b' ^ 2 * y ^ 2 - y / 8) =
        2 * (a' ^ 2 - b' ^ 2) * x ^ 2 + 2 * b' ^ 2 * ((x - y) * (x + y)) - (x - y) / 8 := by
      ring
    rw [hsplit]
    have e1 : |2 * (a' ^ 2 - b' ^ 2) * x ^ 2| ≤ 768 * δ * (1 + b' ^ 2) * y ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg (sq_nonneg x)]
      calc 2 * |a' ^ 2 - b' ^ 2| * x ^ 2 ≤ 2 * (6 * δ * (1 + b' ^ 2)) * (64 * y ^ 2) := by
            gcongr
        _ = 768 * δ * (1 + b' ^ 2) * y ^ 2 := by ring
    have e2 : |2 * b' ^ 2 * ((x - y) * (x + y))| ≤ 864 * δ * b' ^ 2 * y ^ 2 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * b' ^ 2), abs_mul,
        abs_of_pos (by linarith : 0 < x + y)]
      calc 2 * b' ^ 2 * (|x - y| * (x + y)) ≤ 2 * b' ^ 2 * (48 * δ * y * (9 * y)) := by
            gcongr; linarith
        _ = 864 * δ * b' ^ 2 * y ^ 2 := by ring
    have e3 : |(x - y) / 8| ≤ 6 * δ * y := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
      linarith
    have e4 : 0 ≤ δ * y := mul_nonneg hδ0 hy0.le
    have e6 : 0 ≤ δ * (y - y ^ 2) := mul_nonneg hδ0 (sub_nonneg.2 hy2)
    calc |2 * (a' ^ 2 - b' ^ 2) * x ^ 2 + 2 * b' ^ 2 * ((x - y) * (x + y)) - (x - y) / 8|
        ≤ |2 * (a' ^ 2 - b' ^ 2) * x ^ 2| + |2 * b' ^ 2 * ((x - y) * (x + y))| +
            |(x - y) / 8| :=
          (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ ≤ 768 * δ * (1 + b' ^ 2) * y ^ 2 + 864 * δ * b' ^ 2 * y ^ 2 + 6 * δ * y := by
        linarith
      _ ≤ 1632 * δ * (b' ^ 2 * y ^ 2 + 2 * y) := by linarith
  · calc 2 * a' ^ 2 * x ^ 2 ≤ 2 * (8 * (1 + b' ^ 2)) * (64 * y ^ 2) := by gcongr
      _ = 1024 * (b' ^ 2 * y ^ 2 + y ^ 2) := by ring
      _ ≤ 1024 * (b' ^ 2 * y ^ 2 + 2 * y) := by nlinarith

/-- Pointwise comparison of the coefficients of Taubes's functional for two polynomials whose
values `a, b` and derivative values `a', b'` (in norm) satisfy `|a - b| ≤ δ (1 + b)` and
`|a' - b'| ≤ δ (1 + b')`. Here `β = b'² / (1 + b²)² + 2 (1 + b²)⁻¹`. -/
private theorem coefficient_bounds {a b a' b' δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a')
    (hb' : 0 ≤ b') (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hab : |a - b| ≤ δ * (1 + b))
    (hab' : |a' - b'| ≤ δ * (1 + b')) :
    |a ^ 2 / (1 + a ^ 2) - b ^ 2 / (1 + b ^ 2)| ≤ 48 * δ ∧
      |(2 * a' ^ 2 / (1 + a ^ 2) ^ 2 - (1 + a ^ 2)⁻¹ / 8) -
          (2 * b' ^ 2 / (1 + b ^ 2) ^ 2 - (1 + b ^ 2)⁻¹ / 8)| ≤
        1632 * δ * (b' ^ 2 / (1 + b ^ 2) ^ 2 + 2 * (1 + b ^ 2)⁻¹) ∧
      2 * a' ^ 2 / (1 + a ^ 2) ^ 2 ≤ 1024 * (b' ^ 2 / (1 + b ^ 2) ^ 2 + 2 * (1 + b ^ 2)⁻¹) := by
  obtain ⟨hxy, hxy'⟩ := inv_one_add_sq_le_and_abs_sub_le ha hb hδ0 hδ hab
  obtain ⟨-, hD'⟩ := one_add_sq_le_and_abs_sq_sub_sq_le ha' hb' hδ0 hδ hab'
  have ha'2 : a' ^ 2 ≤ 8 * (1 + b' ^ 2) := by
    obtain ⟨-, h2⟩ := abs_le.1 hab'
    nlinarith [sq_nonneg (1 - b'), sq_nonneg (a' - b')]
  have hy0 : 0 < (1 + b ^ 2)⁻¹ := by positivity
  have hy1 : (1 + b ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  obtain ⟨hc, hg⟩ := abs_source_sub_le hδ0 (by positivity) hy0 hy1 hxy hxy' hD' ha'2
  -- Rewrite the divisions through `x = (1 + a²)⁻¹` and `y = (1 + b²)⁻¹`.
  have hdiv (c d : ℝ) : c / (1 + d ^ 2) ^ 2 = c * ((1 + d ^ 2)⁻¹) ^ 2 := by
    rw [inv_pow, div_eq_mul_inv]
  have hh (c : ℝ) : c ^ 2 / (1 + c ^ 2) = 1 - (1 + c ^ 2)⁻¹ := by
    field_simp
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hh, hh, show 1 - (1 + a ^ 2)⁻¹ - (1 - (1 + b ^ 2)⁻¹) =
      -((1 + a ^ 2)⁻¹ - (1 + b ^ 2)⁻¹) by ring, abs_neg]
    nlinarith
  · simpa only [hdiv, mul_assoc] using hc
  · simpa only [hdiv, mul_assoc] using hg

/-! ### Uniform bounds on the minimizers -/

/-- The mean-value bound on the plane: a `C²` square-integrable function with `‖w‖₂ ≤ A` and
`Δw ≥ -K` satisfies `w ≤ A / √|B₁| + K / 8`, where `|B₁|` is the area of the unit disc. -/
private theorem le_div_sqrt_add_of_neg_le_laplacian {w : ℂ → ℝ} {A K : ℝ} (hw : ContDiff ℝ 2 w)
    (hw2 : MemLp w 2 volume) (hA : √(∫ z, w z ^ 2) ≤ A) (hΔ : ∀ z, -K ≤ Δ w z) (z : ℂ) :
    w z ≤ A / √(volume.real (ball (0 : ℂ) 1)) + K / 8 := by
  have h := le_sqrt_integral_sq_div_add_of_neg_le_laplacian (μ := volume) hw hw2 hΔ one_pos z
  have hdim : (Module.finrank ℝ ℂ : ℝ) = 2 := by
    rw [Complex.finrank_real_complex]; norm_num
  rw [hdim] at h
  have hA' := div_le_div_of_nonneg_right hA (Real.sqrt_nonneg (volume.real (ball (0 : ℂ) 1)))
  linarith

/-- **Uniform sup bound for minimizers.** For bounds `B` and `G` there is `M` such that the
minimizer `u` of Taubes's functional for any polynomial `P` of positive degree with
`2 ‖P'‖² / (1 + ‖P‖²)² ≤ G` and `‖u‖₂ ≤ B` satisfies `|u| ≤ M` almost everywhere. -/
theorem exists_forall_ae_abs_value_le_of_forall_sobolevReducedFunctional_le (B G : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ P : Polynomial ℂ, 0 < P.natDegree →
      (∀ z, 2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 ≤ G) →
      ∀ u : W1p (volume : Measure ℂ) ⊤ 2,
      (∀ v, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v) →
      ‖W1p.value u‖ ≤ B → ∀ᵐ z, |W1p.value u z| ≤ M := by
  set M₁ := |B| / √(volume.real (ball (0 : ℂ) 1)) + 1 / 8 / 8 with hM₁
  set K₂ := Real.exp (2 * M₁) / 8 + max G 0 with hK₂def
  have hK₂ : 0 ≤ K₂ := by positivity
  refine ⟨M₁ + K₂ / 8, by positivity, fun P hm hG u hu hB ↦ ?_⟩
  -- The smooth representative `w` of `u` solves
  -- `Δw = (exp (2w) h - 1) / 8 + 2 ‖P'‖² / (1 + ‖P‖²)²`, so `Δw ≥ -1 / 8` and the mean-value
  -- inequality bounds `w` above by its `L²` norm; then `Δw` is bounded above as well, which bounds
  -- `-w`.
  obtain ⟨w, hw, hae, hΔ⟩ :=
    exists_contDiff_ae_eq_and_laplacian_eq_of_forall_sobolevReducedFunctional_le hm hu
  have hae' : (W1p.value u : ℂ → ℝ) =ᵐ[volume] w := by simpa using hae
  have hw2 : MemLp w 2 volume := (W1p.memLp_value u).ae_eq hae'
  have hw2' : ContDiff ℝ 2 w := hw.of_le (by simp)
  have hint : √(∫ z, w z ^ 2) ≤ |B| := by
    have h : ∫ z, w z ^ 2 = ‖W1p.value u‖ ^ 2 := by
      rw [← W1p.integral_value_sq_eq_norm_value_sq_top]
      exact integral_congr_ae (hae'.mono fun z hz ↦ by simp only [hz])
    rw [h, Real.sqrt_sq (norm_nonneg _)]
    exact hB.trans (le_abs_self B)
  have hg (z : ℂ) : 0 ≤ 2 * ‖deriv P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 := by positivity
  have hg' (z : ℂ) : 2 * ‖deriv P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 ≤ max G 0 := by
    rw [Polynomial.deriv]
    exact (hG z).trans (le_max_left _ _)
  -- The upper bound: `Δw ≥ -1 / 8`.
  have hup (z : ℂ) : w z ≤ M₁ := le_div_sqrt_add_of_neg_le_laplacian hw2' hw2 hint (fun z ↦ by
    rw [hΔ z]
    have := mul_nonneg (Real.exp_pos (2 * w z)).le (backgroundWeight_nonneg P.eval z)
    linarith [hg z]) z
  -- The lower bound: `Δ (-w) ≥ -K₂`, since `exp (2w) h ≤ exp (2 M₁)`.
  have hlow (z : ℂ) : -w z ≤ M₁ + K₂ / 8 := by
    have hint' : √(∫ z, (-w) z ^ 2) ≤ |B| := by simpa only [Pi.neg_apply, neg_sq] using hint
    refine (le_div_sqrt_add_of_neg_le_laplacian (w := -w) (K := K₂) hw2'.neg hw2.neg hint'
      (fun z ↦ ?_) z).trans ?_
    · rw [laplacian_neg, Pi.neg_apply, hΔ z, neg_le_neg_iff, hK₂def]
      have h1 : Real.exp (2 * w z) * backgroundWeight P.eval z ≤ Real.exp (2 * M₁) * 1 :=
        mul_le_mul (Real.exp_le_exp.2 (by linarith [hup z])) (backgroundWeight_lt_one P.eval z).le
          (backgroundWeight_nonneg P.eval z) (Real.exp_pos _).le
      linarith [hg' z]
    · rw [hM₁]
      linarith
  filter_upwards [hae'] with z hz
  rw [hz, abs_le]
  exact ⟨by linarith [hlow z], by linarith [hup z, hK₂]⟩

/-! ### Taubes's functional on functions bounded above -/

/-- The potential `h (exp (2u) - 1 - 2u)` of Taubes's functional, `h = ‖P‖² / (1 + ‖P‖²)`. -/
private def potential (P : Polynomial ℂ) (u : W1p (volume : Measure ℂ) ⊤ 2) (z : ℂ) : ℝ :=
  ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)

private theorem potential_def (P : Polynomial ℂ) (u : W1p (volume : Measure ℂ) ⊤ 2) :
    potential P u = fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z) := (rfl)

/-- The coefficient `2 ‖P'‖² / (1 + ‖P‖²)² - (1 + ‖P‖²)⁻¹ / 8` of the linear term of Taubes's
functional. -/
private def linearCoeff (P : Polynomial ℂ) (z : ℂ) : ℝ :=
  2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 - (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8

private theorem linearCoeff_def (P : Polynomial ℂ) :
    linearCoeff P = fun z ↦
      2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 - (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8 :=
  (rfl)

private theorem memLp_linearCoeff {P : Polynomial ℂ} (hP : 0 < P.natDegree) :
    MemLp (linearCoeff P) 2 := by
  rw [linearCoeff_def]
  exact memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight hP

/-- Taubes's functional as a real number, meaningful when the potential is integrable. -/
private def realFunctional (P : Polynomial ℂ) (u : W1p (volume : Measure ℂ) ⊤ 2) : ℝ :=
  ‖W1p.gradient u‖ ^ 2 / 2 + (∫ z, potential P u z) / 16 + ∫ z, linearCoeff P z * W1p.value u z

private theorem realFunctional_def (P : Polynomial ℂ) (u : W1p (volume : Measure ℂ) ⊤ 2) :
    realFunctional P u = ‖W1p.gradient u‖ ^ 2 / 2 + (∫ z, potential P u z) / 16 +
      ∫ z, linearCoeff P z * W1p.value u z := (rfl)

private theorem sobolevReducedFunctional_eq_realFunctional {P : Polynomial ℂ}
    {u : W1p (volume : Measure ℂ) ⊤ 2} (hu : Integrable (potential P u)) :
    sobolevReducedFunctional P u = realFunctional P u := by
  rw [potential_def] at hu
  rw [sobolevReducedFunctional_eq_coe hu, realFunctional_def, potential_def, linearCoeff_def]

/-- A function of `H¹(ℂ)` bounded above has integrable potential. -/
private theorem integrable_potential {P : Polynomial ℂ} {u : W1p (volume : Measure ℂ) ⊤ 2}
    {M : ℝ} (hM : 0 ≤ M) (hu : ∀ᵐ z, W1p.value u z ≤ M) : Integrable (potential P u) := by
  rw [potential_def]
  exact integrable_norm_eval_sq_div_mul_exp_two_mul_sub_one_sub_two_mul hM hu

/-- If the weights `h` of `P` and `Q` differ by at most `ε`, then for `u ≤ M` the potentials
differ by at most `2 ε exp (2M) ‖u‖₂²`. -/
private theorem integral_potential_sub_le {P Q : Polynomial ℂ} {ε M : ℝ} (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hh : ∀ z, |‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) - ‖Q.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2)| ≤ ε)
    {u : W1p (volume : Measure ℂ) ⊤ 2} (hu : ∀ᵐ z, W1p.value u z ≤ M) :
    (∫ z, potential P u z) - ∫ z, potential Q u z ≤
      ε * (2 * Real.exp (2 * M) * ‖W1p.value u‖ ^ 2) := by
  have hiP := integrable_potential (P := P) hM hu
  have hiQ := integrable_potential (P := Q) hM hu
  rw [← integral_sub hiP hiQ, ← W1p.integral_value_sq_eq_norm_value_sq_top, ← integral_const_mul,
    ← integral_const_mul]
  refine integral_mono_ae (hiP.sub hiQ)
    (((W1p.memLp_value u).integrable_sq.const_mul _).const_mul _) ?_
  filter_upwards [hu] with z hz
  have hΦ := Real.exp_two_mul_sub_one_sub_two_mul_nonneg (W1p.value u z)
  have hd : potential P u z - potential Q u z =
      (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) - ‖Q.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2)) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z) := by
    simp only [potential_def]; ring
  rw [hd]
  calc _ ≤ ε * (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z) :=
        mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hh z)) hΦ
    _ ≤ ε * (2 * Real.exp (2 * M) * W1p.value u z ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_two_mul_sub_one_sub_two_mul_le_mul_sq hM hz) hε

/-- If the linear coefficients of `P` and `Q` differ by at most `ε β`, the linear terms of their
functionals at `u` differ by at most `ε ‖β‖₂ ‖u‖₂`, by the Cauchy–Schwarz inequality. -/
private theorem integral_linearCoeff_mul_sub_le {P Q : Polynomial ℂ} {ε : ℝ} {β : ℂ → ℝ}
    (hε : 0 ≤ ε) (hβ : MemLp β 2) (hP : MemLp (linearCoeff P) 2) (hQ : MemLp (linearCoeff Q) 2)
    (hc : ∀ z, |linearCoeff P z - linearCoeff Q z| ≤ ε * β z) (u : W1p (volume : Measure ℂ) ⊤ 2) :
    (∫ z, linearCoeff P z * W1p.value u z) - ∫ z, linearCoeff Q z * W1p.value u z ≤
      ε * (√(∫ z, β z ^ 2) * ‖W1p.value u‖) := by
  have hv := W1p.memLp_value u
  have hcs : ∫ z, β z * |W1p.value u z| ≤ √(∫ z, β z ^ 2) * ‖W1p.value u‖ := by
    have h : (∫ z, β z * |W1p.value u z|) ^ 2 ≤ (∫ z, β z ^ 2) * ∫ z, |W1p.value u z| ^ 2 :=
      sq_integral_mul_le_integral_sq_mul_integral_sq hβ hv.abs
    simp only [sq_abs] at h
    rw [W1p.integral_value_sq_eq_norm_value_sq_top] at h
    calc ∫ z, β z * |W1p.value u z| ≤ √((∫ z, β z ^ 2) * ‖W1p.value u‖ ^ 2) :=
          Real.le_sqrt_of_sq_le h
      _ = √(∫ z, β z ^ 2) * ‖W1p.value u‖ := by
        rw [Real.sqrt_mul (integral_nonneg fun z ↦ sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have hiP : Integrable fun z ↦ linearCoeff P z * W1p.value u z := hP.integrable_mul hv
  have hiQ : Integrable fun z ↦ linearCoeff Q z * W1p.value u z := hQ.integrable_mul hv
  have hiβ : Integrable fun z ↦ β z * |W1p.value u z| := hβ.integrable_mul hv.abs
  rw [← integral_sub hiP hiQ]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hcs hε)
  rw [← integral_const_mul]
  refine integral_mono (hiP.sub hiQ) (hiβ.const_mul ε) fun z ↦ ?_
  calc linearCoeff P z * W1p.value u z - linearCoeff Q z * W1p.value u z
      = (linearCoeff P z - linearCoeff Q z) * W1p.value u z := by ring
    _ ≤ |(linearCoeff P z - linearCoeff Q z) * W1p.value u z| := le_abs_self _
    _ = |linearCoeff P z - linearCoeff Q z| * |W1p.value u z| := abs_mul _ _
    _ ≤ ε * β z * |W1p.value u z| := mul_le_mul_of_nonneg_right (hc z) (abs_nonneg _)
    _ = ε * (β z * |W1p.value u z|) := by ring

/-- **Comparison of Taubes's functionals.** If the weights `h` of `P` and `Q` differ by at most
`ε` and their linear coefficients by at most `ε β`, then for `u ≤ M` the functional of `P` at `u`
exceeds that of `Q` by at most `ε (exp (2M) ‖u‖₂² / 8 + ‖β‖₂ ‖u‖₂)`. -/
private theorem realFunctional_le_add {P Q : Polynomial ℂ} {ε M : ℝ} {β : ℂ → ℝ}
    (hε : 0 ≤ ε) (hM : 0 ≤ M) (hβ : MemLp β 2)
    (hP : MemLp (linearCoeff P) 2) (hQ : MemLp (linearCoeff Q) 2)
    (hh : ∀ z, |‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) - ‖Q.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2)| ≤ ε)
    (hc : ∀ z, |linearCoeff P z - linearCoeff Q z| ≤ ε * β z)
    {u : W1p (volume : Measure ℂ) ⊤ 2} (hu : ∀ᵐ z, W1p.value u z ≤ M) :
    realFunctional P u ≤ realFunctional Q u +
      ε * (Real.exp (2 * M) * ‖W1p.value u‖ ^ 2 / 8 + √(∫ z, β z ^ 2) * ‖W1p.value u‖) := by
  have hpot := integral_potential_sub_le hε hM hh hu
  have hlin := integral_linearCoeff_mul_sub_le hε hβ hP hQ hc u
  rw [realFunctional_def, realFunctional_def]
  linarith

/-- Minimality of `u` compares the real-valued functional at `u` and at `v` when `u, v ≤ M`. -/
private theorem realFunctional_le_of_forall_le {P : Polynomial ℂ} {M : ℝ} (hM : 0 ≤ M)
    {u v : W1p (volume : Measure ℂ) ⊤ 2}
    (hmin : ∀ w, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P w)
    (hu : ∀ᵐ z, W1p.value u z ≤ M) (hv : ∀ᵐ z, W1p.value v z ≤ M) :
    realFunctional P u ≤ realFunctional P v := by
  have h := hmin v
  rwa [sobolevReducedFunctional_eq_realFunctional (integrable_potential hM hu),
    sobolevReducedFunctional_eq_realFunctional (integrable_potential hM hv),
    EReal.coe_le_coe_iff] at h

/-- **Quadratic growth with the convexity defect of the potential.** If `u` minimizes Taubes's
functional and `u, v ≤ M`, then
`I(u) + ‖∇(v - u)‖₂² / 4 + (1 / 16) ∫ h (exp v - exp u)² ≤ I(v)`, and the last integrand is
integrable. This combines the midpoint convexity of the functional with its defect
(`TauCeti.Vortex.sobolevReducedFunctional_midpoint_add_add_exp_sub_exp_sq_le`) with `I(u) ≤ I(m)`
at the midpoint `m` of `v` and `u`. -/
private theorem realFunctional_add_add_le {Q : Polynomial ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hQ : 0 < Q.natDegree) {u v : W1p (volume : Measure ℂ) ⊤ 2}
    (hmin : ∀ w, sobolevReducedFunctional Q u ≤ sobolevReducedFunctional Q w)
    (hu : ∀ᵐ z, W1p.value u z ≤ M) (hv : ∀ᵐ z, W1p.value v z ≤ M) :
    Integrable (fun z ↦ ‖Q.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2) *
        (Real.exp (W1p.value v z) - Real.exp (W1p.value u z)) ^ 2) ∧
      realFunctional Q u + ‖W1p.gradient (v - u)‖ ^ 2 / 4 +
          (∫ z, ‖Q.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2) *
            (Real.exp (W1p.value v z) - Real.exp (W1p.value u z)) ^ 2) / 16 ≤
        realFunctional Q v := by
  have hval : (W1p.value (midpoint ℝ v u) : ℂ → ℝ) =ᵐ[volume]
      fun z ↦ (W1p.value v z + W1p.value u z) / 2 := by
    simpa using W1p.value_midpoint_ae v u
  have hm : ∀ᵐ z, W1p.value (midpoint ℝ v u) z ≤ M := by
    filter_upwards [hval, hu, hv] with z hz hzu hzv
    rw [hz]; linarith
  have hpu := integrable_potential (P := Q) hM hu
  have hpv := integrable_potential (P := Q) hM hv
  have h := sobolevReducedFunctional_midpoint_add_add_exp_sub_exp_sq_le hQ v u
  rw [sobolevReducedFunctional_eq_realFunctional (integrable_potential hM hm),
    sobolevReducedFunctional_eq_realFunctional hpv, sobolevReducedFunctional_eq_realFunctional hpu,
    ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  have hle := realFunctional_le_of_forall_le hM hmin hu hm
  rw [potential_def] at hpu hpv
  exact ⟨(integrable_and_integral_mul_exp_sub_exp_sq_eq hpv hpu).1, by linarith⟩

/-! ### The comparison weight -/

/-- The weight `‖Q'‖² / (1 + ‖Q‖²)² + 2 (1 + ‖Q‖²)⁻¹` controlling the change of the linear
coefficient of Taubes's functional. -/
private def comparisonWeight (Q : Polynomial ℂ) (z : ℂ) : ℝ :=
  ‖Q.derivative.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2) ^ 2 + 2 * (1 + ‖Q.eval z‖ ^ 2)⁻¹

private theorem comparisonWeight_def (Q : Polynomial ℂ) :
    comparisonWeight Q = fun z ↦
      ‖Q.derivative.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2) ^ 2 + 2 * (1 + ‖Q.eval z‖ ^ 2)⁻¹ :=
  (rfl)

private theorem memLp_comparisonWeight {Q : Polynomial ℂ} (hQ : 0 < Q.natDegree) :
    MemLp (comparisonWeight Q) 2 := by
  have h := (Q.memLp_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq).add
    ((Polynomial.memLp_inv_one_add_norm_eval_sq hQ).const_mul 2)
  rw [Pi.add_def] at h
  rw [comparisonWeight_def]
  exact h

private theorem comparisonWeight_nonneg (Q : Polynomial ℂ) (z : ℂ) : 0 ≤ comparisonWeight Q z := by
  simp only [comparisonWeight_def]
  positivity

private theorem exists_comparisonWeight_le (Q : Polynomial ℂ) :
    ∃ C : ℝ, ∀ z, comparisonWeight Q z ≤ C := by
  obtain ⟨C, hC⟩ := Q.exists_forall_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq_le
  refine ⟨C + 2, fun z ↦ ?_⟩
  have h2 : 2 * (1 + ‖Q.eval z‖ ^ 2)⁻¹ ≤ 2 := by
    have : (1 + ‖Q.eval z‖ ^ 2)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by nlinarith [norm_nonneg (Q.eval z)])
    linarith
  simp only [comparisonWeight_def]
  linarith [hC z]

/-- The source term `2 ‖Q'‖² / (1 + ‖Q‖²)²` is at most `1024 β` for the comparison weight `β`. -/
private theorem two_mul_le_comparisonWeight (Q : Polynomial ℂ) (z : ℂ) :
    2 * ‖Q.derivative.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2) ^ 2 ≤ 1024 * comparisonWeight Q z := by
  simp only [comparisonWeight_def]
  exact (coefficient_bounds (norm_nonneg (Q.eval z)) (norm_nonneg (Q.eval z))
    (norm_nonneg (Q.derivative.eval z)) (norm_nonneg (Q.derivative.eval z)) le_rfl
    (by norm_num) (by simp) (by simp)).2.2

/-! ### Converging polynomials -/

/-- The bounds on the coefficients of Taubes's functional for `P` relative to those for `Q`, with
parameter `δ` and radius `R`: `δ ∈ [0, 1 / 2]`, `P` has positive degree, the weights `h` differ by
at most `1632 δ`, the linear coefficients by at most `1632 δ β`, where `β` is
`TauCeti.Vortex.comparisonWeight Q`, the source term `2 ‖P'‖² / (1 + ‖P‖²)²` is at most `1024 β`,
and `‖P‖ ≥ 1` outside the closed disc of radius `R`. -/
private structure CoefficientBounds (P Q : Polynomial ℂ) (δ R : ℝ) : Prop where
  nonneg : 0 ≤ δ
  le_half : δ ≤ 1 / 2
  natDegree_pos : 0 < P.natDegree
  abs_weight_sub_le : ∀ z, |‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) -
    ‖Q.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2)| ≤ 1632 * δ
  abs_linearCoeff_sub_le : ∀ z, |linearCoeff P z - linearCoeff Q z| ≤
    1632 * δ * comparisonWeight Q z
  source_le : ∀ z, 2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 ≤
    1024 * comparisonWeight Q z
  one_le_norm_eval : ∀ z ∉ closedBall (0 : ℂ) R, 1 ≤ ‖P.eval z‖

/-- **Coefficient comparison along converging polynomials.** If the coefficients of `P i`
converge to those of `Q`, of positive degree, and eventually `deg P i ≤ deg Q`, then for some
`δ i → 0` and a radius `R` with `‖Q‖ ≥ 1` outside the closed disc of radius `R`, eventually
`TauCeti.Vortex.CoefficientBounds (P i) Q (δ i) R`. -/
private theorem exists_eventually_coefficient_bounds {ι : Type*} {l : Filter ι}
    {P : ι → Polynomial ℂ} {Q : Polynomial ℂ} (hQ : 0 < Q.natDegree)
    (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ Q.natDegree)
    (hcoeff : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (Q.coeff k))) :
    ∃ δ : ι → ℝ, ∃ R : ℝ, Tendsto δ l (𝓝 0) ∧ (∀ z ∉ closedBall (0 : ℂ) R, 1 ≤ ‖Q.eval z‖) ∧
      ∀ᶠ i in l, CoefficientBounds (P i) Q (δ i) R := by
  have hQ0 : Q ≠ 0 := by rintro rfl; simp at hQ
  obtain ⟨δ, hδ0, hδ, hab⟩ :=
    Polynomial.exists_tendsto_eventually_abs_norm_eval_sub_le hQ hdeg hcoeff
  -- `‖Q‖ ≥ 3` outside a closed disc.
  obtain ⟨R, hR⟩ := Polynomial.exists_forall_le_norm_eval hQ 3
  refine ⟨δ, R, hδ, fun z hz ↦ le_trans (by norm_num) (hR z hz), ?_⟩
  have hlead : ∀ᶠ i in l, (P i).coeff Q.natDegree ≠ 0 :=
    (hcoeff Q.natDegree).eventually_ne (by simpa using hQ0)
  filter_upwards [hab, hδ.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hlead] with i hi hs hl
  have hcb (z : ℂ) := coefficient_bounds (norm_nonneg ((P i).eval z)) (norm_nonneg (Q.eval z))
    (norm_nonneg ((P i).derivative.eval z)) (norm_nonneg (Q.derivative.eval z)) (hδ0 i) hs
    (hi z).1 (hi z).2
  refine ⟨hδ0 i, hs, hQ.trans_le (Polynomial.le_natDegree_of_ne_zero hl),
    fun z ↦ (hcb z).1.trans (by linarith [hδ0 i]), fun z ↦ ?_, fun z ↦ ?_, fun z hz ↦ ?_⟩
  · simpa only [linearCoeff_def, comparisonWeight_def, mul_assoc] using (hcb z).2.1
  · simpa only [comparisonWeight_def] using (hcb z).2.2
  -- `‖P i‖ ≥ ‖Q‖ - δ (1 + ‖Q‖) ≥ (‖Q‖ - 1) / 2 ≥ 1`.
  have h3 := hR z hz
  have h := (abs_le.1 (hi z).1).1
  have : δ i * (1 + ‖Q.eval z‖) ≤ (1 + ‖Q.eval z‖) / 2 := by
    nlinarith [norm_nonneg (Q.eval z)]
  linarith

/-! ### Stability of the minimizer -/

/-- The linear coefficient of `P` is square integrable with `∫ c_P² ≤ 2 ∫ c_Q² + 2 C² ∫ β²` when
`|c_P - c_Q| ≤ C β`. -/
private theorem integral_linearCoeff_sq_le {P Q : Polynomial ℂ} {β : ℂ → ℝ} {C : ℝ}
    (hP : MemLp (linearCoeff P) 2) (hQ : MemLp (linearCoeff Q) 2) (hβ : MemLp β 2)
    (hc : ∀ z, |linearCoeff P z - linearCoeff Q z| ≤ C * β z) :
    ∫ z, linearCoeff P z ^ 2 ≤ 2 * (∫ z, linearCoeff Q z ^ 2) + 2 * C ^ 2 * ∫ z, β z ^ 2 := by
  have hI : Integrable fun z ↦ 2 * linearCoeff Q z ^ 2 + 2 * C ^ 2 * β z ^ 2 :=
    (hQ.integrable_sq.const_mul 2).add (hβ.integrable_sq.const_mul _)
  calc ∫ z, linearCoeff P z ^ 2
      ≤ ∫ z, (2 * linearCoeff Q z ^ 2 + 2 * C ^ 2 * β z ^ 2) := by
        refine integral_mono hP.integrable_sq hI fun z ↦ ?_
        -- `x² ≤ 2 y² + 2 (x - y)²` and `(x - y)² ≤ (C β)²`.
        have h3 := sq_le_sq' (abs_le.1 (hc z)).1 (abs_le.1 (hc z)).2
        have h4 : linearCoeff P z ^ 2 ≤ 2 * linearCoeff Q z ^ 2 +
            2 * (linearCoeff P z - linearCoeff Q z) ^ 2 := by
          nlinarith [sq_nonneg (2 * linearCoeff Q z - linearCoeff P z)]
        dsimp only
        linarith
    _ = 2 * (∫ z, linearCoeff Q z ^ 2) + 2 * C ^ 2 * ∫ z, β z ^ 2 := by
      rw [integral_add (hQ.integrable_sq.const_mul 2) (hβ.integrable_sq.const_mul _),
        integral_const_mul, integral_const_mul]

/-- **Stability of the minimizer.** Let `u` minimize Taubes's functional for `Q` and `v` for `P`,
with `u, v ≤ M`, and suppose the weights differ by at most `ε` and the linear coefficients by at
most `ε β`. Then `‖∇(v - u)‖₂² / 4 + (1 / 16) ∫ h_Q (exp v - exp u)²` is at most `ε (X_u + X_v)`,
where `X_w = exp (2M) ‖w‖₂² / 8 + ‖β‖₂ ‖w‖₂`; the last integrand is integrable. -/
private theorem norm_gradient_sq_div_four_add_le {P Q : Polynomial ℂ} {ε M : ℝ} {β : ℂ → ℝ}
    (hε : 0 ≤ ε) (hM : 0 ≤ M) (hβ : MemLp β 2) (hcP : MemLp (linearCoeff P) 2)
    (hQ : 0 < Q.natDegree)
    (hh : ∀ z, |‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) - ‖Q.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2)| ≤ ε)
    (hc : ∀ z, |linearCoeff P z - linearCoeff Q z| ≤ ε * β z)
    {u v : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ w, sobolevReducedFunctional Q u ≤ sobolevReducedFunctional Q w)
    (hv : ∀ w, sobolevReducedFunctional P v ≤ sobolevReducedFunctional P w)
    (huM : ∀ᵐ z, W1p.value u z ≤ M) (hvM : ∀ᵐ z, W1p.value v z ≤ M) :
    Integrable (fun z ↦ ‖Q.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2) *
        (Real.exp (W1p.value v z) - Real.exp (W1p.value u z)) ^ 2) ∧
      ‖W1p.gradient (v - u)‖ ^ 2 / 4 + (∫ z, ‖Q.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2) *
          (Real.exp (W1p.value v z) - Real.exp (W1p.value u z)) ^ 2) / 16 ≤
        ε * ((Real.exp (2 * M) * ‖W1p.value u‖ ^ 2 / 8 + √(∫ z, β z ^ 2) * ‖W1p.value u‖) +
          (Real.exp (2 * M) * ‖W1p.value v‖ ^ 2 / 8 + √(∫ z, β z ^ 2) * ‖W1p.value v‖)) := by
  -- `I_Q(v) ≤ I_P(v) + ε X_v ≤ I_P(u) + ε X_v ≤ I_Q(u) + ε (X_u + X_v)`.
  have hcQ : MemLp (linearCoeff Q) 2 := memLp_linearCoeff hQ
  have A1 := realFunctional_le_add (P := Q) (Q := P) hε hM hβ hcQ hcP
    (fun z ↦ by rw [abs_sub_comm]; exact hh z) (fun z ↦ by rw [abs_sub_comm]; exact hc z) hvM
  have A3 := realFunctional_le_add (P := P) (Q := Q) hε hM hβ hcP hcQ hh hc huM
  have A2 := realFunctional_le_of_forall_le hM hv hvM huM
  obtain ⟨hint, hgrowth⟩ := realFunctional_add_add_le hM hQ hu huM hvM
  exact ⟨hint, by linarith⟩

/-- Outside a disc where `‖Q‖ ≥ 1`, so that `h_Q ≥ 1 / 2`, the squared difference of two
functions `u, v ≥ -M` is controlled by `h_Q (exp v - exp u)²`:
`∫_{sᶜ} (v - u)² ≤ 2 exp (2M) ∫ h_Q (exp v - exp u)²`. -/
private theorem setIntegral_compl_value_sub_sq_le {Q : Polynomial ℂ} {R M : ℝ}
    (hR : ∀ z ∉ closedBall (0 : ℂ) R, 1 ≤ ‖Q.eval z‖) {u v : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ᵐ z, -M ≤ W1p.value u z) (hv : ∀ᵐ z, -M ≤ W1p.value v z)
    (hint : Integrable (fun z ↦ ‖Q.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2) *
        (Real.exp (W1p.value v z) - Real.exp (W1p.value u z)) ^ 2)) :
    ∫ z in (closedBall (0 : ℂ) R)ᶜ, W1p.value (v - u) z ^ 2 ≤
      2 * Real.exp (2 * M) * ∫ z, ‖Q.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2) *
        (Real.exp (W1p.value v z) - Real.exp (W1p.value u z)) ^ 2 := by
  have hsub := W1p.value_sub_ae v u
  simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at hsub
  have hexp : Real.exp (2 * M) = Real.exp M ^ 2 := by rw [sq, ← Real.exp_add]; ring_nf
  have hee : Real.exp M * Real.exp (-M) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hptw : ∀ᵐ z ∂(volume.restrict (closedBall (0 : ℂ) R)ᶜ), W1p.value (v - u) z ^ 2 ≤
      2 * Real.exp (2 * M) * (‖Q.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2) *
        (Real.exp (W1p.value v z) - Real.exp (W1p.value u z)) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall.compl, ae_restrict_of_ae hsub,
      ae_restrict_of_ae hu, ae_restrict_of_ae hv] with z hz hs ha hb
    rw [hs, Pi.sub_apply]
    have hQz := hR z hz
    have hh2 : 1 / 2 ≤ ‖Q.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    -- `exp (-M) |v - u| ≤ |exp v - exp u|`.
    have he := pow_le_pow_left₀ (by positivity) (exp_neg_mul_abs_sub_le_abs_exp_sub_exp hb ha) 2
    rw [mul_pow, sq_abs, sq_abs] at he
    have hX : 0 ≤ (Real.exp (W1p.value v z) - Real.exp (W1p.value u z)) ^ 2 := sq_nonneg _
    calc (W1p.value v z - W1p.value u z) ^ 2
        = Real.exp M ^ 2 * (Real.exp (-M) ^ 2 * (W1p.value v z - W1p.value u z) ^ 2) := by
          rw [← mul_assoc, ← mul_pow, hee, one_pow, one_mul]
      _ ≤ Real.exp M ^ 2 * (Real.exp (W1p.value v z) - Real.exp (W1p.value u z)) ^ 2 :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ 2 * Real.exp (2 * M) * (‖Q.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2) *
            (Real.exp (W1p.value v z) - Real.exp (W1p.value u z)) ^ 2) := by
          rw [hexp]
          have := mul_le_mul_of_nonneg_right hh2 hX
          nlinarith [sq_nonneg (Real.exp M)]
  calc ∫ z in (closedBall (0 : ℂ) R)ᶜ, W1p.value (v - u) z ^ 2
      ≤ ∫ z in (closedBall (0 : ℂ) R)ᶜ, 2 * Real.exp (2 * M) *
          (‖Q.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2) *
            (Real.exp (W1p.value v z) - Real.exp (W1p.value u z)) ^ 2) :=
        integral_mono_ae (W1p.memLp_value (v - u)).integrable_sq.integrableOn
          (hint.const_mul _).integrableOn hptw
    _ ≤ ∫ z, 2 * Real.exp (2 * M) * (‖Q.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2) *
            (Real.exp (W1p.value v z) - Real.exp (W1p.value u z)) ^ 2) :=
        setIntegral_le_integral (hint.const_mul _) (Eventually.of_forall fun z ↦ by positivity)
    _ = _ := integral_const_mul _ _

/-! ### Continuity of the minimizer -/

/-- `E t² / 8 + A t ≤ E B² / 8 + A B` for `0 ≤ t ≤ B` and `E, A ≥ 0`. -/
private theorem mul_sq_div_eight_add_mul_le {E A t B : ℝ} (hE : 0 ≤ E) (hA : 0 ≤ A) (ht0 : 0 ≤ t)
    (ht : t ≤ B) : E * t ^ 2 / 8 + A * t ≤ E * B ^ 2 / 8 + A * B := by
  have h1 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 ht 2) hE
  have h2 := mul_le_mul_of_nonneg_left ht hA
  linarith

/-- The arithmetic closing the uniform estimates: if `G² / 4 + D / 16 ≤ E` for
`E = 1632 δ (X + X)`, with `0 ≤ D` and `I ≤ 2 exp (2M) D`, then `I ≤ 2 exp (2M) (16 E) + 4 E` and
`G² ≤ 4 E ≤ 2 exp (2M) (16 E) + 4 E`, which is `K δ` for the displayed `K`. -/
private theorem le_mul_and_sq_le_mul {G D I X M δ : ℝ}
    (hGD : G ^ 2 / 4 + D / 16 ≤ 1632 * δ * (X + X)) (hD0 : 0 ≤ D)
    (hI : I ≤ 2 * Real.exp (2 * M) * D) :
    I ≤ (2 * Real.exp (2 * M) * (16 * (2 * 1632 * X)) + 4 * (2 * 1632 * X)) * δ ∧
      G ^ 2 ≤ (2 * Real.exp (2 * M) * (16 * (2 * 1632 * X)) + 4 * (2 * 1632 * X)) * δ := by
  have hK : (2 * Real.exp (2 * M) * (16 * (2 * 1632 * X)) + 4 * (2 * 1632 * X)) * δ =
      2 * Real.exp (2 * M) * (16 * (1632 * δ * (X + X))) + 4 * (1632 * δ * (X + X)) := by ring
  rw [hK]
  generalize 1632 * δ * (X + X) = E at hGD ⊢
  have hE0 : 0 ≤ E := by linarith [sq_nonneg G]
  have he : 0 ≤ 2 * Real.exp (2 * M) := by positivity
  constructor
  · calc I ≤ 2 * Real.exp (2 * M) * D := hI
      _ ≤ 2 * Real.exp (2 * M) * (16 * E) :=
        mul_le_mul_of_nonneg_left (by linarith [sq_nonneg G]) he
      _ ≤ 2 * Real.exp (2 * M) * (16 * E) + 4 * E := by linarith
  · calc G ^ 2 ≤ 4 * E := by linarith
      _ ≤ 2 * Real.exp (2 * M) * (16 * E) + 4 * E :=
        le_add_of_nonneg_left (mul_nonneg he (by linarith))

/-- **Uniform estimates along converging polynomials.** Under the hypotheses of
`TauCeti.Vortex.tendsto_reducedMinimizer`, with `δ i → 0` and the radius `R` of
`TauCeti.Vortex.exists_eventually_coefficient_bounds`, the difference of the minimizers has
eventually `∫_{sᶜ} (w_(P i) - w_Q)² ≤ K δ i` outside the closed disc `s` of radius `R`, and
`‖∇(w_(P i) - w_Q)‖₂² ≤ K δ i`. -/
private theorem exists_eventually_le_mul {ι : Type*} {l : Filter ι} {P : ι → Polynomial ℂ}
    {Q : Polynomial ℂ} (hQ : 0 < Q.natDegree) {δ : ι → ℝ} {R : ℝ}
    (hRQ : ∀ z ∉ closedBall (0 : ℂ) R, 1 ≤ ‖Q.eval z‖)
    (hev : ∀ᶠ i in l, CoefficientBounds (P i) Q (δ i) R) :
    ∃ K : ℝ, ∀ᶠ i in l,
      (∫ z in (closedBall (0 : ℂ) R)ᶜ,
        W1p.value (reducedMinimizer (P i) - reducedMinimizer Q) z ^ 2) ≤ K * δ i ∧
      ‖W1p.gradient (reducedMinimizer (P i) - reducedMinimizer Q)‖ ^ 2 ≤ K * δ i := by
  set β := comparisonWeight Q
  have hβ : MemLp β 2 := memLp_comparisonWeight hQ
  obtain ⟨Cβ, hCβ⟩ := exists_comparisonWeight_le Q
  have hcQ : MemLp (linearCoeff Q) 2 := memLp_linearCoeff hQ
  set w := reducedMinimizer Q
  have hw := forall_sobolevReducedFunctional_reducedMinimizer_le hQ
  -- Uniform bounds: the `L²` norm of the linear coefficient, the `H¹` norm and the sup norm.
  set K := 2 * (∫ z, linearCoeff Q z ^ 2) + 2 * 1632 ^ 2 * ∫ z, β z ^ 2
  obtain ⟨B₀, hB₀⟩ :=
    exists_norm_le_of_sobolevReducedFunctional_le_of_forall_one_le_norm_eval R K 0
  set B := max B₀ ‖w‖
  obtain ⟨M, hM0, hMb⟩ :=
    exists_forall_ae_abs_value_le_of_forall_sobolevReducedFunctional_le B (1024 * Cβ)
  have hgQ (z : ℂ) : 2 * ‖Q.derivative.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2) ^ 2 ≤ 1024 * Cβ :=
    (two_mul_le_comparisonWeight Q z).trans (mul_le_mul_of_nonneg_left (hCβ z) (by norm_num))
  have hwM₀ := hMb Q hQ hgQ w hw ((W1p.norm_value_le w).trans (le_max_right _ _))
  set X := Real.exp (2 * M) * B ^ 2 / 8 + √(∫ z, β z ^ 2) * B
  have hX (u : W1p (volume : Measure ℂ) ⊤ 2) (hu : ‖W1p.value u‖ ≤ B) :
      Real.exp (2 * M) * ‖W1p.value u‖ ^ 2 / 8 + √(∫ z, β z ^ 2) * ‖W1p.value u‖ ≤ X :=
    mul_sq_div_eight_add_mul_le (Real.exp_pos (2 * M)).le (Real.sqrt_nonneg _) (norm_nonneg _) hu
  refine ⟨2 * Real.exp (2 * M) * (16 * (2 * 1632 * X)) + 4 * (2 * 1632 * X), ?_⟩
  filter_upwards [hev] with i ⟨hδ0, hδ2, hPi, hh, hc, hg, hRP⟩
  set wi := reducedMinimizer (P i)
  have hwi := forall_sobolevReducedFunctional_reducedMinimizer_le hPi
  have hcP : MemLp (linearCoeff (P i)) 2 := memLp_linearCoeff hPi
  -- The uniform `H¹` and sup bounds for `wi`.
  have hK := integral_linearCoeff_sq_le (C := 1632) hcP hcQ hβ fun z ↦ (hc z).trans
    (by nlinarith [(comparisonWeight_nonneg Q z : 0 ≤ β z)])
  simp only [linearCoeff_def (P i)] at hK
  have hwiB : ‖W1p.value wi‖ ≤ B :=
    (W1p.norm_value_le wi).trans ((hB₀ (P i) hPi hRP hK
      wi ((hwi 0).trans (by rw [sobolevReducedFunctional_zero, EReal.coe_zero]))).trans
        (le_max_left _ _))
  have hwiM₀ := hMb (P i) hPi (fun z ↦ (hg z).trans
    (mul_le_mul_of_nonneg_left (hCβ z) (by norm_num))) wi hwi hwiB
  -- Stability, then the exterior bound.
  have hε : 0 ≤ 1632 * δ i := by positivity
  obtain ⟨hint, hstab⟩ := norm_gradient_sq_div_four_add_le hε hM0 hβ hcP hQ hh hc hw hwi
    (hwM₀.mono fun z hz ↦ (abs_le.1 hz).2) (hwiM₀.mono fun z hz ↦ (abs_le.1 hz).2)
  have hext := setIntegral_compl_value_sub_sq_le hRQ (hwM₀.mono fun z hz ↦ (abs_le.1 hz).1)
    (hwiM₀.mono fun z hz ↦ (abs_le.1 hz).1) hint
  have hXε := mul_le_mul_of_nonneg_left (add_le_add (hX w ((W1p.norm_value_le w).trans
    (le_max_right _ _))) (hX wi hwiB)) hε
  have hD0 : 0 ≤ ∫ z, ‖Q.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2) *
      (Real.exp (W1p.value wi z) - Real.exp (W1p.value w z)) ^ 2 :=
    integral_nonneg fun z ↦ by positivity
  exact le_mul_and_sq_le_mul (hstab.trans hXε) hD0 hext

/-- **Continuity of the minimizer of Taubes's functional in the polynomial.** If the coefficients
of the polynomials `P i` converge to those of a polynomial `Q` of positive degree, and eventually
`deg P i ≤ deg Q`, then the minimizers of Taubes's functional converge in `H¹(ℂ)`:
`reducedMinimizer (P i) → reducedMinimizer Q`. -/
theorem tendsto_reducedMinimizer {ι : Type*} {l : Filter ι} {P : ι → Polynomial ℂ}
    {Q : Polynomial ℂ} (hQ : 0 < Q.natDegree) (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ Q.natDegree)
    (hcoeff : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (Q.coeff k))) :
    Tendsto (fun i ↦ reducedMinimizer (P i)) l (𝓝 (reducedMinimizer Q)) := by
  obtain ⟨δ, R, hδ, hRQ, hev⟩ := exists_eventually_coefficient_bounds hQ hdeg hcoeff
  obtain ⟨K, hK⟩ := exists_eventually_le_mul hQ hRQ hev
  have hKδ : Tendsto (fun i ↦ K * δ i) l (𝓝 0) := by simpa using hδ.const_mul K
  refine W1p.tendsto_of_tendsto_norm_gradient_sub volume Complex.finrank_real_complex
    (s := closedBall (0 : ℂ) R) measurableSet_closedBall measure_closedBall_lt_top.ne ?_ ?_
  · -- `‖∇(w_(P i) - w_Q)‖₂ ≤ √(K δ i) → 0`.
    refine squeeze_zero' (Eventually.of_forall fun i ↦ norm_nonneg _) ?_
      (by simpa using hKδ.sqrt)
    filter_upwards [hK] with i hi
    exact Real.le_sqrt_of_sq_le hi.2
  · exact squeeze_zero' (Eventually.of_forall fun i ↦
      setIntegral_nonneg measurableSet_closedBall.compl fun z _ ↦ sq_nonneg _)
      (hK.mono fun i hi ↦ hi.1) hKδ

/-- **Continuity of the minimizer on a parameter space.** For a family of polynomials of a fixed
positive degree whose coefficients depend continuously on a parameter, for instance the monic
polynomials `∏ (X - aⱼ)` in the symmetric coordinates of their roots, the minimizer of Taubes's
functional depends continuously on the parameter in `H¹(ℂ)`. -/
theorem continuous_reducedMinimizer {X : Type*} [TopologicalSpace X] {P : X → Polynomial ℂ}
    {m : ℕ} (hm : 0 < m) (hdeg : ∀ x, (P x).natDegree = m)
    (hcoeff : ∀ k, Continuous fun x ↦ (P x).coeff k) :
    Continuous fun x ↦ reducedMinimizer (P x) :=
  continuous_iff_continuousAt.2 fun x ↦ tendsto_reducedMinimizer ((hdeg x).symm ▸ hm)
    (Eventually.of_forall fun y ↦ ((hdeg y).trans (hdeg x).symm).le)
    fun k ↦ (hcoeff k).continuousAt

/-! ### Uniform convergence of the reduced solutions -/

/-- Two-sided bounds on the Laplacian of the reduced solution `w` of `P`: if `|w| ≤ M` and
`2 ‖P'‖² / (1 + ‖P‖²)² ≤ G`, then `-1 / 8 ≤ Δw ≤ exp (2M) / 8 + G`. -/
private theorem laplacian_reducedSolution_bounds {P : Polynomial ℂ} (hm : 0 < P.natDegree)
    {M G : ℝ} (hM : ∀ z, |reducedSolution P z| ≤ M)
    (hG : ∀ z, 2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 ≤ G) (z : ℂ) :
    -(1 / 8) ≤ Δ (reducedSolution P) z ∧
      Δ (reducedSolution P) z ≤ Real.exp (2 * M) / 8 + G := by
  rw [laplacian_reducedSolution hm z, Polynomial.deriv]
  have h0 := backgroundWeight_nonneg P.eval z
  have h1 := (backgroundWeight_lt_one P.eval z).le
  have hg : 0 ≤ 2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 := by positivity
  have he : Real.exp (2 * reducedSolution P z) * backgroundWeight P.eval z ≤
      Real.exp (2 * M) * 1 :=
    mul_le_mul (Real.exp_le_exp.2 (by linarith [(abs_le.1 (hM z)).2])) h1 h0
      (Real.exp_pos _).le
  have he0 := mul_nonneg (Real.exp_pos (2 * reducedSolution P z)).le h0
  constructor <;> linarith [hG z]

/-- The `L²` distance of two reduced solutions is at most the `H¹` distance of the minimizers. -/
private theorem integral_sub_sq_le_norm_sub_sq {P Q : Polynomial ℂ} (hP : 0 < P.natDegree)
    (hQ : 0 < Q.natDegree) :
    ∫ z, (reducedSolution P z - reducedSolution Q z) ^ 2 ≤
      ‖reducedMinimizer P - reducedMinimizer Q‖ ^ 2 := by
  have hae : (W1p.value (reducedMinimizer P - reducedMinimizer Q) : ℂ → ℝ) =ᵐ[volume]
      fun z ↦ reducedSolution P z - reducedSolution Q z := by
    have h := W1p.value_sub_ae (reducedMinimizer P) (reducedMinimizer Q)
    simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at h
    filter_upwards [h, value_reducedMinimizer_ae_eq_reducedSolution hP,
      value_reducedMinimizer_ae_eq_reducedSolution hQ] with z hz hPz hQz
    rw [hz, Pi.sub_apply, hPz, hQz]
  have hsq : ∫ z, (reducedSolution P z - reducedSolution Q z) ^ 2 =
      ∫ z, W1p.value (reducedMinimizer P - reducedMinimizer Q) z ^ 2 :=
    integral_congr_ae (hae.mono fun z hz ↦ by simp only [hz])
  rw [hsq, W1p.integral_value_sq_eq_norm_value_sq_top]
  exact pow_le_pow_left₀ (norm_nonneg _) (W1p.norm_value_le _) 2

/-- Along polynomials whose coefficients converge to those of `Q`, of positive degree, with
eventually `deg P i ≤ deg Q`, the reduced solutions converge to that of `Q` in `L²`, and
eventually their Laplacians stay within a fixed distance of that of `Q`. -/
private theorem exists_eventually_abs_laplacian_sub_le_and_tendsto_integral_sq {ι : Type*}
    {l : Filter ι} {P : ι → Polynomial ℂ} {Q : Polynomial ℂ} (hQ : 0 < Q.natDegree)
    (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ Q.natDegree)
    (hcoeff : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (Q.coeff k))) :
    (∃ K : ℝ, ∀ᶠ i in l, ∀ z,
      |Δ (reducedSolution (P i)) z - Δ (reducedSolution Q) z| ≤ K) ∧
      Tendsto (fun i ↦ ∫ z, (reducedSolution (P i) z - reducedSolution Q z) ^ 2) l (𝓝 0) := by
  obtain ⟨δ, R, -, -, hev⟩ := exists_eventually_coefficient_bounds hQ hdeg hcoeff
  obtain ⟨C, hC⟩ := exists_comparisonWeight_le Q
  have hconv := tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_reducedMinimizer hQ hdeg hcoeff)
  have hint : ∀ᶠ i in l, ∫ z, (reducedSolution (P i) z - reducedSolution Q z) ^ 2 ≤
      ‖reducedMinimizer (P i) - reducedMinimizer Q‖ ^ 2 :=
    hev.mono fun i hi ↦ integral_sub_sq_le_norm_sub_sq hi.natDegree_pos hQ
  refine ⟨?_, squeeze_zero' (Eventually.of_forall fun i ↦ integral_nonneg fun z ↦ sq_nonneg _)
    hint (by simpa using hconv.pow 2)⟩
  -- Uniform sup bounds: the minimizers of `P i` are eventually `L²`-close to that of `Q`.
  set B := ‖W1p.value (reducedMinimizer Q)‖ + 1
  have hB : ∀ᶠ i in l, ‖W1p.value (reducedMinimizer (P i))‖ ≤ B := by
    filter_upwards [(tendsto_order.1 hconv).2 1 one_pos] with i hi
    have h := W1p.norm_value_le (reducedMinimizer (P i) - reducedMinimizer Q)
    rw [W1p.value_sub] at h
    have h' := norm_le_norm_add_norm_sub' (W1p.value (reducedMinimizer (P i)))
      (W1p.value (reducedMinimizer Q))
    linarith
  obtain ⟨M, -, hM⟩ := exists_forall_ae_abs_value_le_of_forall_sobolevReducedFunctional_le B
    (1024 * C)
  have hsup {P : Polynomial ℂ} (hm : 0 < P.natDegree)
      (hG : ∀ z, 2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 ≤ 1024 * C)
      (hPB : ‖W1p.value (reducedMinimizer P)‖ ≤ B) (z : ℂ) : |reducedSolution P z| ≤ M := by
    refine (Continuous.ae_le_iff_le volume (contDiff_reducedSolution P).continuous.abs
      continuous_const).1 ?_ z
    filter_upwards [hM P hm hG _ (forall_sobolevReducedFunctional_reducedMinimizer_le hm) hPB,
      value_reducedMinimizer_ae_eq_reducedSolution hm] with z hz hz'
    rwa [← hz']
  have hGQ (z : ℂ) : 2 * ‖Q.derivative.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2) ^ 2 ≤ 1024 * C :=
    (two_mul_le_comparisonWeight Q z).trans (by linarith [hC z])
  have hQb := laplacian_reducedSolution_bounds hQ
    (hsup hQ hGQ (by simp only [B]; linarith)) hGQ
  refine ⟨Real.exp (2 * M) / 8 + 1024 * C + 1 / 8, ?_⟩
  filter_upwards [hev, hB] with i hi hiB z
  have hGi (z : ℂ) : 2 * ‖(P i).derivative.eval z‖ ^ 2 / (1 + ‖(P i).eval z‖ ^ 2) ^ 2 ≤
      1024 * C :=
    (hi.source_le z).trans (by linarith [hC z])
  have hPb := laplacian_reducedSolution_bounds hi.natDegree_pos
    (hsup hi.natDegree_pos hGi hiB) hGi z
  rw [abs_le]
  constructor <;> linarith [hQb z]

/-- **Uniform convergence of the reduced solutions.** If the coefficients of the polynomials
`P i` converge to those of a polynomial `Q` of positive degree, and eventually
`deg P i ≤ deg Q`, then the smooth solutions of the reduced equations converge uniformly on the
plane: `reducedSolution (P i) → reducedSolution Q` uniformly. -/
theorem tendstoUniformly_reducedSolution {ι : Type*} {l : Filter ι} {P : ι → Polynomial ℂ}
    {Q : Polynomial ℂ} (hQ : 0 < Q.natDegree) (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ Q.natDegree)
    (hcoeff : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (Q.coeff k))) :
    TendstoUniformly (fun i ↦ reducedSolution (P i)) (reducedSolution Q) l := by
  obtain ⟨⟨K, hK⟩, hint⟩ :=
    exists_eventually_abs_laplacian_sub_le_and_tendsto_integral_sq hQ hdeg hcoeff
  -- Apply the `L²`-to-uniform estimate to the differences `w_(P i) - w_Q`.
  have h := tendstoUniformly_zero_of_tendsto_integral_sq_of_abs_laplacian_le (μ := volume)
    (f := fun i ↦ reducedSolution (P i) - reducedSolution Q)
    (.of_forall fun i ↦ ((contDiff_reducedSolution (P i)).sub
      (contDiff_reducedSolution Q)).of_le (by simp))
    (.of_forall fun i ↦ (memLp_reducedSolution (P i)).sub (memLp_reducedSolution Q))
    (hK.mono fun i hi z ↦ by
      rw [ContDiffAt.laplacian_sub
        (((contDiff_reducedSolution (P i)).of_le (by simp)).contDiffAt)
        (((contDiff_reducedSolution Q).of_le (by simp)).contDiffAt)]
      exact hi z) hint
  rw [Metric.tendstoUniformly_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with i hi z
  simpa [Real.dist_eq, abs_sub_comm] using hi z

/-- **Uniform convergence of the derivatives of the reduced solutions.** Under the hypotheses of
`TauCeti.Vortex.tendstoUniformly_reducedSolution`, the derivatives of the reduced solutions also
converge uniformly on the plane: `D (reducedSolution (P i)) → D (reducedSolution Q)`. -/
theorem tendstoUniformly_fderiv_reducedSolution {ι : Type*} {l : Filter ι}
    {P : ι → Polynomial ℂ} {Q : Polynomial ℂ} (hQ : 0 < Q.natDegree)
    (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ Q.natDegree)
    (hcoeff : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (Q.coeff k))) :
    TendstoUniformly (fun i ↦ fderiv ℝ (reducedSolution (P i))) (fderiv ℝ (reducedSolution Q))
      l := by
  obtain ⟨⟨K, hK⟩, -⟩ :=
    exists_eventually_abs_laplacian_sub_le_and_tendsto_integral_sq hQ hdeg hcoeff
  exact (tendstoUniformly_reducedSolution hQ hdeg hcoeff).fderiv_of_abs_laplacian_sub_le
    (.of_forall fun i ↦ (contDiff_reducedSolution (P i)).of_le (by simp))
    ((contDiff_reducedSolution Q).of_le (by simp)) hK

/-- **Continuity of the reduced solutions in the uniform topology.** For a family of
polynomials of a fixed positive degree whose coefficients depend continuously on a parameter, the
smooth reduced solutions depend continuously on the parameter in the topology of uniform
convergence on the plane. -/
theorem continuous_ofFun_reducedSolution {X : Type*} [TopologicalSpace X] {P : X → Polynomial ℂ}
    {m : ℕ} (hm : 0 < m) (hdeg : ∀ x, (P x).natDegree = m)
    (hcoeff : ∀ k, Continuous fun x ↦ (P x).coeff k) :
    Continuous fun x ↦ UniformFun.ofFun (reducedSolution (P x)) :=
  continuous_iff_continuousAt.2 fun x ↦ UniformFun.tendsto_iff_tendstoUniformly.2 <|
    tendstoUniformly_reducedSolution ((hdeg x).symm ▸ hm)
      (Eventually.of_forall fun y ↦ ((hdeg y).trans (hdeg x).symm).le)
      fun k ↦ (hcoeff k).continuousAt

/-- **Continuity of the derivatives of the reduced solutions in the uniform topology.** Under the
hypotheses of `TauCeti.Vortex.continuous_ofFun_reducedSolution`, the derivatives of the reduced
solutions depend continuously on the parameter in the topology of uniform convergence on the
plane. -/
theorem continuous_ofFun_fderiv_reducedSolution {X : Type*} [TopologicalSpace X]
    {P : X → Polynomial ℂ} {m : ℕ} (hm : 0 < m) (hdeg : ∀ x, (P x).natDegree = m)
    (hcoeff : ∀ k, Continuous fun x ↦ (P x).coeff k) :
    Continuous fun x ↦ UniformFun.ofFun (fderiv ℝ (reducedSolution (P x))) :=
  continuous_iff_continuousAt.2 fun x ↦ UniformFun.tendsto_iff_tendstoUniformly.2 <|
    tendstoUniformly_fderiv_reducedSolution ((hdeg x).symm ▸ hm)
      (Eventually.of_forall fun y ↦ ((hdeg y).trans (hdeg x).symm).le)
      fun k ↦ (hcoeff k).continuousAt

end TauCeti.Vortex
