/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Gauge.Fixed
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import TauCeti.Analysis.Calculus.FDeriv.Norm
import TauCeti.Analysis.Calculus.FDeriv.Pi.Lp
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# The energy identity and Gårding inequality for the gauge-fixed vortex operator

In the coordinates of `TauCeti.Vortex.gaugeFixedOperator`, a field `x = (A₁, A₂, P, Q)` has
connection `a = i (A₁ ds + A₂ dt)` and section `α = 2 (P + i Q)`, and a variation
`y = (b₁, b₂, p, q)` has connection part `b = b₁ ds + b₂ dt` and section part `δα = 2 (p + i q)`.
Write `φ = α / 2` and `ψ = δα / 2 = p + i q`. In complex notation the gauge-fixed operator
`L_x = d₀* ⊕ d₁` has its four rows, paired as two complex numbers, equal to

`((∂₁ + i ∂₂) β + i φ conj ψ, (∇₁ + i ∇₂) ψ + i (conj β) φ)`,  `β = b₁ - i b₂`,

where `∇ = d + a` acts on `ψ`.

This file proves the integrated Weitzenböck formula for `L_x* L_x` at an arbitrary `C¹` field
(`TauCeti.Vortex.integral_norm_sq_gaugeFixedOperator`): for a compactly supported `C²`
variation `y`,

`∫ |L_x y|² = ∫ (|∇b|² + |∇_a ψ|²) + ∫ V_x(y)`,

where the covariant gradient density is `TauCeti.Vortex.gaugeFixedGradientDensity` and the
zeroth-order potential (`TauCeti.Vortex.gaugeFixedPotential`) is

`V_x(y) = |φ|² |y|² + κ |ψ|² + Im ((b₁ + i b₂) conj ψ ∂_a α)`,  `∂_a α = ∇₁ α - i ∇₂ α`,

with `κ = ∂₁ A₂ - ∂₂ A₁` the curvature coefficient `TauCeti.Vortex.curvature`. Pointwise,
`|L_x y|²` differs from the integrand on the right by two Jacobian determinants, of `(b₁, b₂)`
and of `(q, p)`, and by the divergence of a current linear in `x` and quadratic in `y`; both
integrate to zero. The curvature and `∂_a α` enter when derivatives of `y` are moved onto the
field. At the vacuum the identity reduces to `‖L₀ y‖² = ‖∇y‖² + ‖y‖² / 4`
(`TauCeti.Vortex.integral_norm_sq_vacuumOperator`). It does not assume the vortex equation; where
the vortex equation holds the potential simplifies
(`TauCeti.Vortex.gaugeFixedPotential_eq_of_equation_eq_zero`), which gives the energy identity
`TauCeti.Vortex.integral_norm_sq_gaugeFixedOperator_of_equation_eq_zero`.

At a vortex `κ = -(1 - |α|²) / 8` and `∂bar_a α = 0`, so the potential is
`|φ|² |b|² + ((12 |φ|² - 1) / 8) |ψ|²` up to a cross term bounded by `|∇₁ α| |y|²`. When
`|α| → 1` and `∇₁ α → 0` at infinity, the potential therefore tends to the vacuum mass `1 / 4`.
For every `a < 1 / 4` this gives a Gårding inequality with a compact remainder
(`TauCeti.Vortex.exists_integral_gaugeFixedGradientDensity_add_mul_integral_norm_sq_le`):

`∫ (|∇b|² + |∇_a ψ|²) + a ∫ |y|² ≤ ∫ |L_x y|² + K ∫_{|z| ≤ R} |y|²`.

Without asymptotic hypotheses, the same pointwise bound for the potential gives a Gårding
inequality on a disc (`TauCeti.Vortex.exists_integral_norm_fderiv_sq_le`): for variations `u`
supported in a fixed closed disc, on whose support the vortex equation holds,
`∫ |Du|² ≤ C (∫ |L_x u|² + ∫ |u|²)`.

For variations vanishing on the disc of radius `R` it gives the exterior bound
`TauCeti.Vortex.exists_exterior_integral_norm_sq_gaugeFixedOperator_ge`, and in addition it
controls the covariant gradient of the variation. Combined with the compactness of `H¹ → L²` on
the disc, an estimate of this form gives finite-dimensionality of the kernel and closedness of
the range of `L_x` on the completed spaces. The radius and the constant depend on the vortex and
on `a`. These are classical test-field estimates; no completed Fredholm realization is
constructed here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980.
* E. J. Weinberg, *Multivortex solutions of the Ginzburg–Landau equations*, Phys. Rev. D 19
  (1979), 3008–3012.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory Filter Metric
open scoped Topology

/-- The covariant gradient density `|∇b|² + |∇_a ψ|²` of a variation `y = (b₁, b₂, p, q)` at the
field `x`, where `ψ = p + i q` is differentiated with the connection `a = i (A₁ ds + A₂ dt)` of
`x`: along the coordinate frame `(∂₁, ∂₂) = (1, i)`,
`∇_j ψ = (∂_j p - A_j q) + i (∂_j q + A_j p)`. Since `ψ = δα / 2`, this is
`|∇b|² + |∇_a δα|² / 4`, the gradient for the coefficient metric of variations. -/
def gaugeFixedGradientDensity (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) : ℝ :=
  fderiv ℝ (fun w ↦ y w 0) z 1 ^ 2 + fderiv ℝ (fun w ↦ y w 0) z I ^ 2 +
    fderiv ℝ (fun w ↦ y w 1) z 1 ^ 2 + fderiv ℝ (fun w ↦ y w 1) z I ^ 2 +
    (fderiv ℝ (fun w ↦ y w 2) z 1 - x z 0 * y z 3) ^ 2 +
    (fderiv ℝ (fun w ↦ y w 3) z 1 + x z 0 * y z 2) ^ 2 +
    (fderiv ℝ (fun w ↦ y w 2) z I - x z 1 * y z 3) ^ 2 +
    (fderiv ℝ (fun w ↦ y w 3) z I + x z 1 * y z 2) ^ 2

/-- The zeroth-order potential of `L_x* L_x` at the field `x`, evaluated on the value
`v = (b₁, b₂, p, q)` of a variation: with `φ = α / 2`, `ψ = p + i q`, the curvature coefficient
`κ = curvature x z` and `∂_a α = ∇₁ α - i ∇₂ α`,

`V_x(v) = |φ|² |v|² + κ |ψ|² + Im ((b₁ + i b₂) conj ψ ∂_a α)`.

See `integral_norm_sq_gaugeFixedOperator`. -/
def gaugeFixedPotential (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ)
    (v : EuclideanSpace ℝ (Fin 4)) : ℝ :=
  (x z 2 ^ 2 + x z 3 ^ 2) * ‖v‖ ^ 2 + curvature x z * (v 2 ^ 2 + v 3 ^ 2) +
    (((v 0 : ℂ) + v 1 * I) * ((v 2 : ℂ) - v 3 * I) *
      (covariantDerivative x z 1 - I * covariantDerivative x z I)).im

/-- The defining formula of the covariant gradient density. -/
theorem gaugeFixedGradientDensity_def (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    gaugeFixedGradientDensity x y z =
      fderiv ℝ (fun w ↦ y w 0) z 1 ^ 2 + fderiv ℝ (fun w ↦ y w 0) z I ^ 2 +
        fderiv ℝ (fun w ↦ y w 1) z 1 ^ 2 + fderiv ℝ (fun w ↦ y w 1) z I ^ 2 +
        (fderiv ℝ (fun w ↦ y w 2) z 1 - x z 0 * y z 3) ^ 2 +
        (fderiv ℝ (fun w ↦ y w 3) z 1 + x z 0 * y z 2) ^ 2 +
        (fderiv ℝ (fun w ↦ y w 2) z I - x z 1 * y z 3) ^ 2 +
        (fderiv ℝ (fun w ↦ y w 3) z I + x z 1 * y z 2) ^ 2 :=
  (rfl)

/-- The defining formula of the potential. -/
theorem gaugeFixedPotential_def (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ)
    (v : EuclideanSpace ℝ (Fin 4)) :
    gaugeFixedPotential x z v =
      (x z 2 ^ 2 + x z 3 ^ 2) * ‖v‖ ^ 2 + curvature x z * (v 2 ^ 2 + v 3 ^ 2) +
        (((v 0 : ℂ) + v 1 * I) * ((v 2 : ℂ) - v 3 * I) *
          (covariantDerivative x z 1 - I * covariantDerivative x z I)).im :=
  (rfl)

/-- The covariant gradient density is nonnegative. -/
theorem gaugeFixedGradientDensity_nonneg (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    0 ≤ gaugeFixedGradientDensity x y z := by
  rw [gaugeFixedGradientDensity_def]
  positivity

variable {x y : ℂ → EuclideanSpace ℝ (Fin 4)}

/-! ### The pointwise identity -/

/-- The potential in the real field coordinates, for a field differentiable at the point. -/
private theorem gaugeFixedPotential_eq {z : ℂ} (hx : DifferentiableAt ℝ x z)
    (v : EuclideanSpace ℝ (Fin 4)) :
    gaugeFixedPotential x z v =
      (x z 2 ^ 2 + x z 3 ^ 2) * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) +
        (fderiv ℝ (fun w ↦ x w 1) z 1 - fderiv ℝ (fun w ↦ x w 0) z I) *
          (v 2 ^ 2 + v 3 ^ 2) +
        2 * (v 0 * (v 2 * (fderiv ℝ (fun w ↦ x w 3) z 1 + x z 0 * x z 2 -
              fderiv ℝ (fun w ↦ x w 2) z I + x z 1 * x z 3) -
            v 3 * (fderiv ℝ (fun w ↦ x w 2) z 1 - x z 0 * x z 3 +
              fderiv ℝ (fun w ↦ x w 3) z I + x z 1 * x z 2)) +
          v 1 * (v 2 * (fderiv ℝ (fun w ↦ x w 2) z 1 - x z 0 * x z 3 +
              fderiv ℝ (fun w ↦ x w 3) z I + x z 1 * x z 2) +
            v 3 * (fderiv ℝ (fun w ↦ x w 3) z 1 + x z 0 * x z 2 -
              fderiv ℝ (fun w ↦ x w 2) z I + x z 1 * x z 3))) := by
  have hp := (differentiableAt_piLp 2).1 hx 2
  have hq := (differentiableAt_piLp 2).1 hx 3
  have h1r := covariantDerivative_re hp hq 1
  have h1i := covariantDerivative_im hp hq 1
  have hIr := covariantDerivative_re hp hq I
  have hIi := covariantDerivative_im hp hq I
  simp only [one_re, one_im, I_re, I_im] at h1r h1i hIr hIi
  rw [gaugeFixedPotential_def, curvature_apply, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
  simp only [mul_im, mul_re, sub_re, sub_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im,
    h1r, h1i, hIr, hIi]
  ring

/-- The remainder in the pointwise Weitzenböck identity: twice the sum of the Jacobian
determinants of `(b₁, b₂)` and of `(q, p)`, plus the divergence `∂₁ W₁ + ∂₂ W₂` of a current that
is linear in the field and quadratic in the variation. It integrates to zero against compactly
supported variations (`integral_weitzenbockRemainder`). -/
private def weitzenbockRemainder (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) : ℝ :=
  2 * (fderiv ℝ (fun w ↦ y w 0) z 1 * fderiv ℝ (fun w ↦ y w 1) z I -
      fderiv ℝ (fun w ↦ y w 1) z 1 * fderiv ℝ (fun w ↦ y w 0) z I +
    fderiv ℝ (fun w ↦ y w 3) z 1 * fderiv ℝ (fun w ↦ y w 2) z I -
      fderiv ℝ (fun w ↦ y w 2) z 1 * fderiv ℝ (fun w ↦ y w 3) z I) +
  fderiv ℝ (fun w ↦ 2 * y w 0 * (x w 2 * y w 3 - x w 3 * y w 2) -
      2 * y w 1 * (x w 2 * y w 2 + x w 3 * y w 3) - x w 1 * (y w 2 ^ 2 + y w 3 ^ 2)) z 1 +
  fderiv ℝ (fun w ↦ 2 * y w 1 * (x w 2 * y w 3 - x w 3 * y w 2) +
      2 * y w 0 * (x w 2 * y w 2 + x w 3 * y w 3) + x w 0 * (y w 2 ^ 2 + y w 3 ^ 2)) z I

/-- **The pointwise Weitzenböck identity for `L_x* L_x`.** The squared norm of `L_x y` is the
covariant gradient density plus the potential, up to the remainder `weitzenbockRemainder`. -/
private theorem norm_sq_gaugeFixedOperator_eq {z : ℂ} (hx : DifferentiableAt ℝ x z)
    (hy : DifferentiableAt ℝ y z) :
    ‖gaugeFixedOperator x y z‖ ^ 2 = gaugeFixedGradientDensity x y z +
      gaugeFixedPotential x z (y z) + weitzenbockRemainder x y z := by
  have hxi := (differentiableAt_piLp 2).1 hx
  have hyi := (differentiableAt_piLp 2).1 hy
  rw [gaugeFixedPotential_eq hx, gaugeFixedGradientDensity_def, weitzenbockRemainder,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
  simp (disch := fun_prop) [fderiv_fun_mul, fderiv_fun_add, fderiv_fun_sub, fderiv_fun_pow]
  ring

/-! ### The integrated identity -/

/-- The alternating form `(u, v) ↦ u₀ v₁ - u₁ v₀ + u₃ v₂ - u₂ v₃`. Its values on the two partial
derivatives of a variation are the Jacobian determinants of `(b₁, b₂)` and of `(q, p)`. -/
private def jacobianForm : LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin 4)) :=
  LinearMap.mk₂ ℝ (fun u v ↦ u 0 * v 1 - u 1 * v 0 + u 3 * v 2 - u 2 * v 3)
    (fun _ _ _ ↦ by simp only [PiLp.add_apply]; ring)
    (fun _ _ _ ↦ by simp only [PiLp.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ ↦ by simp only [PiLp.add_apply]; ring)
    (fun _ _ _ ↦ by simp only [PiLp.smul_apply, smul_eq_mul]; ring)

private theorem jacobianForm_isAlt : jacobianForm.IsAlt := fun u ↦ by
  simp only [jacobianForm, LinearMap.mk₂_apply]
  ring

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure]

/-- The potential along a compactly supported continuous variation is integrable. -/
theorem integrable_gaugeFixedPotential (hx : ContDiff ℝ 1 x) (hy : Continuous y)
    (hyc : HasCompactSupport y) : Integrable (fun z ↦ gaugeFixedPotential x z (y z)) μ := by
  have := hx.continuous
  rw [funext fun z ↦ gaugeFixedPotential_eq (hx.differentiable one_ne_zero z) (y z)]
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop)
    (hyc.mono' <| Function.support_subset_iff'.2 fun z hz ↦ ?_)
  simp [image_eq_zero_of_notMem_tsupport hz]

/-- The covariant gradient density of a compactly supported `C¹` variation is integrable. -/
theorem integrable_gaugeFixedGradientDensity (hx : Continuous x) (hy : ContDiff ℝ 1 y)
    (hyc : HasCompactSupport y) : Integrable (gaugeFixedGradientDensity x y) μ := by
  have := hy.continuous
  refine Continuous.integrable_of_hasCompactSupport ?_
    (hyc.mono' <| Function.support_subset_iff'.2 fun z hz ↦ ?_)
  · simp only [funext (gaugeFixedGradientDensity_def x y)]
    fun_prop
  · simp [gaugeFixedGradientDensity_def, (hy.differentiable one_ne_zero z).fderiv_piLp_apply,
      fderiv_of_notMem_tsupport ℝ hz, image_eq_zero_of_notMem_tsupport hz]

/-- The Jacobian form of the two partial derivatives of a compactly supported `C¹` variation is
integrable. -/
private theorem integrable_jacobianForm_fderiv (hy : ContDiff ℝ 1 y) (hyc : HasCompactSupport y) :
    Integrable (fun z ↦ jacobianForm (fderiv ℝ y z 1) (fderiv ℝ y z I)) μ := by
  have hdi (z : ℂ) := (hy.differentiable one_ne_zero z).fderiv_piLp_apply
  refine Continuous.integrable_of_hasCompactSupport ?_
    (hyc.mono' <| Function.support_subset_iff'.2 fun z hz ↦ ?_)
  · simp only [jacobianForm, LinearMap.mk₂_apply, ← hdi]
    fun_prop
  · simp [jacobianForm, fderiv_of_notMem_tsupport ℝ hz]

/-- The remainder of the pointwise Weitzenböck identity is integrable and integrates to zero:
the Jacobian determinants by `integral_bilinForm_fderiv_apply_eq_zero_of_isAlt`, the divergence
because its current is compactly supported. -/
private theorem integral_weitzenbockRemainder (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 2 y)
    (hyc : HasCompactSupport y) :
    Integrable (weitzenbockRemainder x y) μ ∧ ∫ z, weitzenbockRemainder x y z ∂μ = 0 := by
  have hy₁ : ContDiff ℝ 1 y := hy.of_le (by norm_num)
  have hxi := (contDiff_piLp 2).1 hx
  have hyi := (contDiff_piLp 2).1 hy₁
  have hy0 {z : ℂ} (hz : z ∉ tsupport y) (i : Fin 4) : y z i = 0 := by
    simp [image_eq_zero_of_notMem_tsupport hz]
  have hdi (z : ℂ) := (hy₁.differentiable one_ne_zero z).fderiv_piLp_apply
  set J : ℂ → ℝ := fun z ↦ 2 * jacobianForm (fderiv ℝ y z 1) (fderiv ℝ y z I) with hJ
  set W₁ : ℂ → ℝ := fun w ↦ 2 * y w 0 * (x w 2 * y w 3 - x w 3 * y w 2) -
      2 * y w 1 * (x w 2 * y w 2 + x w 3 * y w 3) - x w 1 * (y w 2 ^ 2 + y w 3 ^ 2) with hW₁
  set W₂ : ℂ → ℝ := fun w ↦ 2 * y w 1 * (x w 2 * y w 3 - x w 3 * y w 2) +
      2 * y w 0 * (x w 2 * y w 2 + x w 3 * y w 3) + x w 0 * (y w 2 ^ 2 + y w 3 ^ 2) with hW₂
  have hR : weitzenbockRemainder x y = fun z ↦ J z + fderiv ℝ W₁ z 1 + fderiv ℝ W₂ z I := by
    funext z
    simp only [weitzenbockRemainder, hJ, hW₁, hW₂, jacobianForm, LinearMap.mk₂_apply, hdi z]
  -- The Jacobian term is integrable and integrates to zero.
  have hJi : Integrable J μ := (integrable_jacobianForm_fderiv hy₁ hyc).const_mul 2
  have hJ0 : ∫ z, J z ∂μ = 0 := by
    rw [integral_const_mul,
      integral_bilinForm_fderiv_apply_eq_zero_of_isAlt jacobianForm_isAlt hy hyc 1 I, mul_zero]
  -- The two currents are compactly supported and `C¹`, so their divergences integrate to zero.
  have hint (W : ℂ → ℝ) (hW : ContDiff ℝ 1 W) (hWc : HasCompactSupport W) (v : ℂ) :
      Integrable (fun z ↦ fderiv ℝ W z v) μ :=
    ((hW.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hWc.fderiv_apply (𝕜 := ℝ) v)
  have hW₁d : ContDiff ℝ 1 W₁ := by
    have := hxi; have := hyi
    fun_prop
  have hW₂d : ContDiff ℝ 1 W₂ := by
    have := hxi; have := hyi
    fun_prop
  have hW₁c : HasCompactSupport W₁ :=
    hyc.mono' <| Function.support_subset_iff'.2 fun z hz ↦ by simp [hW₁, hy0 hz]
  have hW₂c : HasCompactSupport W₂ :=
    hyc.mono' <| Function.support_subset_iff'.2 fun z hz ↦ by simp [hW₂, hy0 hz]
  have h₁ : Integrable (fun z ↦ J z + fderiv ℝ W₁ z 1) μ := hJi.add (hint W₁ hW₁d hW₁c 1)
  rw [hR]
  refine ⟨h₁.add (hint W₂ hW₂d hW₂c I), ?_⟩
  rw [integral_add h₁ (hint W₂ hW₂d hW₂c I), integral_add hJi (hint W₁ hW₁d hW₁c 1), hJ0,
    integral_fderiv_apply_eq_zero_of_hasCompactSupport hW₁d hW₁c,
    integral_fderiv_apply_eq_zero_of_hasCompactSupport hW₂d hW₂c]
  simp

/-- **The Weitzenböck formula for `L_x* L_x`.** For a `C¹` field `x` and a compactly supported
`C²` variation `y`,
`∫ |L_x y|² = ∫ (|∇b|² + |∇_a ψ|²) + ∫ V_x(y)`,
with the covariant gradient density `gaugeFixedGradientDensity` and the potential
`gaugeFixedPotential`. No vortex equation is assumed. -/
theorem integral_norm_sq_gaugeFixedOperator (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 2 y)
    (hyc : HasCompactSupport y) :
    ∫ z, ‖gaugeFixedOperator x y z‖ ^ 2 ∂μ =
      (∫ z, gaugeFixedGradientDensity x y z ∂μ) + ∫ z, gaugeFixedPotential x z (y z) ∂μ := by
  have hy₁ : ContDiff ℝ 1 y := hy.of_le (by norm_num)
  have hG := integrable_gaugeFixedGradientDensity (μ := μ) hx.continuous hy₁ hyc
  have hP := integrable_gaugeFixedPotential (μ := μ) hx hy.continuous hyc
  obtain ⟨hRi, hR0⟩ := integral_weitzenbockRemainder (μ := μ) hx hy hyc
  have h₁ : Integrable (fun z ↦ gaugeFixedGradientDensity x y z +
      gaugeFixedPotential x z (y z)) μ := hG.add hP
  simp_rw [fun z ↦ norm_sq_gaugeFixedOperator_eq (hx.differentiable one_ne_zero z)
    (hy₁.differentiable one_ne_zero z)]
  rw [integral_add h₁ hRi, integral_add hG hP, hR0, add_zero]

/-! ### The potential at a vortex -/

/-- The elementary inequality behind the lower bound for the potential at a vortex: with
`s = |φ|²`, `n = |c|` and `B = |b|²`, `P = |ψ|²`, the potential
`s (B + P) - (1 - 4 s) P / 8 + 2 Im ((b₁ + i b₂) conj ψ c)` is at least
`(min s ((12 s - 1) / 8) - n) (B + P)`. -/
private theorem min_sub_mul_le_potential {s cr ci n v₀ v₁ v₂ v₃ : ℝ} (hn : 0 ≤ n)
    (hn' : n ^ 2 = cr ^ 2 + ci ^ 2) :
    (min s ((12 * s - 1) / 8) - n) * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2) ≤
      s * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2) - (1 - 4 * s) / 8 * (v₂ ^ 2 + v₃ ^ 2) +
        2 * (v₀ * (v₂ * ci - v₃ * cr) + v₁ * (v₂ * cr + v₃ * ci)) := by
  set B := v₀ ^ 2 + v₁ ^ 2
  set P := v₂ ^ 2 + v₃ ^ 2
  set S := v₀ * (v₂ * ci - v₃ * cr) + v₁ * (v₂ * cr + v₃ * ci)
  -- Cauchy–Schwarz and the arithmetic-geometric mean bound the cross term by `n (B + P)`.
  have hsq : (2 * S) ^ 2 ≤ (n * (B + P)) ^ 2 := by
    have hcs : S ^ 2 ≤ B * (P * n ^ 2) := by
      rw [hn']
      nlinarith [sq_nonneg (v₀ * (v₂ * cr + v₃ * ci) - v₁ * (v₂ * ci - v₃ * cr))]
    have hB : 0 ≤ B := by positivity
    have hP : 0 ≤ P := by positivity
    nlinarith [sq_nonneg (B - P), sq_nonneg n, mul_nonneg hB hP]
  have hcross := (abs_le_of_sq_le_sq' hsq (by positivity)).1
  have h₁ : min s ((12 * s - 1) / 8) * B ≤ s * B :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
  have h₂ : min s ((12 * s - 1) / 8) * P ≤ (12 * s - 1) / 8 * P :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
  have hBP : v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2 = B + P := by ring
  rw [hBP]
  nlinarith

/-- The coefficient `min (|φ|², (12 |φ|² - 1) / 8) - |∇₁ α|` bounding the potential from below
at a vortex (`vortexMass_mul_norm_sq_le_gaugeFixedPotential`). -/
def vortexMass (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) : ℝ :=
  min (x z 2 ^ 2 + x z 3 ^ 2) ((12 * (x z 2 ^ 2 + x z 3 ^ 2) - 1) / 8) -
    ‖covariantDerivative x z 1‖

/-- The defining formula of `vortexMass`. -/
theorem vortexMass_def (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    vortexMass x z =
      min (x z 2 ^ 2 + x z 3 ^ 2) ((12 * (x z 2 ^ 2 + x z 3 ^ 2) - 1) / 8) -
        ‖covariantDerivative x z 1‖ :=
  (rfl)

/-- At a point where the vortex equation holds, `κ = -(1 - |α|²) / 8` and `∂bar_a α = 0`, so the
potential is `|φ|² |b|² + (3 |φ|² / 2 - 1 / 8) |ψ|²` plus a coupling through `∇₁ α` alone. -/
theorem gaugeFixedPotential_eq_of_equation_eq_zero {z : ℂ} (hx : DifferentiableAt ℝ x z)
    (hsol : equation x z = 0) (v : EuclideanSpace ℝ (Fin 4)) :
    gaugeFixedPotential x z v =
      (x z 2 ^ 2 + x z 3 ^ 2) * (v 0 ^ 2 + v 1 ^ 2) +
        (3 * (x z 2 ^ 2 + x z 3 ^ 2) / 2 - 1 / 8) * (v 2 ^ 2 + v 3 ^ 2) +
        2 * ((covariantDerivative x z 1).im * (v 0 * v 2 + v 1 * v 3) +
          (covariantDerivative x z 1).re * (v 1 * v 2 - v 0 * v 3)) := by
  have hcurv := curvature_eq_of_equation_eq_zero hsol
  have he1 := congrArg (fun e : EuclideanSpace ℝ (Fin 3) ↦ e 1) hsol
  have he2 := congrArg (fun e : EuclideanSpace ℝ (Fin 3) ↦ e 2) hsol
  simp only [equation_apply_one, equation_apply_two, PiLp.zero_apply] at he1 he2
  have hp := (differentiableAt_piLp 2).1 hx 2
  have hq := (differentiableAt_piLp 2).1 hx 3
  have hcr := covariantDerivative_re hp hq 1
  have hci := covariantDerivative_im hp hq 1
  simp only [one_re, one_im, mul_one, mul_zero, add_zero] at hcr hci
  rw [gaugeFixedPotential_eq hx, hcr, hci]
  -- By the holomorphicity rows, the cross term only involves `∇₁ α`.
  linear_combination (v 2 ^ 2 + v 3 ^ 2) * hcurv + 2 * (v 0 * v 3 - v 1 * v 2) * he1 -
    2 * (v 0 * v 2 + v 1 * v 3) * he2

/-- At a point where the vortex equation holds, the potential is bounded below by
`min (|φ|², (12 |φ|² - 1) / 8) - |∇₁ α|` times `|v|²`. -/
theorem vortexMass_mul_norm_sq_le_gaugeFixedPotential {z : ℂ}
    (hx : DifferentiableAt ℝ x z) (hsol : equation x z = 0) (v : EuclideanSpace ℝ (Fin 4)) :
    vortexMass x z * ‖v‖ ^ 2 ≤ gaugeFixedPotential x z v := by
  have hn : ‖covariantDerivative x z 1‖ ^ 2 =
      (covariantDerivative x z 1).re ^ 2 + (covariantDerivative x z 1).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [vortexMass, gaugeFixedPotential_eq_of_equation_eq_zero hx hsol,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
  convert min_sub_mul_le_potential (norm_nonneg _) hn using 1
  ring

/-! ### The Gårding inequality at a vortex -/

/-- When `|α| → 1` and `∇₁ α → 0`, the coefficient `vortexMass` exceeds any `a < 1 / 4` off a
closed disc, on which it is bounded below. -/
private theorem exists_lt_vortexMass (hx : ContDiff ℝ 1 x)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hcov : Tendsto (fun z ↦ covariantDerivative x z 1) (cocompact ℂ) (𝓝 0))
    {a : ℝ} (ha : a < 1 / 4) :
    ∃ R > 0, ∃ b : ℝ, ∀ z, (z ∈ closedBall 0 R → b ≤ vortexMass x z) ∧
      (z ∉ closedBall 0 R → a < vortexMass x z) := by
  have := hx.continuous
  have hmc : Continuous (vortexMass x) := by
    have := continuous_covariantDerivative hx 1
    unfold vortexMass
    fun_prop
  have hs : Tendsto (fun z ↦ x z 2 ^ 2 + x z 3 ^ 2) (cocompact ℂ) (𝓝 (1 / 4)) := by
    convert hlim.const_mul (1 / 4 : ℝ) using 1
    · funext z
      ring
    · norm_num
  -- The coefficient tends to the vacuum mass `1 / 4` at infinity.
  have hml : Tendsto (vortexMass x) (cocompact ℂ) (𝓝 (1 / 4)) := by
    unfold vortexMass
    convert (hs.min (((hs.const_mul 12).sub_const 1).div_const 8)).sub hcov.norm using 2
    norm_num
  obtain ⟨R, _, hR⟩ := hasBasis_cobounded_norm.mem_iff.mp
    ((Metric.cobounded_eq_cocompact (α := ℂ)).symm ▸ hml.eventually (lt_mem_nhds ha))
  obtain ⟨b, hb⟩ := (isCompact_closedBall (0 : ℂ) (max R 1)).bddBelow_image hmc.continuousOn
  refine ⟨max R 1, by positivity, b, fun z ↦ ⟨fun hz ↦ hb ⟨z, hz, rfl⟩, fun hz ↦ hR ?_⟩⟩
  simp only [mem_closedBall, dist_zero_right, not_le] at hz
  exact (le_max_left R 1).trans hz.le

/-- **The Gårding inequality for the gauge-fixed operator at a vortex.** Let `x` be a `C¹`
solution of the vortex equation on the whole plane with `|α| → 1` and `∇₁ α → 0` at infinity.
For every `a < 1 / 4` there are a radius `R > 0` and a constant `K`, depending only on the vortex
and on `a`, such that every compactly supported `C²` variation `y` satisfies
`∫ (|∇b|² + |∇_a ψ|²) + a ∫ |y|² ≤ ∫ |L_x y|² + K ∫_{|z| ≤ R} |y|²`. -/
theorem exists_integral_gaugeFixedGradientDensity_add_mul_integral_norm_sq_le
    (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hcov : Tendsto (fun z ↦ covariantDerivative x z 1) (cocompact ℂ) (𝓝 0))
    {a : ℝ} (ha : a < 1 / 4) :
    ∃ R > 0, ∃ K : ℝ, ∀ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 y →
      HasCompactSupport y →
      (∫ z, gaugeFixedGradientDensity x y z ∂μ) + a * ∫ z, ‖y z‖ ^ 2 ∂μ ≤
        ∫ z, ‖gaugeFixedOperator x y z‖ ^ 2 ∂μ + K * ∫ z in closedBall 0 R, ‖y z‖ ^ 2 ∂μ := by
  obtain ⟨R, hR, b, hb⟩ := exists_lt_vortexMass hx hlim hcov ha
  refine ⟨R, hR, a - b, fun y hy hyc ↦ ?_⟩
  have hn : Integrable (fun z ↦ ‖y z‖ ^ 2) μ :=
    Continuous.integrable_of_hasCompactSupport (f := fun z ↦ ‖y z‖ ^ 2)
      (hy.continuous.norm.pow 2) (hyc.comp_left (g := fun v ↦ ‖v‖ ^ 2) (by simp))
  have hnB := (hn.indicator (measurableSet_closedBall (x := (0 : ℂ)) (ε := R))).const_mul (a - b)
  -- Pointwise, the potential is at least `a |y|²` off the disc and `b |y|²` on it.
  have hpt (z : ℂ) : a * ‖y z‖ ^ 2 - (a - b) * (closedBall 0 R).indicator
      (fun z ↦ ‖y z‖ ^ 2) z ≤ gaugeFixedPotential x z (y z) := by
    refine le_trans ?_ (vortexMass_mul_norm_sq_le_gaugeFixedPotential
      (hx.differentiable one_ne_zero z) (hsol z) (y z))
    by_cases hz : z ∈ closedBall (0 : ℂ) R
    · rw [Set.indicator_of_mem hz]
      nlinarith [mul_le_mul_of_nonneg_right ((hb z).1 hz) (sq_nonneg ‖y z‖)]
    · rw [Set.indicator_of_notMem hz, mul_zero, sub_zero]
      exact mul_le_mul_of_nonneg_right ((hb z).2 hz).le (sq_nonneg _)
  have hlow : ∫ z, (a * ‖y z‖ ^ 2 - (a - b) * (closedBall 0 R).indicator
      (fun z ↦ ‖y z‖ ^ 2) z) ∂μ ≤ ∫ z, gaugeFixedPotential x z (y z) ∂μ :=
    integral_mono ((hn.const_mul a).sub hnB)
      (integrable_gaugeFixedPotential hx hy.continuous hyc) hpt
  rw [integral_sub (hn.const_mul a) hnB, integral_const_mul, integral_const_mul,
    integral_indicator measurableSet_closedBall] at hlow
  rw [integral_norm_sq_gaugeFixedOperator hx hy hyc]
  linarith

/-! ### The Gårding inequality on a disc -/

/-- The integrand of the energy identity `integral_norm_sq_gaugeFixedOperator`: the covariant
gradient density of `u` plus the zeroth-order potential. -/
private def energyIntegrand (x u : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) : ℝ :=
  gaugeFixedGradientDensity x u z + gaugeFixedPotential x z (u z)

/-- The pointwise lower bound behind the Gårding inequality: where the vortex equation holds or
`u` vanishes, the energy integrand controls half the squared gradient, up to a zeroth-order term
whose coefficient is bounded by the coefficients of `x`. -/
private theorem sum_sq_div_two_le (u : ℂ → EuclideanSpace ℝ (Fin 4)) {z : ℂ}
    (hx : DifferentiableAt ℝ x z) (hsol : u z ≠ 0 → equation x z = 0) :
    (∑ i, (fderiv ℝ (fun w ↦ u w i) z 1 ^ 2 + fderiv ℝ (fun w ↦ u w i) z I ^ 2)) / 2 ≤
      energyIntegrand x u z +
        (x z 0 ^ 2 + x z 1 ^ 2 + ‖covariantDerivative x z 1‖ + 2) * ‖u z‖ ^ 2 := by
  -- The potential is at least `-(1 / 8 + |∇₁ α|) |u|²`.
  have hV : -(1 / 8 + ‖covariantDerivative x z 1‖) * ‖u z‖ ^ 2 ≤
      gaugeFixedPotential x z (u z) := by
    by_cases hz : u z = 0
    · simp [gaugeFixedPotential_def, hz]
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
      (vortexMass_mul_norm_sq_le_gaugeFixedPotential hx (hsol hz) (u z))
    have hs : 0 ≤ x z 2 ^ 2 + x z 3 ^ 2 := by positivity
    have hm : -(1 / 8) ≤ min (x z 2 ^ 2 + x z 3 ^ 2) ((12 * (x z 2 ^ 2 + x z 3 ^ 2) - 1) / 8) :=
      le_min (by linarith) (by linarith)
    rw [vortexMass_def]
    linarith
  have hN : ‖u z‖ ^ 2 = u z 0 ^ 2 + u z 1 ^ 2 + u z 2 ^ 2 + u z 3 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
  rw [hN] at hV ⊢
  rw [energyIntegrand, gaugeFixedGradientDensity_def, Fin.sum_univ_four]
  nlinarith [norm_nonneg (covariantDerivative x z 1),
    sq_nonneg (fderiv ℝ (fun w ↦ u w 2) z 1 - 2 * (x z 0 * u z 3)),
    sq_nonneg (fderiv ℝ (fun w ↦ u w 2) z I - 2 * (x z 1 * u z 3)),
    sq_nonneg (fderiv ℝ (fun w ↦ u w 3) z 1 + 2 * (x z 0 * u z 2)),
    sq_nonneg (fderiv ℝ (fun w ↦ u w 3) z I + 2 * (x z 1 * u z 2)),
    mul_nonneg (sq_nonneg (x z 0)) (sq_nonneg (u z 0)),
    mul_nonneg (sq_nonneg (x z 0)) (sq_nonneg (u z 1)),
    mul_nonneg (sq_nonneg (x z 1)) (sq_nonneg (u z 0)),
    mul_nonneg (sq_nonneg (x z 1)) (sq_nonneg (u z 1)),
    sq_nonneg (u z 0), sq_nonneg (u z 1), sq_nonneg (u z 2), sq_nonneg (u z 3)]

/-- **The Gårding inequality for the gauge-fixed vortex operator on a disc.** For a `C¹` field `x`
and a radius `r`, there is a constant `C` such that every `C²` variation `u` vanishing outside the
closed disc of radius `r`, on whose support the vortex equation holds, satisfies
`∫ |Du|² ≤ C (∫ |L_x u|² + ∫ |u|²)`. -/
theorem exists_integral_norm_fderiv_sq_le (hx : ContDiff ℝ 1 x) (r : ℝ) :
    ∃ C, ∀ u : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 u → (∀ z, r < ‖z‖ → u z = 0) →
      (∀ z, u z ≠ 0 → equation x z = 0) →
      ∫ z, ‖fderiv ℝ u z‖ ^ 2 ≤
        C * ((∫ z, ‖gaugeFixedOperator x u z‖ ^ 2) + ∫ z, ‖u z‖ ^ 2) := by
  have hxi (i : Fin 4) : Continuous fun z ↦ x z i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hx.continuous
  -- Bound the coefficient of the zeroth-order term on the disc.
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
    (f := fun z ↦ x z 0 ^ 2 + x z 1 ^ 2 + ‖covariantDerivative x z 1‖ + 2)
    (((((hxi 0).pow 2).add ((hxi 1).pow 2)).add
      (continuous_covariantDerivative hx 1).norm).add continuous_const).continuousOn
  refine ⟨4 * max M 1, fun u hu hr hsol ↦ ?_⟩
  have hc : HasCompactSupport u :=
    HasCompactSupport.intro (isCompact_closedBall 0 r) fun z hz ↦ hr z (by simpa using hz)
  have hG := integrable_gaugeFixedGradientDensity (μ := volume) hx.continuous
    (hu.of_le one_le_two) hc
  have hV := integrable_gaugeFixedPotential (μ := volume) hx hu.continuous hc
  have hQi : Integrable (energyIntegrand x u) := hG.add hV
  have hE : ∫ z, ‖gaugeFixedOperator x u z‖ ^ 2 = ∫ z, energyIntegrand x u z := by
    rw [integral_norm_sq_gaugeFixedOperator hx hu hc, ← integral_add hG hV]
    rfl
  have hn : Integrable fun z ↦ ‖u z‖ ^ 2 :=
    Continuous.integrable_of_hasCompactSupport (f := fun z ↦ ‖u z‖ ^ 2)
      (hu.continuous.norm.pow 2) (hc.comp_left (g := fun v ↦ ‖v‖ ^ 2) (by simp))
  have hfi : Integrable fun z ↦ ‖fderiv ℝ u z‖ ^ 2 :=
    Continuous.integrable_of_hasCompactSupport (f := fun z ↦ ‖fderiv ℝ u z‖ ^ 2)
      ((hu.continuous_fderiv two_ne_zero).norm.pow 2)
      ((hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L ↦ ‖L‖ ^ 2) (by simp))
  -- Pointwise, `|Du|² ≤ 2 (|∂₁u|² + |∂₂u|²) ≤ 4 E + 4 M |u|²` for the energy integrand `E`.
  have hpt (z : ℂ) :
      ‖fderiv ℝ u z‖ ^ 2 ≤ 4 * energyIntegrand x u z + 4 * max M 1 * ‖u z‖ ^ 2 := by
    have hD := norm_fderiv_sq_le_two_mul_sum_sq u z
    have hS := sum_sq_div_two_le u (hx.differentiable one_ne_zero z) (hsol z)
    have hMu : (x z 0 ^ 2 + x z 1 ^ 2 + ‖covariantDerivative x z 1‖ + 2) * ‖u z‖ ^ 2 ≤
        max M 1 * ‖u z‖ ^ 2 := by
      by_cases hz : r < ‖z‖
      · simp [hr z hz]
      · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact (le_abs_self _).trans ((hM z (by simpa using hz)).trans (le_max_left _ _))
    linarith
  have hE0 : 0 ≤ ∫ z, energyIntegrand x u z := hE ▸ integral_nonneg fun z ↦ sq_nonneg _
  rw [hE]
  calc ∫ z, ‖fderiv ℝ u z‖ ^ 2
      ≤ ∫ z, (4 * energyIntegrand x u z + 4 * max M 1 * ‖u z‖ ^ 2) :=
        integral_mono hfi ((hQi.const_mul 4).add (hn.const_mul _)) hpt
    _ = 4 * (∫ z, energyIntegrand x u z) + 4 * max M 1 * ∫ z, ‖u z‖ ^ 2 := by
        rw [integral_add (hQi.const_mul 4) (hn.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ 4 * max M 1 * ((∫ z, energyIntegrand x u z) + ∫ z, ‖u z‖ ^ 2) := by
        have : 1 ≤ max M 1 := le_max_right _ _
        nlinarith

end TauCeti.Vortex
