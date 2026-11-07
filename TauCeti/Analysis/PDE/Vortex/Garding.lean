/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.GaugeFixed
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
and of `(q, p)`, and by the divergence of a current bilinear in `x` and `y`; both integrate to
zero. The curvature and `∂_a α` enter when derivatives of `y` are moved onto the field. At the
vacuum the identity reduces to `‖L₀ y‖² = ‖∇y‖² + ‖y‖² / 4`
(`TauCeti.Vortex.integral_norm_sq_vacuumOperator`). Unlike the energy identity
`TauCeti.Vortex.integral_norm_sq_gaugeFixedOperator_of_equation_eq_zero`, it does not assume the
vortex equation on the support of the variation.

At a vortex `κ = -(1 - |α|²) / 8` and `∂bar_a α = 0`, so the potential is
`|φ|² |b|² + ((12 |φ|² - 1) / 8) |ψ|²` up to a cross term bounded by `|∇₁ α| |y|²`. When
`|α| → 1` and `∇₁ α → 0` at infinity, the potential therefore tends to the vacuum mass `1 / 4`.
For every `a < 1 / 4` this gives a Gårding inequality with a compact remainder
(`TauCeti.Vortex.exists_integral_gaugeFixedGradientDensity_add_mul_integral_norm_sq_le`):

`∫ (|∇b|² + |∇_a ψ|²) + a ∫ |y|² ≤ ∫ |L_x y|² + K ∫_{|z| ≤ R} |y|²`.

For variations vanishing on the disc of radius `R` it recovers the exterior bound
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
  have hp : DifferentiableAt ℝ (fun w ↦ x w 2) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) 2).differentiableAt.comp z hx :)
  have hq : DifferentiableAt ℝ (fun w ↦ x w 3) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) 3).differentiableAt.comp z hx :)
  have h1r := re_covariantDerivative hp hq 1
  have h1i := im_covariantDerivative hp hq 1
  have hIr := re_covariantDerivative hp hq I
  have hIi := im_covariantDerivative hp hq I
  simp only [one_re, one_im, I_re, I_im] at h1r h1i hIr hIi
  rw [gaugeFixedPotential_def, curvature_apply, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
  simp only [mul_im, mul_re, sub_re, sub_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im,
    h1r, h1i, hIr, hIi]
  ring

/-- The remainder in the pointwise Weitzenböck identity: twice the sum of the Jacobian
determinants of `(b₁, b₂)` and of `(q, p)`, plus the divergence `∂₁ W₁ + ∂₂ W₂` of a current that
is bilinear in the field and the variation. It integrates to zero against compactly supported
variations (`integral_weitzenbockRemainder`). -/
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
  have hxi (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ x w i) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hx :)
  have hyi (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ y w i) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hy :)
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

/-- A real function on the plane that vanishes off the topological support of a compactly
supported variation has compact support. -/
private theorem hasCompactSupport_of_notMem_tsupport (hyc : HasCompactSupport y) {f : ℂ → ℝ}
    (hf : ∀ z, z ∉ tsupport y → f z = 0) : HasCompactSupport f :=
  hyc.mono' fun z hz ↦ by_contra fun h ↦ hz (hf z h)

/-- Off the topological support of a variation its partial derivatives vanish. -/
private theorem fderiv_apply_eq_zero_of_notMem_tsupport {z : ℂ} (hz : z ∉ tsupport y)
    (i : Fin 4) (v : ℂ) : fderiv ℝ (fun w ↦ y w i) z v = 0 := by
  have h : (fun w ↦ y w i) =ᶠ[𝓝 z] fun _ ↦ 0 :=
    (notMem_tsupport_iff_eventuallyEq.mp hz).mono fun w hw ↦ by simp [hw]
  simp [h.fderiv_eq]

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure]

/-- The potential along a compactly supported `C¹` variation is integrable. -/
private theorem integrable_gaugeFixedPotential (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y)
    (hyc : HasCompactSupport y) : Integrable (fun z ↦ gaugeFixedPotential x z (y z)) μ := by
  have hxi (i : Fin 4) : ContDiff ℝ 1 fun w ↦ x w i :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hx :)
  have hcx (i : Fin 4) : Continuous fun w ↦ x w i := (hxi i).continuous
  have hcy (i : Fin 4) : Continuous fun w ↦ y w i :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hy.continuous :)
  have hdx (i : Fin 4) (v : ℂ) : Continuous fun z ↦ fderiv ℝ (fun w ↦ x w i) z v :=
    ((hxi i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  rw [funext fun z ↦ gaugeFixedPotential_eq (hx.differentiable one_ne_zero z) (y z)]
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop)
    (hasCompactSupport_of_notMem_tsupport hyc fun z hz ↦ ?_)
  simp [image_eq_zero_of_notMem_tsupport hz]

/-- The covariant gradient density of a compactly supported `C¹` variation is integrable. -/
private theorem integrable_gaugeFixedGradientDensity (hx : Continuous x) (hy : ContDiff ℝ 1 y)
    (hyc : HasCompactSupport y) : Integrable (gaugeFixedGradientDensity x y) μ := by
  have hcx (i : Fin 4) : Continuous fun w ↦ x w i :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hx :)
  have hcy (i : Fin 4) : Continuous fun w ↦ y w i :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hy.continuous :)
  have hdy (i : Fin 4) (v : ℂ) : Continuous fun z ↦ fderiv ℝ (fun w ↦ y w i) z v :=
    ((((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hy).continuous_fderiv
      one_ne_zero).clm_apply continuous_const :)
  refine Continuous.integrable_of_hasCompactSupport ?_
    (hasCompactSupport_of_notMem_tsupport hyc fun z hz ↦ ?_)
  · simp only [funext (gaugeFixedGradientDensity_def x y)]
    fun_prop
  · simp [gaugeFixedGradientDensity_def, fderiv_apply_eq_zero_of_notMem_tsupport hz,
      image_eq_zero_of_notMem_tsupport hz]

/-- The Jacobian form of the two partial derivatives of a compactly supported `C¹` variation is
integrable. -/
private theorem integrable_jacobianForm_fderiv (hy : ContDiff ℝ 1 y) (hyc : HasCompactSupport y) :
    Integrable (fun z ↦ jacobianForm (fderiv ℝ y z 1) (fderiv ℝ y z I)) μ := by
  have hdi (z : ℂ) (i : Fin 4) (v : ℂ) : fderiv ℝ (fun w ↦ y w i) z v = fderiv ℝ y z v i :=
    congrArg (· v) ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp z
      (hy.differentiable one_ne_zero z).hasFDerivAt).fderiv
  have hdy (i : Fin 4) (v : ℂ) : Continuous fun z ↦ fderiv ℝ (fun w ↦ y w i) z v :=
    ((((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hy).continuous_fderiv
      one_ne_zero).clm_apply continuous_const :)
  refine Continuous.integrable_of_hasCompactSupport ?_
    (hasCompactSupport_of_notMem_tsupport hyc fun z hz ↦ ?_)
  · simp only [jacobianForm, LinearMap.mk₂_apply, ← hdi]
    fun_prop
  · simp [jacobianForm, ← hdi, fderiv_apply_eq_zero_of_notMem_tsupport hz]

/-- The remainder of the pointwise Weitzenböck identity is integrable and integrates to zero:
the Jacobian determinants by `integral_bilinForm_fderiv_apply_eq_zero_of_isAlt`, the divergence
because its current is compactly supported. -/
private theorem integral_weitzenbockRemainder (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 2 y)
    (hyc : HasCompactSupport y) :
    Integrable (weitzenbockRemainder x y) μ ∧ ∫ z, weitzenbockRemainder x y z ∂μ = 0 := by
  have hy₁ : ContDiff ℝ 1 y := hy.of_le (by norm_num)
  have hxi (i : Fin 4) : ContDiff ℝ 1 fun w ↦ x w i :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hx :)
  have hyi (i : Fin 4) : ContDiff ℝ 1 fun w ↦ y w i :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hy₁ :)
  have hy0 {z : ℂ} (hz : z ∉ tsupport y) (i : Fin 4) : y z i = 0 := by
    simp [image_eq_zero_of_notMem_tsupport hz]
  have hdi (z : ℂ) (i : Fin 4) (v : ℂ) : fderiv ℝ (fun w ↦ y w i) z v = fderiv ℝ y z v i :=
    congrArg (· v) ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp z
      (hy₁.differentiable one_ne_zero z).hasFDerivAt).fderiv
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
    hasCompactSupport_of_notMem_tsupport hyc fun z hz ↦ by simp [hW₁, hy0 hz]
  have hW₂c : HasCompactSupport W₂ :=
    hasCompactSupport_of_notMem_tsupport hyc fun z hz ↦ by simp [hW₂, hy0 hz]
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
  have hP := integrable_gaugeFixedPotential (μ := μ) hx hy₁ hyc
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
private def vortexMass (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) : ℝ :=
  min (x z 2 ^ 2 + x z 3 ^ 2) ((12 * (x z 2 ^ 2 + x z 3 ^ 2) - 1) / 8) -
    ‖covariantDerivative x z 1‖

/-- At a point where the vortex equation holds, the potential is bounded below by
`min (|φ|², (12 |φ|² - 1) / 8) - |∇₁ α|` times `|v|²`. -/
private theorem vortexMass_mul_norm_sq_le_gaugeFixedPotential {z : ℂ}
    (hx : DifferentiableAt ℝ x z) (hsol : equation x z = 0) (v : EuclideanSpace ℝ (Fin 4)) :
    vortexMass x z * ‖v‖ ^ 2 ≤ gaugeFixedPotential x z v := by
  have hcurv := curvature_eq_of_equation_eq_zero hsol
  have he1 := congrArg (fun e : EuclideanSpace ℝ (Fin 3) ↦ e 1) hsol
  have he2 := congrArg (fun e : EuclideanSpace ℝ (Fin 3) ↦ e 2) hsol
  simp only [equation_apply_one, equation_apply_two, PiLp.zero_apply] at he1 he2
  have hp : DifferentiableAt ℝ (fun w ↦ x w 2) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) 2).differentiableAt.comp z hx :)
  have hq : DifferentiableAt ℝ (fun w ↦ x w 3) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) 3).differentiableAt.comp z hx :)
  have hcr := re_covariantDerivative hp hq 1
  have hci := im_covariantDerivative hp hq 1
  simp only [one_re, one_im, mul_one, mul_zero, add_zero] at hcr hci
  have hn : ‖covariantDerivative x z 1‖ ^ 2 =
      (covariantDerivative x z 1).re ^ 2 + (covariantDerivative x z 1).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [vortexMass, gaugeFixedPotential_eq hx, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
  -- By the holomorphicity rows, the cross term only involves `∇₁ α`.
  convert min_sub_mul_le_potential (norm_nonneg _) hn using 1
  rw [hcr, hci]
  linear_combination (v 2 ^ 2 + v 3 ^ 2) * hcurv + 2 * (v 0 * v 3 - v 1 * v 2) * he1 -
    2 * (v 0 * v 2 + v 1 * v 3) * he2

/-! ### The Gårding inequality at a vortex -/

/-- The covariant derivative `∇₁ α` of the section of a `C¹` field is continuous. -/
private theorem continuous_covariantDerivative_one (hx : ContDiff ℝ 1 x) :
    Continuous fun z ↦ covariantDerivative x z 1 := by
  have hxi (i : Fin 4) : ContDiff ℝ 1 fun w ↦ x w i :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hx :)
  have hcx (i : Fin 4) : Continuous fun w ↦ x w i := (hxi i).continuous
  have hdx (i : Fin 4) (v : ℂ) : Continuous fun z ↦ fderiv ℝ (fun w ↦ x w i) z v :=
    ((hxi i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  simp only [covariantDerivative_apply, sectionValue_apply,
    fderiv_sectionValue_apply ((hxi 2).differentiable one_ne_zero _)
      ((hxi 3).differentiable one_ne_zero _)]
  fun_prop

/-- When `|α| → 1` and `∇₁ α → 0`, the coefficient `vortexMass` exceeds any `a < 1 / 4` off a
closed disc, on which it is bounded below. -/
private theorem exists_lt_vortexMass (hx : ContDiff ℝ 1 x)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hcov : Tendsto (fun z ↦ covariantDerivative x z 1) (cocompact ℂ) (𝓝 0))
    {a : ℝ} (ha : a < 1 / 4) :
    ∃ R > 0, ∃ b : ℝ, ∀ z, (z ∈ closedBall 0 R → b ≤ vortexMass x z) ∧
      (z ∉ closedBall 0 R → a < vortexMass x z) := by
  have hxi (i : Fin 4) : Continuous fun w ↦ x w i :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hx.continuous :)
  have hmc : Continuous (vortexMass x) := by
    have := continuous_covariantDerivative_one hx
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
  have hy₁ : ContDiff ℝ 1 y := hy.of_le (by norm_num)
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
    integral_mono ((hn.const_mul a).sub hnB) (integrable_gaugeFixedPotential hx hy₁ hyc) hpt
  rw [integral_sub (hn.const_mul a) hnB, integral_const_mul, integral_const_mul,
    integral_indicator measurableSet_closedBall] at hlow
  rw [integral_norm_sq_gaugeFixedOperator hx hy hyc]
  linarith

end TauCeti.Vortex
