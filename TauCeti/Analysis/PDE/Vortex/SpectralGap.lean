/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.ExteriorEstimate
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.Analysis.Sobolev.Poincare.Schrodinger

/-!
# The spectral gap of `L_x L_x*` at a plane vortex

For an actual plane vortex `x` with `|α| → 1`, the formal adjoint `L_x*` of the gauge-fixed
operator `L_x = d₀* ⊕ d₁` is coercive on the whole plane: there is `c > 0`, depending on the
vortex, with

`c ∫ |η|² ≤ ∫ |L_x* η|²`

for every compactly supported `C²` field `η`. Equivalently, the quadratic form of `L_x L_x*` is
bounded below by `c` on test fields, so `L_x L_x*` has a spectral gap. On a Sobolev realization
of `L_x` this is the estimate that forces the cokernel to vanish and makes
`L_x* (L_x L_x*)⁻¹` a right inverse of `L_x`. No decay of the connection or of derivatives is
assumed.

The exterior estimate `exists_exterior_integral_norm_sq_gaugeFixedAdjoint_ge` gives such a bound
only for fields vanishing near the zeros of `α`. Globally the Weitzenböck formula at a vortex
(`gaugeFixedOperator_gaugeFixedAdjoint_of_equation_eq_zero`) still gives, after integration,

`∫ |L_x* η|² ≥ ∫ (|∇η₀|² + |∇η₁|² + P (η₀² + η₁²)) + (1/8) ∫ (η₂² + η₃²)`,  `P = |α|²/4`.

The section components have the positive potential `1/8`, but the connection components only
the potential `P`, which vanishes at the zeros of `α`. Since `P → 1/4` at infinity, the
Poincaré inequality for Schrödinger forms
(`TauCeti.exists_pos_mul_integral_norm_sq_le_integral_norm_fderiv_sq_add_integral_mul_norm_sq`)
bounds the connection part below by a positive multiple of `∫ (η₀² + η₁²)`.

These are classical test-field estimates. They do not construct the completed Sobolev
realization of `L_x` or a uniform gap over the noncompact vortex moduli space.

## Main results

* `TauCeti.Vortex.exists_pos_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint`: the
  global coercivity of `L_x*` at a vortex with `|α| → 1`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

namespace TauCeti.Vortex

open Complex MeasureTheory Filter
open scoped Laplacian Topology RealInnerProductSpace

variable {x η : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- The pointwise Weitzenböck bound at a vortex point, keeping the gradients of the two
connection components and the potentials `P = |α|²/4` and `1/8`. -/
private theorem le_inner_gaugeFixedOperator_gaugeFixedAdjoint_add_laplacian {z : ℂ}
    (hx : DifferentiableAt ℝ x z) (hη : ContDiffAt ℝ 2 η z) (hsol : equation x z = 0) :
    (‖fderiv ℝ (fun w ↦ η w 0) z‖ ^ 2 + 2 * (x z 2 ^ 2 + x z 3 ^ 2) * η z 0 ^ 2) / 2 +
      (‖fderiv ℝ (fun w ↦ η w 1) z‖ ^ 2 + 2 * (x z 2 ^ 2 + x z 3 ^ 2) * η z 1 ^ 2) / 2 +
      (η z 2 ^ 2 + η z 3 ^ 2) / 8 ≤
      ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ +
        Δ (fun w ↦ ‖η w‖ ^ 2) z / 2 := by
  have hdi (i : Fin 4) : fderiv ℝ (fun w ↦ η w i) z =
      (EuclideanSpace.proj i) ∘L fderiv ℝ η z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp z
      (hη.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hΔi (i : Fin 4) : Δ (fun w ↦ η w i) z = (Δ η z) i :=
    hη.laplacian_CLM_comp_left (l := EuclideanSpace.proj (𝕜 := ℝ) i)
  -- The operator norm of a gradient is controlled by its two partial derivatives.
  have hnorm (i : Fin 4) : ‖fderiv ℝ (fun w ↦ η w i) z‖ ^ 2 ≤
      2 * (fderiv ℝ η z 1 i ^ 2 + fderiv ℝ η z I i ^ 2) := by
    have h := (fderiv ℝ (fun w ↦ η w i) z).opNorm_sq_le_card_mul_sum_norm_apply_sq_orthonormalBasis
      orthonormalBasisOneI
    simpa [hdi, Fin.sum_univ_two] using h
  have h₀ := hnorm 0
  have h₁ := hnorm 1
  suffices key : fderiv ℝ η z 1 0 ^ 2 + fderiv ℝ η z I 0 ^ 2 +
      (x z 2 ^ 2 + x z 3 ^ 2) * η z 0 ^ 2 +
      (fderiv ℝ η z 1 1 ^ 2 + fderiv ℝ η z I 1 ^ 2 + (x z 2 ^ 2 + x z 3 ^ 2) * η z 1 ^ 2) +
      (η z 2 ^ 2 + η z 3 ^ 2) / 8 ≤
      ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ +
        Δ (fun w ↦ ‖η w‖ ^ 2) z / 2 by
    linarith
  rw [gaugeFixedOperator_gaugeFixedAdjoint_of_equation_eq_zero hx hη hsol,
    hη.laplacian_norm_sq orthonormalBasisOneI]
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four, Fin.isValue, hΔi, one_div, hdi,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    coe_orthonormalBasisOneI, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_two,
    Matrix.cons_val_fin_one]
  -- Complete the section derivatives to covariant-gradient squares; what remains is the
  -- nonnegative potential `P / 2` on the section components.
  have hp : 0 ≤ (x z 2 ^ 2 + x z 3 ^ 2) / 2 := by positivity
  nlinarith only [
    sq_nonneg (fderiv ℝ η z 1 2 - x z 0 * η z 3),
    sq_nonneg (fderiv ℝ η z I 2 - x z 1 * η z 3),
    sq_nonneg (fderiv ℝ η z 1 3 + x z 0 * η z 2),
    sq_nonneg (fderiv ℝ η z I 3 + x z 1 * η z 2),
    mul_nonneg hp (sq_nonneg (η z 2)), mul_nonneg hp (sq_nonneg (η z 3))]

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure]

/-- The integrated Weitzenböck bound at a vortex: `∫ |L_x* η|²` dominates the gradients and the
potential `P = |α|²/4` of the two connection components and the potential `1/8` of the section
components. The integrability of the left side is a hypothesis, supplied by the caller. -/
private theorem integral_le_integral_norm_sq_gaugeFixedAdjoint (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0) (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
    (hG : Integrable (fun z ↦
      (‖fderiv ℝ (fun w ↦ η w 0) z‖ ^ 2 + 2 * (x z 2 ^ 2 + x z 3 ^ 2) * η z 0 ^ 2) / 2 +
      (‖fderiv ℝ (fun w ↦ η w 1) z‖ ^ 2 + 2 * (x z 2 ^ 2 + x z 3 ^ 2) * η z 1 ^ 2) / 2 +
      (η z 2 ^ 2 + η z 3 ^ 2) / 8) μ) :
    ∫ z, ((‖fderiv ℝ (fun w ↦ η w 0) z‖ ^ 2 + 2 * (x z 2 ^ 2 + x z 3 ^ 2) * η z 0 ^ 2) / 2 +
      (‖fderiv ℝ (fun w ↦ η w 1) z‖ ^ 2 + 2 * (x z 2 ^ 2 + x z 3 ^ 2) * η z 1 ^ 2) / 2 +
      (η z 2 ^ 2 + η z 3 ^ 2) / 8) ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ := by
  have hL := contDiff_gaugeFixedAdjoint hx hη
  have hLc := hasCompactSupport_gaugeFixedAdjoint (x := x) hηc
  have hi : Integrable (fun z ↦ ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫) μ :=
    ((continuous_gaugeFixedOperator hx.continuous hL).inner
      hη.continuous).integrable_of_hasCompactSupport
      (hηc.mono fun z hz hzero ↦ hz (by simp [hzero]))
  have hnc : HasCompactSupport (fun z ↦ ‖η z‖ ^ 2) :=
    hηc.comp_left (g := fun v ↦ ‖v‖ ^ 2) (by simp)
  have hΔ : Integrable (fun z ↦ Δ (fun w ↦ ‖η w‖ ^ 2) z / 2) μ :=
    ((hη.norm_sq ℝ).continuous_laplacian.div_const 2).integrable_of_hasCompactSupport
      (hnc.laplacian.comp_left (g := fun t : ℝ ↦ t / 2) (by simp))
  -- `∫ |L_x* η|² = ∫ ⟪L_x L_x* η, η⟫`, and the Laplacian of `|η|²` integrates to zero.
  have hW : ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ =
      ∫ z, (⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ +
        Δ (fun w ↦ ‖η w‖ ^ 2) z / 2) ∂μ := by
    rw [integral_add hi hΔ, integral_div,
      integral_laplacian_eq_zero_of_hasCompactSupport (hη.norm_sq ℝ) hnc, zero_div, add_zero,
      integral_inner_gaugeFixedOperator hL hLc (hη.of_le (by norm_num))]
    simp only [real_inner_self_eq_norm_sq]
  rw [hW]
  exact integral_mono hG (hi.fun_add hΔ) fun z ↦
    le_inner_gaugeFixedOperator_gaugeFixedAdjoint_add_laplacian
      (hx.differentiable one_ne_zero z) hη.contDiffAt (hsol z)

/-- **Spectral gap of `L_x L_x*` at a vortex.** For an actual vortex with unit-modulus end,
there is `c > 0`, depending only on the vortex, such that `c ∫|η|² ≤ ∫|L_x* η|²` for every
compactly supported `C²` field `η`. -/
theorem exists_pos_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint
    (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ c > 0, ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      c * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ := by
  -- The connection components see the potential `2 P ≥ 1/4` outside a disc.
  obtain ⟨R, -, hR⟩ := exists_exterior_lt_mass hlim (by norm_num : (1 : ℝ) / 8 < 1 / 4)
  have hxi (i : Fin 4) : Continuous fun z ↦ x z i := by fun_prop
  have hPc : Continuous fun z ↦ 2 * (x z 2 ^ 2 + x z 3 ^ 2) := by
    have := hxi 2; have := hxi 3; fun_prop
  obtain ⟨c, hc, hgap⟩ :=
    exists_pos_mul_integral_norm_sq_le_integral_norm_fderiv_sq_add_integral_mul_norm_sq
      (μ := μ) (F := ℝ) hPc.locallyIntegrable (ae_of_all _ fun z ↦ by positivity)
      (by norm_num : (0 : ℝ) < 1 / 4) (ae_of_all _ fun z hz ↦ by linarith [hR z hz])
  refine ⟨min (c / 2) (1 / 8), by positivity, fun η hη hηc ↦ ?_⟩
  have hu (i : Fin 4) : ContDiff ℝ 2 fun w ↦ η w i :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hη :)
  have huc (i : Fin 4) : HasCompactSupport fun w ↦ η w i :=
    hηc.comp_left (g := EuclideanSpace.proj (𝕜 := ℝ) i) (map_zero _)
  -- Integrability of the pieces.
  have hBs (i : Fin 4) : HasCompactSupport fun z ↦ η z i ^ 2 :=
    (huc i).comp_left (g := fun t : ℝ ↦ t ^ 2) (by simp)
  have hBc (i : Fin 4) : Continuous fun z ↦ η z i ^ 2 := (hu i).continuous.pow 2
  have hB (i : Fin 4) : Integrable (fun z ↦ η z i ^ 2) μ :=
    (hBc i).integrable_of_hasCompactSupport (hBs i)
  have hDi (i : Fin 4) : Integrable (fun z ↦ ‖fderiv ℝ (fun w ↦ η w i) z‖ ^ 2) μ := by
    have hc' : Continuous fun z ↦ ‖fderiv ℝ (fun w ↦ η w i) z‖ ^ 2 :=
      ((hu i).continuous_fderiv (by norm_num)).norm.pow 2
    exact hc'.integrable_of_hasCompactSupport
      (((huc i).fderiv (𝕜 := ℝ)).comp_left (g := fun L ↦ ‖L‖ ^ 2) (by simp))
  have hPi (i : Fin 4) :
      Integrable (fun z ↦ 2 * (x z 2 ^ 2 + x z 3 ^ 2) * η z i ^ 2) μ :=
    (hPc.mul (hBc i)).integrable_of_hasCompactSupport (hBs i).mul_left
  have hA' (i : Fin 4) : Integrable (fun z ↦
      (‖fderiv ℝ (fun w ↦ η w i) z‖ ^ 2 + 2 * (x z 2 ^ 2 + x z 3 ^ 2) * η z i ^ 2) / 2) μ :=
    ((hDi i).fun_add (hPi i)).div_const 2
  have hB' : Integrable (fun z ↦ (η z 2 ^ 2 + η z 3 ^ 2) / 8) μ :=
    ((hB 2).fun_add (hB 3)).div_const 8
  -- The integrated Weitzenböck bound, split into its pieces.
  have hlow := integral_le_integral_norm_sq_gaugeFixedAdjoint (μ := μ) hx hsol hη hηc
    (((hA' 0).fun_add (hA' 1)).fun_add hB')
  rw [integral_add ((hA' 0).fun_add (hA' 1)) hB', integral_add (hA' 0) (hA' 1),
    integral_div, integral_div, integral_div, integral_add (hB 2) (hB 3)] at hlow
  -- The Poincaré inequality for the two connection components.
  have hA (i : Fin 4) : c * ∫ z, η z i ^ 2 ∂μ ≤
      ∫ z, (‖fderiv ℝ (fun w ↦ η w i) z‖ ^ 2 + 2 * (x z 2 ^ 2 + x z 3 ^ 2) * η z i ^ 2) ∂μ := by
    rw [integral_add (hDi i) (hPi i)]
    simpa only [Real.norm_eq_abs, sq_abs] using hgap _ ((hu i).of_le one_le_two) (huc i)
  -- `∫ |η|²` is the sum of the integrals of the squared components.
  have hnorm : ∫ z, ‖η z‖ ^ 2 ∂μ =
      ∫ z, η z 0 ^ 2 ∂μ + ∫ z, η z 1 ^ 2 ∂μ + ∫ z, η z 2 ^ 2 ∂μ + ∫ z, η z 3 ^ 2 ∂μ := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four, Fin.isValue]
    rw [integral_add (((hB 0).fun_add (hB 1)).fun_add (hB 2)) (hB 3),
      integral_add ((hB 0).fun_add (hB 1)) (hB 2), integral_add (hB 0) (hB 1)]
  have hB₀ (i : Fin 4) : 0 ≤ ∫ z, η z i ^ 2 ∂μ := integral_nonneg fun _ ↦ by positivity
  rw [hnorm]
  nlinarith [hA 0, hA 1, hB₀ 0, hB₀ 1, hB₀ 2, hB₀ 3,
    mul_le_mul_of_nonneg_right (min_le_left (c / 2) (1 / 8)) (hB₀ 0),
    mul_le_mul_of_nonneg_right (min_le_left (c / 2) (1 / 8)) (hB₀ 1),
    mul_le_mul_of_nonneg_right (min_le_right (c / 2) (1 / 8)) (hB₀ 2),
    mul_le_mul_of_nonneg_right (min_le_right (c / 2) (1 / 8)) (hB₀ 3)]

end TauCeti.Vortex
