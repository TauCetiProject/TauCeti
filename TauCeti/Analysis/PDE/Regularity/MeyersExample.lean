/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.Sobolev.WeakDeriv.Removable
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Meyers' planar example

For `0 < μ ≤ 1` let `a = TauCeti.PDE.meyersCoefficient μ` be the coefficient field on the plane

`a(x) = μ² I + (1 - μ²) x̂ x̂ᵀ`, where `x̂ = x / ‖x‖`,

whose eigenvalue in the radial direction `x̂` is `1` and in the tangential direction is `μ²`. It is
measurable and uniformly elliptic with constants `μ²` and `1`, so its ellipticity ratio is `1 / μ²`.
The function `u(x) = ‖x‖ ^ (μ - 1) x₀` (`TauCeti.PDE.meyersSolution μ`), homogeneous of degree
`μ`, solves `div(a ∇u) = 0` weakly on every open set, across the origin, while its gradient has
size comparable to `‖x‖ ^ (μ - 1)`. On a bounded open set containing the origin it therefore lies
in `W^{1,p}` exactly for `p (1 - μ) < 2`.

The same field and solution make sense for every `μ > 0`. For `μ ≥ 1` the field is uniformly
elliptic with constants `1` and `μ²`, the solution lies in `W^{1,p}` of every bounded open set for
every `p`, and it is still a weak solution. In that range `u(t e₀) = t ^ μ` vanishes to order
`μ > 1` at the origin while `u > 0` on the half-plane `0 < x₀`, which is the counterexample to
Hopf's lemma for measurable divergence-form coefficients
(`TauCeti.PDE.exists_uniformlyEllipticOn_energyFormH1_eq_zero_tendsto_div`).

This is Meyers' example showing that his higher integrability theorem is sharp in its dependence
on the ellipticity: weak solutions of `div(a ∇u) = 0` with bounded measurable, uniformly elliptic
coefficients have gradients in `L^p_loc` for some `p > 2`, but `p` cannot be chosen independently
of the ellipticity ratio, and tends to `2` as the ratio tends to infinity.

## Main declarations

* `TauCeti.PDE.uniformlyEllipticOn_meyersCoefficient`: for `μ ≤ 1`, Meyers' coefficient is
  uniformly elliptic with constants `μ²` and `1`;
  `TauCeti.PDE.uniformlyEllipticOn_meyersCoefficient_of_one_le`: for `μ ≥ 1`, with constants `1`
  and `μ²`.
* `TauCeti.PDE.continuous_meyersSolution`, `TauCeti.PDE.meyersSolution_pos`,
  `TauCeti.PDE.meyersSolution_smul_single_zero`: Meyers' solution is continuous, positive on the
  half-plane `0 < x₀`, and equal to `t ^ μ` at `t e₀`.
* `TauCeti.PDE.not_exists_tendsto_meyersCoefficient`: for `μ² ≠ 1`, Meyers' coefficient has no
  limit at the origin within the half-plane `0 < x₀`.
* `TauCeti.PDE.gradient_meyersSolution`, `TauCeti.PDE.norm_gradient_meyersSolution_le`,
  `TauCeti.PDE.mul_rpow_le_norm_gradient_meyersSolution`: away from the origin, the gradient of
  Meyers' solution, the upper bound `‖∇u(x)‖ ≤ (1 + |μ - 1|) ‖x‖ ^ (μ - 1)` for every `μ`, and the
  lower bound `μ ‖x‖ ^ (μ - 1) ≤ ‖∇u(x)‖` for `0 < μ ≤ 1`.
* `TauCeti.PDE.gradient_ae_eq_gradient_meyersSolution`: the weak gradient of an element of
  `W^{1,p}(Ω)` equal to Meyers' solution is its classical gradient.
* `TauCeti.PDE.energyFormH1_meyersCoefficient_eq_zero`: an element of `H¹(Ω)` equal to Meyers'
  solution is a weak solution of `div(a ∇u) = 0` on `Ω`.
* `TauCeti.PDE.exists_w1p_value_ae_eq_meyersSolution`: on a bounded open set, Meyers' solution
  lies in `W^{1,p}` when `p (1 - μ) < 2`, and
  `TauCeti.PDE.exists_w1p_value_ae_eq_meyersSolution_iff`: on a bounded open set containing the
  origin, exactly then.
* `TauCeti.PDE.exists_meyersSolution_not_exists_w1p`: for every `p > 2` some `μ ∈ (0, 1)` gives a
  weak solution in `H¹(Ω)` that is not in `W^{1,p}(Ω)`.

## The argument

Away from the origin, `a ∇u = μ (∂₁ψ, -∂₀ψ)` for the stream function `ψ(x) = ‖x‖ ^ (μ - 1) x₁`, a
pointwise identity of homogeneous functions. Both `u` and `ψ` are continuous, since `μ > 0`, and
differentiable away from the origin with gradients bounded by `(1 + |μ - 1|) ‖x‖ ^ (μ - 1)`, which
is locally integrable in the plane; so their classical gradients are weak gradients across the
origin (`TauCeti.hasWeakFDerivOn_of_hasFDerivAt_off_countable`). For a test function `φ`, the weak
form is then `μ ∫ (∂₀φ ∂₁ψ - ∂₁φ ∂₀ψ)`, which vanishes after moving the derivatives of `ψ` onto `φ`,
because the mixed derivatives of `φ` commute. The weak form is continuous on `H¹(Ω)`, so it vanishes
on the closure `H¹₀(Ω)` of the test functions.

For integrability, `‖∇u(x)‖ ≤ (1 + |μ - 1|) ‖x‖ ^ (μ - 1)`, with the lower bound
`μ ‖x‖ ^ (μ - 1) ≤ ‖∇u(x)‖` for `μ ≤ 1`, and `‖x‖ ^ s` is integrable on a disc about the origin
exactly when `s > -2` (`TauCeti.integrableOn_norm_rpow_ball_iff`).

## References

* N. G. Meyers, *An `Lᵖ`-estimate for the gradient of solutions of second order elliptic
  divergence equations*, Ann. Scuola Norm. Sup. Pisa (3) 17 (1963), 189–206, §5.
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace LineDeriv
open scoped NNReal ENNReal Topology InnerProductSpace Distributions Matrix Gradient

namespace TauCeti

namespace PDE

variable {μ : ℝ}

/-- **Meyers' coefficient field** `a(x) = μ² I + (1 - μ²) x xᵀ / ‖x‖²` on the plane. Its
eigenvalue in the radial direction `x` is `1` and in the tangential direction is `μ²`. At the
origin, where the direction is undefined, it is `μ² I`. -/
def meyersCoefficient (μ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : Matrix (Fin 2) (Fin 2) ℝ :=
  μ ^ 2 • 1 + ((1 - μ ^ 2) / ‖x‖ ^ 2) • Matrix.vecMulVec x x

/-- Unfolding `TauCeti.PDE.meyersCoefficient`. -/
theorem meyersCoefficient_apply (x : EuclideanSpace ℝ (Fin 2)) :
    meyersCoefficient μ x = μ ^ 2 • 1 + ((1 - μ ^ 2) / ‖x‖ ^ 2) • Matrix.vecMulVec x x :=
  (rfl)

/-- The bilinear form of Meyers' coefficient:
`ηᵀ a(x) ξ = μ² ⟪η, ξ⟫ + (1 - μ²) ⟪η, x⟫ ⟪x, ξ⟫ / ‖x‖²`. -/
theorem dotProduct_meyersCoefficient_mulVec (x η ξ : EuclideanSpace ℝ (Fin 2)) :
    η ⬝ᵥ (meyersCoefficient μ x *ᵥ ξ) =
      μ ^ 2 * ⟪η, ξ⟫_ℝ + (1 - μ ^ 2) / ‖x‖ ^ 2 * (⟪η, x⟫_ℝ * ⟪x, ξ⟫_ℝ) := by
  simp [meyersCoefficient, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Fin.sum_univ_two,
    PiLp.inner_apply]
  ring

/-- The bilinear form of Meyers' coefficient is bounded by `μ² + |1 - μ²|`. -/
theorem abs_dotProduct_meyersCoefficient_mulVec_le (x η ξ : EuclideanSpace ℝ (Fin 2)) :
    |η ⬝ᵥ (meyersCoefficient μ x *ᵥ ξ)| ≤ (μ ^ 2 + |1 - μ ^ 2|) * ‖η‖ * ‖ξ‖ := by
  have hcx : |(1 - μ ^ 2) / ‖x‖ ^ 2| * ‖x‖ ^ 2 ≤ |1 - μ ^ 2| := by
    rcases eq_or_ne ‖x‖ 0 with h | h
    · simp [h]
    · rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 2),
        div_mul_cancel₀ _ (pow_ne_zero 2 h)]
  rw [dotProduct_meyersCoefficient_mulVec]
  calc |μ ^ 2 * ⟪η, ξ⟫_ℝ + (1 - μ ^ 2) / ‖x‖ ^ 2 * (⟪η, x⟫_ℝ * ⟪x, ξ⟫_ℝ)|
      ≤ μ ^ 2 * (‖η‖ * ‖ξ‖) + |(1 - μ ^ 2) / ‖x‖ ^ 2| * ((‖η‖ * ‖x‖) * (‖x‖ * ‖ξ‖)) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
        · rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (mul_le_mul (abs_real_inner_le_norm _ _)
            (abs_real_inner_le_norm _ _) (abs_nonneg _) (by positivity)) (abs_nonneg _)
    _ = (μ ^ 2 + |(1 - μ ^ 2) / ‖x‖ ^ 2| * ‖x‖ ^ 2) * ‖η‖ * ‖ξ‖ := by ring
    _ ≤ (μ ^ 2 + |1 - μ ^ 2|) * ‖η‖ * ‖ξ‖ := by gcongr

/-- For `0 < μ ≤ 1`, Meyers' coefficient is uniformly elliptic with constants `μ²` and `1`, so
its ellipticity ratio is `1 / μ²`. -/
theorem uniformlyEllipticOn_meyersCoefficient (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (Ω : Set (EuclideanSpace ℝ (Fin 2))) :
    UniformlyEllipticOn Ω (meyersCoefficient μ) (μ ^ 2) 1 := by
  have hc : 0 ≤ 1 - μ ^ 2 := by nlinarith
  refine UniformlyEllipticOn.of_bounds (by positivity) (by nlinarith) (fun x _ ξ => ?_)
    (fun x _ η ξ => ?_)
  · rw [Matrix.toQuadraticForm'_apply, dotProduct_meyersCoefficient_mulVec,
      real_inner_self_eq_norm_sq, real_inner_comm x ξ]
    have : 0 ≤ (1 - μ ^ 2) / ‖x‖ ^ 2 * (⟪x, ξ⟫_ℝ * ⟪x, ξ⟫_ℝ) :=
      mul_nonneg (div_nonneg hc (by positivity)) (mul_self_nonneg _)
    linarith
  · simpa [abs_of_nonneg hc] using abs_dotProduct_meyersCoefficient_mulVec_le (μ := μ) x η ξ

/-- For `μ ≥ 1`, the bilinear form of Meyers' coefficient is bounded by `μ²`, its tangential
eigenvalue: `ηᵀ a(x) ξ = ⟪η, μ² ξ + t x⟫` with `‖μ² ξ + t x‖ ≤ μ² ‖ξ‖`. -/
private theorem abs_dotProduct_meyersCoefficient_mulVec_le_sq (hμ : 1 ≤ μ)
    (x η ξ : EuclideanSpace ℝ (Fin 2)) :
    |η ⬝ᵥ (meyersCoefficient μ x *ᵥ ξ)| ≤ μ ^ 2 * ‖η‖ * ‖ξ‖ := by
  set t : ℝ := (1 - μ ^ 2) / ‖x‖ ^ 2 * ⟪x, ξ⟫_ℝ with ht
  have heq : η ⬝ᵥ (meyersCoefficient μ x *ᵥ ξ) = ⟪η, μ ^ 2 • ξ + t • x⟫_ℝ := by
    rw [dotProduct_meyersCoefficient_mulVec, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, ht]
    ring
  -- The cross term `t (2 μ² ⟪ξ, x⟫ + t ‖x‖²) = (1 - μ⁴) ⟪x, ξ⟫² / ‖x‖²` is nonpositive.
  have hcross : t * (2 * μ ^ 2 * ⟪ξ, x⟫_ℝ + t * ‖x‖ ^ 2) ≤ 0 := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp [ht]
    have h : t * (2 * μ ^ 2 * ⟪ξ, x⟫_ℝ + t * ‖x‖ ^ 2) =
        (1 - μ ^ 2) * (1 + μ ^ 2) / ‖x‖ ^ 2 * ⟪x, ξ⟫_ℝ ^ 2 := by
      rw [ht, real_inner_comm ξ x]
      field_simp
      ring
    rw [h]
    exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)) (by positivity))
      (sq_nonneg _)
  have hw : ‖μ ^ 2 • ξ + t • x‖ ≤ μ ^ 2 * ‖ξ‖ := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ μ ^ 2)]
    nlinarith [sq_abs t]
  rw [heq, mul_assoc, mul_comm ‖η‖, ← mul_assoc]
  exact (abs_real_inner_le_norm _ _).trans
    (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hw (norm_nonneg η))

/-- For `μ ≥ 1`, Meyers' coefficient is uniformly elliptic with constants `1` and `μ²`, so its
ellipticity ratio is `μ²`. -/
theorem uniformlyEllipticOn_meyersCoefficient_of_one_le (hμ : 1 ≤ μ)
    (Ω : Set (EuclideanSpace ℝ (Fin 2))) :
    UniformlyEllipticOn Ω (meyersCoefficient μ) 1 (μ ^ 2) := by
  refine UniformlyEllipticOn.of_bounds one_pos (by nlinarith) (fun x _ ξ => ?_)
    (fun x _ η ξ => abs_dotProduct_meyersCoefficient_mulVec_le_sq hμ x η ξ)
  rw [Matrix.toQuadraticForm'_apply, dotProduct_meyersCoefficient_mulVec,
    real_inner_self_eq_norm_sq, real_inner_comm x ξ]
  -- The radial term loses at most `(μ² - 1) ‖ξ‖²`, by the Cauchy–Schwarz inequality.
  have hcs : ⟪x, ξ⟫_ℝ * ⟪x, ξ⟫_ℝ ≤ ‖x‖ ^ 2 * ‖ξ‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using real_inner_mul_inner_self_le x ξ
  have h : (μ ^ 2 - 1) / ‖x‖ ^ 2 * (⟪x, ξ⟫_ℝ * ⟪x, ξ⟫_ℝ) ≤ (μ ^ 2 - 1) * ‖ξ‖ ^ 2 := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
        zero_mul]
      exact mul_nonneg (by nlinarith) (by positivity)
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hcs (by nlinarith : (0 : ℝ) ≤ μ ^ 2 - 1)]
  have h' : (1 - μ ^ 2) / ‖x‖ ^ 2 * (⟪x, ξ⟫_ℝ * ⟪x, ξ⟫_ℝ) =
      -((μ ^ 2 - 1) / ‖x‖ ^ 2 * (⟪x, ξ⟫_ℝ * ⟪x, ξ⟫_ℝ)) := by ring
  linarith

/-- Meyers' coefficient is strongly measurable. -/
theorem stronglyMeasurable_meyersCoefficient : StronglyMeasurable (meyersCoefficient μ) := by
  have : Measurable (meyersCoefficient μ) := by
    unfold meyersCoefficient
    fun_prop
  -- The matrix space is metrizable through its underlying function type.
  exact Measurable.stronglyMeasurable (β := Fin 2 → Fin 2 → ℝ) this

/-- Along the ray through `(1, c)`, the entry `a₀₀` of Meyers' coefficient is the constant
`μ² + (1 - μ²) / (1 + c²)`. -/
private theorem meyersCoefficient_smul_apply_zero_zero (c : ℝ) {t : ℝ} (ht : t ≠ 0) :
    meyersCoefficient μ (t • WithLp.toLp 2 ![1, c]) 0 0 = μ ^ 2 + (1 - μ ^ 2) / (1 + c ^ 2) := by
  have hn : ‖t • WithLp.toLp 2 ![(1 : ℝ), c]‖ ^ 2 = t ^ 2 * (1 + c ^ 2) := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    simp only [PiLp.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
    ring
  rw [meyersCoefficient_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, hn]
  simp only [Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.vecMulVec_apply,
    PiLp.smul_apply, Matrix.cons_val_zero]
  have h1 : 1 + c ^ 2 ≠ 0 := by positivity
  field_simp

open Filter in
/-- **Meyers' coefficient is discontinuous at the origin.** For `μ² ≠ 1` it has no limit at the
origin within the half-plane `0 < x₀`: along the ray through `e₀` its entry `a₀₀` is `1`, and
along the ray through `e₀ + e₁` it is `(1 + μ²) / 2`. -/
theorem not_exists_tendsto_meyersCoefficient (hμ : μ ^ 2 ≠ 1) :
    ¬ ∃ L, Tendsto (meyersCoefficient μ) (𝓝[{x | 0 < x 0}] 0) (𝓝 L) := by
  rintro ⟨L, hL⟩
  have key : ∀ c : ℝ, L 0 0 = μ ^ 2 + (1 - μ ^ 2) / (1 + c ^ 2) := by
    intro c
    -- The ray `t ↦ t (1, c)`, `t > 0`, approaches the origin inside the half-plane.
    have hγ : Tendsto (fun t : ℝ => t • WithLp.toLp 2 ![(1 : ℝ), c]) (𝓝[>] 0)
        (𝓝[{x : EuclideanSpace ℝ (Fin 2) | 0 < x 0}] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · simpa using ((continuous_id.smul continuous_const).tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Ioi 0) (a := (0 : ℝ)))
          (f := fun t : ℝ => t • WithLp.toLp 2 ![(1 : ℝ), c])
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa using ht
    have hent : Tendsto (fun t : ℝ => meyersCoefficient μ (t • WithLp.toLp 2 ![1, c]) 0 0)
        (𝓝[>] 0) (𝓝 (L 0 0)) :=
      ((continuous_id.matrix_elem 0 0).tendsto L).comp (hL.comp hγ)
    refine tendsto_nhds_unique hent (tendsto_const_nhds.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (meyersCoefficient_smul_apply_zero_zero c (ne_of_gt ht)).symm
  have h := (key 0).symm.trans (key 1)
  norm_num at h
  exact hμ (by linarith)

/-! ### The radial coordinate functions -/

/-- The function `x ↦ ‖x‖ ^ (μ - 1) xᵢ`, homogeneous of degree `μ`. -/
private def radialCoord (μ : ℝ) (i : Fin 2) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ‖x‖ ^ (μ - 1) * x i

/-- The classical gradient of `TauCeti.PDE.radialCoord` away from the origin. -/
private def radialCoordGradient (μ : ℝ) (i : Fin 2) (x : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  ‖x‖ ^ (μ - 1) • EuclideanSpace.single i 1 + ((μ - 1) * ‖x‖ ^ (μ - 3) * x i) • x

private theorem norm_rpow_sub_one {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) :
    ‖x‖ ^ (μ - 1) = ‖x‖ ^ (μ - 3) * ‖x‖ ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_add (norm_pos_iff.2 hx)]
  congr 1
  ring

private theorem hasFDerivAt_radialCoord {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) (i : Fin 2) :
    HasFDerivAt (radialCoord μ i) (innerSL ℝ (radialCoordGradient μ i x)) x := by
  refine ((hasFDerivAt_norm_rpow_of_ne (μ - 1) hx).mul
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt).congr_fderiv ?_
  ext v
  simp [radialCoordGradient, EuclideanSpace.inner_single_left, show μ - 1 - 2 = μ - 3 by ring]
  ring

private theorem abs_radialCoord_le (i : Fin 2) (x : EuclideanSpace ℝ (Fin 2)) (hμ : 0 < μ) :
    |radialCoord μ i x| ≤ ‖x‖ ^ μ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [radialCoord, Real.zero_rpow hμ.ne']
  rw [radialCoord, abs_mul, abs_of_nonneg (by positivity)]
  calc ‖x‖ ^ (μ - 1) * |x i| ≤ ‖x‖ ^ (μ - 1) * ‖x‖ :=
        mul_le_mul_of_nonneg_left (by simpa using PiLp.norm_apply_le x i) (by positivity)
    _ = ‖x‖ ^ μ := by
        rw [← Real.rpow_add_one (norm_pos_iff.2 hx).ne']
        ring_nf

private theorem continuous_radialCoord (hμ : 0 < μ) (i : Fin 2) :
    Continuous (radialCoord μ i) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · have h0 : radialCoord μ i 0 = 0 := by simp [radialCoord]
    rw [ContinuousAt, h0]
    refine squeeze_zero_norm (fun y => (abs_radialCoord_le i y hμ)) ?_
    simpa [Real.zero_rpow hμ.ne'] using
      ((continuous_norm.rpow_const fun _ => Or.inr hμ.le).tendsto
        (0 : EuclideanSpace ℝ (Fin 2)))
  · exact (hasFDerivAt_radialCoord hx i).continuousAt

private theorem norm_radialCoordGradient_le (i : Fin 2) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ≠ 0) : ‖radialCoordGradient μ i x‖ ≤ (1 + |μ - 1|) * ‖x‖ ^ (μ - 1) := by
  have hxi : |x i| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x i
  calc ‖radialCoordGradient μ i x‖
      ≤ ‖x‖ ^ (μ - 1) * 1 + |μ - 1| * ‖x‖ ^ (μ - 3) * |x i| * ‖x‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        simp [norm_smul, abs_of_nonneg (by positivity : 0 ≤ ‖x‖ ^ (μ - 3)),
          abs_of_nonneg (by positivity : 0 ≤ ‖x‖ ^ (μ - 1))]
    _ ≤ ‖x‖ ^ (μ - 1) * 1 + |μ - 1| * ‖x‖ ^ (μ - 3) * ‖x‖ * ‖x‖ := by gcongr
    _ = (1 + |μ - 1|) * ‖x‖ ^ (μ - 1) := by
        rw [norm_rpow_sub_one hx]
        ring

private theorem measurable_radialCoordGradient (i : Fin 2) :
    Measurable (radialCoordGradient μ i) := by
  unfold radialCoordGradient
  fun_prop

private theorem locallyIntegrable_radialCoordGradient (hμ0 : 0 < μ) (i : Fin 2) :
    LocallyIntegrable (fun x => innerSL ℝ (radialCoordGradient μ i x))
      (volume : Measure (EuclideanSpace ℝ (Fin 2))) := by
  refine locallyIntegrable_of_norm_le_rpow (C := 1 + |μ - 1|) (α := 1 - μ) (by simp)
    (by simp; linarith)
    ?_ ((innerSL ℝ).continuous.comp_aestronglyMeasurable
      (measurable_radialCoordGradient i).aestronglyMeasurable)
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : EuclideanSpace ℝ (Fin 2)))]
    with x hx
  rw [innerSL_apply_norm, neg_sub]
  exact norm_radialCoordGradient_le i hx

/-- The radial coordinate function has its classical gradient as weak gradient on every open set:
the singularity at the origin is removable. -/
private theorem hasWeakFDerivOn_radialCoord (hμ0 : 0 < μ) (i : Fin 2)
    (Ω : Opens (EuclideanSpace ℝ (Fin 2))) :
    HasWeakFDerivOn volume Ω (radialCoord μ i) (fun x => innerSL ℝ (radialCoordGradient μ i x)) :=
  hasWeakFDerivOn_of_hasFDerivAt_off_countable (countable_singleton 0)
    (continuous_radialCoord hμ0 i).continuousOn
    ((locallyIntegrable_radialCoordGradient hμ0 i).locallyIntegrableOn _)
    fun _ hx => hasFDerivAt_radialCoord hx.2 i

/-! ### Meyers' solution -/

/-- Meyers' solution `u(x) = |x|^(μ - 1) x₀` of `div(a ∇u) = 0` for
`a = TauCeti.PDE.meyersCoefficient μ`, homogeneous of degree `μ`. -/
def meyersSolution (μ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ‖x‖ ^ (μ - 1) * x 0

/-- Unfolding `TauCeti.PDE.meyersSolution`. -/
theorem meyersSolution_apply (x : EuclideanSpace ℝ (Fin 2)) :
    meyersSolution μ x = ‖x‖ ^ (μ - 1) * x 0 :=
  (rfl)

private theorem meyersSolution_eq_radialCoord : meyersSolution μ = radialCoord μ 0 := (rfl)

/-- Meyers' solution vanishes at the origin. -/
@[simp]
theorem meyersSolution_zero : meyersSolution μ 0 = 0 := by
  simp [meyersSolution]

/-- For `μ > 0`, Meyers' solution is continuous, also at the origin. -/
theorem continuous_meyersSolution (hμ : 0 < μ) : Continuous (meyersSolution μ) :=
  continuous_radialCoord hμ 0

/-- Meyers' solution is positive on the open half-plane `0 < x₀`. -/
theorem meyersSolution_pos {x : EuclideanSpace ℝ (Fin 2)} (hx : 0 < x 0) :
    0 < meyersSolution μ x := by
  have : x ≠ 0 := fun h => by simp [h] at hx
  rw [meyersSolution_apply]
  exact mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.2 this) _) hx

/-- On the ray through `e₀`, Meyers' solution is `t ↦ t ^ μ`. -/
theorem meyersSolution_smul_single_zero {t : ℝ} (ht : 0 < t) :
    meyersSolution μ (t • EuclideanSpace.single 0 1) = t ^ μ := by
  rw [meyersSolution_apply, norm_smul, PiLp.norm_single, norm_one, mul_one,
    Real.norm_of_nonneg ht.le]
  simp only [PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul, mul_one]
  rw [← Real.rpow_add_one ht.ne', sub_add_cancel]

/-- Away from the origin, Meyers' solution has gradient
`‖x‖ ^ (μ - 1) e₀ + (μ - 1) ‖x‖ ^ (μ - 3) x₀ x`. -/
theorem hasGradientAt_meyersSolution {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) :
    HasGradientAt (meyersSolution μ)
      (‖x‖ ^ (μ - 1) • EuclideanSpace.single 0 1 + ((μ - 1) * ‖x‖ ^ (μ - 3) * x 0) • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact hasFDerivAt_radialCoord (μ := μ) hx 0

/-- The gradient of Meyers' solution away from the origin. -/
theorem gradient_meyersSolution {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) :
    ∇ (meyersSolution μ) x =
      ‖x‖ ^ (μ - 1) • EuclideanSpace.single 0 1 + ((μ - 1) * ‖x‖ ^ (μ - 3) * x 0) • x :=
  (hasGradientAt_meyersSolution hx).gradient

private theorem gradient_meyersSolution_eq_radialCoordGradient {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ≠ 0) : ∇ (meyersSolution μ) x = radialCoordGradient μ 0 x :=
  gradient_meyersSolution hx

/-- The coordinates of the gradient of `TauCeti.PDE.radialCoord` away from the origin. -/
private theorem radialCoordGradient_apply {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0)
    (i j : Fin 2) : radialCoordGradient μ i x j =
      ‖x‖ ^ (μ - 3) * (‖x‖ ^ 2 * (if j = i then 1 else 0) + (μ - 1) * x i * x j) := by
  simp only [radialCoordGradient, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    PiLp.single_apply, norm_rpow_sub_one hx]
  split_ifs <;> ring

/-- Away from the origin, Meyers' coefficient maps the gradient of `‖x‖ ^ (μ - 1) x₀` to the
rotated gradient of the stream function `μ ‖x‖ ^ (μ - 1) x₁`. -/
private theorem dotProduct_meyersCoefficient_mulVec_radialCoordGradient
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) (η : EuclideanSpace ℝ (Fin 2)) :
    η ⬝ᵥ (meyersCoefficient μ x *ᵥ radialCoordGradient μ 0 x) =
      μ * (η 0 * radialCoordGradient μ 1 x 1 - η 1 * radialCoordGradient μ 1 x 0) := by
  have hr : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hr0 : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hx)
  have hG := radialCoordGradient_apply (μ := μ) hx
  have hinner : ∀ y z : EuclideanSpace ℝ (Fin 2), ⟪y, z⟫_ℝ = y 0 * z 0 + y 1 * z 1 := by
    intro y z
    simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]
  rw [dotProduct_meyersCoefficient_mulVec, hinner, hinner, hinner, hG, hG, hG, hG]
  simp only [Fin.isValue, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one,
    one_ne_zero, ↓reduceIte]
  generalize ‖x‖ ^ (μ - 3) = t
  rw [div_eq_mul_inv]
  have hinv : ‖x‖ ^ 2 * (‖x‖ ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hr0
  generalize (‖x‖ ^ 2)⁻¹ = s at hinv
  rw [hr] at hinv ⊢
  linear_combination (μ * t * x 0 * (1 - μ ^ 2) * (η 0 * x 0 + η 1 * x 1)) * hinv

/-- The weak gradient of an element of `W^{1,p}(Ω)` equal to Meyers' solution is its classical
gradient. -/
private theorem gradient_ae_eq_radialCoordGradient (hμ0 : 0 < μ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin 2))} (u : W1p volume Ω p)
    (hu : W1p.value u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin 2)))] meyersSolution μ) :
    W1p.gradient u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin 2)))]
      radialCoordGradient μ 0 := by
  filter_upwards [((W1p.hasWeakFDerivOn u).congr_ae hu).ae_eq
    (hasWeakFDerivOn_radialCoord hμ0 0 Ω)] with x hx
  exact innerSL_inj.1 hx

/-- The mixed derivatives of a test function `φ` commute, so, by the weak derivative identities of
the stream function `ψ = ‖x‖ ^ (μ - 1) x₁`, `∫ ∂₀φ ∂₁ψ = ∫ ∂₁φ ∂₀ψ`. -/
private theorem integral_lineDeriv_smul_radialCoordGradient_comm (hμ0 : 0 < μ)
    {Ω : Opens (EuclideanSpace ℝ (Fin 2))} (φ : 𝓓(Ω, ℝ)) :
    ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ (Fin 2) → ℝ) x
        (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) • radialCoordGradient μ 1 x 1 =
      ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ (Fin 2) → ℝ) x
        (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) • radialCoordGradient μ 1 x 0 := by
  have hψ := hasWeakFDerivOn_radialCoord hμ0 1 Ω
  have h1 := HasWeakLineDerivOn.integral_lineDeriv_smul_eq_neg_integral_smul
    (hψ.hasWeakLineDerivOn (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))
    (∂_{EuclideanSpace.single (0 : Fin 2) (1 : ℝ)} φ)
  have h0 := HasWeakLineDerivOn.integral_lineDeriv_smul_eq_neg_integral_smul
    (hψ.hasWeakLineDerivOn (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))
    (∂_{EuclideanSpace.single (1 : Fin 2) (1 : ℝ)} φ)
  simp only [TestFunction.lineDeriv_lineDerivOp_comm φ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
    (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))] at h1
  rw [h0] at h1
  simpa [TestFunction.lineDerivOp_apply, EuclideanSpace.inner_single_right] using h1.symm

/-- The weak equation for Meyers' solution against a test function: by the pointwise identity
`a ∇u = μ (∂₁ψ, -∂₀ψ)`, the energy form is `μ ∫ (∂₀φ ∂₁ψ - ∂₁φ ∂₀ψ) = 0`. -/
private theorem energyFormH1_meyersCoefficient_ofTestFunctionₗ_eq_zero (hμ0 : 0 < μ)
    {Ω : Opens (EuclideanSpace ℝ (Fin 2))} (u : W1p volume Ω 2)
    (hu : W1p.value u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin 2)))] meyersSolution μ)
    (φ : 𝓓(Ω, ℝ)) :
    energyFormH1 (meyersCoefficient μ) 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) = 0 := by
  have hloc : ∀ i, LocallyIntegrableOn (fun x => radialCoordGradient μ 1 x i) Ω volume :=
    fun i => by
      simpa [EuclideanSpace.inner_single_right] using
        ((hasWeakFDerivOn_radialCoord hμ0 1 Ω).hasWeakLineDerivOn
          (EuclideanSpace.single i (1 : ℝ))).locallyIntegrableOn_deriv
  have hd : ∀ x i, (∇ (φ : EuclideanSpace ℝ (Fin 2) → ℝ) x) i =
      lineDeriv ℝ (φ : EuclideanSpace ℝ (Fin 2) → ℝ) x (EuclideanSpace.single i (1 : ℝ)) := by
    intro x i
    rw [(φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv, ← inner_gradient_left,
      EuclideanSpace.inner_single_right]
    simp
  rw [energyFormH1_zero_zero_eq_setIntegral]
  calc ∫ x in Ω, matrixBilinearForm (meyersCoefficient μ x)
        (W1p.gradient (W1p.ofTestFunctionₗ volume Ω 2 φ) x) (W1p.gradient u x)
      = ∫ x in Ω, μ * (lineDeriv ℝ (φ : EuclideanSpace ℝ (Fin 2) → ℝ) x
            (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) • radialCoordGradient μ 1 x 1 -
          lineDeriv ℝ (φ : EuclideanSpace ℝ (Fin 2) → ℝ) x
            (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) • radialCoordGradient μ 1 x 0) := by
        refine integral_congr_ae ?_
        filter_upwards [gradient_ae_eq_radialCoordGradient hμ0 u hu,
          gradientTestFunctionLp_apply_ae (mu := volume) 2 φ,
          ae_restrict_of_ae (compl_mem_ae_iff.2
            (measure_singleton (0 : EuclideanSpace ℝ (Fin 2))))] with x hx hφ h0
        rw [W1p.gradient_ofTestFunctionₗ, hφ, hx, matrixBilinearForm_apply,
          dotProduct_meyersCoefficient_mulVec_radialCoordGradient h0, hd, hd, smul_eq_mul,
          smul_eq_mul]
    _ = μ * ((∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ (Fin 2) → ℝ) x
            (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) • radialCoordGradient μ 1 x 1) -
          ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ (Fin 2) → ℝ) x
            (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) • radialCoordGradient μ 1 x 0) := by
        rw [integral_const_mul, integral_sub
          ((integrable_lineDeriv_smul_of_locallyIntegrableOn (hloc 1) φ _).restrict)
          ((integrable_lineDeriv_smul_of_locallyIntegrableOn (hloc 0) φ _).restrict),
          setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul,
          setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul]
    _ = 0 := by
        rw [integral_lineDeriv_smul_radialCoordGradient_comm hμ0 φ, sub_self, mul_zero]

/-- **Meyers' solution is a weak solution.** For `μ > 0` and every open `Ω ⊆ ℝ²`, an element
`u ∈ H¹(Ω)` equal to `‖x‖ ^ (μ - 1) x₀` almost everywhere on `Ω` is a weak solution of
`div(a ∇u) = 0` for Meyers' coefficient `a`: `∫_Ω ⟨a ∇u, ∇v⟩ = 0` for every `v ∈ H¹₀(Ω)`. The
equation also holds across the origin, where, for `μ ≠ 1`, `a` is discontinuous, and for `μ < 1`
also `∇u` is unbounded. -/
theorem energyFormH1_meyersCoefficient_eq_zero (hμ0 : 0 < μ)
    {Ω : Opens (EuclideanSpace ℝ (Fin 2))} (u : W1p volume Ω 2)
    (hu : W1p.value u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin 2)))] meyersSolution μ)
    (v : W1p0 volume Ω 2) :
    energyFormH1 (meyersCoefficient μ) 0 0 u (v : W1p volume Ω 2) = 0 := by
  have hcoeff := memLp_energyIntegrand_of_bounds (Omega := Ω) (mu := volume)
    (b := 0) (c := 0) (beta := 0) (gamma := 0) (by positivity)
    stronglyMeasurable_meyersCoefficient.aestronglyMeasurable aestronglyMeasurable_const
    aestronglyMeasurable_const (fun x _ η ξ => abs_dotProduct_meyersCoefficient_mulVec_le x η ξ)
    (fun _ _ => by simp) (fun _ _ => by simp)
  have hclosed : IsClosed {w : W1p volume Ω 2 | energyFormH1L hcoeff u w = 0} :=
    isClosed_eq (energyFormH1L hcoeff u).continuous continuous_const
  refine (energyFormH1L_apply hcoeff u _).symm.trans
    (w1p0Submodule_subset_of_isClosed hclosed (fun φ => ?_) v.2)
  rw [Set.mem_ofPred_eq, energyFormH1L_apply]
  exact energyFormH1_meyersCoefficient_ofTestFunctionₗ_eq_zero hμ0 u hu φ

/-- Away from the origin, the gradient of Meyers' solution has length at least
`μ ‖x‖ ^ (μ - 1)`. -/
private theorem mul_rpow_le_norm_radialCoordGradient (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) :
    μ * ‖x‖ ^ (μ - 1) ≤ ‖radialCoordGradient μ 0 x‖ := by
  have hr : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hc : 0 ≤ 1 - μ ^ 2 := by nlinarith
  refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, radialCoordGradient_apply hx,
    radialCoordGradient_apply hx, norm_rpow_sub_one hx]
  simp only [Fin.isValue, one_ne_zero, ↓reduceIte]
  generalize ‖x‖ ^ (μ - 3) = t
  rw [hr]
  have : 0 ≤ t ^ 2 * (x 0 ^ 2 + x 1 ^ 2) * (1 - μ ^ 2) * x 1 ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) hc) (sq_nonneg _)
  linarith

/-- Away from the origin, the gradient of Meyers' solution has length at most
`(1 + |μ - 1|) ‖x‖ ^ (μ - 1)`. -/
theorem norm_gradient_meyersSolution_le {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) :
    ‖∇ (meyersSolution μ) x‖ ≤ (1 + |μ - 1|) * ‖x‖ ^ (μ - 1) := by
  rw [gradient_meyersSolution_eq_radialCoordGradient hx]
  exact norm_radialCoordGradient_le 0 hx

/-- Away from the origin, the gradient of Meyers' solution has length at least
`μ ‖x‖ ^ (μ - 1)`. -/
theorem mul_rpow_le_norm_gradient_meyersSolution (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) :
    μ * ‖x‖ ^ (μ - 1) ≤ ‖∇ (meyersSolution μ) x‖ := by
  rw [gradient_meyersSolution_eq_radialCoordGradient hx]
  exact mul_rpow_le_norm_radialCoordGradient hμ0 hμ1 hx

/-- The weak gradient of an element of `W^{1,p}(Ω)` equal to Meyers' solution is its classical
gradient. -/
theorem gradient_ae_eq_gradient_meyersSolution (hμ0 : 0 < μ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin 2))} (u : W1p volume Ω p)
    (hu : W1p.value u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin 2)))] meyersSolution μ) :
    W1p.gradient u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin 2)))]
      ∇ (meyersSolution μ) := by
  filter_upwards [gradient_ae_eq_radialCoordGradient hμ0 u hu, ae_restrict_of_ae
    (compl_mem_ae_iff.2 (measure_singleton (0 : EuclideanSpace ℝ (Fin 2))))] with x hx h0
  rw [hx, gradient_meyersSolution_eq_radialCoordGradient h0]

/-- If the gradient of Meyers' solution is `p`-integrable on an open set containing the origin,
then `p (1 - μ) < 2`: near the origin it is bounded below by `μ ‖x‖ ^ (μ - 1)`. -/
private theorem lt_two_of_memLp_radialCoordGradient (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) {Ω : Opens (EuclideanSpace ℝ (Fin 2))}
    (h0 : (0 : EuclideanSpace ℝ (Fin 2)) ∈ Ω)
    (hmem : MemLp (radialCoordGradient μ 0) p
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin 2))))) :
    p.toReal * (1 - μ) < 2 := by
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 Ω.isOpen 0 h0
  have hint : IntegrableOn (fun x => ‖radialCoordGradient μ 0 x‖ ^ p.toReal) (ball 0 r) :=
    (hmem.integrable_norm_rpow hp0 hp).mono_measure (Measure.restrict_mono hball le_rfl)
  -- `‖x‖ ^ (p (μ - 1)) ≤ μ ^ (-p) ‖∇u‖ ^ p` away from the origin.
  have hpow : IntegrableOn (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖ ^ (p.toReal * (μ - 1)))
      (ball 0 r) := by
    refine (hint.const_mul (μ ^ (-p.toReal))).mono'
      (by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin 2) =>
        ‖x‖ ^ (p.toReal * (μ - 1))).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.2
      (measure_singleton (0 : EuclideanSpace ℝ (Fin 2))))] with x hx
    rw [Real.norm_of_nonneg (by positivity), mul_comm p.toReal,
      Real.rpow_mul (norm_nonneg x), Real.rpow_neg hμ0.le, le_inv_mul_iff₀ (by positivity),
      ← Real.mul_rpow hμ0.le (by positivity)]
    exact Real.rpow_le_rpow (by positivity)
      (mul_rpow_le_norm_radialCoordGradient hμ0 hμ1 hx) hpr.le
  have := (integrableOn_norm_rpow_ball_iff hr).1 hpow
  rw [finrank_euclideanSpace_fin] at this
  push_cast at this
  nlinarith

/-- On a bounded open set, the gradient of Meyers' solution is `p`-integrable when
`p (1 - μ) < 2`: it is bounded by `(1 + |μ - 1|) ‖x‖ ^ (μ - 1)`. -/
private theorem memLp_radialCoordGradient {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) {Ω : Opens (EuclideanSpace ℝ (Fin 2))}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 2))))
    (h : p.toReal * (1 - μ) < 2) :
    MemLp (radialCoordGradient μ 0) p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin 2)))) := by
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hGm := (measurable_radialCoordGradient (μ := μ) 0).aestronglyMeasurable
    (μ := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin 2))))
  obtain ⟨R, hR⟩ := hb.subset_ball (0 : EuclideanSpace ℝ (Fin 2))
  refine (integrable_norm_rpow_iff hGm hp0 hp).1 ?_
  have hker : IntegrableOn (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖ ^ (p.toReal * (μ - 1)))
      (Ω : Set (EuclideanSpace ℝ (Fin 2))) :=
    IntegrableOn.mono_set
      (integrableOn_norm_rpow_ball (by rw [finrank_euclideanSpace_fin]; push_cast; nlinarith)) hR
  refine (hker.const_mul ((1 + |μ - 1|) ^ p.toReal)).mono'
    ((measurable_radialCoordGradient 0).norm.pow_const _).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.2
    (measure_singleton (0 : EuclideanSpace ℝ (Fin 2))))] with x hx
  rw [Real.norm_of_nonneg (by positivity), mul_comm p.toReal, Real.rpow_mul (norm_nonneg x),
    ← Real.mul_rpow (by positivity) (by positivity)]
  exact Real.rpow_le_rpow (norm_nonneg _) (norm_radialCoordGradient_le 0 hx) hpr.le

/-- On a bounded open set, Meyers' solution is bounded, hence `p`-integrable. -/
private theorem memLp_meyersSolution (hμ0 : 0 < μ) {p : ℝ≥0∞}
    {Ω : Opens (EuclideanSpace ℝ (Fin 2))}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 2)))) :
    MemLp (meyersSolution μ) p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin 2)))) := by
  obtain ⟨R, hR⟩ := hb.subset_ball (0 : EuclideanSpace ℝ (Fin 2))
  have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin 2)))) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  refine MemLp.of_bound (continuous_radialCoord hμ0 0).aestronglyMeasurable (R ^ μ) ?_
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  rw [Real.norm_eq_abs, meyersSolution_eq_radialCoord]
  refine (abs_radialCoord_le 0 x hμ0).trans (Real.rpow_le_rpow (norm_nonneg x) ?_ hμ0.le)
  exact (mem_ball_zero_iff.1 (hR hx)).le

/-- **Sobolev integrability of Meyers' solution.** Let `0 < μ`, `1 ≤ p < ∞`, and let `Ω ⊆ ℝ²`
be a bounded open set. If `p (1 - μ) < 2`, in particular for every `p` if `μ ≥ 1`, then
`‖x‖ ^ (μ - 1) x₀` lies in `W^{1,p}(Ω)`: its gradient is bounded by a multiple of
`‖x‖ ^ (μ - 1)`, which is `p`-integrable near the origin of the plane in this range. -/
theorem exists_w1p_value_ae_eq_meyersSolution (hμ0 : 0 < μ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) {Ω : Opens (EuclideanSpace ℝ (Fin 2))}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 2))))
    (h : p.toReal * (1 - μ) < 2) :
    ∃ u : W1p volume Ω p,
      W1p.value u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin 2)))] meyersSolution μ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hu := memLp_meyersSolution (p := p) hμ0 hb
  have hg := memLp_radialCoordGradient hp0 hp hb h
  refine ⟨W1p.mk hu.toLp hg.toLp
    (((hasWeakFDerivOn_radialCoord hμ0 0 Ω).congr_ae hu.coeFn_toLp.symm).congr_ae_deriv
      (hg.coeFn_toLp.mono fun x hx => by simp only [hx])), ?_⟩
  rw [W1p.value_mk]
  exact hu.coeFn_toLp

/-- **Sobolev integrability of Meyers' solution near the origin.** Let `0 < μ`, `1 ≤ p < ∞`, and
let `Ω ⊆ ℝ²` be a bounded open set containing the origin. Then `‖x‖ ^ (μ - 1) x₀` lies in
`W^{1,p}(Ω)` exactly when `p (1 - μ) < 2`, that is `p < 2 / (1 - μ)` for `μ < 1`, and always for
`μ ≥ 1`. Its gradient has size comparable to `‖x‖ ^ (μ - 1)`, which is `p`-integrable near the
origin of the plane exactly in this range. -/
theorem exists_w1p_value_ae_eq_meyersSolution_iff (hμ0 : 0 < μ) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {Ω : Opens (EuclideanSpace ℝ (Fin 2))}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 2))))
    (h0 : (0 : EuclideanSpace ℝ (Fin 2)) ∈ Ω) :
    (∃ u : W1p volume Ω p,
      W1p.value u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin 2)))] meyersSolution μ) ↔
      p.toReal * (1 - μ) < 2 := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  refine ⟨fun ⟨u, hu⟩ => ?_, exists_w1p_value_ae_eq_meyersSolution hμ0 hp hb⟩
  rcases le_or_gt μ 1 with hμ1 | hμ1
  · exact lt_two_of_memLp_radialCoordGradient hμ0 hμ1 hp0 hp h0
      ((Lp.memLp (W1p.gradient u)).ae_eq (gradient_ae_eq_radialCoordGradient hμ0 u hu))
  · nlinarith [ENNReal.toReal_nonneg (a := p)]

/-- **Meyers' example: no higher integrability exponent works for all coefficients.** For every
`p > 2` there is `0 < μ < 1` with the following property. For the coefficient
`a = TauCeti.PDE.meyersCoefficient μ`, uniformly elliptic with constants `μ²` and `1`
(`TauCeti.PDE.uniformlyEllipticOn_meyersCoefficient`), and every bounded open `Ω ⊆ ℝ²`
containing the origin, the function `‖x‖ ^ (μ - 1) x₀` lies in `H¹(Ω)` and is a weak solution of
`div(a ∇u) = 0` there, but does not lie in `W^{1,p}(Ω)`. So the exponent in Meyers' higher
integrability theorem for measurable coefficients cannot be chosen independently of the
ellipticity ratio. -/
theorem exists_meyersSolution_not_exists_w1p {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 2 < p) :
    ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ ∀ {Ω : Opens (EuclideanSpace ℝ (Fin 2))},
      Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 2))) →
      (0 : EuclideanSpace ℝ (Fin 2)) ∈ Ω →
      ∃ u : W1p volume Ω 2,
        W1p.value u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin 2)))] meyersSolution μ ∧
        (∀ v : W1p0 volume Ω 2,
          energyFormH1 (meyersCoefficient μ) 0 0 u (v : W1p volume Ω 2) = 0) ∧
        ¬ ∃ w : W1p volume Ω p,
          W1p.value w =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin 2)))]
            meyersSolution μ := by
  -- Compare with a finite exponent `2 < q ≤ p` and choose `μ` with `q (1 - μ) = 2`.
  set q : ℝ≥0∞ := min p 4
  have hq2 : 2 < q := lt_min hp (by norm_num)
  have hqp : q ≤ p := min_le_left p 4
  have hq : q ≠ ∞ := (min_le_right p 4).trans_lt ENNReal.ofNat_lt_top |>.ne
  have : Fact (1 ≤ q) := ⟨(by norm_num : (1 : ℝ≥0∞) ≤ 2).trans hq2.le⟩
  have hqr : 2 < q.toReal := by
    simpa using (ENNReal.toReal_lt_toReal (by norm_num) hq).2 hq2
  refine ⟨1 - 2 / q.toReal, by
    rw [sub_pos, div_lt_one (by linarith)]; exact hqr, by
    rw [sub_lt_self_iff]; positivity, fun {Ω} hb h0 => ?_⟩
  have hμ0 : 0 < 1 - 2 / q.toReal := by rw [sub_pos, div_lt_one (by linarith)]; exact hqr
  obtain ⟨u, hu⟩ := exists_w1p_value_ae_eq_meyersSolution hμ0 (p := 2) (by norm_num) hb
    (by simp; linarith)
  have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin 2)))) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  refine ⟨u, hu, energyFormH1_meyersCoefficient_eq_zero hμ0 u hu, ?_⟩
  rintro ⟨w, hw⟩
  have := (exists_w1p_value_ae_eq_meyersSolution_iff hμ0 hq hb h0).1
    ⟨W1p.ofExponentLE hqp w, (W1p.value_ofExponentLE_ae hqp w).trans hw⟩
  rw [sub_sub_cancel, mul_div_cancel₀ _ (by linarith)] at this
  exact lt_irrefl _ this

end PDE

end TauCeti
