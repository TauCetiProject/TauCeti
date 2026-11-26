/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import TauCeti.Analysis.PDE.Ellipticity.RadialCoefficient
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.Sobolev.WeakDeriv.Removable
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Meyers' example

Let `n` be a natural number, so that `ℝ^{n+2}` is a Euclidean space of dimension at least two. For
`0 < μ ≤ 1` let `a = TauCeti.PDE.meyersCoefficient μ` be the coefficient field

`a(x) = κ I + (1 - κ) x̂ x̂ᵀ`, where `x̂ = x / ‖x‖` and `κ = μ (μ + n) / (n + 1)`,

whose eigenvalue in the radial direction `x̂` is `1` and in the tangential directions is `κ`; in the
plane, `n = 0`, it is `μ²`. It is measurable and uniformly elliptic with constants `κ` and `1`, so
its ellipticity ratio `1 / κ` tends to infinity as `μ → 0`. The function `u(x) = ‖x‖ ^ (μ - 1) x₀`
(`TauCeti.PDE.meyersSolution μ`), homogeneous of degree `μ`, solves `div(a ∇u) = 0` weakly on every
open set, across the origin, while its gradient has size comparable to `‖x‖ ^ (μ - 1)`. On a
bounded open set containing the origin it therefore lies in `W^{1,p}` exactly for
`p (1 - μ) < n + 2`.

The same field and solution make sense for every `μ > 0`. For `μ ≥ 1` the field is uniformly
elliptic with constants `1` and `κ`, the solution lies in `W^{1,p}` of every bounded open set for
every `p`, and it is still a weak solution. In that range `u(t e₀) = t ^ μ` vanishes to order
`μ > 1` at the origin while `u > 0` on the half-space `0 < x₀`, which in the plane is the
counterexample to Hopf's lemma for measurable divergence-form coefficients
(`TauCeti.PDE.exists_uniformlyEllipticOn_energyFormH1_eq_zero_tendsto_div`).

In the plane this is Meyers' example showing that his higher integrability theorem is sharp in its
dependence on the ellipticity: weak solutions of `div(a ∇u) = 0` with bounded measurable, uniformly
elliptic coefficients have gradients in `L^p_loc` for some `p > 2`, but `p` cannot be chosen
independently of the ellipticity ratio, and tends to `2` as the ratio tends to infinity.

For `0 < μ ≤ 1` the solution is `μ`-Hölder on `ℝ^{n+2}` and, being `t ^ μ` along the ray through
`e₀`, no better at the origin. So in every dimension the Hölder exponent of De Giorgi's theorem
cannot be chosen independently of the ellipticity ratio either; this is drawn out in
`TauCeti.Analysis.PDE.Regularity.DeGiorgiExponent`.

## Main declarations

* `TauCeti.PDE.meyersEigenvalue`: the tangential eigenvalue `μ (μ + n) / (n + 1)` of Meyers'
  coefficient, characterized by `TauCeti.PDE.meyersEigenvalue_eq_iff`;
  `TauCeti.PDE.meyersEigenvalue_pos`, `TauCeti.PDE.meyersEigenvalue_le_one` and
  `TauCeti.PDE.one_le_meyersEigenvalue`: it is positive for `μ > 0`, at most `1` for `0 ≤ μ ≤ 1`
  and at least `1` for `μ ≥ 1`; `TauCeti.PDE.exists_meyersEigenvalue_eq`: it takes every value in
  `(0, 1]` at some `μ ∈ (0, 1]`.
* `TauCeti.PDE.uniformlyEllipticOn_meyersCoefficient`: for `μ ≤ 1`, Meyers' coefficient is
  uniformly elliptic with constants `μ (μ + n) / (n + 1)` and `1`;
  `TauCeti.PDE.uniformlyEllipticOn_meyersCoefficient_of_one_le`: for `μ ≥ 1`, with constants `1`
  and `μ (μ + n) / (n + 1)`; `TauCeti.PDE.uniformlyEllipticOn_smul_meyersCoefficient`: for
  `μ (μ + n) / (n + 1) = λ / Λ` with `0 < λ ≤ Λ`, the field `Λ a` has constants `λ` and `Λ`.
* `TauCeti.PDE.continuous_meyersSolution`, `TauCeti.PDE.meyersSolution_pos`,
  `TauCeti.PDE.meyersSolution_smul_single_zero`: Meyers' solution is continuous, positive on the
  half-space `0 < x₀`, and equal to `t ^ μ` at `t e₀`.
* `TauCeti.PDE.not_exists_tendsto_meyersCoefficient`: unless its tangential eigenvalue is `1`,
  Meyers' coefficient has no limit at the origin within the half-space `0 < x₀`.
* `TauCeti.PDE.gradient_meyersSolution`, `TauCeti.PDE.norm_gradient_meyersSolution_le`,
  `TauCeti.PDE.mul_rpow_le_norm_gradient_meyersSolution`: away from the origin, the gradient of
  Meyers' solution, the upper bound `‖∇u(x)‖ ≤ (1 + |μ - 1|) ‖x‖ ^ (μ - 1)` for every `μ`, and the
  lower bound `μ ‖x‖ ^ (μ - 1) ≤ ‖∇u(x)‖` for `0 < μ ≤ 1`.
* `TauCeti.PDE.gradient_ae_eq_gradient_meyersSolution`: the weak gradient of an element of
  `W^{1,p}(Ω)` equal to Meyers' solution is its classical gradient.
* `TauCeti.PDE.abs_meyersSolution_le`, `TauCeti.PDE.holderWith_meyersSolution`,
  `TauCeti.PDE.not_holderOnWith_meyersSolution`: Meyers' solution is bounded by `‖x‖ ^ μ`, and for
  `0 ≤ μ ≤ 1` it is `μ`-Hölder on `ℝ^{n+2}` but not `α`-Hölder near the origin for any `α > μ`.
* `TauCeti.PDE.energyFormH1_meyersCoefficient_eq_zero`: an element of `H¹(Ω)` equal to Meyers'
  solution is a weak solution of `div(a ∇u) = 0` on `Ω`, and
  `TauCeti.PDE.energyFormH1_smul_meyersCoefficient_eq_zero`: also of `div(c a ∇u) = 0`.
* `TauCeti.PDE.exists_w1p_value_ae_eq_meyersSolution`: on a bounded open set, Meyers' solution
  lies in `W^{1,p}` when `p (1 - μ) < n + 2`, and
  `TauCeti.PDE.exists_w1p_value_ae_eq_meyersSolution_iff`: on a bounded open set containing the
  origin, exactly then.
* `TauCeti.PDE.toReal_mul_one_sub_lt_of_memLp_gradient_meyersSolution`: if the gradient of Meyers'
  solution is `p`-integrable on some neighbourhood of the origin, then `p (1 - μ) < n + 2`.
* `TauCeti.PDE.exists_meyersSolution_not_exists_w1p`: for every `p > n + 2` some `μ ∈ (0, 1)`
  gives a weak solution in `H¹(Ω)` that is not in `W^{1,p}(Ω)`.

## The argument

Write `Rᵢ(x) = ‖x‖ ^ (μ - 1) xᵢ`, so that `u = R₀`. Away from the origin there is the pointwise
identity of homogeneous functions

`a ∇R₀ = μ / (n + 1) div W`, `Wᵢⱼ = Rⱼ δᵢ₀ - Rᵢ δⱼ₀`,

for the antisymmetric matrix field `W`, whose divergence has components
`(div W)ᵢ = ∑ⱼ ∂ⱼWᵢⱼ = δᵢ₀ ∑ⱼ ∂ⱼRⱼ - ∂₀Rᵢ`. The value `κ = μ (μ + n) / (n + 1)` of the tangential
eigenvalue is exactly the one that makes this identity hold. In the plane `W` is given by the
stream function `R₁`. All `Rᵢ` are continuous, since `μ > 0`, and differentiable away from the
origin with gradients bounded by `(1 + |μ - 1|) ‖x‖ ^ (μ - 1)`, which is locally integrable in
`ℝ^{n+2}`; so their classical gradients are weak gradients across the origin
(`TauCeti.hasWeakFDerivOn_of_hasFDerivAt_off_countable`). For a test function `φ`, the weak form is
then `μ / (n + 1) ∑ᵢ ∫ (∂₀φ ∂ᵢRᵢ - ∂ᵢφ ∂₀Rᵢ)`, which vanishes term by term after moving the
derivatives of `Rᵢ` onto `φ`, because the mixed derivatives of `φ` commute. The weak form is
continuous on `H¹(Ω)`, so it vanishes on the closure `H¹₀(Ω)` of the test functions.

For integrability, `‖∇u(x)‖ ≤ (1 + |μ - 1|) ‖x‖ ^ (μ - 1)`, with the lower bound
`μ ‖x‖ ^ (μ - 1) ≤ ‖∇u(x)‖` for `μ ≤ 1`, and `‖x‖ ^ s` is integrable on a ball about the origin of
`ℝ^{n+2}` exactly when `s > -(n + 2)` (`TauCeti.integrableOn_norm_rpow_ball_iff`).

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

variable {n : ℕ} {μ : ℝ}

/-- The tangential eigenvalue `μ (μ + n) / (n + 1)` of Meyers' coefficient field on `ℝ^{n+2}`
(`TauCeti.PDE.meyersCoefficient`); in the plane, `n = 0`, it is `μ²`. It is the value for which
`‖x‖ ^ (μ - 1) x₀` solves `div(a ∇u) = 0`. -/
def meyersEigenvalue (n : ℕ) (μ : ℝ) : ℝ :=
  μ * (μ + n) / (n + 1)

/-- Unfolding `TauCeti.PDE.meyersEigenvalue`. -/
theorem meyersEigenvalue_apply (n : ℕ) (μ : ℝ) : meyersEigenvalue n μ = μ * (μ + n) / (n + 1) :=
  (rfl)

/-- In the plane, the tangential eigenvalue of Meyers' coefficient is `μ²`. -/
@[simp]
theorem meyersEigenvalue_zero (μ : ℝ) : meyersEigenvalue 0 μ = μ ^ 2 := by
  simp [meyersEigenvalue_apply, sq]

/-- The tangential eigenvalue of Meyers' coefficient is `κ` exactly when `μ (μ + n) = (n + 1) κ`. -/
theorem meyersEigenvalue_eq_iff {κ : ℝ} :
    meyersEigenvalue n μ = κ ↔ μ * (μ + n) = (n + 1) * κ := by
  rw [meyersEigenvalue_apply, div_eq_iff (by positivity), mul_comm κ]

/-- **Meyers' coefficient field** on `ℝ^{n+2}`,
`a(x) = κ I + (1 - κ) x xᵀ / ‖x‖²` with `κ = μ (μ + n) / (n + 1)`
(`TauCeti.PDE.meyersEigenvalue`). Its eigenvalue in the radial direction `x` is `1` and in the
tangential directions is `κ`; in the plane, `n = 0`, it is `μ²`. At the origin, where the direction
is undefined, it is `κ I`. The tangential eigenvalue `κ` is the one for which `‖x‖ ^ (μ - 1) x₀`
solves `div(a ∇u) = 0`. It is the radial coefficient field
`TauCeti.PDE.radialCoefficient κ (1 - κ)`. -/
def meyersCoefficient (μ : ℝ) (x : EuclideanSpace ℝ (Fin (n + 2))) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
  radialCoefficient (meyersEigenvalue n μ) (1 - meyersEigenvalue n μ) x

/-- Unfolding `TauCeti.PDE.meyersCoefficient`. -/
theorem meyersCoefficient_apply (x : EuclideanSpace ℝ (Fin (n + 2))) :
    meyersCoefficient μ x = meyersEigenvalue n μ • 1 +
      ((1 - meyersEigenvalue n μ) / ‖x‖ ^ 2) • Matrix.vecMulVec x x :=
  radialCoefficient_apply x

/-- Meyers' coefficient is the radial coefficient field `α I + β x̂ x̂ᵀ` with
`α = κ = μ (μ + n) / (n + 1)` and `β = 1 - κ`. -/
theorem meyersCoefficient_eq_radialCoefficient :
    meyersCoefficient (n := n) μ =
      radialCoefficient (meyersEigenvalue n μ) (1 - meyersEigenvalue n μ) :=
  (rfl)

/-- The bilinear form of Meyers' coefficient: with `κ = μ (μ + n) / (n + 1)`,
`ηᵀ a(x) ξ = κ ⟪η, ξ⟫ + (1 - κ) ⟪η, x⟫ ⟪x, ξ⟫ / ‖x‖²`. -/
theorem dotProduct_meyersCoefficient_mulVec (x η ξ : EuclideanSpace ℝ (Fin (n + 2))) :
    η ⬝ᵥ (meyersCoefficient μ x *ᵥ ξ) = meyersEigenvalue n μ * ⟪η, ξ⟫_ℝ +
      (1 - meyersEigenvalue n μ) / ‖x‖ ^ 2 * (⟪η, x⟫_ℝ * ⟪x, ξ⟫_ℝ) :=
  dotProduct_radialCoefficient_mulVec x η ξ

/-- With `κ = μ (μ + n) / (n + 1)`, the bilinear form of Meyers' coefficient is bounded by
`|κ| + |1 - κ|`. -/
theorem abs_dotProduct_meyersCoefficient_mulVec_le (x η ξ : EuclideanSpace ℝ (Fin (n + 2))) :
    |η ⬝ᵥ (meyersCoefficient μ x *ᵥ ξ)| ≤
      (|meyersEigenvalue n μ| + |1 - meyersEigenvalue n μ|) * ‖η‖ * ‖ξ‖ :=
  abs_dotProduct_radialCoefficient_mulVec_le x η ξ

/-- The tangential eigenvalue of Meyers' coefficient is positive for `μ > 0`. -/
theorem meyersEigenvalue_pos (hμ : 0 < μ) : 0 < meyersEigenvalue n μ := by
  rw [meyersEigenvalue_apply]
  positivity

/-- The tangential eigenvalue of Meyers' coefficient is at most `1` for `0 ≤ μ ≤ 1`. -/
theorem meyersEigenvalue_le_one (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    meyersEigenvalue n μ ≤ 1 := by
  rw [meyersEigenvalue_apply, div_le_one (by positivity)]
  nlinarith

/-- The tangential eigenvalue of Meyers' coefficient is at least `1` for `μ ≥ 1`. -/
theorem one_le_meyersEigenvalue (hμ : 1 ≤ μ) : 1 ≤ meyersEigenvalue n μ := by
  rw [meyersEigenvalue_apply, one_le_div (by positivity)]
  nlinarith

/-- Every `κ ∈ (0, 1]` is the tangential eigenvalue of Meyers' coefficient for some `μ ∈ (0, 1]`,
namely the positive root `μ = (√(n² + 4 (n + 1) κ) - n) / 2` of `μ (μ + n) = (n + 1) κ`. -/
theorem exists_meyersEigenvalue_eq {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 ∧ meyersEigenvalue n μ = κ := by
  set s := √((n : ℝ) ^ 2 + 4 * (n + 1) * κ)
  have hD : 0 ≤ (n : ℝ) ^ 2 + 4 * (n + 1) * κ := by positivity
  have hs2 : s ^ 2 = (n : ℝ) ^ 2 + 4 * (n + 1) * κ := Real.sq_sqrt hD
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  refine ⟨(s - n) / 2, ?_, ?_, meyersEigenvalue_eq_iff.2 ?_⟩
  · -- `s² > n²` since `κ > 0`.
    have : (n : ℝ) < s := by nlinarith [mul_pos (by positivity : (0 : ℝ) < n + 1) hκ0]
    linarith
  · -- `s² ≤ (n + 2)²` since `κ ≤ 1`.
    have : s ≤ n + 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hκ1 (by positivity : (0 : ℝ) ≤ n + 1)]
    linarith
  · linear_combination hs2 / 4

/-- For `0 < μ ≤ 1`, Meyers' coefficient is uniformly elliptic with constants
`μ (μ + n) / (n + 1)` and `1`, so its ellipticity ratio is `(n + 1) / (μ (μ + n))`. -/
theorem uniformlyEllipticOn_meyersCoefficient (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 2)))) :
    UniformlyEllipticOn Ω (meyersCoefficient μ) (meyersEigenvalue n μ) 1 := by
  have h := uniformlyEllipticOn_radialCoefficient (meyersEigenvalue_pos (n := n) hμ0)
    (sub_nonneg.2 (meyersEigenvalue_le_one (n := n) hμ0.le hμ1)) Ω
  rwa [add_sub_cancel, ← meyersCoefficient_eq_radialCoefficient] at h

/-- For `μ ≥ 1`, Meyers' coefficient is uniformly elliptic with constants `1` and
`μ (μ + n) / (n + 1)`, which is its ellipticity ratio. -/
theorem uniformlyEllipticOn_meyersCoefficient_of_one_le (hμ : 1 ≤ μ)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 2)))) :
    UniformlyEllipticOn Ω (meyersCoefficient μ) 1 (meyersEigenvalue n μ) := by
  have h := uniformlyEllipticOn_radialCoefficient_of_nonpos (α := meyersEigenvalue n μ)
    (β := 1 - meyersEigenvalue n μ) (by simp) (sub_nonpos.2 (one_le_meyersEigenvalue hμ)) Ω
  rwa [add_sub_cancel, ← meyersCoefficient_eq_radialCoefficient] at h

/-- **Meyers' coefficient at prescribed ellipticity constants.** Let `0 < λ ≤ Λ` and let `μ > 0`
satisfy `μ (μ + n) / (n + 1) = λ / Λ`. Then `Λ a`, for Meyers' coefficient `a`, is uniformly
elliptic with constants `λ` and `Λ`. Every `λ / Λ ∈ (0, 1]` is attained by some `μ ∈ (0, 1]`
(`TauCeti.PDE.exists_meyersEigenvalue_eq`). -/
theorem uniformlyEllipticOn_smul_meyersCoefficient (hμ0 : 0 < μ) {lam Lam : ℝ} (hlam : 0 < lam)
    (hLam : lam ≤ Lam) (hμ : meyersEigenvalue n μ = lam / Lam)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 2)))) :
    UniformlyEllipticOn Ω (Lam • meyersCoefficient μ) lam Lam := by
  have hLam0 : 0 < Lam := hlam.trans_le hLam
  have hμ1 : μ ≤ 1 := by
    by_contra hμ1
    have h1 : meyersEigenvalue n μ ≤ 1 := by rw [hμ]; exact (div_le_one hLam0).2 hLam
    rw [meyersEigenvalue_apply, div_le_one (by positivity)] at h1
    nlinarith
  have := (uniformlyEllipticOn_meyersCoefficient hμ0 hμ1 Ω).const_smul hLam0
  rwa [hμ, mul_div_cancel₀ _ hLam0.ne', mul_one] at this

/-- Meyers' coefficient is strongly measurable. -/
theorem stronglyMeasurable_meyersCoefficient :
    StronglyMeasurable (meyersCoefficient (n := n) μ) :=
  stronglyMeasurable_radialCoefficient

open Filter in
/-- **Meyers' coefficient is discontinuous at the origin.** If its tangential eigenvalue
`μ (μ + n) / (n + 1)` is not `1`, it has no limit at the origin within the half-space `0 < x₀`:
along the ray through `e₀` its entry `a₀₀` is `1`, and along the ray through `e₀ + e₁` it is the
average of `1` and the tangential eigenvalue. -/
theorem not_exists_tendsto_meyersCoefficient (hμ : meyersEigenvalue n μ ≠ 1) :
    ¬ ∃ L, Tendsto (meyersCoefficient μ) (𝓝[{x : EuclideanSpace ℝ (Fin (n + 2)) | 0 < x 0}] 0)
      (𝓝 L) := by
  refine not_exists_tendsto_radialCoefficient_of_ne (v := EuclideanSpace.single 0 1)
    (w := EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1) (fun t ht => by simpa using ht)
    (fun t ht => by simpa using ht) fun h => hμ ?_
  have hw : ‖EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ) + EuclideanSpace.single 1 1‖ ^ 2 =
      2 := by
    rw [norm_add_sq_real, EuclideanSpace.inner_single_left]
    norm_num
  have h00 := congrFun (congrFun h 0) 0
  rw [radialCoefficient_apply_apply, radialCoefficient_apply_apply, hw] at h00
  norm_num at h00
  linarith

/-! ### The radial coordinate functions -/

/-- The function `x ↦ ‖x‖ ^ (μ - 1) xᵢ`, homogeneous of degree `μ`. -/
private def radialCoord (μ : ℝ) (i : Fin (n + 2)) (x : EuclideanSpace ℝ (Fin (n + 2))) : ℝ :=
  ‖x‖ ^ (μ - 1) * x i

/-- The classical gradient of `TauCeti.PDE.radialCoord` away from the origin. -/
private def radialCoordGradient (μ : ℝ) (i : Fin (n + 2)) (x : EuclideanSpace ℝ (Fin (n + 2))) :
    EuclideanSpace ℝ (Fin (n + 2)) :=
  ‖x‖ ^ (μ - 1) • EuclideanSpace.single i 1 + ((μ - 1) * ‖x‖ ^ (μ - 3) * x i) • x

private theorem norm_rpow_sub_one {x : EuclideanSpace ℝ (Fin (n + 2))} (hx : x ≠ 0) :
    ‖x‖ ^ (μ - 1) = ‖x‖ ^ (μ - 3) * ‖x‖ ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_add (norm_pos_iff.2 hx)]
  congr 1
  ring

private theorem hasFDerivAt_radialCoord {x : EuclideanSpace ℝ (Fin (n + 2))} (hx : x ≠ 0)
    (i : Fin (n + 2)) :
    HasFDerivAt (radialCoord μ i) (innerSL ℝ (radialCoordGradient μ i x)) x := by
  refine ((hasFDerivAt_norm_rpow_of_ne (μ - 1) hx).mul
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt).congr_fderiv ?_
  ext v
  simp [radialCoordGradient, EuclideanSpace.inner_single_left, show μ - 1 - 2 = μ - 3 by ring]
  ring

private theorem abs_radialCoord_le (i : Fin (n + 2)) (x : EuclideanSpace ℝ (Fin (n + 2))) :
    |radialCoord μ i x| ≤ ‖x‖ ^ μ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simpa [radialCoord] using Real.rpow_nonneg le_rfl μ
  rw [radialCoord, abs_mul, abs_of_nonneg (by positivity)]
  calc ‖x‖ ^ (μ - 1) * |x i| ≤ ‖x‖ ^ (μ - 1) * ‖x‖ :=
        mul_le_mul_of_nonneg_left (by simpa using PiLp.norm_apply_le x i) (by positivity)
    _ = ‖x‖ ^ μ := by
        rw [← Real.rpow_add_one (norm_pos_iff.2 hx).ne']
        ring_nf

private theorem continuous_radialCoord (hμ : 0 < μ) (i : Fin (n + 2)) :
    Continuous (radialCoord μ i) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · have h0 : radialCoord μ i 0 = 0 := by simp [radialCoord]
    rw [ContinuousAt, h0]
    refine squeeze_zero_norm (fun y => (abs_radialCoord_le i y)) ?_
    simpa [Real.zero_rpow hμ.ne'] using
      ((continuous_norm.rpow_const fun _ => Or.inr hμ.le).tendsto
        (0 : EuclideanSpace ℝ (Fin (n + 2))))
  · exact (hasFDerivAt_radialCoord hx i).continuousAt

private theorem norm_radialCoordGradient_le (i : Fin (n + 2)) {x : EuclideanSpace ℝ (Fin (n + 2))}
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

private theorem measurable_radialCoordGradient (i : Fin (n + 2)) :
    Measurable (radialCoordGradient μ i) := by
  unfold radialCoordGradient
  fun_prop

private theorem locallyIntegrable_radialCoordGradient (hμ0 : 0 < μ) (i : Fin (n + 2)) :
    LocallyIntegrable (fun x => innerSL ℝ (radialCoordGradient μ i x))
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 2)))) := by
  refine locallyIntegrable_of_norm_le_rpow (C := 1 + |μ - 1|) (α := 1 - μ) (by simp)
    (by simp; linarith)
    ?_ ((innerSL ℝ).continuous.comp_aestronglyMeasurable
      (measurable_radialCoordGradient i).aestronglyMeasurable)
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : EuclideanSpace ℝ (Fin (n + 2))))]
    with x hx
  rw [innerSL_apply_norm, neg_sub]
  exact norm_radialCoordGradient_le i hx

/-- The radial coordinate function has its classical gradient as weak gradient on every open set:
the singularity at the origin is removable. -/
private theorem hasWeakFDerivOn_radialCoord (hμ0 : 0 < μ) (i : Fin (n + 2))
    (Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))) :
    HasWeakFDerivOn volume Ω (radialCoord μ i) (fun x => innerSL ℝ (radialCoordGradient μ i x)) :=
  hasWeakFDerivOn_of_hasFDerivAt_off_countable (countable_singleton 0)
    (continuous_radialCoord hμ0 i).continuousOn
    ((locallyIntegrable_radialCoordGradient hμ0 i).locallyIntegrableOn _)
    fun _ hx => hasFDerivAt_radialCoord hx.2 i

/-! ### Meyers' solution -/

/-- Meyers' solution `u(x) = |x|^(μ - 1) x₀` of `div(a ∇u) = 0` for
`a = TauCeti.PDE.meyersCoefficient μ`, homogeneous of degree `μ`. -/
def meyersSolution (μ : ℝ) (x : EuclideanSpace ℝ (Fin (n + 2))) : ℝ :=
  ‖x‖ ^ (μ - 1) * x 0

/-- Unfolding `TauCeti.PDE.meyersSolution`. -/
theorem meyersSolution_apply (x : EuclideanSpace ℝ (Fin (n + 2))) :
    meyersSolution μ x = ‖x‖ ^ (μ - 1) * x 0 :=
  (rfl)

private theorem meyersSolution_eq_radialCoord : meyersSolution (n := n) μ = radialCoord μ 0 :=
  (rfl)

/-- Meyers' solution vanishes at the origin. -/
@[simp]
theorem meyersSolution_zero : meyersSolution μ (0 : EuclideanSpace ℝ (Fin (n + 2))) = 0 := by
  simp [meyersSolution]

/-- For `μ > 0`, Meyers' solution is continuous, also at the origin. -/
theorem continuous_meyersSolution (hμ : 0 < μ) : Continuous (meyersSolution (n := n) μ) :=
  continuous_radialCoord hμ 0

/-- Meyers' solution is positive on the open half-space `0 < x₀`. -/
theorem meyersSolution_pos {x : EuclideanSpace ℝ (Fin (n + 2))} (hx : 0 < x 0) :
    0 < meyersSolution μ x := by
  have : x ≠ 0 := fun h => by simp [h] at hx
  rw [meyersSolution_apply]
  exact mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.2 this) _) hx

/-- On the ray through `e₀`, Meyers' solution is `t ↦ t ^ μ`. -/
theorem meyersSolution_smul_single_zero {t : ℝ} (ht : 0 < t) :
    meyersSolution μ (t • EuclideanSpace.single (0 : Fin (n + 2)) 1) = t ^ μ := by
  rw [meyersSolution_apply, norm_smul, PiLp.norm_single, norm_one, mul_one,
    Real.norm_of_nonneg ht.le]
  simp only [PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul, mul_one]
  rw [← Real.rpow_add_one ht.ne', sub_add_cancel]

/-- Away from the origin, Meyers' solution has gradient
`‖x‖ ^ (μ - 1) e₀ + (μ - 1) ‖x‖ ^ (μ - 3) x₀ x`. -/
theorem hasGradientAt_meyersSolution {x : EuclideanSpace ℝ (Fin (n + 2))} (hx : x ≠ 0) :
    HasGradientAt (meyersSolution μ)
      (‖x‖ ^ (μ - 1) • EuclideanSpace.single 0 1 + ((μ - 1) * ‖x‖ ^ (μ - 3) * x 0) • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact hasFDerivAt_radialCoord (μ := μ) hx 0

/-- The gradient of Meyers' solution away from the origin. -/
theorem gradient_meyersSolution {x : EuclideanSpace ℝ (Fin (n + 2))} (hx : x ≠ 0) :
    ∇ (meyersSolution μ) x =
      ‖x‖ ^ (μ - 1) • EuclideanSpace.single 0 1 + ((μ - 1) * ‖x‖ ^ (μ - 3) * x 0) • x :=
  (hasGradientAt_meyersSolution hx).gradient

private theorem gradient_meyersSolution_eq_radialCoordGradient {x : EuclideanSpace ℝ (Fin (n + 2))}
    (hx : x ≠ 0) : ∇ (meyersSolution μ) x = radialCoordGradient μ 0 x :=
  gradient_meyersSolution hx

/-- The coordinates of the gradient of `TauCeti.PDE.radialCoord` away from the origin. -/
private theorem radialCoordGradient_apply {x : EuclideanSpace ℝ (Fin (n + 2))} (hx : x ≠ 0)
    (i j : Fin (n + 2)) : radialCoordGradient μ i x j =
      ‖x‖ ^ (μ - 3) * (‖x‖ ^ 2 * (if j = i then 1 else 0) + (μ - 1) * x i * x j) := by
  simp only [radialCoordGradient, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    PiLp.single_apply, norm_rpow_sub_one hx]
  split_ifs <;> ring

/-- Away from the origin, Meyers' coefficient maps the gradient of `R₀ = ‖x‖ ^ (μ - 1) x₀` to the
divergence of an antisymmetric matrix field: with `Rᵢ = ‖x‖ ^ (μ - 1) xᵢ`,

`ηᵀ a(x) ∇R₀ = μ / (n + 1) ∑ᵢ (η₀ ∂ᵢRᵢ - ηᵢ ∂₀Rᵢ)`,

which is `η · div W` for `Wᵢⱼ = μ / (n + 1) (Rⱼ δᵢ₀ - Rᵢ δⱼ₀)`. In the plane this is the stream
function `μ R₁`. The tangential eigenvalue `μ (μ + n) / (n + 1)` is exactly the one for which the
identity holds. -/
private theorem dotProduct_meyersCoefficient_mulVec_radialCoordGradient
    {x : EuclideanSpace ℝ (Fin (n + 2))} (hx : x ≠ 0) (η : EuclideanSpace ℝ (Fin (n + 2))) :
    η ⬝ᵥ (meyersCoefficient μ x *ᵥ radialCoordGradient μ 0 x) = μ / (n + 1) *
      ∑ i, (η 0 * radialCoordGradient μ i x i - η i * radialCoordGradient μ i x 0) := by
  have hR : ∑ i, x i * x i = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [sq]
  have hG := radialCoordGradient_apply (μ := μ) hx
  have hinner : ∀ y : EuclideanSpace ℝ (Fin (n + 2)), ⟪y, radialCoordGradient μ 0 x⟫_ℝ =
      ‖x‖ ^ (μ - 3) * (‖x‖ ^ 2 * y 0 + (μ - 1) * x 0 * ⟪y, x⟫_ℝ) := by
    intro y
    rw [radialCoordGradient, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      EuclideanSpace.inner_single_right, norm_rpow_sub_one hx, conj_trivial]
    ring
  -- Each summand, split into the parts that sum to `‖x‖²`, to `η₀` and to `⟪η, x⟫`.
  have hterm : ∀ i, η 0 * radialCoordGradient μ i x i - η i * radialCoordGradient μ i x 0 =
      ‖x‖ ^ (μ - 3) * ‖x‖ ^ 2 * η 0 + ‖x‖ ^ (μ - 3) * (μ - 1) * η 0 * (x i * x i) -
        ‖x‖ ^ (μ - 3) * ‖x‖ ^ 2 * (if 0 = i then η i else 0) -
        ‖x‖ ^ (μ - 3) * (μ - 1) * x 0 * (η i * x i) := fun i => by
    rw [hG, hG, ite_eq_left rfl]
    -- The Kronecker deltas `δ₀ᵢ` in `∂₀Rᵢ` and in the claimed right-hand side agree.
    by_cases h : 0 = i
    · rw [ite_eq_left h, ite_eq_left h, h]
      ring
    · rw [ite_eq_right h, ite_eq_right h]
      ring
  have hηx : ∑ i, η i * x i = ⟪η, x⟫_ℝ := by
    simp [PiLp.inner_apply, mul_comm]
  have hsum : ∑ i, (η 0 * radialCoordGradient μ i x i - η i * radialCoordGradient μ i x 0) =
      ‖x‖ ^ (μ - 3) * ((n + 1 : ℝ) * ‖x‖ ^ 2 * η 0 + (μ - 1) * η 0 * ‖x‖ ^ 2 -
        (μ - 1) * x 0 * ⟪η, x⟫_ℝ) := by
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true, hR, hηx]
    push_cast
    ring
  rw [dotProduct_meyersCoefficient_mulVec, hinner, hinner, hsum, real_inner_self_eq_norm_sq,
    meyersEigenvalue_apply]
  field_simp
  ring

/-- The weak gradient of an element of `W^{1,p}(Ω)` equal to Meyers' solution is its classical
gradient. -/
private theorem gradient_ae_eq_radialCoordGradient (hμ0 : 0 < μ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))} (u : W1p volume Ω p)
    (hu : W1p.value u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))]
      meyersSolution μ) :
    W1p.gradient u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))]
      radialCoordGradient μ 0 := by
  filter_upwards [((W1p.hasWeakFDerivOn u).congr_ae hu).ae_eq
    (hasWeakFDerivOn_radialCoord hμ0 0 Ω)] with x hx
  exact innerSL_inj.1 hx

/-- The mixed derivatives of a test function `φ` commute, so, by the weak derivative identities of
`Rᵢ = ‖x‖ ^ (μ - 1) xᵢ`, `∫ ∂₀φ ∂ᵢRᵢ = ∫ ∂ᵢφ ∂₀Rᵢ`. -/
private theorem integral_lineDeriv_smul_radialCoordGradient_comm (hμ0 : 0 < μ)
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))} (φ : 𝓓(Ω, ℝ)) (i : Fin (n + 2)) :
    ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ (Fin (n + 2)) → ℝ) x
        (EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ)) • radialCoordGradient μ i x i =
      ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ (Fin (n + 2)) → ℝ) x
        (EuclideanSpace.single i (1 : ℝ)) • radialCoordGradient μ i x 0 := by
  have hψ := hasWeakFDerivOn_radialCoord hμ0 i Ω
  have h1 := HasWeakLineDerivOn.integral_lineDeriv_smul_eq_neg_integral_smul
    (hψ.hasWeakLineDerivOn (EuclideanSpace.single i (1 : ℝ)))
    (∂_{EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ)} φ)
  have h0 := HasWeakLineDerivOn.integral_lineDeriv_smul_eq_neg_integral_smul
    (hψ.hasWeakLineDerivOn (EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ)))
    (∂_{EuclideanSpace.single i (1 : ℝ)} φ)
  simp only [TestFunction.lineDeriv_lineDerivOp_comm φ
    (EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))] at h1
  rw [h0] at h1
  simpa [TestFunction.lineDerivOp_apply, EuclideanSpace.inner_single_right] using h1.symm

/-- The weak equation for Meyers' solution against a test function: by the pointwise identity
`a ∇R₀ = μ / (n + 1) div W` for an antisymmetric `W`, the energy form is
`μ / (n + 1) ∑ᵢ ∫ (∂₀φ ∂ᵢRᵢ - ∂ᵢφ ∂₀Rᵢ) = 0`. -/
private theorem energyFormH1_meyersCoefficient_ofTestFunctionₗ_eq_zero (hμ0 : 0 < μ)
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))} (u : W1p volume Ω 2)
    (hu : W1p.value u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))]
      meyersSolution μ)
    (φ : 𝓓(Ω, ℝ)) :
    energyFormH1 (meyersCoefficient μ) 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) = 0 := by
  have hloc : ∀ i j, LocallyIntegrableOn (fun x => radialCoordGradient μ i x j) Ω volume :=
    fun i j => by
      simpa [EuclideanSpace.inner_single_right] using
        ((hasWeakFDerivOn_radialCoord hμ0 i Ω).hasWeakLineDerivOn
          (EuclideanSpace.single j (1 : ℝ))).locallyIntegrableOn_deriv
  have hd : ∀ x i, (∇ (φ : EuclideanSpace ℝ (Fin (n + 2)) → ℝ) x) i =
      lineDeriv ℝ (φ : EuclideanSpace ℝ (Fin (n + 2)) → ℝ) x (EuclideanSpace.single i (1 : ℝ)) := by
    intro x i
    rw [(φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv, ← inner_gradient_left,
      EuclideanSpace.inner_single_right]
    simp
  -- The two families of integrands `∂₀φ ∂ᵢRᵢ` and `∂ᵢφ ∂₀Rᵢ`, integrable on `Ω`.
  set A : Fin (n + 2) → EuclideanSpace ℝ (Fin (n + 2)) → ℝ := fun i x =>
    lineDeriv ℝ (φ : EuclideanSpace ℝ (Fin (n + 2)) → ℝ) x
      (EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ)) • radialCoordGradient μ i x i with hA
  set B : Fin (n + 2) → EuclideanSpace ℝ (Fin (n + 2)) → ℝ := fun i x =>
    lineDeriv ℝ (φ : EuclideanSpace ℝ (Fin (n + 2)) → ℝ) x
      (EuclideanSpace.single i (1 : ℝ)) • radialCoordGradient μ i x 0 with hB
  have hAi : ∀ i, Integrable (A i) := fun i =>
    integrable_lineDeriv_smul_of_locallyIntegrableOn (hloc i i) φ _
  have hBi : ∀ i, Integrable (B i) := fun i =>
    integrable_lineDeriv_smul_of_locallyIntegrableOn (hloc i 0) φ _
  rw [energyFormH1_zero_zero_eq_setIntegral]
  calc ∫ x in Ω, matrixBilinearForm (meyersCoefficient μ x)
        (W1p.gradient (W1p.ofTestFunctionₗ volume Ω 2 φ) x) (W1p.gradient u x)
      = ∫ x in Ω, ∑ i, μ / (n + 1) * (A i x - B i x) := by
        refine integral_congr_ae ?_
        filter_upwards [gradient_ae_eq_radialCoordGradient hμ0 u hu,
          gradientTestFunctionLp_apply_ae (mu := volume) 2 φ,
          ae_restrict_of_ae (compl_mem_ae_iff.2
            (measure_singleton (0 : EuclideanSpace ℝ (Fin (n + 2)))))] with x hx hφ h0
        rw [W1p.gradient_ofTestFunctionₗ, hφ, hx, matrixBilinearForm_apply,
          dotProduct_meyersCoefficient_mulVec_radialCoordGradient h0, Finset.mul_sum]
        simp only [hA, hB, hd, smul_eq_mul]
    _ = ∑ i, μ / (n + 1) * ((∫ x, A i x) - ∫ x, B i x) := by
        rw [integral_finsetSum (f := fun i x => μ / (n + 1) * (A i x - B i x)) _
          fun i _ => ((hAi i).sub (hBi i)).restrict.const_mul _]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_const_mul, integral_sub (hAi i).restrict (hBi i).restrict, hA, hB,
          setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul,
          setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul]
    _ = 0 := Finset.sum_eq_zero fun i _ => by
        rw [hA, hB, integral_lineDeriv_smul_radialCoordGradient_comm hμ0 φ i, sub_self, mul_zero]

/-- **Meyers' solution is a weak solution.** For `μ > 0` and every open `Ω ⊆ ℝ^{n+2}`, an element
`u ∈ H¹(Ω)` equal to `‖x‖ ^ (μ - 1) x₀` almost everywhere on `Ω` is a weak solution of
`div(a ∇u) = 0` for Meyers' coefficient `a`: `∫_Ω ⟨a ∇u, ∇v⟩ = 0` for every `v ∈ H¹₀(Ω)`. The
equation also holds across the origin, where, for `μ ≠ 1`, `a` is discontinuous, and for `μ < 1`
also `∇u` is unbounded. -/
theorem energyFormH1_meyersCoefficient_eq_zero (hμ0 : 0 < μ)
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))} (u : W1p volume Ω 2)
    (hu : W1p.value u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))]
      meyersSolution μ)
    (v : W1p0 volume Ω 2) :
    energyFormH1 (meyersCoefficient μ) 0 0 u (v : W1p volume Ω 2) = 0 := by
  have hcoeff := memLp_energyIntegrand_of_bounds (Omega := Ω) (mu := volume)
    (b := 0) (c := 0) (beta := 0) (gamma := 0) (by positivity)
    stronglyMeasurable_meyersCoefficient.aestronglyMeasurable aestronglyMeasurable_const
    aestronglyMeasurable_const
    (fun x _ η ξ => abs_dotProduct_meyersCoefficient_mulVec_le (μ := μ) x η ξ)
    (fun _ _ => by simp) (fun _ _ => by simp)
  have hclosed : IsClosed {w : W1p volume Ω 2 | energyFormH1L hcoeff u w = 0} :=
    isClosed_eq (energyFormH1L hcoeff u).continuous continuous_const
  refine (energyFormH1L_apply hcoeff u _).symm.trans
    (w1p0Submodule_subset_of_isClosed hclosed (fun φ => ?_) v.property)
  rw [Set.mem_ofPred_eq, energyFormH1L_apply]
  exact energyFormH1_meyersCoefficient_ofTestFunctionₗ_eq_zero hμ0 u hu φ

/-- **Meyers' solution solves the equation of every multiple of Meyers' coefficient.** For `μ > 0`,
every `c` and every open `Ω ⊆ ℝ^{n+2}`, an element `u ∈ H¹(Ω)` equal to `‖x‖ ^ (μ - 1) x₀`
almost everywhere on `Ω` satisfies `∫_Ω ⟨c a ∇u, ∇v⟩ = 0` for every `v ∈ H¹₀(Ω)`, where `a` is
Meyers' coefficient. -/
theorem energyFormH1_smul_meyersCoefficient_eq_zero (hμ0 : 0 < μ) (c : ℝ)
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))} (u : W1p volume Ω 2)
    (hu : W1p.value u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))]
      meyersSolution μ)
    (v : W1p0 volume Ω 2) :
    energyFormH1 (c • meyersCoefficient μ) 0 0 u (v : W1p volume Ω 2) = 0 := by
  have := energyFormH1_smul_coefficients (meyersCoefficient μ) 0 0 c u (v : W1p volume Ω 2)
  rw [smul_zero, smul_zero] at this
  rw [this, energyFormH1_meyersCoefficient_eq_zero hμ0 u hu v, mul_zero]

/-- Away from the origin, the gradient of Meyers' solution has length at least
`μ ‖x‖ ^ (μ - 1)`. -/
private theorem mul_rpow_le_norm_radialCoordGradient (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    {x : EuclideanSpace ℝ (Fin (n + 2))} (hx : x ≠ 0) :
    μ * ‖x‖ ^ (μ - 1) ≤ ‖radialCoordGradient μ 0 x‖ := by
  have hc : 0 ≤ 1 - μ ^ 2 := by nlinarith
  have hx0 : x 0 ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using PiLp.norm_apply_le x 0) 2
  refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
  have hn : ‖radialCoordGradient μ 0 x‖ ^ 2 = (‖x‖ ^ (μ - 1)) ^ 2 +
      2 * ‖x‖ ^ (μ - 1) * ((μ - 1) * ‖x‖ ^ (μ - 3) * x 0) * x 0 +
      ((μ - 1) * ‖x‖ ^ (μ - 3) * x 0) ^ 2 * ‖x‖ ^ 2 := by
    simp [radialCoordGradient, norm_add_sq_real, norm_smul, real_inner_smul_left,
      real_inner_smul_right, EuclideanSpace.inner_single_left, mul_pow]
    ring
  rw [hn, norm_rpow_sub_one hx]
  generalize ‖x‖ ^ (μ - 3) = t
  -- The defect is `t² ‖x‖² (1 - μ²) (‖x‖² - x₀²) ≥ 0`.
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (t * ‖x‖)) hc) (sub_nonneg.2 hx0)]

/-- Away from the origin, the gradient of Meyers' solution has length at most
`(1 + |μ - 1|) ‖x‖ ^ (μ - 1)`. -/
theorem norm_gradient_meyersSolution_le {x : EuclideanSpace ℝ (Fin (n + 2))} (hx : x ≠ 0) :
    ‖∇ (meyersSolution μ) x‖ ≤ (1 + |μ - 1|) * ‖x‖ ^ (μ - 1) := by
  rw [gradient_meyersSolution_eq_radialCoordGradient hx]
  exact norm_radialCoordGradient_le 0 hx

/-- Away from the origin, the gradient of Meyers' solution has length at least
`μ ‖x‖ ^ (μ - 1)`. -/
theorem mul_rpow_le_norm_gradient_meyersSolution (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    {x : EuclideanSpace ℝ (Fin (n + 2))} (hx : x ≠ 0) :
    μ * ‖x‖ ^ (μ - 1) ≤ ‖∇ (meyersSolution μ) x‖ := by
  rw [gradient_meyersSolution_eq_radialCoordGradient hx]
  exact mul_rpow_le_norm_radialCoordGradient hμ0 hμ1 hx

/-- The weak gradient of an element of `W^{1,p}(Ω)` equal to Meyers' solution is its classical
gradient. -/
theorem gradient_ae_eq_gradient_meyersSolution (hμ0 : 0 < μ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))} (u : W1p volume Ω p)
    (hu : W1p.value u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))]
      meyersSolution μ) :
    W1p.gradient u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))]
      ∇ (meyersSolution μ) := by
  filter_upwards [gradient_ae_eq_radialCoordGradient hμ0 u hu, ae_restrict_of_ae
    (compl_mem_ae_iff.2 (measure_singleton (0 : EuclideanSpace ℝ (Fin (n + 2)))))] with x hx h0
  rw [hx, gradient_meyersSolution_eq_radialCoordGradient h0]

/-! ### Hölder continuity -/

/-- Meyers' solution is bounded by `‖x‖ ^ μ`. -/
theorem abs_meyersSolution_le (x : EuclideanSpace ℝ (Fin (n + 2))) :
    |meyersSolution μ x| ≤ ‖x‖ ^ μ :=
  abs_radialCoord_le 0 x

/-- For `0 ≤ μ ≤ 1`, on the ball of radius `‖x‖ / 2` about a point `x`, which avoids the origin,
Meyers' solution is Lipschitz with constant `2 (‖x‖ / 2) ^ (μ - 1)`. -/
private theorem abs_meyersSolution_sub_le_of_dist_lt (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    {x y : EuclideanSpace ℝ (Fin (n + 2))} (hxy : dist y x < ‖x‖ / 2) :
    |meyersSolution μ y - meyersSolution μ x| ≤ 2 * (‖x‖ / 2) ^ (μ - 1) * ‖y - x‖ := by
  have hx : 0 < ‖x‖ / 2 := dist_nonneg.trans_lt hxy
  -- On the ball, `‖z‖ > ‖x‖ / 2`, so the gradient bound `(1 + |μ - 1|) ‖z‖ ^ (μ - 1)` is at
  -- most `2 (‖x‖ / 2) ^ (μ - 1)`.
  have hball : ∀ z ∈ ball x (‖x‖ / 2), ‖x‖ / 2 < ‖z‖ := fun z hz => by
    rw [mem_ball, dist_eq_norm] at hz
    linarith [norm_sub_norm_le x z, norm_sub_rev x z]
  have hz0 : ∀ z ∈ ball x (‖x‖ / 2), z ≠ 0 := fun z hz =>
    norm_pos_iff.1 (hx.trans (hball z hz))
  have h := (convex_ball x (‖x‖ / 2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := meyersSolution μ) (C := 2 * (‖x‖ / 2) ^ (μ - 1))
    (f' := fun z => InnerProductSpace.toDual ℝ _ (∇ (meyersSolution μ) z))
    (fun z hz => (hasGradientAt_iff_hasFDerivAt.1
      (hasGradientAt_meyersSolution (hz0 z hz)).differentiableAt.hasGradientAt).hasFDerivWithinAt)
    (fun z hz => ?_) (mem_ball_self hx) hxy
  · simpa only [Real.norm_eq_abs] using h
  rw [LinearIsometryEquiv.norm_map]
  calc ‖∇ (meyersSolution μ) z‖ ≤ (1 + |μ - 1|) * ‖z‖ ^ (μ - 1) :=
        norm_gradient_meyersSolution_le (hz0 z hz)
    _ ≤ 2 * (‖x‖ / 2) ^ (μ - 1) := by
        gcongr ?_ * ?_
        · rw [abs_of_nonpos (by linarith)]
          linarith
        · exact Real.rpow_le_rpow_of_nonpos hx (hball z hz).le (by linarith)

/-- **Meyers' solution is `μ`-Hölder.** For `0 ≤ μ ≤ 1` the function `‖x‖ ^ (μ - 1) x₀`,
homogeneous of degree `μ`, is Hölder continuous on all of `ℝ^{n+2}` with exponent `μ` and
constant `4`. By `TauCeti.PDE.not_holderOnWith_meyersSolution` no larger exponent works near the
origin. -/
theorem holderWith_meyersSolution (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    HolderWith 4 μ.toNNReal (meyersSolution (n := n) μ) := by
  -- It suffices to bound `|u y - u x|` for `‖y‖ ≤ ‖x‖`.
  suffices h : ∀ x y : EuclideanSpace ℝ (Fin (n + 2)), ‖y‖ ≤ ‖x‖ →
      |meyersSolution μ y - meyersSolution μ x| ≤ 4 * dist y x ^ μ by
    refine holderOnWith_univ.1 (HolderOnWith.of_dist_le fun x _ y _ => ?_)
    rw [Real.dist_eq, NNReal.coe_ofNat, Real.coe_toNNReal μ hμ0]
    rcases le_total ‖y‖ ‖x‖ with hyx | hxy
    · rw [abs_sub_comm, dist_comm]
      exact h x y hyx
    · exact h y x hxy
  intro x y hyx
  rcases lt_or_ge (dist y x) (‖x‖ / 2) with hd | hd
  · -- Nearby points: the Lipschitz bound on the ball, and `d ^ (1 - μ) ≤ (‖x‖ / 2) ^ (1 - μ)`.
    have hx : 0 < ‖x‖ / 2 := dist_nonneg.trans_lt hd
    refine (abs_meyersSolution_sub_le_of_dist_lt hμ0 hμ1 hd).trans ?_
    rw [← dist_eq_norm]
    rcases eq_or_lt_of_le (dist_nonneg : 0 ≤ dist y x) with h0 | h0
    · rw [← h0, mul_zero]
      positivity
    calc 2 * (‖x‖ / 2) ^ (μ - 1) * dist y x
        = 2 * ((‖x‖ / 2) ^ (μ - 1) * dist y x ^ (1 - μ)) * dist y x ^ μ := by
          rw [mul_assoc 2, mul_assoc, mul_assoc, ← Real.rpow_add h0, sub_add_cancel,
            Real.rpow_one]
      _ ≤ 2 * ((‖x‖ / 2) ^ (μ - 1) * (‖x‖ / 2) ^ (1 - μ)) * dist y x ^ μ := by
          gcongr
      _ ≤ 4 * dist y x ^ μ := by
          rw [← Real.rpow_add hx, sub_add_sub_cancel, sub_self, Real.rpow_zero]
          nlinarith [Real.rpow_nonneg h0.le μ]
  · -- Distant points: `|u y| + |u x| ≤ 2 ‖x‖ ^ μ ≤ 2 (2 d) ^ μ ≤ 4 d ^ μ`.
    have hxd : ‖x‖ ≤ 2 * dist y x := by linarith
    calc |meyersSolution μ y - meyersSolution μ x|
        ≤ |meyersSolution μ y| + |meyersSolution μ x| := abs_sub _ _
      _ ≤ ‖y‖ ^ μ + ‖x‖ ^ μ := add_le_add (abs_meyersSolution_le y) (abs_meyersSolution_le x)
      _ ≤ 2 * (2 * dist y x) ^ μ := by
          have h1 := Real.rpow_le_rpow (norm_nonneg y) hyx hμ0
          have h2 := Real.rpow_le_rpow (norm_nonneg x) hxd hμ0
          linarith
      _ ≤ 4 * dist y x ^ μ := by
          rw [Real.mul_rpow zero_le_two dist_nonneg]
          have : (2 : ℝ) ^ μ ≤ 2 := by
            simpa using Real.rpow_le_rpow_of_exponent_le one_le_two hμ1
          nlinarith [Real.rpow_nonneg (dist_nonneg : 0 ≤ dist y x) μ]

/-- **Meyers' solution is no better than `μ`-Hölder at the origin.** For every exponent `α > μ`,
the function `‖x‖ ^ (μ - 1) x₀` is not `α`-Hölder on any neighbourhood of the origin, with any
constant: along the ray through `e₀` it equals `t ^ μ`, and `t ^ μ ≤ C t ^ α` fails for small
`t > 0`. -/
theorem not_holderOnWith_meyersSolution {α : ℝ≥0} (hα : μ < α) (C : ℝ≥0)
    {s : Set (EuclideanSpace ℝ (Fin (n + 2)))} (hs : s ∈ 𝓝 0) :
    ¬ HolderOnWith C α (meyersSolution μ) s := by
  intro h
  have hray : Filter.Tendsto (fun t : ℝ => t • EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using ((Filter.tendsto_id (x := 𝓝[>] (0 : ℝ))).mono_right nhdsWithin_le_nhds).smul_const
      (EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ))
  have hsmall : Filter.Tendsto (fun t : ℝ => (C : ℝ) * t ^ ((α : ℝ) - μ)) (𝓝[>] 0) (𝓝 0) := by
    simpa [Real.zero_rpow (sub_pos.2 hα).ne'] using
      (((continuous_id.rpow_const fun _ => Or.inr (sub_pos.2 hα).le).tendsto (0 : ℝ)).mono_left
        nhdsWithin_le_nhds).const_mul (C : ℝ)
  obtain ⟨t, ht, hts, htC⟩ := (eventually_mem_nhdsWithin.and ((hray.eventually_mem hs).and
    (hsmall.eventually (gt_mem_nhds one_pos)))).exists
  have ht0 : (0 : ℝ) < t := ht
  have hd := h.dist_le hts (mem_of_mem_nhds hs)
  rw [meyersSolution_smul_single_zero ht0, meyersSolution_zero, dist_zero_right, dist_zero_right,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht0 _), norm_smul, PiLp.norm_single,
    norm_one, mul_one, Real.norm_of_nonneg ht0.le] at hd
  -- `t ^ μ ≤ C t ^ α = (C t ^ (α - μ)) t ^ μ < t ^ μ`.
  have : (C : ℝ) * t ^ (α : ℝ) = (C * t ^ ((α : ℝ) - μ)) * t ^ μ := by
    rw [mul_assoc, ← Real.rpow_add ht0, sub_add_cancel]
  rw [this] at hd
  nlinarith [Real.rpow_pos_of_pos ht0 μ]

/-- **The gradient of Meyers' solution is not `p`-integrable near the origin for large `p`.** For
`μ > 0`, if the gradient of `‖x‖ ^ (μ - 1) x₀` is `p`-integrable on a neighbourhood of the origin
of `ℝ^{n+2}`, then `p (1 - μ) < n + 2`. For finite `p` and `μ < 1` this says
`p < (n + 2) / (1 - μ)`: near the origin the gradient is bounded below by `μ ‖x‖ ^ (μ - 1)`. For
`p = ∞` the conclusion is trivial, since `p.toReal = 0`. -/
theorem toReal_mul_one_sub_lt_of_memLp_gradient_meyersSolution (hμ0 : 0 < μ) {p : ℝ≥0∞}
    {s : Set (EuclideanSpace ℝ (Fin (n + 2)))} (hs : s ∈ 𝓝 0)
    (hmem : MemLp (∇ (meyersSolution μ)) p (volume.restrict s)) :
    p.toReal * (1 - μ) < n + 2 := by
  rcases le_or_gt 1 μ with hμ1 | hμ1
  · nlinarith [ENNReal.toReal_nonneg (a := p)]
  rcases (ENNReal.toReal_nonneg (a := p)).eq_or_lt with hpr | hpr
  · rw [← hpr, zero_mul]
    positivity
  obtain ⟨hp0, hp⟩ := ENNReal.toReal_pos_iff.1 hpr
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hs
  have hint : IntegrableOn (fun x => ‖∇ (meyersSolution μ) x‖ ^ p.toReal) (ball 0 r) :=
    (hmem.integrable_norm_rpow hp0.ne' hp.ne).mono_measure (Measure.restrict_mono hball le_rfl)
  -- `‖x‖ ^ (p (μ - 1)) ≤ μ ^ (-p) ‖∇u‖ ^ p` away from the origin.
  have hpow : IntegrableOn (fun x : EuclideanSpace ℝ (Fin (n + 2)) => ‖x‖ ^ (p.toReal * (μ - 1)))
      (ball 0 r) := by
    refine (hint.const_mul (μ ^ (-p.toReal))).mono'
      (by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin (n + 2)) =>
        ‖x‖ ^ (p.toReal * (μ - 1))).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.2
      (measure_singleton (0 : EuclideanSpace ℝ (Fin (n + 2)))))] with x hx
    rw [Real.norm_of_nonneg (by positivity), mul_comm p.toReal,
      Real.rpow_mul (norm_nonneg x), Real.rpow_neg hμ0.le, le_inv_mul_iff₀ (by positivity),
      ← Real.mul_rpow hμ0.le (by positivity)]
    exact Real.rpow_le_rpow (by positivity)
      (mul_rpow_le_norm_gradient_meyersSolution hμ0 hμ1.le hx) hpr.le
  have := (integrableOn_norm_rpow_ball_iff hr).1 hpow
  rw [finrank_euclideanSpace_fin] at this
  push_cast at this
  nlinarith

/-- On a bounded open set, the gradient of Meyers' solution is `p`-integrable when
`p (1 - μ) < n + 2`: it is bounded by `(1 + |μ - 1|) ‖x‖ ^ (μ - 1)`. -/
private theorem memLp_radialCoordGradient {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) {Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 2)))))
    (h : p.toReal * (1 - μ) < n + 2) :
    MemLp (radialCoordGradient μ 0) p
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))) := by
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hGm := (measurable_radialCoordGradient (μ := μ) 0).aestronglyMeasurable
    (μ := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2)))))
  obtain ⟨R, hR⟩ := hb.subset_ball (0 : EuclideanSpace ℝ (Fin (n + 2)))
  refine (integrable_norm_rpow_iff hGm hp0 hp).1 ?_
  have hker : IntegrableOn (fun x : EuclideanSpace ℝ (Fin (n + 2)) => ‖x‖ ^ (p.toReal * (μ - 1)))
      (Ω : Set (EuclideanSpace ℝ (Fin (n + 2)))) :=
    IntegrableOn.mono_set
      (integrableOn_norm_rpow_ball (by rw [finrank_euclideanSpace_fin]; push_cast; nlinarith)) hR
  refine (hker.const_mul ((1 + |μ - 1|) ^ p.toReal)).mono'
    ((measurable_radialCoordGradient 0).norm.pow_const _).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.2
    (measure_singleton (0 : EuclideanSpace ℝ (Fin (n + 2)))))] with x hx
  rw [Real.norm_of_nonneg (by positivity), mul_comm p.toReal, Real.rpow_mul (norm_nonneg x),
    ← Real.mul_rpow (by positivity) (by positivity)]
  exact Real.rpow_le_rpow (norm_nonneg _) (norm_radialCoordGradient_le 0 hx) hpr.le

/-- On a bounded open set, Meyers' solution is bounded, hence `p`-integrable. -/
private theorem memLp_meyersSolution (hμ0 : 0 < μ) {p : ℝ≥0∞}
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))) :
    MemLp (meyersSolution μ) p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))) := by
  obtain ⟨R, hR⟩ := hb.subset_ball (0 : EuclideanSpace ℝ (Fin (n + 2)))
  have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  refine MemLp.of_bound (continuous_radialCoord hμ0 0).aestronglyMeasurable (R ^ μ) ?_
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  rw [Real.norm_eq_abs, meyersSolution_eq_radialCoord]
  refine (abs_radialCoord_le 0 x).trans (Real.rpow_le_rpow (norm_nonneg x) ?_ hμ0.le)
  exact (mem_ball_zero_iff.1 (hR hx)).le

/-- **Sobolev integrability of Meyers' solution.** Let `0 < μ`, `1 ≤ p < ∞`, and let
`Ω ⊆ ℝ^{n+2}` be a bounded open set. If `p (1 - μ) < n + 2`, in particular for every `p` if
`μ ≥ 1`, then `‖x‖ ^ (μ - 1) x₀` lies in `W^{1,p}(Ω)`: its gradient is bounded by a multiple of
`‖x‖ ^ (μ - 1)`, which is `p`-integrable near the origin of `ℝ^{n+2}` in this range. -/
theorem exists_w1p_value_ae_eq_meyersSolution (hμ0 : 0 < μ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) {Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 2)))))
    (h : p.toReal * (1 - μ) < n + 2) :
    ∃ u : W1p volume Ω p,
      W1p.value u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))]
        meyersSolution μ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hu := memLp_meyersSolution (p := p) hμ0 hb
  have hg := memLp_radialCoordGradient hp0 hp hb h
  refine ⟨W1p.mk hu.toLp hg.toLp
    (((hasWeakFDerivOn_radialCoord hμ0 0 Ω).congr_ae hu.coeFn_toLp.symm).congr_ae_deriv
      (hg.coeFn_toLp.mono fun x hx => by simp only [hx])), ?_⟩
  rw [W1p.value_mk]
  exact hu.coeFn_toLp

/-- **Sobolev integrability of Meyers' solution near the origin.** Let `0 < μ`, `1 ≤ p < ∞`, and
let `Ω ⊆ ℝ^{n+2}` be a bounded open set containing the origin. Then `‖x‖ ^ (μ - 1) x₀` lies in
`W^{1,p}(Ω)` exactly when `p (1 - μ) < n + 2`, that is `p < (n + 2) / (1 - μ)` for `μ < 1`, and
always for `μ ≥ 1`. Its gradient has size comparable to `‖x‖ ^ (μ - 1)`, which is `p`-integrable
near the origin of `ℝ^{n+2}` exactly in this range. -/
theorem exists_w1p_value_ae_eq_meyersSolution_iff (hμ0 : 0 < μ) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 2)))))
    (h0 : (0 : EuclideanSpace ℝ (Fin (n + 2))) ∈ Ω) :
    (∃ u : W1p volume Ω p,
      W1p.value u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))] meyersSolution μ) ↔
      p.toReal * (1 - μ) < n + 2 := by
  refine ⟨fun ⟨u, hu⟩ => ?_, exists_w1p_value_ae_eq_meyersSolution hμ0 hp hb⟩
  exact toReal_mul_one_sub_lt_of_memLp_gradient_meyersSolution hμ0 (Ω.isOpen.mem_nhds h0)
    ((Lp.memLp (W1p.gradient u)).ae_eq (gradient_ae_eq_gradient_meyersSolution hμ0 u hu))

/-- **Meyers' example: no higher integrability exponent works for all coefficients.** For every
`p > n + 2` there is `0 < μ < 1` with the following property. For the coefficient
`a = TauCeti.PDE.meyersCoefficient μ` on `ℝ^{n+2}`, uniformly elliptic with constants
`μ (μ + n) / (n + 1)` and `1` (`TauCeti.PDE.uniformlyEllipticOn_meyersCoefficient`), and every
bounded open `Ω ⊆ ℝ^{n+2}` containing the origin, the function `‖x‖ ^ (μ - 1) x₀` lies in `H¹(Ω)`
and is a weak solution of `div(a ∇u) = 0` there, but does not lie in `W^{1,p}(Ω)`. So in the plane,
where the range is `p > 2`, the exponent in Meyers' higher integrability theorem for measurable
coefficients cannot be chosen independently of the ellipticity ratio. -/
theorem exists_meyersSolution_not_exists_w1p {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : (n + 2 : ℝ≥0∞) < p) :
    ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ ∀ {Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))},
      Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 2)))) →
      (0 : EuclideanSpace ℝ (Fin (n + 2))) ∈ Ω →
      ∃ u : W1p volume Ω 2,
        W1p.value u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))]
          meyersSolution μ ∧
        (∀ v : W1p0 volume Ω 2,
          energyFormH1 (meyersCoefficient μ) 0 0 u (v : W1p volume Ω 2) = 0) ∧
        ¬ ∃ w : W1p volume Ω p,
          W1p.value w =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))]
            meyersSolution μ := by
  -- Compare with a finite exponent `n + 2 < q ≤ p` and choose `μ` with `q (1 - μ) = n + 2`.
  set q : ℝ≥0∞ := min p (n + 3)
  have hq2 : (n + 2 : ℝ≥0∞) < q :=
    lt_min hp (ENNReal.add_lt_add_left (ENNReal.natCast_ne_top n) (by norm_num))
  have hqp : q ≤ p := min_le_left p _
  have hq : q ≠ ∞ := ((min_le_right p _).trans_lt (by simp [ENNReal.add_lt_top])).ne
  have : Fact (1 ≤ q) := ⟨((by norm_num : (1 : ℝ≥0∞) ≤ 2).trans le_add_self).trans hq2.le⟩
  have hqr : (n + 2 : ℝ) < q.toReal := by
    have := (ENNReal.toReal_lt_toReal (by simp [ENNReal.add_eq_top]) hq).2 hq2
    simpa [ENNReal.toReal_add] using this
  have hn2 : (0 : ℝ) < n + 2 := by positivity
  have hμ0 : 0 < 1 - (n + 2) / q.toReal := by
    rw [sub_pos, div_lt_one (by linarith)]
    exact hqr
  refine ⟨1 - (n + 2) / q.toReal, hμ0, by rw [sub_lt_self_iff]; exact div_pos hn2 (by linarith),
    fun {Ω} hb h0 => ?_⟩
  obtain ⟨u, hu⟩ := exists_w1p_value_ae_eq_meyersSolution hμ0 (p := 2) (by norm_num) hb (by
    rw [ENNReal.toReal_ofNat, sub_sub_cancel, mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith)
  have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  refine ⟨u, hu, energyFormH1_meyersCoefficient_eq_zero hμ0 u hu, ?_⟩
  rintro ⟨w, hw⟩
  have := (exists_w1p_value_ae_eq_meyersSolution_iff hμ0 hq hb h0).1
    ⟨W1p.ofExponentLE hqp w, (W1p.coeFn_value_ofExponentLE hqp w).eventuallyEq.trans hw⟩
  rw [sub_sub_cancel, mul_div_cancel₀ _ (by linarith)] at this
  exact lt_irrefl _ this

end PDE

end TauCeti
