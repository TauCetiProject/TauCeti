/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Probability.Distributions.Gaussian.Fernique
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.Probability.Distributions.Gaussian.Stein

/-!
# The James–Stein estimator

For `X ~ N(θ, I)` on `ℝ^p` with `p ≥ 3`, the James–Stein estimator
`δ(X) = (1 - (p - 2) / ‖X‖²) X` has squared-error risk

`E‖δ(X) - θ‖² = p - (p - 2)² E‖X‖⁻²`,

which is strictly less than the risk `p` of `X` itself, at every `θ`. So `X` is inadmissible
for the mean of a Gaussian vector in dimension at least `3`.

The proof applies Stein's identity (`TauCeti.Probability.gaussian_integration_by_parts`) to the
bounded fields `x ↦ (‖x‖² + ε)⁻¹ x`, which gives the risk of `x - c (‖x‖² + ε)⁻¹ x` for every
`ε > 0`, and lets `ε → 0` by dominated convergence. The dominating function is integrable
because `‖x‖⁻²` is (`TauCeti.Probability.integrable_inv_norm_sq_multivariateGaussian`).

## Main results

* `TauCeti.james_stein_risk_eq_and_lt`: the risk of the James–Stein estimator, and its strict
  domination of `X`.

## References

* M. J. Schervish, *Theory of Statistics*, Springer, 1995, Theorem 3.50, p. 163, and (3.54),
  pp. 164–165.
* W. James and C. Stein, *Estimation with quadratic loss*, Proc. Fourth Berkeley Symp. Math.
  Statist. Probab. 1 (1961), 361–379.

The proofs are adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>), file
`CKSD/Inference/Gaussian.lean`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TauCeti.Probability
open scoped Topology

namespace TauCeti

variable {p : ℕ}

/-- The regularized shrinkage field `y ↦ (‖y‖² + ε)⁻¹ y`, `ε > 0`, is differentiable, and its
diagonal partial derivatives are `∂ᵢ gᵢ(x) = (‖x‖² + ε)⁻¹ - 2 xᵢ² / (‖x‖² + ε)²`. -/
private theorem differentiable_and_fderiv_inv_norm_sq_add_smul {ε : ℝ} (hε : 0 < ε) :
    Differentiable ℝ (fun y : EuclideanSpace ℝ (Fin p) ↦ (‖y‖ ^ 2 + ε)⁻¹ • y) ∧
      ∀ (i : Fin p) (x : EuclideanSpace ℝ (Fin p)),
        fderiv ℝ (fun y : EuclideanSpace ℝ (Fin p) ↦ (‖y‖ ^ 2 + ε)⁻¹ • y) x
          (EuclideanSpace.single i 1) i =
          (‖x‖ ^ 2 + ε)⁻¹ - 2 * x i ^ 2 / (‖x‖ ^ 2 + ε) ^ 2 := by
  have hgd (x : EuclideanSpace ℝ (Fin p)) :
      HasFDerivAt (fun y : EuclideanSpace ℝ (Fin p) ↦ (‖y‖ ^ 2 + ε)⁻¹ • y)
        ((‖x‖ ^ 2 + ε)⁻¹ • ContinuousLinearMap.id ℝ _ + ((-((‖x‖ ^ 2 + ε) ^ 2)⁻¹) •
          (2 • (innerSL ℝ x).comp (ContinuousLinearMap.id ℝ _))).smulRight x) x :=
    ((hasDerivAt_inv (by positivity)).comp_hasFDerivAt x
      (((hasFDerivAt_id x).norm_sq).add_const ε)).smul (hasFDerivAt_id x)
  refine ⟨fun x ↦ (hgd x).differentiableAt, fun i x ↦ ?_⟩
  rw [(hgd x).fderiv]
  simp [EuclideanSpace.inner_single_right]
  ring

/-- The diagonal partial derivatives of the regularized shrinkage field are bounded by `3 / ε`. -/
private theorem abs_inv_norm_sq_add_sub_le {ε : ℝ} (hε : 0 < ε) (x : EuclideanSpace ℝ (Fin p))
    (i : Fin p) : |(‖x‖ ^ 2 + ε)⁻¹ - 2 * x i ^ 2 / (‖x‖ ^ 2 + ε) ^ 2| ≤ 3 / ε := by
  have h1 : x i ^ 2 ≤ ‖x‖ ^ 2 := by
    simpa using pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le x i) 2
  have ha : (‖x‖ ^ 2 + ε)⁻¹ ≤ 1 / ε := by
    rw [one_div]
    exact inv_anti₀ hε (by nlinarith [sq_nonneg ‖x‖])
  have hb : 2 * x i ^ 2 / (‖x‖ ^ 2 + ε) ^ 2 ≤ 2 / ε := by
    rw [div_le_div_iff₀ (by positivity) hε]
    nlinarith [sq_nonneg (x i), sq_nonneg ‖x‖]
  have hb0 : 0 ≤ 2 * x i ^ 2 / (‖x‖ ^ 2 + ε) ^ 2 := by positivity
  have ha0 : 0 ≤ (‖x‖ ^ 2 + ε)⁻¹ := by positivity
  have h3 : 3 / ε = 1 / ε + 2 / ε := by ring
  rw [abs_le, h3]
  constructor <;> linarith

/-- The regularized shrinkage field `y ↦ (‖y‖² + ε)⁻¹ y`, `ε > 0`, is in `L²` of `N(θ, I)`. -/
private theorem memLp_inv_norm_sq_add_smul (θ : EuclideanSpace ℝ (Fin p)) {ε : ℝ} (hε : 0 < ε) :
    MemLp (fun y : EuclideanSpace ℝ (Fin p) ↦ (‖y‖ ^ 2 + ε)⁻¹ • y) 2
      (multivariateGaussian θ 1) := by
  refine MemLp.of_le ((IsGaussian.memLp_two_id (μ := multivariateGaussian θ 1)).const_smul ε⁻¹)
    (by fun_prop) (ae_of_all _ fun x ↦ ?_)
  have hpos : 0 < ‖x‖ ^ 2 + ε := by positivity
  simp only [norm_smul, Pi.smul_apply, id, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos),
    abs_of_pos (inv_pos.2 hε)]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hε (by linarith [sq_nonneg ‖x‖])) (norm_nonneg _)

/-- The squared norm of the regularized shrinkage field:
`‖(‖x‖² + e)⁻¹ x‖² = ‖x‖² / (‖x‖² + e)²`. -/
private theorem norm_inv_norm_sq_add_smul_sq (x : EuclideanSpace ℝ (Fin p)) (e : ℝ) :
    ‖(‖x‖ ^ 2 + e)⁻¹ • x‖ ^ 2 = ‖x‖ ^ 2 / (‖x‖ ^ 2 + e) ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, div_eq_mul_inv, mul_comm]

/-- The bound `‖x‖² / (‖x‖² + ε)² ≤ ‖x‖⁻²` for `x ≠ 0` and `ε ≥ 0`. -/
private theorem norm_sq_div_norm_sq_add_sq_le {x : EuclideanSpace ℝ (Fin p)} (hx : x ≠ 0)
    {e : ℝ} (he : 0 ≤ e) : ‖x‖ ^ 2 / (‖x‖ ^ 2 + e) ^ 2 ≤ (‖x‖ ^ 2)⁻¹ := by
  have hx2 : 0 < ‖x‖ ^ 2 := by positivity
  rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hx2]
  nlinarith

/-- Stein's identity for the regularized shrinkage field `g(x) = (‖x‖² + ε)⁻¹ x` under
`N(θ, I)`: `E⟪X - θ, g X⟫ = E[p (‖X‖² + ε)⁻¹ - 2 ‖X‖² / (‖X‖² + ε)²]`. -/
private theorem integral_inner_sub_inv_norm_sq_add_smul (θ : EuclideanSpace ℝ (Fin p)) {ε : ℝ}
    (hε : 0 < ε) :
    ∫ x, inner ℝ (x - θ) ((‖x‖ ^ 2 + ε)⁻¹ • x) ∂multivariateGaussian θ 1 =
      ∫ x, ((p : ℝ) * (‖x‖ ^ 2 + ε)⁻¹ - 2 * ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε) ^ 2)
        ∂multivariateGaussian θ 1 := by
  set P := multivariateGaussian θ (1 : Matrix (Fin p) (Fin p) ℝ)
  have hP : multivariateGaussian θ ((1 : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ)) = P := by
    rw [one_smul]
  set g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) := fun y ↦ (‖y‖ ^ 2 + ε)⁻¹ • y
  obtain ⟨hgd, hfd⟩ := differentiable_and_fderiv_inv_norm_sq_add_smul (p := p) hε
  have hgL2 : MemLp g 2 P := memLp_inv_norm_sq_add_smul θ hε
  have hdint (i : Fin p) : Integrable (fun x : EuclideanSpace ℝ (Fin p) ↦
      (‖x‖ ^ 2 + ε)⁻¹ - 2 * x i ^ 2 / (‖x‖ ^ 2 + ε) ^ 2) P := by
    refine Integrable.of_bound (by fun_prop) (3 / ε) (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs]
    exact abs_inv_norm_sq_add_sub_le hε x i
  have hstein (i : Fin p) := gaussian_integration_by_parts zero_le_one hgd (hP ▸ hgL2) i
    (by simp_rw [hP, hfd]; exact hdint i)
  simp only [one_mul, hfd, hP] at hstein
  have hxi (i : Fin p) : MemLp (fun x : EuclideanSpace ℝ (Fin p) ↦ x i - θ i) 2 P :=
    (IsGaussian.memLp_dual P (EuclideanSpace.proj i) 2 (by simp)).sub (memLp_const _)
  have hgi (i : Fin p) : MemLp (fun x ↦ g x i) 2 P :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hgL2
  have hrhs (x : EuclideanSpace ℝ (Fin p)) :
      (p : ℝ) * (‖x‖ ^ 2 + ε)⁻¹ - 2 * ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε) ^ 2 =
        ∑ i, ((‖x‖ ^ 2 + ε)⁻¹ - 2 * x i ^ 2 / (‖x‖ ^ 2 + ε) ^ 2) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum,
      ← EuclideanSpace.real_norm_sq_eq]
    simp
  have hlhs (x : EuclideanSpace ℝ (Fin p)) :
      inner ℝ (x - θ) ((‖x‖ ^ 2 + ε)⁻¹ • x) = ∑ i, (x i - θ i) * g x i := by
    simp [g, PiLp.inner_apply, mul_comm]
  simp_rw [hlhs, hrhs]
  rw [integral_finsetSum (f := fun i x ↦ (x i - θ i) * g x i) _
      fun i _ ↦ (hxi i).integrable_mul (hgi i),
    integral_finsetSum _ fun i _ ↦ hdint i]
  exact Finset.sum_congr rfl fun i _ ↦ hstein i

/-- The risk of the regularized James–Stein rule `x - c (‖x‖² + ε)⁻¹ x` under `N(θ, I)`. -/
private theorem integral_norm_sub_sub_smul_inv_norm_sq_add_smul_sq
    (θ : EuclideanSpace ℝ (Fin p)) {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    ∫ x, ‖x - θ - c • ((‖x‖ ^ 2 + ε)⁻¹ • x)‖ ^ 2 ∂multivariateGaussian θ 1 =
      p - 2 * c * ∫ x, ((p : ℝ) * (‖x‖ ^ 2 + ε)⁻¹ - 2 * ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε) ^ 2)
        ∂multivariateGaussian θ 1 +
      c ^ 2 * ∫ x, ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε) ^ 2 ∂multivariateGaussian θ 1 := by
  set P := multivariateGaussian θ (1 : Matrix (Fin p) (Fin p) ℝ)
  have hsub : MemLp (fun x : EuclideanSpace ℝ (Fin p) ↦ x - θ) 2 P :=
    (IsGaussian.memLp_two_id (μ := P)).sub (memLp_const _)
  have hgL2 := memLp_inv_norm_sq_add_smul θ hε
  have hqint : Integrable (fun x : EuclideanSpace ℝ (Fin p) ↦ ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε) ^ 2) P := by
    simpa only [norm_inv_norm_sq_add_smul_sq] using hgL2.integrable_norm_pow (by norm_num)
  have hinner : Integrable (fun x : EuclideanSpace ℝ (Fin p) ↦
      inner ℝ (x - θ) ((‖x‖ ^ 2 + ε)⁻¹ • x)) P :=
    hsub.integrable_inner hgL2
  have hexp (x : EuclideanSpace ℝ (Fin p)) : ‖x - θ - c • ((‖x‖ ^ 2 + ε)⁻¹ • x)‖ ^ 2 =
      ‖x - θ‖ ^ 2 - 2 * c * inner ℝ (x - θ) ((‖x‖ ^ 2 + ε)⁻¹ • x) +
        c ^ 2 * (‖x‖ ^ 2 / (‖x‖ ^ 2 + ε) ^ 2) := by
    rw [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      norm_inv_norm_sq_add_smul_sq, inner_smul_right]
    ring
  have hsq : Integrable (fun x : EuclideanSpace ℝ (Fin p) ↦ ‖x - θ‖ ^ 2) P :=
    hsub.integrable_norm_pow (by norm_num)
  have h1 : Integrable (fun x : EuclideanSpace ℝ (Fin p) ↦
      ‖x - θ‖ ^ 2 - 2 * c * inner ℝ (x - θ) ((‖x‖ ^ 2 + ε)⁻¹ • x)) P :=
    hsq.sub (hinner.const_mul _)
  simp_rw [hexp]
  rw [integral_add h1 (hqint.const_mul _),
    integral_sub hsq (hinner.const_mul _), integral_const_mul, integral_const_mul,
    integral_norm_sub_sq_multivariateGaussian Matrix.PosSemidef.one,
    integral_inner_sub_inv_norm_sq_add_smul θ hε, Matrix.trace_one, Fintype.card_fin]

/-- Under `N(θ, I)` in positive dimension, almost every point is nonzero. -/
private theorem ae_ne_zero_multivariateGaussian_one [NeZero p] (θ : EuclideanSpace ℝ (Fin p)) :
    ∀ᵐ x ∂multivariateGaussian θ (1 : Matrix (Fin p) (Fin p) ℝ), x ≠ 0 := by
  have hac : multivariateGaussian θ (1 : Matrix (Fin p) (Fin p) ℝ) ≪ volume := by
    rw [multivariateGaussian_eq_withDensity Matrix.PosDef.one θ]
    exact withDensity_absolutelyContinuous _ _
  exact hac (by simp)

variable {ε : ℕ → ℝ}

/-- The regularized weights `(‖x‖² + εₙ)⁻¹` increase to `‖x‖⁻²` at every `x ≠ 0`. -/
private theorem tendsto_inv_norm_sq_add (hεlim : Tendsto ε atTop (𝓝 0))
    {x : EuclideanSpace ℝ (Fin p)} (hx : x ≠ 0) :
    Tendsto (fun n ↦ (‖x‖ ^ 2 + ε n)⁻¹) atTop (𝓝 (‖x‖ ^ 2)⁻¹) := by
  have h := (tendsto_const_nhds (x := ‖x‖ ^ 2)).add hεlim
  rw [add_zero] at h
  exact h.inv₀ (by positivity)

/-- The risks of the regularized rules `x - c (‖x‖² + εₙ)⁻¹ x` converge to the risk of the
rule `(1 - c / ‖x‖²) x` as `εₙ → 0`, in dimension at least `3`. -/
private theorem tendsto_integral_norm_sub_sub_smul_inv_norm_sq_add_smul_sq (hp : 3 ≤ p)
    (θ : EuclideanSpace ℝ (Fin p)) (c : ℝ) (hε0 : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, ‖x - θ - c • ((‖x‖ ^ 2 + ε n)⁻¹ • x)‖ ^ 2
        ∂multivariateGaussian θ 1) atTop
      (𝓝 (∫ x, ‖(1 - c / ‖x‖ ^ 2) • x - θ‖ ^ 2 ∂multivariateGaussian θ 1)) := by
  have : NeZero p := ⟨by omega⟩
  set P := multivariateGaussian θ (1 : Matrix (Fin p) (Fin p) ℝ)
  have hJi : Integrable (fun x : EuclideanSpace ℝ (Fin p) ↦ (‖x‖ ^ 2)⁻¹)
      (multivariateGaussian θ 1) := by
    simpa using integrable_inv_norm_sq_multivariateGaussian (by simpa using hp) 1 θ
  have hsq : Integrable (fun x : EuclideanSpace ℝ (Fin p) ↦ ‖x - θ‖ ^ 2) P :=
    ((IsGaussian.memLp_two_id (μ := P)).sub (memLp_const θ)).integrable_norm_pow (by norm_num)
  refine tendsto_integral_of_dominated_convergence
    (fun x ↦ 2 * ‖x - θ‖ ^ 2 + 2 * c ^ 2 * (‖x‖ ^ 2)⁻¹)
    (fun n ↦ Measurable.aestronglyMeasurable (by fun_prop))
    ((hsq.const_mul 2).add (hJi.const_mul _)) (fun n ↦ ?_) ?_
  · filter_upwards [ae_ne_zero_multivariateGaussian_one θ] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hg : ‖c • ((‖x‖ ^ 2 + ε n)⁻¹ • x)‖ ^ 2 ≤ c ^ 2 * (‖x‖ ^ 2)⁻¹ := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_inv_norm_sq_add_smul_sq]
      exact mul_le_mul_of_nonneg_left (norm_sq_div_norm_sq_add_sq_le hx (hε0 n).le) (sq_nonneg _)
    have h1 := TauCeti.norm_sub_sq_le_two_mul (x - θ) (c • ((‖x‖ ^ 2 + ε n)⁻¹ • x)) 0
    simp only [sub_zero] at h1
    linarith
  · filter_upwards [ae_ne_zero_multivariateGaussian_one θ] with x hx
    have hδ : (1 - c / ‖x‖ ^ 2) • x - θ = x - θ - c • ((‖x‖ ^ 2)⁻¹ • x) := by
      rw [sub_smul, one_smul, div_eq_mul_inv, mul_smul]
      abel
    rw [hδ]
    exact ((continuous_norm.tendsto _).comp ((tendsto_const_nhds (x := x - θ)).sub
      (((tendsto_inv_norm_sq_add hεlim hx).smul_const x).const_smul c))).pow 2

/-- `‖x‖² / (‖x‖² + εₙ)² → ‖x‖⁻²` at every `x ≠ 0`. -/
private theorem tendsto_norm_sq_div_norm_sq_add_sq (hεlim : Tendsto ε atTop (𝓝 0))
    {x : EuclideanSpace ℝ (Fin p)} (hx : x ≠ 0) :
    Tendsto (fun n ↦ ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε n) ^ 2) atTop (𝓝 (‖x‖ ^ 2)⁻¹) := by
  simp_rw [div_eq_mul_inv, ← inv_pow]
  convert ((tendsto_inv_norm_sq_add hεlim hx).pow 2).const_mul (‖x‖ ^ 2) using 2
  field_simp

/-- The two regularized integrals in the risk converge, to `E‖X‖⁻²` and `(p - 2) E‖X‖⁻²`. -/
private theorem tendsto_integrals_inv_norm_sq_add (hp : 3 ≤ p) (θ : EuclideanSpace ℝ (Fin p))
    (hε0 : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε n) ^ 2 ∂multivariateGaussian θ 1) atTop
        (𝓝 (∫ x, (‖x‖ ^ 2)⁻¹ ∂multivariateGaussian θ 1)) ∧
      Tendsto (fun n ↦ ∫ x, ((p : ℝ) * (‖x‖ ^ 2 + ε n)⁻¹ - 2 * ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε n) ^ 2)
        ∂multivariateGaussian θ 1) atTop
        (𝓝 (((p : ℝ) - 2) * ∫ x, (‖x‖ ^ 2)⁻¹ ∂multivariateGaussian θ 1)) := by
  have : NeZero p := ⟨by omega⟩
  have hJi : Integrable (fun x : EuclideanSpace ℝ (Fin p) ↦ (‖x‖ ^ 2)⁻¹)
      (multivariateGaussian θ 1) := by
    simpa using integrable_inv_norm_sq_multivariateGaussian (by simpa using hp) 1 θ
  have hne := ae_ne_zero_multivariateGaussian_one θ
  -- The quadratic weight `‖x‖² / (‖x‖² + ε)²` and the inverse weight `(‖x‖² + ε)⁻¹` are both
  -- dominated by `(‖x‖²)⁻¹`, and converge to it pointwise off the origin.
  have hB_le (n : ℕ) : ∀ᵐ x ∂multivariateGaussian θ 1,
      ‖‖x‖ ^ 2 / (‖x‖ ^ 2 + ε n) ^ 2‖ ≤ (‖x‖ ^ 2)⁻¹ := by
    filter_upwards [hne] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    exact norm_sq_div_norm_sq_add_sq_le hx (hε0 n).le
  have hA_le (n : ℕ) : ∀ᵐ x ∂multivariateGaussian θ 1, ‖(‖x‖ ^ 2 + ε n)⁻¹‖ ≤ (‖x‖ ^ 2)⁻¹ := by
    filter_upwards [hne] with x hx
    rw [Real.norm_of_nonneg (inv_nonneg.2 (by linarith [hε0 n, sq_nonneg ‖x‖]))]
    exact inv_anti₀ (pow_pos (norm_pos_iff.2 hx) 2) (by linarith [hε0 n])
  have hBm (n : ℕ) : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin p) ↦
      ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε n) ^ 2) (multivariateGaussian θ 1) :=
    Measurable.aestronglyMeasurable (by fun_prop)
  have hAm (n : ℕ) : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin p) ↦
      (‖x‖ ^ 2 + ε n)⁻¹) (multivariateGaussian θ 1) :=
    Measurable.aestronglyMeasurable (by fun_prop)
  have hB := tendsto_integral_of_dominated_convergence _ hBm hJi hB_le
    (by filter_upwards [hne] with x hx using tendsto_norm_sq_div_norm_sq_add_sq hεlim hx)
  have hA := tendsto_integral_of_dominated_convergence _ hAm hJi hA_le
    (by filter_upwards [hne] with x hx using tendsto_inv_norm_sq_add hεlim hx)
  refine ⟨hB, ?_⟩
  have heq (n : ℕ) : ∫ x, ((p : ℝ) * (‖x‖ ^ 2 + ε n)⁻¹ - 2 * ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε n) ^ 2)
        ∂multivariateGaussian θ 1 =
      (p : ℝ) * ∫ x, (‖x‖ ^ 2 + ε n)⁻¹ ∂multivariateGaussian θ 1 -
        2 * ∫ x, ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε n) ^ 2 ∂multivariateGaussian θ 1 := by
    simp_rw [mul_div_assoc]
    rw [integral_sub (((hJi.mono' (hAm n) (hA_le n))).const_mul _)
        ((hJi.mono' (hBm n) (hB_le n)).const_mul _), integral_const_mul, integral_const_mul]
  simp_rw [heq, sub_mul]
  exact (hA.const_mul _).sub (hB.const_mul 2)

/-- **The James–Stein estimator.** For `X ~ N(θ, I)` on `ℝ^p` with `p ≥ 3`, the estimator
`(1 - (p - 2) / ‖X‖²) X` has risk `p - (p - 2)² E‖X‖⁻²`, which is strictly less than the risk
`p` of `X`. -/
theorem james_stein_risk_eq_and_lt (hp : 3 ≤ p) (θ : EuclideanSpace ℝ (Fin p)) :
    ∫ x, ‖(1 - ((p : ℝ) - 2) / ‖x‖ ^ 2) • x - θ‖ ^ 2 ∂multivariateGaussian θ 1 =
        p - ((p : ℝ) - 2) ^ 2 * ∫ x, (‖x‖ ^ 2)⁻¹ ∂multivariateGaussian θ 1 ∧
      ∫ x, ‖(1 - ((p : ℝ) - 2) / ‖x‖ ^ 2) • x - θ‖ ^ 2 ∂multivariateGaussian θ 1 < p := by
  have : NeZero p := ⟨by omega⟩
  set c : ℝ := (p : ℝ) - 2
  set J := ∫ x, (‖x‖ ^ 2)⁻¹ ∂multivariateGaussian θ (1 : Matrix (Fin p) (Fin p) ℝ)
  set ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hε0 (n : ℕ) : 0 < ε n := by positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨hB, hA⟩ := tendsto_integrals_inv_norm_sq_add hp θ hε0 hεlim
  have hlim := (tendsto_const_nhds (x := (p : ℝ))).sub (hA.const_mul (2 * c)) |>.add
    (hB.const_mul (c ^ 2))
  simp_rw [← integral_norm_sub_sub_smul_inv_norm_sq_add_smul_sq θ (hε0 _)] at hlim
  have heq := tendsto_nhds_unique
    (tendsto_integral_norm_sub_sub_smul_inv_norm_sq_add_smul_sq hp θ c hε0 hεlim) hlim
  have hJpos : 0 < J := by
    have hJi : Integrable (fun x : EuclideanSpace ℝ (Fin p) ↦ (‖x‖ ^ 2)⁻¹)
        (multivariateGaussian θ 1) := by
      simpa using integrable_inv_norm_sq_multivariateGaussian (by simpa using hp) 1 θ
    have hsupp : Function.support (fun x : EuclideanSpace ℝ (Fin p) ↦ (‖x‖ ^ 2)⁻¹) =
        {x | x ≠ 0} := by
      ext x
      simp
    rw [integral_pos_iff_support_of_nonneg (fun _ ↦ by positivity) hJi, hsupp,
      (ae_iff_prob_eq_one (by fun_prop)).1 (ae_ne_zero_multivariateGaussian_one θ)]
    exact one_pos
  have hc1 : 1 ≤ c := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  refine ⟨by rw [heq]; ring, ?_⟩
  rw [heq]
  nlinarith [mul_pos (by nlinarith : 0 < c ^ 2) hJpos]

end TauCeti
