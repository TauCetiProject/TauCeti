/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Pseudodifferential.Adjoint.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic

/-!
# The asymptotic expansion of the adjoint symbol

Let `a` be a symbol of order `m` with values in operators between complex Hilbert spaces `V` and
`W`, vanishing for positions outside a compact set. Its adjoint symbol `a*`
(`TauCeti.Symbol.adjoint`), whose quantization is the formal adjoint of the quantization of `a`,
has the asymptotic expansion

`a* ∼ ∑_α (1 / α!) ∂_ξ^α D_x^α a†`, with `D_x = -i ∂_x`,

where `a†(x, ξ) = a(x, ξ)†` is the pointwise Hilbert space adjoint: after removing the terms with
`|α| < N`, the remainder is a symbol of order `m - N`. This file proves this, with an actual
remainder symbol, which moreover satisfies its estimates uniformly in the position.

Summing over words `w = [j₁, …, j_k]` of coordinate indices instead of multi-indices absorbs the
multinomial coefficients, so the term of order `m - k` is

`TauCeti.Symbol.adjointTerm a k = ((-i)^k / k!) ∑_{|w| = k} (∂_ξ^w ∂_x^w a)†`

(`TauCeti.Symbol.coefficient_adjointTerm`). It is defined for arbitrary symbols `a` by the
recursion `adjointTerm a (k + 1) = (-i / (k + 1)) ∑ⱼ adjointTerm (∂_{xⱼ} ∂_{ξⱼ} a) k`, starting
from the pointwise adjoint `adjointTerm a 0 = a†`, and it commutes with position and frequency
derivatives.

## Main results

* `TauCeti.Symbol.adjointTerm`: the terms of the expansion, with their closed form
  `TauCeti.Symbol.coefficient_adjointTerm` and the commutation rules
  `TauCeti.Symbol.spatialDeriv_adjointTerm` and
  `TauCeti.Symbol.coefficient_frequencyDeriv_adjointTerm`.
* `TauCeti.Symbol.adjointRemainder a ha N`: the remainder `a* - ∑_{k < N} adjointTerm a k`, a
  symbol of order `m - N`, satisfying its estimates uniformly in the position
  (`TauCeti.Symbol.isUniform_adjointRemainder`).
* `TauCeti.Symbol.adjoint_eq_sum_adjointTerm_add_adjointRemainder`: **the adjoint expansion**
  `a* = ∑_{k < N} adjointTerm a k + adjointRemainder a ha N`, for every `N`.
* `TauCeti.Symbol.adjoint_eq_map_add_adjointRemainder_one`: in particular `a*` agrees with the
  pointwise adjoint `a†` up to a symbol of order `m - 1`.

## Proof outline

Interpolate between the pointwise adjoint and the adjoint symbol by the family

`a*_t(y, ξ) = (∫ exp(2πi ⟪θ, y⟫) â(θ, ξ - 2π t θ) dθ)†`, `t ∈ [0, 1]`,

where `â(θ, ξ)` is the Fourier transform of the position slice `x ↦ a(x, ξ)`, so that
`a*_1 = a*`, and `a*_0 = a†` by Fourier inversion. Differentiating under the integral sign, and
using `-2π θⱼ (∂_{ξⱼ} a)^ = i (∂_{xⱼ} ∂_{ξⱼ} a)^`, the integral inside the adjoint has derivative
`i ∑ⱼ` the integrals of `∂_{xⱼ} ∂_{ξⱼ} a`. Since the adjoint is conjugate-linear,
`d/dt a*_t = -i ∑ⱼ (∂_{xⱼ} ∂_{ξⱼ} a)*_t`. The recursion defining `adjointTerm` is the matching
identity for the polynomial `∑_{k < N} t^k adjointTerm a k`, so the derivative of the remainder
`a*_t - ∑_{k < N + 1} t^k adjointTerm a k` is `-i` times the sum over `j` of the remainders with
`N` terms of `∂_{xⱼ} ∂_{ξⱼ} a`, and this remainder vanishes at `t = 0`. By induction on `N` and
the mean value inequality on `[0, 1]`, the remainder is bounded by `C ⟨ξ⟩ ^ (m - N)`, uniformly
in the position: each step lowers the order by one. The base case is the bound
`‖a*_t‖ ≤ C ⟨ξ⟩ ^ m`, uniform for `|t| ≤ 2`, from the decay of `â(θ, ξ - sθ)` for bounded shift
scales `s` (`TauCeti.Symbol.HasCompactSpatialSupport.exists_norm_fourier_slice_sub_smul_le`).

Since both the adjoint symbol and the terms `adjointTerm` commute with position and frequency
derivatives, so does the remainder, and the derivative estimates follow from the bound applied to
the derivatives of `a`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.7.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.3).
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Finset
open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-! ### The integral inside the interpolating family -/

section Scaled

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {a : Symbol n V W m}

variable (a) in
/-- The integral `∫ exp(2πi ⟪θ, y⟫) â(θ, ξ - 2π t θ) dθ`, whose adjoint interpolates between the
pointwise adjoint `a(y, ξ)†` (`t = 0`) and the adjoint symbol (`t = 1`). -/
private def scaledLeft (t : ℝ) (y ξ : CoordinateSpace n) : V →L[ℂ] W :=
  ∫ θ, (𝐞 ⟪θ, y⟫ : ℂ) • 𝓕 (fun x ↦ a.coefficient (x, ξ - (t * (2 * π)) • θ)) θ

private theorem HasCompactSpatialSupport.continuous_scaledLeft_integrand
    (ha : a.HasCompactSpatialSupport) (s : ℝ) (y ξ : CoordinateSpace n) :
    Continuous fun θ : CoordinateSpace n ↦
      (𝐞 ⟪θ, y⟫ : ℂ) • 𝓕 (fun x ↦ a.coefficient (x, ξ - s • θ)) θ :=
  (by fun_prop : Continuous fun θ : CoordinateSpace n ↦ (𝐞 ⟪θ, y⟫ : ℂ)).smul
    (ha.continuous_fourier_slice.comp
      (continuous_id.prodMk (continuous_const.sub (continuous_id.const_smul s))) :)

private theorem HasCompactSpatialSupport.integrable_scaledLeft_integrand
    (ha : a.HasCompactSpatialSupport) (s : ℝ) (y ξ : CoordinateSpace n) :
    Integrable fun θ : CoordinateSpace n ↦
      (𝐞 ⟪θ, y⟫ : ℂ) • 𝓕 (fun x ↦ a.coefficient (x, ξ - s • θ)) θ := by
  obtain ⟨C, -, hC⟩ := ha.exists_norm_fourier_slice_sub_smul_le |s|
  refine ((integrable_one_add_norm_rpow_neg_succ.mul_const ((1 + ‖ξ‖ ^ 2) ^ (m / 2))).const_mul
    C).mono' (ha.continuous_scaledLeft_integrand s y ξ).aestronglyMeasurable
      (.of_forall fun θ ↦ ?_)
  rw [norm_smul, Circle.norm_coe, one_mul]
  exact hC s le_rfl θ ξ

/-- `‖∫ exp(2πi ⟪θ, y⟫) â(θ, ξ - 2π t θ) dθ‖ ≤ C ⟨ξ⟩ ^ m`, uniformly for `|t| ≤ 2` and all
positions. -/
private theorem HasCompactSpatialSupport.exists_norm_scaledLeft_le
    (ha : a.HasCompactSpatialSupport) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ 2 → ∀ y ξ,
      ‖scaledLeft a t y ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_fourier_slice_sub_smul_le (2 * (2 * π))
  set I := ∫ θ : CoordinateSpace n, (1 + ‖θ‖) ^ (-((n : ℝ) + 1))
  have hI : 0 ≤ I := integral_nonneg fun θ ↦ by positivity
  refine ⟨C * I, mul_nonneg hC0 hI, fun t ht y ξ ↦ ?_⟩
  refine (norm_integral_le_of_norm_le ((integrable_one_add_norm_rpow_neg_succ.mul_const
    ((1 + ‖ξ‖ ^ 2) ^ (m / 2))).const_mul C) (.of_forall fun θ ↦ ?_)).trans_eq ?_
  · rw [norm_smul, Circle.norm_coe, one_mul]
    exact hC _ (by rw [abs_mul, abs_of_pos Real.two_pi_pos]; gcongr) θ ξ
  · rw [integral_const_mul, integral_mul_const]
    ring

/-- At `t = 0` the integral is `a(y, ξ)`, by Fourier inversion. -/
private theorem HasCompactSpatialSupport.scaledLeft_zero [CompleteSpace W]
    (ha : a.HasCompactSpatialSupport) (y ξ : CoordinateSpace n) :
    scaledLeft a 0 y ξ = a.coefficient (y, ξ) := by
  have h := congrFun (ha.fourierInv_fourier_slice ξ) y
  rw [Real.fourierInv_eq] at h
  simpa [scaledLeft, Circle.smul_def] using h

/-- **Differentiation in the parameter** of the shifted Fourier slice: since
`2π θⱼ b̂ = -i (∂_{xⱼ} b)^`, `d/dt â(θ, ξ - 2π t θ) = i ∑ⱼ (∂_{xⱼ} ∂_{ξⱼ} a)^(θ, ξ - 2π t θ)`. -/
private theorem HasCompactSpatialSupport.hasDerivAt_fourier_slice_sub_smul
    (ha : a.HasCompactSpatialSupport) (t : ℝ) (θ ξ : CoordinateSpace n) :
    HasDerivAt (fun t : ℝ ↦ 𝓕 (fun x ↦ a.coefficient (x, ξ - (t * (2 * π)) • θ)) θ)
      (Complex.I • ∑ j, 𝓕 (fun x ↦ (Symbol.spatialDeriv j (Symbol.frequencyDeriv j a)).coefficient
        (x, ξ - (t * (2 * π)) • θ)) θ) t := by
  set ζ := ξ - (t * (2 * π)) • θ
  set g : CoordinateSpace n → V →L[ℂ] W := fun η ↦ 𝓕 (fun x ↦ a.coefficient (x, η)) θ
  have hg : HasFDerivAt g (fderiv ℝ g ζ) ζ :=
    (ha.hasFDerivAt_fourier_slice θ ζ).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ ↦ ξ - (t * (2 * π)) • θ) (-((2 * π) • θ)) t := by
    simpa using (((hasDerivAt_id t).mul_const (2 * π)).smul_const θ).const_sub ξ
  refine (hg.comp_hasDerivAt t hl).congr_deriv ?_
  rw [ContinuousLinearMap.apply_eq_sum_single, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hgj : fderiv ℝ g ζ (EuclideanSpace.single j 1) =
      𝓕 (fun x ↦ (Symbol.frequencyDeriv j a).coefficient (x, ζ)) θ := by
    rw [← ha.coordinateDeriv_fourier_slice j θ ζ, coordinateDeriv_cons, coordinateDeriv_nil]
  rw [hgj, (ha.frequencyDeriv j).fourier_spatialDeriv_slice j θ ζ,
    EuclideanSpace.inner_single_right, one_mul, conj_trivial, smul_smul, ← Complex.coe_smul]
  congr 1
  simp only [PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
  push_cast
  linear_combination (-(2 * ↑π * ↑(θ.ofLp j)) : ℂ) * Complex.I_sq

/-- **Differentiation in the parameter** under the integral sign:
`d/dt ∫ exp(2πi ⟪θ, y⟫) â(θ, ξ - 2π t θ) dθ` is `i ∑ⱼ` the corresponding integrals for
`∂_{xⱼ} ∂_{ξⱼ} a`. -/
private theorem HasCompactSpatialSupport.hasDerivAt_scaledLeft (ha : a.HasCompactSpatialSupport)
    {t₀ : ℝ} (ht₀ : |t₀| ≤ 1) (y ξ : CoordinateSpace n) :
    HasDerivAt (fun t ↦ scaledLeft a t y ξ)
      (Complex.I • ∑ j,
        scaledLeft (Symbol.spatialDeriv j (Symbol.frequencyDeriv j a)) t₀ y ξ) t₀ := by
  -- Differentiate under the integral sign, dominating the derivatives of the integrands for
  -- `t` within distance one of `t₀` by the decay of the shifted Fourier slices of the symbols
  -- `∂_{xⱼ} ∂_{ξⱼ} a`.
  have hd (j : Fin n) := (ha.frequencyDeriv j).spatialDeriv j
  choose C hC0 hC using fun j ↦ (hd j).exists_norm_fourier_slice_sub_smul_le (2 * (2 * π))
  have hball : ∀ t ∈ Metric.ball t₀ 1, |t * (2 * π)| ≤ 2 * (2 * π) := fun t ht ↦ by
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have := abs_sub_abs_le_abs_sub t t₀
    rw [abs_mul, abs_of_pos Real.two_pi_pos]
    gcongr
    linarith
  set F' : ℝ → CoordinateSpace n → V →L[ℂ] W := fun t θ ↦ Complex.I • ∑ j,
    (𝐞 ⟪θ, y⟫ : ℂ) • 𝓕 (fun x ↦ (Symbol.spatialDeriv j (Symbol.frequencyDeriv j a)).coefficient
      (x, ξ - (t * (2 * π)) • θ)) θ
  set bound : CoordinateSpace n → ℝ := fun θ ↦
    (∑ j, C j * (1 + ‖ξ‖ ^ 2) ^ ((m - 1) / 2)) * (1 + ‖θ‖) ^ (-((n : ℝ) + 1))
  have hint (j : Fin n) := (hd j).integrable_scaledLeft_integrand (t₀ * (2 * π)) y ξ
  have hmeas : ∀ᶠ t in nhds t₀, AEStronglyMeasurable (fun θ : CoordinateSpace n ↦
      (𝐞 ⟪θ, y⟫ : ℂ) • 𝓕 (fun x ↦ a.coefficient (x, ξ - (t * (2 * π)) • θ)) θ) volume :=
    .of_forall fun t ↦ (ha.continuous_scaledLeft_integrand _ y ξ).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable (F' t₀) volume :=
    ((continuous_finsetSum _ fun j _ ↦ (hd j).continuous_scaledLeft_integrand _ y ξ).const_smul
      Complex.I).aestronglyMeasurable
  have hbound : ∀ᵐ θ ∂(volume : Measure (CoordinateSpace n)), ∀ t ∈ Metric.ball t₀ 1,
      ‖F' t θ‖ ≤ bound θ := .of_forall fun θ t ht ↦ by
    simp only [F', bound, Finset.sum_mul]
    rw [norm_smul, Complex.norm_I, one_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    rw [norm_smul, Circle.norm_coe, one_mul]
    exact (hC j _ (hball t ht) θ ξ).trans_eq (by ring)
  have hdiff : ∀ᵐ θ ∂(volume : Measure (CoordinateSpace n)), ∀ t ∈ Metric.ball t₀ 1,
      HasDerivAt (fun t ↦ (𝐞 ⟪θ, y⟫ : ℂ) •
        𝓕 (fun x ↦ a.coefficient (x, ξ - (t * (2 * π)) • θ)) θ) (F' t θ) t :=
    .of_forall fun θ t _ ↦ by
      refine ((ha.hasDerivAt_fourier_slice_sub_smul t θ ξ).const_smul
        (𝐞 ⟪θ, y⟫ : ℂ)).congr_deriv ?_
      simp only [F', Finset.smul_sum, smul_comm (𝐞 ⟪θ, y⟫ : ℂ) Complex.I]
  obtain ⟨-, h⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds t₀ one_pos) hmeas (ha.integrable_scaledLeft_integrand _ y ξ) hF'meas
    hbound (integrable_one_add_norm_rpow_neg_succ.const_mul _) hdiff
  refine h.congr_deriv ?_
  simp only [F']
  rw [integral_smul, integral_finsetSum _ fun j _ ↦ hint j]
  simp only [scaledLeft]

end Scaled

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

open ContinuousLinearMap (adjointRealCLM adjointRealCLM_apply)

/-! ### The terms of the expansion -/

section Term

/-- The term of order `m - k` in the asymptotic expansion of the adjoint symbol `a*`:
`((-i)^k / k!) ∑_{|w| = k} (∂_ξ^w ∂_x^w a)†`, the sum running over the words `w` of coordinate
indices of length `k` (`coefficient_adjointTerm`). It is defined by the recursion
`adjointTerm a (k + 1) = (-i / (k + 1)) ∑ⱼ adjointTerm (∂_{xⱼ} ∂_{ξⱼ} a) k`, starting from the
pointwise adjoint `adjointTerm a 0 = a†`. -/
def adjointTerm : {m : ℝ} → Symbol n V W m → (k : ℕ) → Symbol n W V (m - k)
  | _, a, 0 => inclusion (by simp) (a.map adjointRealCLM)
  | _, a, k + 1 => inclusion (by push_cast; linarith)
      ((-Complex.I / (k + 1)) • ∑ j, adjointTerm (spatialDeriv j (frequencyDeriv j a)) k)

theorem adjointTerm_zero (a : Symbol n V W m) :
    a.adjointTerm 0 = inclusion (by simp) (a.map adjointRealCLM) := by
  rw [adjointTerm]

theorem adjointTerm_succ (a : Symbol n V W m) (k : ℕ) :
    a.adjointTerm (k + 1) = inclusion (by push_cast; linarith)
      ((-Complex.I / (k + 1)) • ∑ j, (spatialDeriv j (frequencyDeriv j a)).adjointTerm k) := by
  rw [adjointTerm]

@[simp]
theorem coefficient_adjointTerm_zero (a : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (a.adjointTerm 0).coefficient p = ContinuousLinearMap.adjoint (a.coefficient p) := by
  rw [adjointTerm_zero, coefficient_inclusion, coefficient_map, adjointRealCLM_apply]

theorem coefficient_adjointTerm_succ (a : Symbol n V W m) (k : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (a.adjointTerm (k + 1)).coefficient p = (-Complex.I / (k + 1)) •
      ∑ j, ((spatialDeriv j (frequencyDeriv j a)).adjointTerm k).coefficient p := by
  simp [adjointTerm_succ]

/-- **The terms of the adjoint expansion** are `((-i)^k / k!) ∑_{|w| = k} (∂_ξ^w ∂_x^w a)†`, the
sum running over the words `w` of coordinate indices of length `k`. Grouping the words by the
multi-index they determine gives the familiar form `∑_{|α| = k} (1 / α!) ∂_ξ^α D_x^α a†` with
`D_x = -i ∂_x`. -/
theorem coefficient_adjointTerm (a : Symbol n V W m) (k : ℕ) (x ξ : CoordinateSpace n) :
    (a.adjointTerm k).coefficient (x, ξ) = ((-Complex.I) ^ k / k.factorial) •
      ∑ w : Fin k → Fin n, ContinuousLinearMap.adjoint
        (mixedDeriv (List.ofFn w) (List.ofFn w) a.coefficient x ξ) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [coefficient_adjointTerm_succ, ← (Fin.snocEquiv fun _ ↦ Fin n).sum_comp,
      Fintype.sum_prod_type]
    simp only [ih, mixedDeriv_frequencyDeriv, mixedDeriv_spatialDeriv, Finset.smul_sum, smul_smul,
      Fin.snocEquiv_apply, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last,
      List.concat_eq_append]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun w _ ↦ ?_
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- Position derivatives commute with the terms of the adjoint expansion. -/
@[simp]
theorem spatialDeriv_adjointTerm (l : Fin n) (a : Symbol n V W m) (k : ℕ) :
    spatialDeriv l (a.adjointTerm k) = (spatialDeriv l a).adjointTerm k := by
  induction k generalizing m with
  | zero => simp [adjointTerm_zero, spatialDeriv_inclusion]
  | succ k ih =>
    rw [adjointTerm_succ, adjointTerm_succ, spatialDeriv_inclusion, map_smul, map_sum]
    refine congrArg (inclusion _) (congrArg (_ • ·) (Finset.sum_congr rfl fun j _ ↦ ?_))
    rw [ih, spatialDeriv_comm, spatialDeriv_frequencyDeriv_comm l j]

/-- Frequency derivatives commute with the terms of the adjoint expansion. The orders of the two
sides differ by their bookkeeping, so the rule is stated for their coefficients. -/
theorem coefficient_frequencyDeriv_adjointTerm (l : Fin n) (a : Symbol n V W m) (k : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (frequencyDeriv l (a.adjointTerm k)).coefficient p =
      ((frequencyDeriv l a).adjointTerm k).coefficient p := by
  induction k generalizing m with
  | zero => simp [adjointTerm_zero, frequencyDeriv_inclusion]
  | succ k ih =>
    simp only [adjointTerm_succ, frequencyDeriv_inclusion, map_smul, map_sum,
      coefficient_inclusion, coefficient_smul, coefficient_sum, Pi.smul_apply, Finset.sum_apply]
    refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
    rw [ih, ← spatialDeriv_frequencyDeriv_comm, frequencyDeriv_comm]

end Term

/-! ### The remainder of the expansion along the interpolating family -/

section Remainder

variable {a : Symbol n V W m}

variable (a) in
/-- The family `a*_t(y, ξ) = (∫ exp(2πi ⟪θ, y⟫) â(θ, ξ - 2π t θ) dθ)†` interpolating between the
pointwise adjoint (`t = 0`) and the adjoint symbol (`t = 1`). -/
private def scaledAdjoint (t : ℝ) (y ξ : CoordinateSpace n) : W →L[ℂ] V :=
  ContinuousLinearMap.adjoint (scaledLeft a t y ξ)

/-- At `t = 1` the family is the adjoint symbol. -/
private theorem coefficient_adjoint_eq_scaledAdjoint_one (ha : a.HasCompactSpatialSupport)
    (y ξ : CoordinateSpace n) :
    (adjoint a ha).coefficient (y, ξ) = scaledAdjoint a 1 y ξ := by
  simp only [coefficient_adjoint, scaledAdjoint, scaledLeft, one_mul]

/-- The derivative `d/dt a*_t = -i ∑ⱼ (∂_{xⱼ} ∂_{ξⱼ} a)*_t`: the adjoint is conjugate-linear. -/
private theorem HasCompactSpatialSupport.hasDerivAt_scaledAdjoint
    (ha : a.HasCompactSpatialSupport) {t₀ : ℝ} (ht₀ : |t₀| ≤ 1) (y ξ : CoordinateSpace n) :
    HasDerivAt (fun t ↦ scaledAdjoint a t y ξ)
      ((-Complex.I) • ∑ j,
        scaledAdjoint (Symbol.spatialDeriv j (Symbol.frequencyDeriv j a)) t₀ y ξ) t₀ := by
  have h := adjointRealCLM.hasFDerivAt.comp_hasDerivAt t₀ (ha.hasDerivAt_scaledLeft ht₀ y ξ)
  simp only [Function.comp_def, adjointRealCLM_apply] at h
  refine h.congr_deriv ?_
  rw [LinearIsometryEquiv.map_smulₛₗ, Complex.conj_I, map_sum]
  simp only [scaledAdjoint]

variable (a) in
/-- The remainder `a*_t - ∑_{k < N} t^k adjointTerm a k` of the expansion along the
interpolating family. -/
private def remainderAt (N : ℕ) (t : ℝ) (y ξ : CoordinateSpace n) : W →L[ℂ] V :=
  scaledAdjoint a t y ξ - ∑ k ∈ range N, t ^ k • (a.adjointTerm k).coefficient (y, ξ)

/-- The derivative of the polynomial part `∑_{k < N + 1} t^k adjointTerm a k` is given by the
recursion defining `adjointTerm`. -/
private theorem hasDerivAt_sum_pow_smul_adjointTerm (N : ℕ) (a : Symbol n V W m)
    (y ξ : CoordinateSpace n) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ ∑ k ∈ range (N + 1), t ^ k • (a.adjointTerm k).coefficient (y, ξ))
      (∑ k ∈ range N, t ^ k • ((-Complex.I) •
        ∑ j, ((spatialDeriv j (frequencyDeriv j a)).adjointTerm k).coefficient (y, ξ))) t := by
  have h := HasDerivAt.fun_sum (u := range (N + 1)) fun k _ ↦
    (hasDerivAt_pow k t).smul_const ((a.adjointTerm k).coefficient (y, ξ))
  refine h.congr_deriv ?_
  rw [Finset.sum_range_succ']
  simp only [CharP.cast_eq_zero, zero_mul, zero_smul, add_zero]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [coefficient_adjointTerm_succ, Nat.add_sub_cancel, mul_comm, mul_smul]
  congr 1
  rw [← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  field_simp

/-- The derivative in `t` of the remainder with `N + 1` terms is `-i ∑ⱼ` the remainders with `N`
terms of `∂_{xⱼ} ∂_{ξⱼ} a`. -/
private theorem HasCompactSpatialSupport.hasDerivAt_remainderAt (ha : a.HasCompactSpatialSupport)
    (N : ℕ) {t : ℝ} (ht : |t| ≤ 1) (y ξ : CoordinateSpace n) :
    HasDerivAt (fun t ↦ remainderAt a (N + 1) t y ξ)
      ((-Complex.I) • ∑ j,
        remainderAt (Symbol.spatialDeriv j (Symbol.frequencyDeriv j a)) N t y ξ) t := by
  refine ((ha.hasDerivAt_scaledAdjoint ht y ξ).fun_sub
    (hasDerivAt_sum_pow_smul_adjointTerm N a y ξ t)).congr_deriv ?_
  simp only [remainderAt, smul_sub, Finset.smul_sum, Finset.sum_sub_distrib, smul_comm (t ^ _)]
  rw [Finset.sum_comm]

/-- The remainder vanishes at `t = 0`, by Fourier inversion. -/
private theorem HasCompactSpatialSupport.remainderAt_zero (ha : a.HasCompactSpatialSupport)
    (N : ℕ) (y ξ : CoordinateSpace n) : remainderAt a (N + 1) 0 y ξ = 0 := by
  rw [remainderAt, scaledAdjoint, ha.scaledLeft_zero, Finset.sum_range_succ']
  simp

/-- **The remainder estimate.** `‖a*_t - ∑_{k < N} t^k adjointTerm a k‖ ≤ C ⟨ξ⟩ ^ (m - N)`,
uniformly for `t ∈ [0, 1]` and all positions. -/
private theorem exists_norm_remainderAt_le (N : ℕ) :
    ∀ {m : ℝ} {a : Symbol n V W m}, a.HasCompactSpatialSupport → ∃ C, 0 ≤ C ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ξ,
        ‖remainderAt a N t y ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - N) / 2) := by
  induction N with
  | zero =>
    intro m a ha
    obtain ⟨C, hC0, hC⟩ := ha.exists_norm_scaledLeft_le
    refine ⟨C, hC0, fun t ht y ξ ↦ ?_⟩
    have ht2 : |t| ≤ 2 := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa [remainderAt, scaledAdjoint] using hC t ht2 y ξ
  | succ N ih =>
    intro m a ha
    choose C hC0 hC using fun j : Fin n ↦ ih ((ha.frequencyDeriv j).spatialDeriv j)
    refine ⟨∑ j, C j, Finset.sum_nonneg fun j _ ↦ hC0 j, fun t ht y ξ ↦ ?_⟩
    have hw : (1 + ‖ξ‖ ^ 2) ^ ((m - 1 - N) / 2) =
        (1 + ‖ξ‖ ^ 2) ^ ((m - ((N + 1 : ℕ) : ℝ)) / 2) := by
      congr 1
      push_cast
      ring
    have hbound : ∀ s ∈ Set.Ico (0 : ℝ) 1,
        ‖(-Complex.I) • ∑ j, remainderAt (spatialDeriv j (frequencyDeriv j a)) N s y ξ‖ ≤
          (∑ j, C j) * (1 + ‖ξ‖ ^ 2) ^ ((m - ((N + 1 : ℕ) : ℝ)) / 2) := by
      intro s hs
      rw [norm_smul, norm_neg, Complex.norm_I, one_mul, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
      rw [← hw]
      exact hC j s (Set.Ico_subset_Icc_self hs) y ξ
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s hs ↦ (ha.hasDerivAt_remainderAt N (abs_le.2 ⟨by linarith [hs.1], hs.2⟩) y
        ξ).hasDerivWithinAt) hbound t ht
    rw [ha.remainderAt_zero, sub_zero, sub_zero] at hmv
    have hB : 0 ≤ (∑ j, C j) * (1 + ‖ξ‖ ^ 2) ^ ((m - ((N + 1 : ℕ) : ℝ)) / 2) :=
      mul_nonneg (Finset.sum_nonneg fun j _ ↦ hC0 j) (by positivity)
    exact hmv.trans (mul_le_of_le_one_right hB ht.2)

end Remainder

/-! ### The remainder symbol -/

section RemainderSymbol

variable {a : Symbol n V W m}

variable (a) in
/-- The remainder `a* - ∑_{k < N} adjointTerm a k`, as a symbol of order `m`. -/
private def remainderSymbol (ha : a.HasCompactSpatialSupport) (N : ℕ) : Symbol n W V m :=
  adjoint a ha - ∑ k ∈ range N, inclusion (sub_le_self _ (Nat.cast_nonneg k)) (a.adjointTerm k)

private theorem coefficient_remainderSymbol (ha : a.HasCompactSpatialSupport) (N : ℕ)
    (y ξ : CoordinateSpace n) :
    (remainderSymbol a ha N).coefficient (y, ξ) = remainderAt a N 1 y ξ := by
  simp [remainderSymbol, remainderAt, coefficient_adjoint_eq_scaledAdjoint_one ha]

private theorem spatialDeriv_remainderSymbol (ha : a.HasCompactSpatialSupport) (N : ℕ)
    (j : Fin n) :
    spatialDeriv j (remainderSymbol a ha N) =
      remainderSymbol (spatialDeriv j a) (ha.spatialDeriv j) N := by
  simp only [remainderSymbol, map_sub, map_sum, spatialDeriv_adjoint, spatialDeriv_inclusion,
    spatialDeriv_adjointTerm]

private theorem coefficient_frequencyDeriv_remainderSymbol (ha : a.HasCompactSpatialSupport)
    (N : ℕ) (j : Fin n) :
    (frequencyDeriv j (remainderSymbol a ha N)).coefficient =
      (remainderSymbol (frequencyDeriv j a) (ha.frequencyDeriv j) N).coefficient := by
  funext p
  simp only [remainderSymbol, map_sub, map_sum, coefficient_sub, coefficient_sum,
    frequencyDeriv_inclusion, coefficient_inclusion, Pi.sub_apply, Finset.sum_apply,
    frequencyDeriv_adjoint, coefficient_frequencyDeriv_adjointTerm]

/-- The symbol estimates of order `m - N` for the remainder, uniformly in the position: the
remainder commutes with position and frequency derivatives, and a frequency derivative lowers the
order of `a` by one. -/
private theorem exists_bound_remainderSymbol (N : ℕ) (α β : List (Fin n)) :
    ∀ {m : ℝ} {a : Symbol n V W m} (ha : a.HasCompactSpatialSupport), ∃ C, 0 ≤ C ∧ ∀ y ξ,
      ‖mixedDeriv α β (remainderSymbol a ha N).coefficient y ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - N - β.length) / 2) := by
  obtain ⟨D, hD⟩ : ∃ D, α.length + β.length = D := ⟨_, rfl⟩
  induction D generalizing α β with
  | zero =>
    obtain ⟨rfl, rfl⟩ : α = [] ∧ β = [] := by
      simpa [List.length_eq_zero_iff] using hD
    intro m a ha
    obtain ⟨C, hC0, hC⟩ := exists_norm_remainderAt_le N ha
    refine ⟨C, hC0, fun y ξ ↦ ?_⟩
    simpa [coefficient_remainderSymbol] using hC 1 ⟨zero_le_one, le_rfl⟩ y ξ
  | succ D ih =>
    intro m a ha
    rcases List.eq_nil_or_concat' β with rfl | ⟨β', j, rfl⟩
    · rcases List.eq_nil_or_concat' α with rfl | ⟨α', j, rfl⟩
      · simp at hD
      · obtain ⟨C, hC0, hC⟩ := ih α' [] (by simpa using hD) (ha.spatialDeriv j)
        refine ⟨C, hC0, fun y ξ ↦ ?_⟩
        rw [← mixedDeriv_spatialDeriv, spatialDeriv_remainderSymbol]
        exact hC y ξ
    · obtain ⟨C, hC0, hC⟩ := ih α β' (by simp at hD; omega) (ha.frequencyDeriv j)
      refine ⟨C, hC0, fun y ξ ↦ ?_⟩
      rw [← mixedDeriv_frequencyDeriv, coefficient_frequencyDeriv_remainderSymbol]
      refine (hC y ξ).trans_eq ?_
      congr 2
      simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      ring

end RemainderSymbol

/-! ### The adjoint expansion -/

section Expansion

variable {a : Symbol n V W m}

variable (a) in
/-- The remainder `a* - ∑_{k < N} adjointTerm a k` of the adjoint expansion after `N` terms, a
symbol of order `m - N` (`adjoint_eq_sum_adjointTerm_add_adjointRemainder`), satisfying its
estimates uniformly in the position (`isUniform_adjointRemainder`). -/
def adjointRemainder (ha : a.HasCompactSpatialSupport) (N : ℕ) : Symbol n W V (m - N) where
  coefficient := (remainderSymbol a ha N).coefficient
  contDiff_coefficient := (remainderSymbol a ha N).contDiff_coefficient
  exists_bound _ _ α β := (exists_bound_remainderSymbol N α β ha).imp
    fun _ hC ↦ ⟨hC.1, fun y _ ξ ↦ hC.2 y ξ⟩

@[simp]
theorem coefficient_adjointRemainder (ha : a.HasCompactSpatialSupport) (N : ℕ) :
    (adjointRemainder a ha N).coefficient =
      (adjoint a ha).coefficient - ∑ k ∈ range N, (a.adjointTerm k).coefficient := by
  simp [adjointRemainder, remainderSymbol]

/-- The remainder of the adjoint expansion satisfies its estimates of order `m - N` uniformly in
the position. -/
theorem isUniform_adjointRemainder (ha : a.HasCompactSpatialSupport) (N : ℕ) :
    (adjointRemainder a ha N).IsUniform :=
  isUniform_iff.2 fun α β ↦ exists_bound_remainderSymbol N α β ha

/-- **The asymptotic expansion of the adjoint symbol.** For every `N`,
`a* = ∑_{k < N} adjointTerm a k + adjointRemainder a ha N`, where `adjointTerm a k` is the term
`((-i)^k / k!) ∑_{|w| = k} (∂_ξ^w ∂_x^w a)†` of order `m - k` and the remainder is a symbol of
order `m - N`. -/
theorem adjoint_eq_sum_adjointTerm_add_adjointRemainder (ha : a.HasCompactSpatialSupport)
    (N : ℕ) :
    adjoint a ha = ∑ k ∈ range N, inclusion (sub_le_self _ (Nat.cast_nonneg k)) (a.adjointTerm k) +
      inclusion (sub_le_self _ (Nat.cast_nonneg N)) (adjointRemainder a ha N) := by
  ext1
  simp

/-- The adjoint symbol `a*` is the pointwise adjoint `a†` up to a symbol of order `m - 1`. -/
theorem adjoint_eq_map_add_adjointRemainder_one (ha : a.HasCompactSpatialSupport) :
    adjoint a ha = a.map adjointRealCLM + inclusion (by simp) (adjointRemainder a ha 1) := by
  ext1
  funext p
  simp

end Expansion

end Symbol

end TauCeti
