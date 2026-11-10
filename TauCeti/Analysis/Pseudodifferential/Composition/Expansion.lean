/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Fourier.Inversion

/-!
# The asymptotic expansion of the composition symbol

Let `a` be a symbol of order `m'` with values in `W →L[ℂ] U` and `b` a symbol of order `m` with
values in `V →L[ℂ] W` that vanishes for positions outside a compact set. Their composition symbol
`a # b` (`TauCeti.Symbol.sharp`), whose quantization is `Op(a) ∘ Op(b)`, has the asymptotic
expansion

`a # b ∼ ∑_α (1 / α!) ∂_ξ^α a · D_x^α b`, with `D_x = -i ∂_x`,

meaning that after removing the terms with `|α| < N` the remainder is a symbol of order
`m' + m - N`. This file proves this, with an actual remainder symbol.

Summing over words `w = [j₁, …, j_k]` of coordinate indices instead of multi-indices absorbs the
multinomial coefficients, so the term of order `m' + m - k` is

`TauCeti.Symbol.sharpTerm a b k = ((-i)^k / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b`

(`TauCeti.Symbol.coefficient_sharpTerm`). It is defined for arbitrary symbols `a`, `b` by the
recursion `sharpTerm a b (k + 1) = (-i / (k + 1)) ∑ⱼ sharpTerm (∂_{ξⱼ} a) (∂_{xⱼ} b) k`, starting
from the pointwise composition `sharpTerm a b 0 = a ∘ b`, and it satisfies the Leibniz rules in
the position and the frequency.

## Main results

* `TauCeti.Symbol.sharpTerm`: the terms of the expansion, with their closed form
  `TauCeti.Symbol.coefficient_sharpTerm` and the Leibniz rules
  `TauCeti.Symbol.spatialDeriv_sharpTerm` and `TauCeti.Symbol.coefficient_frequencyDeriv_sharpTerm`.
* `TauCeti.Symbol.sharpRemainder a b hb N`: the remainder `a # b - ∑_{k < N} sharpTerm a b k`, a
  symbol of order `m' + m - N`.
* `TauCeti.Symbol.sharp_eq_sum_sharpTerm_add_sharpRemainder`: **the composition expansion**
  `a # b = ∑_{k < N} sharpTerm a b k + sharpRemainder a b hb N`, for every `N`.
* `TauCeti.Symbol.sharp_eq_comp_add_sharpRemainder_one`: in particular `a # b` agrees with the
  pointwise composition `a ∘ b` up to a symbol of order `m' + m - 1`.

The intermediate spaces `W` and `U` are complete; otherwise the Bochner integral defining `a # b`
vanishes identically and no expansion can hold.

## Proof outline

Interpolate between the pointwise composition and the composition symbol by the family

`(a #_t b)(x, ξ) = ∫ exp(2πi ⟪η, x⟫) a(x, ξ + 2π t η) ∘ b̂(η, ξ) dη`, `t ∈ [0, 1]`,

so that `a #_1 b = a # b`, and `a #_0 b = a ∘ b` by Fourier inversion. Differentiating under the
integral sign, and using `2π ηⱼ b̂ = -i (∂_{xⱼ} b)^`,
`d/dt (a #_t b) = -i ∑ⱼ (∂_{ξⱼ} a) #_t (∂_{xⱼ} b)`. The recursion defining `sharpTerm` is the
matching identity for the polynomial `∑_{k < N} t^k sharpTerm a b k`. So the derivative of the
remainder `a #_t b - ∑_{k < N + 1} t^k sharpTerm a b k` is `-i` times the sum over `j` of the
remainders with `N` terms of `(∂_{ξⱼ} a, ∂_{xⱼ} b)`, and this remainder vanishes at `t = 0`.
By induction on `N` and the mean value inequality on `[0, 1]`, the remainder is bounded by
`C ⟨ξ⟩ ^ (m' + m - N)`, locally uniformly in the position: each step lowers the order of `a` by
one. The base case is the bound `‖a #_t b‖ ≤ C ⟨ξ⟩ ^ (m' + m)`, uniform for `|t| ≤ 2` by
Peetre's inequality and the rapid decay of `b̂`
(`TauCeti.Symbol.HasCompactSpatialSupport.exists_norm_comp_fourier_slice_le`).

The derivative estimates follow from the Leibniz rules, which hold for `a # b` and for each
`sharpTerm`: a position or frequency derivative of the remainder is the sum of the remainders
with the derivative on `a` or on `b`, and a frequency derivative lowers the order of one factor.
An induction on the number of derivatives then gives every symbol estimate of order
`m' + m - N`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.8.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (2.5)–(2.7).
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Finset
open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' : ℝ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U]

/-! ### The terms of the expansion -/

section Term

/-- The term of order `m' + m - k` in the asymptotic expansion of the composition symbol `a # b`:
`((-i)^k / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b`, the sum running over the words `w` of coordinate
indices of length `k` (`coefficient_sharpTerm`). It is defined by the recursion
`sharpTerm a b (k + 1) = (-i / (k + 1)) ∑ⱼ sharpTerm (∂_{ξⱼ} a) (∂_{xⱼ} b) k`, starting from the
pointwise composition `sharpTerm a b 0 = a ∘ b`. -/
def sharpTerm : {m m' : ℝ} → Symbol n W U m' → Symbol n V W m → (k : ℕ) →
    Symbol n V U (m' + m - k)
  | _, _, a, b, 0 => inclusion (by simp) (a.comp b)
  | _, _, a, b, k + 1 => inclusion (by push_cast; linarith)
      ((-Complex.I / (k + 1)) • ∑ j, sharpTerm (frequencyDeriv j a) (spatialDeriv j b) k)

theorem sharpTerm_zero (a : Symbol n W U m') (b : Symbol n V W m) :
    a.sharpTerm b 0 = inclusion (by simp) (a.comp b) := by
  rw [sharpTerm]

theorem sharpTerm_succ (a : Symbol n W U m') (b : Symbol n V W m) (k : ℕ) :
    a.sharpTerm b (k + 1) = inclusion (by push_cast; linarith)
      ((-Complex.I / (k + 1)) • ∑ j, (frequencyDeriv j a).sharpTerm (spatialDeriv j b) k) := by
  rw [sharpTerm]

@[simp]
theorem coefficient_sharpTerm_zero (a : Symbol n W U m') (b : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (a.sharpTerm b 0).coefficient p = (a.coefficient p).comp (b.coefficient p) := by
  rw [sharpTerm_zero, coefficient_inclusion, coefficient_comp]

theorem coefficient_sharpTerm_succ (a : Symbol n W U m') (b : Symbol n V W m) (k : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (a.sharpTerm b (k + 1)).coefficient p = (-Complex.I / (k + 1)) •
      ∑ j, ((frequencyDeriv j a).sharpTerm (spatialDeriv j b) k).coefficient p := by
  rw [sharpTerm_succ, coefficient_inclusion, coefficient_smul, coefficient_sum, Pi.smul_apply,
    Finset.sum_apply]

/-- **The terms of the composition expansion** are
`((-i)^k / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b`, the sum running over the words `w` of coordinate
indices of length `k`. Grouping the words by the multi-index they determine gives the familiar
form `∑_{|α| = k} (1 / α!) ∂_ξ^α a · D_x^α b` with `D_x = -i ∂_x`. -/
theorem coefficient_sharpTerm (a : Symbol n W U m') (b : Symbol n V W m) (k : ℕ)
    (x ξ : CoordinateSpace n) :
    (a.sharpTerm b k).coefficient (x, ξ) = ((-Complex.I) ^ k / k.factorial) •
      ∑ w : Fin k → Fin n, (mixedDeriv [] (List.ofFn w) a.coefficient x ξ).comp
        (mixedDeriv (List.ofFn w) [] b.coefficient x ξ) := by
  induction k generalizing m m' with
  | zero => simp
  | succ k ih =>
    rw [coefficient_sharpTerm_succ, ← (Fin.snocEquiv fun _ ↦ Fin n).sum_comp,
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

/-- **Leibniz rule in the position** for the terms of the composition expansion. -/
theorem spatialDeriv_sharpTerm (l : Fin n) (a : Symbol n W U m') (b : Symbol n V W m) (k : ℕ) :
    spatialDeriv l (a.sharpTerm b k) =
      (spatialDeriv l a).sharpTerm b k + a.sharpTerm (spatialDeriv l b) k := by
  induction k generalizing m m' with
  | zero => rw [sharpTerm_zero, sharpTerm_zero, sharpTerm_zero, spatialDeriv_inclusion,
      spatialDeriv_comp, map_add]
  | succ k ih =>
    rw [sharpTerm_succ, sharpTerm_succ, sharpTerm_succ, spatialDeriv_inclusion, map_smul, map_sum,
      ← map_add, ← smul_add, ← Finset.sum_add_distrib]
    refine congrArg _ (congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_))
    rw [ih, spatialDeriv_frequencyDeriv_comm, spatialDeriv_comm]

/-- **Leibniz rule in the frequency** for the terms of the composition expansion. The orders of
the three terms differ, so the rule is stated for their coefficients. -/
theorem coefficient_frequencyDeriv_sharpTerm (l : Fin n) (a : Symbol n W U m')
    (b : Symbol n V W m) (k : ℕ) (p : CoordinateSpace n × CoordinateSpace n) :
    (frequencyDeriv l (a.sharpTerm b k)).coefficient p =
      ((frequencyDeriv l a).sharpTerm b k).coefficient p +
        (a.sharpTerm (frequencyDeriv l b) k).coefficient p := by
  induction k generalizing m m' with
  | zero =>
    rw [sharpTerm_zero, frequencyDeriv_inclusion, coefficient_inclusion, frequencyDeriv_comp,
      coefficient_add, Pi.add_apply, coefficient_inclusion, coefficient_inclusion,
      coefficient_sharpTerm_zero, coefficient_sharpTerm_zero, coefficient_comp, coefficient_comp]
  | succ k ih =>
    rw [sharpTerm_succ, frequencyDeriv_inclusion, coefficient_inclusion, map_smul, map_sum,
      coefficient_smul, coefficient_sum, Pi.smul_apply, Finset.sum_apply,
      coefficient_sharpTerm_succ, coefficient_sharpTerm_succ, ← smul_add, ← Finset.sum_add_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
    rw [ih, frequencyDeriv_comm, spatialDeriv_frequencyDeriv_comm]

end Term

/-! ### The interpolating family `a #_t b` -/

section Scaled

variable {a : Symbol n W U m'} {b : Symbol n V W m}

variable (a b) in
/-- The integrand `exp(2πi ⟪η, x⟫) a(x, ξ + 2π t η) ∘ b̂(η, ξ)` of `a #_t b`. -/
private def scaledIntegrand (t : ℝ) (x ξ η : CoordinateSpace n) : V →L[ℂ] U :=
  (𝐞 ⟪η, x⟫ : ℂ) • (a.coefficient (x, ξ + t • (2 * π) • η)).comp
    (𝓕 (fun y ↦ b.coefficient (y, ξ)) η)

variable (a b) in
/-- The family `(a #_t b)(x, ξ) = ∫ exp(2πi ⟪η, x⟫) a(x, ξ + 2π t η) ∘ b̂(η, ξ) dη` interpolating
between the pointwise composition (`t = 0`) and the composition symbol (`t = 1`). -/
private def scaledSharp (t : ℝ) (x ξ : CoordinateSpace n) : V →L[ℂ] U :=
  ∫ η, scaledIntegrand a b t x ξ η

/-- The weight `⟨η⟩ ^ (-(n + 1))` is integrable on `ℝⁿ`. -/
private theorem integrable_weight :
    Integrable fun η : CoordinateSpace n ↦ (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) :=
  integrable_rpow_neg_one_add_norm_sq (by rw [finrank_euclideanSpace_fin]; linarith)

/-- The integrand of `a #_t b` decays like `⟨η⟩ ^ (-(n + 1))`, with the weight `⟨ξ⟩ ^ (m' + m)`,
uniformly for `|t| ≤ 2` and positions in a compact set. -/
private theorem exists_norm_scaledIntegrand_le (hb : b.HasCompactSpatialSupport)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ 2 → ∀ x ∈ K, ∀ ξ η, ‖scaledIntegrand a b t x ξ η‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
  obtain ⟨C, hC0, hC⟩ := hb.exists_norm_comp_fourier_slice_le a hK ((n : ℝ) + 1) (R := 4 * π)
    (by linarith [Real.two_le_pi])
  refine ⟨C, hC0, fun t ht x hx ξ η ↦ ?_⟩
  rw [scaledIntegrand, norm_smul, Circle.norm_coe, one_mul]
  refine hC x hx ξ η _ ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg Real.two_pi_pos.le]
  nlinarith [mul_nonneg (sub_nonneg.2 ht) (by positivity : 0 ≤ 2 * π * ‖η‖)]

private theorem continuous_scaledIntegrand (hb : b.HasCompactSpatialSupport) (t : ℝ)
    (x ξ : CoordinateSpace n) : Continuous (scaledIntegrand a b t x ξ) := by
  have he : Continuous fun η : CoordinateSpace n ↦ (𝐞 ⟪η, x⟫ : ℂ) := by fun_prop
  have ha : Continuous fun η : CoordinateSpace n ↦ a.coefficient (x, ξ + t • (2 * π) • η) :=
    a.contDiff_coefficient.continuous.comp (by fun_prop)
  have hB : Continuous fun η : CoordinateSpace n ↦ 𝓕 (fun y ↦ b.coefficient (y, ξ)) η := by
    have h := hb.continuous_fourier_slice.comp
      (by fun_prop : Continuous fun η : CoordinateSpace n ↦ (η, ξ))
    simpa only [Function.comp_def] using h
  exact he.smul (ha.clm_comp hB)

private theorem integrable_scaledIntegrand (hb : b.HasCompactSpatialSupport) {t : ℝ}
    (ht : |t| ≤ 2) (x ξ : CoordinateSpace n) : Integrable (scaledIntegrand a b t x ξ) := by
  obtain ⟨C, -, hC⟩ := exists_norm_scaledIntegrand_le (a := a) hb (isCompact_singleton (x := x))
  exact (integrable_weight.const_mul (C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2))).mono'
    (continuous_scaledIntegrand hb t x ξ).aestronglyMeasurable
    (.of_forall fun η ↦ hC t ht x rfl ξ η)

/-- `‖(a #_t b)(x, ξ)‖ ≤ C ⟨ξ⟩ ^ (m' + m)`, uniformly for `|t| ≤ 2` and positions in a compact
set. -/
private theorem exists_norm_scaledSharp_le (hb : b.HasCompactSpatialSupport)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ 2 → ∀ x ∈ K, ∀ ξ,
      ‖scaledSharp a b t x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_scaledIntegrand_le (a := a) hb hK
  set I := ∫ η : CoordinateSpace n, (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  have hI : 0 ≤ I := integral_nonneg fun η ↦ by positivity
  refine ⟨C * I, mul_nonneg hC0 hI, fun t ht x hx ξ ↦ ?_⟩
  refine (norm_integral_le_of_norm_le (integrable_weight.const_mul
    (C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2))) (.of_forall fun η ↦ hC t ht x hx ξ η)).trans_eq ?_
  rw [integral_const_mul]
  ring

/-- At `t = 1` the family is the composition symbol. -/
private theorem scaledSharp_one (hb : b.HasCompactSpatialSupport) (x ξ : CoordinateSpace n) :
    scaledSharp a b 1 x ξ = (a.sharp b hb).coefficient (x, ξ) := by
  simp only [scaledSharp, scaledIntegrand, one_smul, coefficient_sharp]

/-- At `t = 0` the family is the pointwise composition, by Fourier inversion. -/
private theorem scaledSharp_zero [CompleteSpace W] [CompleteSpace U]
    (hb : b.HasCompactSpatialSupport) (x ξ : CoordinateSpace n) :
    scaledSharp a b 0 x ξ = (a.coefficient (x, ξ)).comp (b.coefficient (x, ξ)) := by
  set f : CoordinateSpace n → V →L[ℂ] W := fun y ↦ b.coefficient (y, ξ)
  set φ : 𝓢(CoordinateSpace n, V →L[ℂ] W) := hb.sliceSchwartz ξ
  have hfS : ⇑φ = f := hb.coe_sliceSchwartz ξ
  have hFS : 𝓕 f = ⇑(𝓕 φ : 𝓢(CoordinateSpace n, V →L[ℂ] W)) := by
    rw [SchwartzMap.fourier_coe, hfS]
  have hint : Integrable (𝓕 f) := hFS ▸ (𝓕 φ : 𝓢(CoordinateSpace n, V →L[ℂ] W)).integrable
  have hinv : 𝓕⁻ (𝓕 f) = f :=
    Continuous.fourierInv_fourier_eq (hfS ▸ φ.continuous) (hfS ▸ φ.integrable) hint
  have hint' : Integrable fun η : CoordinateSpace n ↦ (𝐞 ⟪η, x⟫ : ℂ) • 𝓕 f η :=
    hint.norm.mono' ((by fun_prop : Continuous fun η : CoordinateSpace n ↦ (𝐞 ⟪η, x⟫ : ℂ)).smul
      (hFS ▸ (𝓕 φ : 𝓢(CoordinateSpace n, V →L[ℂ] W)).continuous)).aestronglyMeasurable
      (.of_forall fun η ↦ by rw [norm_smul, Circle.norm_coe, one_mul])
  calc scaledSharp a b 0 x ξ
      = ∫ η, ContinuousLinearMap.compL ℂ V W U (a.coefficient (x, ξ))
          ((𝐞 ⟪η, x⟫ : ℂ) • 𝓕 f η) := by
        simp only [scaledSharp, scaledIntegrand, zero_smul, add_zero, map_smul,
          ContinuousLinearMap.compL_apply, f]
    _ = (a.coefficient (x, ξ)).comp (𝓕⁻ (𝓕 f) x) := by
        rw [ContinuousLinearMap.integral_comp_comm _ hint', Real.fourierInv_eq,
          ContinuousLinearMap.compL_apply]
        simp only [Circle.smul_def]
    _ = _ := by rw [hinv]

/-- **Differentiation in the parameter** of the integrand: since `2π ηⱼ b̂ = -i (∂_{xⱼ} b)^`,
`d/dt` of the integrand of `a #_t b` is `-i ∑ⱼ` the integrand of `(∂_{ξⱼ} a) #_t (∂_{xⱼ} b)`. -/
private theorem hasDerivAt_scaledIntegrand (hb : b.HasCompactSpatialSupport) (t : ℝ)
    (x ξ η : CoordinateSpace n) :
    HasDerivAt (fun t ↦ scaledIntegrand a b t x ξ η)
      (∑ j, (-Complex.I) • scaledIntegrand (frequencyDeriv j a) (spatialDeriv j b) t x ξ η) t := by
  set c : CoordinateSpace n := (2 * π) • η
  set B := 𝓕 (fun y ↦ b.coefficient (y, ξ)) η
  set Φ : (W →L[ℂ] U) →L[ℝ] (V →L[ℂ] W) →L[ℝ] (V →L[ℂ] U) :=
    (ContinuousLinearMap.compL ℂ V W U).bilinearRestrictScalars ℝ
  set g : CoordinateSpace n → W →L[ℂ] U := fun ζ ↦ a.coefficient (x, ζ)
  have hg : HasFDerivAt g (fderiv ℝ g (ξ + t • c)) (ξ + t • c) :=
    ((a.contDiff_coefficient.comp (contDiff_prodMk_right x)).differentiable (by simp)
      _).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ ↦ ξ + t • c) c t := by
    simpa using ((hasDerivAt_id t).smul_const c).const_add ξ
  have h := ((Φ.flip B).hasFDerivAt.comp_hasDerivAt t (hg.comp_hasDerivAt t hl)).const_smul
    (𝐞 ⟪η, x⟫ : ℂ)
  have hgj (j : Fin n) (ζ : CoordinateSpace n) : fderiv ℝ g ζ (EuclideanSpace.single j 1) =
      (frequencyDeriv j a).coefficient (x, ζ) := by
    rw [coefficient_frequencyDeriv, coordinateDeriv_cons, coordinateDeriv_nil]
  refine (h.congr_of_eventuallyEq (.of_forall fun s ↦ ?_)).congr_deriv ?_
  · simp only [scaledIntegrand, Pi.smul_apply, Function.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.bilinearRestrictScalars_apply_apply, ContinuousLinearMap.compL_apply, Φ,
      g, B, c]
  rw [ContinuousLinearMap.apply_eq_sum_single (fderiv ℝ g (ξ + t • c)) c, map_sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [scaledIntegrand, hb.fourier_spatialDeriv_slice, hgj, map_smul, Φ, c, B,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
    ContinuousLinearMap.comp_smul, PiLp.smul_apply, smul_smul, EuclideanSpace.inner_single_right,
    ← Complex.coe_smul]
  rw [smul_apply, ContinuousLinearMap.compL_apply, smul_smul]
  congr 1
  simp only [smul_eq_mul, starRingEnd_apply, star_trivial, one_mul]
  push_cast
  linear_combination (↑(𝐞 ⟪η, x⟫) * 2 * ↑π * ↑(η.ofLp j) : ℂ) * Complex.I_sq

/-- **Differentiation in the parameter** under the integral sign:
`d/dt (a #_t b) = -i ∑ⱼ (∂_{ξⱼ} a) #_t (∂_{xⱼ} b)`. -/
private theorem hasDerivAt_scaledSharp (hb : b.HasCompactSpatialSupport) {t₀ : ℝ} (ht₀ : |t₀| ≤ 1)
    (x ξ : CoordinateSpace n) :
    HasDerivAt (fun t ↦ scaledSharp a b t x ξ)
      (∑ j, (-Complex.I) • scaledSharp (frequencyDeriv j a) (spatialDeriv j b) t₀ x ξ) t₀ := by
  choose C hC0 hC using fun j ↦ exists_norm_scaledIntegrand_le (a := frequencyDeriv j a)
    (hb.spatialDeriv j) (isCompact_singleton (x := x))
  have hball : ∀ t ∈ Metric.ball t₀ 1, |t| ≤ 2 := fun t ht ↦ by
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have := abs_sub_abs_le_abs_sub t t₀
    linarith
  have ht₀2 : |t₀| ≤ 2 := by linarith
  set F' : ℝ → CoordinateSpace n → V →L[ℂ] U := fun t η ↦
    ∑ j, (-Complex.I) • scaledIntegrand (frequencyDeriv j a) (spatialDeriv j b) t x ξ η
  set bound : CoordinateSpace n → ℝ := fun η ↦
    (∑ j, C j * (1 + ‖ξ‖ ^ 2) ^ ((m' - 1 + m) / 2)) * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  have hint (j : Fin n) : Integrable fun η ↦
      (-Complex.I) • scaledIntegrand (frequencyDeriv j a) (spatialDeriv j b) t₀ x ξ η :=
    (integrable_scaledIntegrand (a := frequencyDeriv j a) (hb.spatialDeriv j) ht₀2 x ξ).fun_smul _
  have hmeas : ∀ᶠ t in nhds t₀,
      AEStronglyMeasurable (scaledIntegrand a b t x ξ) (volume : Measure (CoordinateSpace n)) :=
    .of_forall fun t ↦ (continuous_scaledIntegrand hb t x ξ).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable (F' t₀) (volume : Measure (CoordinateSpace n)) :=
    (continuous_finsetSum _ fun j _ ↦ (continuous_scaledIntegrand (hb.spatialDeriv j) t₀ x
      ξ).const_smul (-Complex.I)).aestronglyMeasurable
  have hbound : ∀ᵐ η ∂(volume : Measure (CoordinateSpace n)), ∀ t ∈ Metric.ball t₀ 1,
      ‖F' t η‖ ≤ bound η := .of_forall fun η t ht ↦ by
    simp only [F', bound, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
    exact hC j t (hball t ht) x rfl ξ η
  have hdiff : ∀ᵐ η ∂(volume : Measure (CoordinateSpace n)), ∀ t ∈ Metric.ball t₀ 1,
      HasDerivAt (fun t ↦ scaledIntegrand a b t x ξ η) (F' t η) t :=
    .of_forall fun η t _ ↦ hasDerivAt_scaledIntegrand hb t x ξ η
  obtain ⟨-, h⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds t₀ one_pos) hmeas (integrable_scaledIntegrand hb ht₀2 x ξ) hF'meas
    hbound (integrable_weight.const_mul _) hdiff
  refine h.congr_deriv ?_
  simp only [F']
  rw [integral_finsetSum _ fun j _ ↦ hint j]
  simp only [integral_smul, scaledSharp]

end Scaled

/-! ### The remainder of the expansion along the family -/

section Remainder

variable {a : Symbol n W U m'} {b : Symbol n V W m}

variable (a b) in
/-- The remainder `a #_t b - ∑_{k < N} t^k sharpTerm a b k` of the expansion along the
interpolating family. -/
private def remainderAt (N : ℕ) (t : ℝ) (x ξ : CoordinateSpace n) : V →L[ℂ] U :=
  scaledSharp a b t x ξ - ∑ k ∈ range N, t ^ k • (a.sharpTerm b k).coefficient (x, ξ)

/-- The derivative of the polynomial part `∑_{k < N + 1} t^k sharpTerm a b k` is given by the
recursion defining `sharpTerm`. -/
private theorem hasDerivAt_sum_pow_smul_sharpTerm (N : ℕ) (a : Symbol n W U m')
    (b : Symbol n V W m) (x ξ : CoordinateSpace n) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ ∑ k ∈ range (N + 1), t ^ k • (a.sharpTerm b k).coefficient (x, ξ))
      (∑ k ∈ range N, t ^ k • ((-Complex.I) •
        ∑ j, ((frequencyDeriv j a).sharpTerm (spatialDeriv j b) k).coefficient (x, ξ))) t := by
  have h := HasDerivAt.fun_sum (u := range (N + 1)) fun k _ ↦
    (hasDerivAt_pow k t).smul_const ((a.sharpTerm b k).coefficient (x, ξ))
  refine h.congr_deriv ?_
  rw [Finset.sum_range_succ']
  simp only [CharP.cast_eq_zero, zero_mul, zero_smul, add_zero]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [coefficient_sharpTerm_succ, Nat.add_sub_cancel, mul_comm, mul_smul]
  congr 1
  rw [← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  field_simp

/-- The derivative in `t` of the remainder with `N + 1` terms is `-i ∑ⱼ` the remainders with `N`
terms of `(∂_{ξⱼ} a, ∂_{xⱼ} b)`. -/
private theorem hasDerivAt_remainderAt (hb : b.HasCompactSpatialSupport) (N : ℕ) {t : ℝ}
    (ht : |t| ≤ 1) (x ξ : CoordinateSpace n) :
    HasDerivAt (fun t ↦ remainderAt a b (N + 1) t x ξ)
      ((-Complex.I) • ∑ j, remainderAt (frequencyDeriv j a) (spatialDeriv j b) N t x ξ) t := by
  refine ((hasDerivAt_scaledSharp (a := a) hb ht x ξ).fun_sub
    (hasDerivAt_sum_pow_smul_sharpTerm N a b x ξ t)).congr_deriv ?_
  simp only [remainderAt, smul_sub, Finset.smul_sum, Finset.sum_sub_distrib, smul_comm (t ^ _)]
  rw [Finset.sum_comm]

/-- The remainder vanishes at `t = 0`. -/
private theorem remainderAt_zero [CompleteSpace W] [CompleteSpace U]
    (hb : b.HasCompactSpatialSupport) (N : ℕ) (x ξ : CoordinateSpace n) :
    remainderAt a b (N + 1) 0 x ξ = 0 := by
  rw [remainderAt, scaledSharp_zero hb, Finset.sum_range_succ']
  simp

/-- **The remainder estimate.** `‖a #_t b - ∑_{k < N} t^k sharpTerm a b k‖ ≤ C ⟨ξ⟩ ^ (m' + m - N)`,
uniformly for `t ∈ [0, 1]` and positions in a compact set. -/
private theorem exists_norm_remainderAt_le [CompleteSpace W] [CompleteSpace U] (N : ℕ) :
    ∀ {m m' : ℝ} (a : Symbol n W U m') {b : Symbol n V W m}, b.HasCompactSpatialSupport →
      ∀ {K : Set (CoordinateSpace n)}, IsCompact K → ∃ C, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ x ∈ K, ∀ ξ, ‖remainderAt a b N t x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - N) / 2) := by
  induction N with
  | zero =>
    intro m m' a b hb K hK
    obtain ⟨C, hC0, hC⟩ := exists_norm_scaledSharp_le (a := a) hb hK
    refine ⟨C, hC0, fun t ht x hx ξ ↦ ?_⟩
    have ht2 : |t| ≤ 2 := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa [remainderAt] using hC t ht2 x hx ξ
  | succ N ih =>
    intro m m' a b hb K hK
    choose C hC0 hC using fun j ↦ ih (frequencyDeriv j a) (hb.spatialDeriv j) hK
    refine ⟨∑ j, C j, Finset.sum_nonneg fun j _ ↦ hC0 j, fun t ht x hx ξ ↦ ?_⟩
    have hw : (1 + ‖ξ‖ ^ 2) ^ ((m' - 1 + m - N) / 2) =
        (1 + ‖ξ‖ ^ 2) ^ ((m' + m - ((N + 1 : ℕ) : ℝ)) / 2) := by
      congr 1
      push_cast
      ring
    have hbound : ∀ s ∈ Set.Ico (0 : ℝ) 1,
        ‖(-Complex.I) • ∑ j, remainderAt (frequencyDeriv j a) (spatialDeriv j b) N s x ξ‖ ≤
          (∑ j, C j) * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - ((N + 1 : ℕ) : ℝ)) / 2) := by
      intro s hs
      rw [norm_smul, norm_neg, Complex.norm_I, one_mul, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
      rw [← hw]
      exact hC j s (Set.Ico_subset_Icc_self hs) x hx ξ
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s hs ↦ (hasDerivAt_remainderAt hb N (abs_le.2 ⟨by linarith [hs.1], hs.2⟩) x
        ξ).hasDerivWithinAt) hbound t ht
    rw [remainderAt_zero hb, sub_zero, sub_zero] at hmv
    have hB : 0 ≤ (∑ j, C j) * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - ((N + 1 : ℕ) : ℝ)) / 2) :=
      mul_nonneg (Finset.sum_nonneg fun j _ ↦ hC0 j) (by positivity)
    exact hmv.trans (mul_le_of_le_one_right hB ht.2)

end Remainder

/-! ### The remainder symbol -/

section Symbol

variable {a : Symbol n W U m'} {b : Symbol n V W m}

variable (a) in
/-- The remainder `a # b - ∑_{k < N} sharpTerm a b k`, as a symbol of order `m' + m`. -/
private def remainderSymbol (hb : b.HasCompactSpatialSupport) (N : ℕ) : Symbol n V U (m' + m) :=
  a.sharp b hb - ∑ k ∈ range N, inclusion (sub_le_self _ (Nat.cast_nonneg k)) (a.sharpTerm b k)

private theorem coefficient_remainderSymbol (hb : b.HasCompactSpatialSupport) (N : ℕ)
    (x ξ : CoordinateSpace n) :
    (remainderSymbol a hb N).coefficient (x, ξ) = remainderAt a b N 1 x ξ := by
  simp [remainderSymbol, remainderAt, scaledSharp_one hb]

private theorem spatialDeriv_remainderSymbol (hb : b.HasCompactSpatialSupport) (N : ℕ)
    (j : Fin n) :
    spatialDeriv j (remainderSymbol a hb N) =
      remainderSymbol (spatialDeriv j a) hb N + remainderSymbol a (hb.spatialDeriv j) N := by
  simp only [remainderSymbol, map_sub, map_sum, spatialDeriv_sharp, spatialDeriv_inclusion,
    spatialDeriv_sharpTerm, map_add, Finset.sum_add_distrib]
  abel

private theorem coefficient_frequencyDeriv_remainderSymbol (hb : b.HasCompactSpatialSupport)
    (N : ℕ) (j : Fin n) :
    (frequencyDeriv j (remainderSymbol a hb N)).coefficient =
      (remainderSymbol (frequencyDeriv j a) hb N).coefficient +
        (remainderSymbol a (hb.frequencyDeriv j) N).coefficient := by
  funext ⟨x, ξ⟩
  simp only [remainderSymbol, map_sub, map_sum, coefficient_sub, coefficient_sum,
    frequencyDeriv_inclusion, coefficient_inclusion, Pi.sub_apply, Pi.add_apply,
    Finset.sum_apply, coefficient_frequencyDeriv_sharp, coefficient_frequencyDeriv_sharpTerm,
    Finset.sum_add_distrib]
  abel

/-- The symbol estimates of order `m' + m - N` for the remainder, by induction on the number of
derivatives: each derivative falls on one of the two symbols by the Leibniz rules, and a frequency
derivative lowers the order of that symbol by one. -/
private theorem exists_bound_remainderSymbol [CompleteSpace W] [CompleteSpace U] (N D : ℕ) :
    ∀ {m m' : ℝ} (a : Symbol n W U m') {b : Symbol n V W m} (hb : b.HasCompactSpatialSupport)
      (α β : List (Fin n)), α.length + β.length = D → ∀ {K : Set (CoordinateSpace n)},
        IsCompact K → ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
          ‖mixedDeriv α β (remainderSymbol a hb N).coefficient x ξ‖ ≤
            C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - N - β.length) / 2) := by
  induction D with
  | zero =>
    intro m m' a b hb α β hD K hK
    obtain ⟨rfl, rfl⟩ : α = [] ∧ β = [] := by
      simpa [List.length_eq_zero_iff] using hD
    obtain ⟨C, hC0, hC⟩ := exists_norm_remainderAt_le N a hb hK
    refine ⟨C, hC0, fun x hx ξ ↦ ?_⟩
    simpa [coefficient_remainderSymbol] using hC 1 ⟨zero_le_one, le_rfl⟩ x hx ξ
  | succ D ih =>
    intro m m' a b hb α β hD K hK
    rcases List.eq_nil_or_concat' β with rfl | ⟨β', j, rfl⟩
    · rcases List.eq_nil_or_concat' α with rfl | ⟨α', j, rfl⟩
      · simp at hD
      · have hlen : α'.length + ([] : List (Fin n)).length = D := by
          simp only [List.length_append, List.length_singleton, List.length_nil] at hD ⊢
          omega
        obtain ⟨C₁, hC₁0, hC₁⟩ := ih (spatialDeriv j a) hb α' [] hlen hK
        obtain ⟨C₂, hC₂0, hC₂⟩ := ih a (hb.spatialDeriv j) α' [] hlen hK
        refine ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun x hx ξ ↦ ?_⟩
        rw [← mixedDeriv_spatialDeriv j (remainderSymbol a hb N), spatialDeriv_remainderSymbol,
          coefficient_add]
        exact norm_mixedDeriv_add_le (remainderSymbol _ hb N).contDiff_coefficient
          (remainderSymbol a (hb.spatialDeriv j) N).contDiff_coefficient (hC₁ x hx ξ)
          (hC₂ x hx ξ)
    · have hlen : α.length + β'.length = D := by
        simp only [List.length_append, List.length_singleton] at hD
        omega
      obtain ⟨C₁, hC₁0, hC₁⟩ := ih (frequencyDeriv j a) hb α β' hlen hK
      obtain ⟨C₂, hC₂0, hC₂⟩ := ih a (hb.frequencyDeriv j) α β' hlen hK
      refine ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun x hx ξ ↦ ?_⟩
      have e₁ : (m' - 1 + m - N - β'.length) / 2 = (m' + m - N - (β' ++ [j]).length) / 2 := by
        simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
        ring
      have e₂ : (m' + (m - 1) - N - β'.length) / 2 = (m' + m - N - (β' ++ [j]).length) / 2 := by
        simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
        ring
      have h₁ := hC₁ x hx ξ
      have h₂ := hC₂ x hx ξ
      rw [e₁] at h₁
      rw [e₂] at h₂
      rw [← mixedDeriv_frequencyDeriv j (remainderSymbol a hb N),
        coefficient_frequencyDeriv_remainderSymbol]
      exact norm_mixedDeriv_add_le (remainderSymbol _ hb N).contDiff_coefficient
        (remainderSymbol a (hb.frequencyDeriv j) N).contDiff_coefficient h₁ h₂

variable [CompleteSpace W] [CompleteSpace U]

variable (a b) in
/-- The remainder `a # b - ∑_{k < N} sharpTerm a b k` of the composition expansion after `N`
terms, a symbol of order `m' + m - N` (`sharp_eq_sum_sharpTerm_add_sharpRemainder`). -/
def sharpRemainder (hb : b.HasCompactSpatialSupport) (N : ℕ) : Symbol n V U (m' + m - N) where
  coefficient := (remainderSymbol a hb N).coefficient
  contDiff_coefficient := (remainderSymbol a hb N).contDiff_coefficient
  exists_bound _ hK α β := exists_bound_remainderSymbol N _ a hb α β rfl hK

@[simp]
theorem coefficient_sharpRemainder (hb : b.HasCompactSpatialSupport) (N : ℕ) :
    (a.sharpRemainder b hb N).coefficient =
      (a.sharp b hb).coefficient - ∑ k ∈ range N, (a.sharpTerm b k).coefficient := by
  simp [sharpRemainder, remainderSymbol]

/-- **The asymptotic expansion of the composition symbol.** For every `N`,
`a # b = ∑_{k < N} sharpTerm a b k + sharpRemainder a b hb N`, where `sharpTerm a b k` is the
term `((-i)^k / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b` of order `m' + m - k` and the remainder is a
symbol of order `m' + m - N`. -/
theorem sharp_eq_sum_sharpTerm_add_sharpRemainder (hb : b.HasCompactSpatialSupport) (N : ℕ) :
    a.sharp b hb = ∑ k ∈ range N, inclusion (sub_le_self _ (Nat.cast_nonneg k)) (a.sharpTerm b k) +
      inclusion (sub_le_self _ (Nat.cast_nonneg N)) (a.sharpRemainder b hb N) := by
  ext1
  simp

/-- The composition symbol `a # b` is the pointwise composition `a ∘ b` up to a symbol of order
`m' + m - 1`. -/
theorem sharp_eq_comp_add_sharpRemainder_one (hb : b.HasCompactSpatialSupport) :
    a.sharp b hb = a.comp b + inclusion (by simp) (a.sharpRemainder b hb 1) := by
  ext1
  funext p
  simp

end Symbol

end Symbol

end TauCeti
