/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Amplitude.LeftSymbol
public import TauCeti.Analysis.Pseudodifferential.AsymptoticSum
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The asymptotic expansion of the left symbol of an amplitude

Let `a(x, y, ξ)` be an amplitude of order `m` with compact support in the input position `y`.
Its left symbol `c = a.leftSymbol ha`, the symbol of order `m` with the same quantization
(`TauCeti.Amplitude.quantizeSchwartzValue_leftSymbol`), has the asymptotic expansion obtained by
Taylor expanding `a` in `y` at the diagonal `y = x`:

`c(x, ξ) ∼ ∑_γ (1 / γ!) ∂_ξ^γ D_y^γ a(x, y, ξ)|_{y = x}`, with `D_y = -i ∂_y`,

meaning that after removing the terms with `|γ| < N` the remainder is a symbol of order `m - N`.
This file proves this, with an actual remainder symbol. In particular `c` agrees with the
restriction `a(x, x, ξ)` of `a` to the diagonal up to a symbol of order `m - 1`.

Summing over words `w = [j₁, …, j_k]` of coordinate indices instead of multi-indices absorbs the
multinomial coefficients, so the term of order `m - k` is

`TauCeti.Amplitude.leftTerm a k = ((-i)^k / k!) ∑_{|w| = k} (∂_y^w ∂_ξ^w a)(x, x, ξ)`

(`TauCeti.Amplitude.coefficient_leftTerm`). It is defined by the recursion
`leftTerm a (k + 1) = (-i / (k + 1)) ∑ⱼ leftTerm (∂_{y_j} ∂_{ξ_j} a) k`, starting from the
restriction `leftTerm a 0 = a.diagonal` of `a` to the diagonal (`TauCeti.Amplitude.diagonal`).

## Main results

* `TauCeti.Amplitude.leftTerm`: the terms of the expansion, with their closed form
  `TauCeti.Amplitude.coefficient_leftTerm` and the Leibniz rules
  `TauCeti.Amplitude.spatialDeriv_leftTerm` and
  `TauCeti.Amplitude.coefficient_frequencyDeriv_leftTerm`.
* `TauCeti.Amplitude.leftRemainder a ha N`: the remainder `c - ∑_{k < N} leftTerm a k`, a symbol of
  order `m - N`.
* `TauCeti.Amplitude.leftSymbol_eq_sum_leftTerm_add_leftRemainder`: **the expansion**
  `c = ∑_{k < N} leftTerm a k + leftRemainder a ha N`, for every `N`; in the vocabulary of
  asymptotic sums, `TauCeti.Amplitude.isAsymptoticSum_leftSymbol`.
* `TauCeti.Amplitude.leftSymbol_eq_diagonal_add_leftRemainder_one`: `c` is `a(x, x, ξ)` up to a
  symbol of order `m - 1`.

## Proof outline

Interpolate between the restriction to the diagonal and the left symbol by the family

`c_t(x, ξ) = ∫ exp(2πi ⟪θ, x⟫) â(x, θ, ξ + 2π t θ) dθ`, `t ∈ [0, 1]`,

whose integrand is `TauCeti.Amplitude.leftIntegrand a (2πt)`, so that `c_1 = c`, and
`c_0(x, ξ) = a(x, x, ξ)` by Fourier inversion in `y`. Differentiating under the integral sign, and
using `2π θⱼ ∂_{ξ_j} â = -i (∂_{y_j} ∂_{ξ_j} a)^`, `d/dt c_t(a) = -i ∑ⱼ c_t(∂_{y_j} ∂_{ξ_j} a)`.
The recursion defining `leftTerm` is the matching identity for the polynomial
`∑_{k < N} t^k leftTerm a k`. So the derivative of the remainder
`c_t(a) - ∑_{k < N + 1} t^k leftTerm a k` is `-i` times the sum over `j` of the remainders with `N`
terms of `∂_{y_j} ∂_{ξ_j} a`, and this remainder vanishes at `t = 0`. By induction on `N` and the
mean value inequality on `[0, 1]`, the remainder is bounded by `C ⟨ξ⟩ ^ (m - N)`, locally
uniformly in the position: each step lowers the order of the amplitude by one. The base case is
the bound `‖c_t(x, ξ)‖ ≤ C ⟨ξ⟩ ^ m`, from
`TauCeti.Amplitude.HasCompactInputSupport.exists_norm_leftIntegrand_le`.

The derivative estimates follow from the Leibniz rules, which hold for the left symbol and for
each `leftTerm`: a position derivative `∂_{x_j}` of the remainder of `a` is the sum of the
remainders of `∂_{x_j} a` and `∂_{y_j} a`, and a frequency derivative `∂_{ξ_j}` is the remainder
of `∂_{ξ_j} a`, an amplitude of order `m - 1`. An induction on the number of derivatives then
gives every symbol estimate of order `m - N`
(`TauCeti.Amplitude.exists_norm_mixedDeriv_le_of_leibniz`). The argument parallels the composition
expansion of `TauCeti.Analysis.Pseudodifferential.Composition.Expansion`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (1.21)–(1.28).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.7.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Finset
open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace TauCeti

namespace Amplitude

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-! ### The terms of the expansion -/

section Term

/-- The term of order `m - k` in the asymptotic expansion of the left symbol of an amplitude `a`:
`((-i)^k / k!) ∑_{|w| = k} (∂_y^w ∂_ξ^w a)(x, x, ξ)`, the sum running over the words `w` of
coordinate indices of length `k` (`coefficient_leftTerm`). It is defined by the recursion
`leftTerm a (k + 1) = (-i / (k + 1)) ∑ⱼ leftTerm (∂_{y_j} ∂_{ξ_j} a) k`, starting from the
restriction `leftTerm a 0 = a.diagonal` to the diagonal. -/
def leftTerm : {m : ℝ} → Amplitude n V W m → (k : ℕ) → Symbol n V W (m - k)
  | _, a, 0 => Symbol.inclusion (by simp) a.diagonal
  | _, a, k + 1 => Symbol.inclusion (by push_cast; linarith)
      ((-Complex.I / (k + 1)) • ∑ j, leftTerm (spatialDerivSnd j (frequencyDeriv j a)) k)

theorem leftTerm_zero (a : Amplitude n V W m) :
    a.leftTerm 0 = Symbol.inclusion (by simp) a.diagonal := by
  rw [leftTerm]

theorem leftTerm_succ (a : Amplitude n V W m) (k : ℕ) :
    a.leftTerm (k + 1) = Symbol.inclusion (by push_cast; linarith)
      ((-Complex.I / (k + 1)) • ∑ j, (spatialDerivSnd j (frequencyDeriv j a)).leftTerm k) := by
  rw [leftTerm]

@[simp]
theorem coefficient_leftTerm_zero (a : Amplitude n V W m) (x ξ : CoordinateSpace n) :
    (a.leftTerm 0).coefficient (x, ξ) = a.coefficient (x, x, ξ) := by
  rw [leftTerm_zero, Symbol.coefficient_inclusion, coefficient_diagonal]

theorem coefficient_leftTerm_succ (a : Amplitude n V W m) (k : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (a.leftTerm (k + 1)).coefficient p = (-Complex.I / (k + 1)) •
      ∑ j, ((spatialDerivSnd j (frequencyDeriv j a)).leftTerm k).coefficient p := by
  simp [leftTerm_succ]

/-- The coefficient of `∂_{y_j} ∂_{ξ_j} a`. -/
private theorem coefficient_spatialDerivSnd_frequencyDeriv (j : Fin n) (a : Amplitude n V W m) :
    (spatialDerivSnd j (frequencyDeriv j a)).coefficient =
      iteratedFDerivAlong ℝ [(0, EuclideanSpace.single j 1, 0), (0, 0, EuclideanSpace.single j 1)]
        a.coefficient := by
  rw [coefficient_spatialDerivSnd_eq_iteratedFDerivAlong,
    coefficient_frequencyDeriv_eq_iteratedFDerivAlong, ← iteratedFDerivAlong_append,
    List.singleton_append]

/-- **The terms of the expansion** are `((-i)^k / k!) ∑_{|w| = k} (∂_y^w ∂_ξ^w a)(x, x, ξ)`, the
sum running over the words `w` of coordinate indices of length `k`. Grouping the words by the
multi-index they determine gives the familiar form `∑_{|γ| = k} (1 / γ!) ∂_ξ^γ D_y^γ a` with
`D_y = -i ∂_y`. -/
theorem coefficient_leftTerm (a : Amplitude n V W m) (k : ℕ) (x ξ : CoordinateSpace n) :
    (a.leftTerm k).coefficient (x, ξ) = ((-Complex.I) ^ k / k.factorial) •
      ∑ w : Fin k → Fin n, iteratedFDerivAlong ℝ
        (amplitudeDirections [] (List.ofFn w) (List.ofFn w)) a.coefficient (x, x, ξ) := by
  induction k generalizing m with
  | zero => simp [amplitudeDirections_def]
  | succ k ih =>
    rw [coefficient_leftTerm_succ, ← (Fin.consEquiv fun _ ↦ Fin n).sum_comp,
      Fintype.sum_prod_type]
    simp only [ih, Finset.smul_sum, smul_smul, Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero,
      Fin.cons_succ]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun w _ ↦ ?_
    congr 1
    · rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · rw [coefficient_spatialDerivSnd_frequencyDeriv, ← iteratedFDerivAlong_append]
      refine congrFun (List.Perm.iteratedFDerivAlong_eq ?_ a.contDiff_coefficient (by simp)) _
      simp only [amplitudeDirections_def, List.map_nil, List.nil_append, List.map_cons,
        List.cons_append]
      refine List.perm_append_comm.trans ?_
      simp only [List.cons_append, List.nil_append]
      exact List.Perm.cons _ List.perm_middle.symm

/-- **Leibniz rule in the position** for the terms of the expansion. -/
theorem spatialDeriv_leftTerm (l : Fin n) (a : Amplitude n V W m) (k : ℕ) :
    Symbol.spatialDeriv l (a.leftTerm k) =
      (spatialDerivFst l a).leftTerm k + (spatialDerivSnd l a).leftTerm k := by
  induction k generalizing m with
  | zero => simp [leftTerm_zero, spatialDeriv_diagonal]
  | succ k ih =>
    rw [leftTerm_succ, leftTerm_succ, leftTerm_succ, Symbol.spatialDeriv_inclusion, map_smul,
      map_sum, ← map_add, ← smul_add, ← Finset.sum_add_distrib]
    congr 2
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [ih, spatialDerivFst_spatialDerivSnd_comm, spatialDerivFst_frequencyDeriv_comm,
      spatialDerivSnd_comm l j, spatialDerivSnd_frequencyDeriv_comm l j]

/-- **Leibniz rule in the frequency** for the terms of the expansion. The orders of the two sides
differ by their presentation, so the rule is stated for their coefficients. -/
theorem coefficient_frequencyDeriv_leftTerm (l : Fin n) (a : Amplitude n V W m) (k : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (Symbol.frequencyDeriv l (a.leftTerm k)).coefficient p =
      ((frequencyDeriv l a).leftTerm k).coefficient p := by
  induction k generalizing m with
  | zero =>
    obtain ⟨x, ξ⟩ := p
    simp [leftTerm_zero, frequencyDeriv_diagonal]
  | succ k ih =>
    simp only [leftTerm_succ, Symbol.frequencyDeriv_inclusion, map_smul, map_sum,
      Symbol.coefficient_inclusion, Symbol.coefficient_smul, Symbol.coefficient_sum, Pi.smul_apply,
      Finset.sum_apply]
    refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
    rw [ih, ← spatialDerivSnd_frequencyDeriv_comm, frequencyDeriv_comm]

end Term

/-! ### The interpolating family `c_t` -/

section Scaled

variable {a : Amplitude n V W m}

variable (a) in
/-- The family `c_t(x, ξ) = ∫ exp(2πi ⟪θ, x⟫) â(x, θ, ξ + 2π t θ) dθ` interpolating between the
restriction of `a` to the diagonal (`t = 0`) and its left symbol (`t = 1`). -/
private def scaledLeft (t : ℝ) (x ξ : CoordinateSpace n) : V →L[ℂ] W :=
  ∫ θ, leftIntegrand a (t * (2 * π)) (x, ξ) θ

/-- The frequency shifts `2π t θ` of the family with `|t| ≤ 2` are at most `4π ‖θ‖`. -/
private theorem abs_mul_two_pi_le {t : ℝ} (ht : |t| ≤ 2) : |t * (2 * π)| ≤ 4 * π := by
  rw [abs_mul, abs_of_pos Real.two_pi_pos]
  nlinarith [Real.pi_pos]

/-- `‖c_t(x, ξ)‖ ≤ C ⟨ξ⟩ ^ m`, uniformly for `|t| ≤ 2` and positions in a compact set. -/
private theorem exists_norm_scaledLeft_le (ha : a.HasCompactInputSupport)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ 2 → ∀ x ∈ K, ∀ ξ,
      ‖scaledLeft a t x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_leftIntegrand_le hK (R := 4 * π)
    (by linarith [Real.two_le_pi])
  set I := ∫ θ : CoordinateSpace n, (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  have hI : 0 ≤ I := integral_nonneg fun θ ↦ by positivity
  refine ⟨C * I, mul_nonneg hC0 hI, fun t ht x hx ξ ↦ ?_⟩
  refine (norm_integral_le_of_norm_le ((integrable_rpow_neg_one_add_norm_sq (by simp)).const_mul
    (C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)))
    (.of_forall fun θ ↦ hC _ (abs_mul_two_pi_le ht) x hx ξ θ)).trans_eq ?_
  rw [integral_const_mul]
  ring

/-- At `t = 1` the family is the left symbol. -/
private theorem scaledLeft_one (ha : a.HasCompactInputSupport) (x ξ : CoordinateSpace n) :
    scaledLeft a 1 x ξ = (a.leftSymbol ha).coefficient (x, ξ) := by
  simp only [scaledLeft, leftIntegrand_apply, one_mul, coefficient_leftSymbol]

/-- At `t = 0` the family is the restriction of `a` to the diagonal, by Fourier inversion in the
input position. -/
private theorem scaledLeft_zero [CompleteSpace W] (ha : a.HasCompactInputSupport)
    (x ξ : CoordinateSpace n) :
    scaledLeft a 0 x ξ = a.coefficient (x, x, ξ) := by
  set f : CoordinateSpace n → V →L[ℂ] W := fun y ↦ a.coefficient (x, y, ξ)
  have hsmooth : ContDiff ℝ ∞ f := a.contDiff_coefficient.comp (by fun_prop)
  set g := (ha.hasCompactSupport_slice x ξ).toSchwartzMap hsmooth
  have hg : ⇑g = f := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  have h : scaledLeft a 0 x ξ = ∫ θ, 𝐞 ⟪θ, x⟫ • 𝓕 f θ := by
    simp only [scaledLeft, leftIntegrand_apply, zero_mul, zero_smul, add_zero, Circle.smul_def, f]
  rw [h, ← hg, ← SchwartzMap.fourier_coe, ← Real.fourierInv_eq, ← SchwartzMap.fourierInv_coe,
    fourierInv_fourier_eq, hg]

/-- **Differentiation in the parameter** of the integrand: since
`2π θⱼ ∂_{ξ_j} â = -i (∂_{y_j} ∂_{ξ_j} a)^`, `d/dt` of the integrand of `c_t(a)` is `-i ∑ⱼ` the
integrand of `c_t(∂_{y_j} ∂_{ξ_j} a)`. -/
private theorem hasDerivAt_leftIntegrand (ha : a.HasCompactInputSupport) (t : ℝ)
    (x ξ θ : CoordinateSpace n) :
    HasDerivAt (fun t ↦ leftIntegrand a (t * (2 * π)) (x, ξ) θ)
      (∑ j, (-Complex.I) •
        leftIntegrand (spatialDerivSnd j (frequencyDeriv j a)) (t * (2 * π)) (x, ξ) θ) t := by
  set c : CoordinateSpace n := (2 * π) • θ
  set g : CoordinateSpace n → V →L[ℂ] W := fun ζ ↦ 𝓕 (fun y ↦ a.coefficient (x, y, ζ)) θ
  set ζ₀ := ξ + (t * (2 * π)) • θ
  have hg : HasFDerivAt g ((∫ y, (𝐞 (-⟪y, θ⟫) : ℂ) • fderiv ℝ
      (fun q : CoordinateSpace n × CoordinateSpace n ↦ a.coefficient (q.1, y, q.2)) (x, ζ₀)).comp
        (ContinuousLinearMap.inr ℝ (CoordinateSpace n) (CoordinateSpace n))) ζ₀ :=
    (ha.hasFDerivAt_fourier_slice θ (x, ζ₀)).comp ζ₀ (hasFDerivAt_prodMk_right x ζ₀)
  have hl : HasDerivAt (fun t : ℝ ↦ ξ + (t * (2 * π)) • θ) c t := by
    simpa using (((hasDerivAt_id t).mul_const (2 * π)).smul_const θ).const_add ξ
  have h := (hg.comp_hasDerivAt t hl).const_smul (𝐞 ⟪θ, x⟫ : ℂ)
  refine (h.congr_of_eventuallyEq (.of_forall fun s ↦ ?_)).congr_deriv ?_
  · simp only [leftIntegrand_apply, Pi.smul_apply, Function.comp_apply, g]
  rw [ContinuousLinearMap.apply_eq_sum_single _ c, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [leftIntegrand_apply, (ha.frequencyDeriv j).fourier_spatialDerivSnd_slice,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    ha.fderiv_fourier_slice_apply]
  simp only [coefficient_frequencyDeriv, c, PiLp.smul_apply, smul_eq_mul, smul_smul]
  rw [← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  linear_combination (↑(𝐞 ⟪θ, x⟫) * 2 * ↑π * ↑(θ.ofLp j) : ℂ) * Complex.I_sq

/-- **Differentiation in the parameter** under the integral sign:
`d/dt c_t(a) = -i ∑ⱼ c_t(∂_{y_j} ∂_{ξ_j} a)`. -/
private theorem hasDerivAt_scaledLeft (ha : a.HasCompactInputSupport) {t₀ : ℝ} (ht₀ : |t₀| ≤ 1)
    (x ξ : CoordinateSpace n) :
    HasDerivAt (fun t ↦ scaledLeft a t x ξ)
      (∑ j, (-Complex.I) • scaledLeft (spatialDerivSnd j (frequencyDeriv j a)) t₀ x ξ) t₀ := by
  have hb (j : Fin n) : (spatialDerivSnd j (frequencyDeriv j a)).HasCompactInputSupport :=
    (ha.frequencyDeriv j).spatialDerivSnd j
  choose C _ hC using fun j ↦ (hb j).exists_norm_leftIntegrand_le
    (isCompact_singleton (x := x)) (R := 4 * π) (by linarith [Real.two_le_pi])
  have hball : ∀ t ∈ Metric.ball t₀ 1, |t * (2 * π)| ≤ 4 * π := fun t ht ↦ by
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have := abs_sub_abs_le_abs_sub t t₀
    exact abs_mul_two_pi_le (by linarith)
  set F' : ℝ → CoordinateSpace n → V →L[ℂ] W := fun t θ ↦
    ∑ j, (-Complex.I) •
      leftIntegrand (spatialDerivSnd j (frequencyDeriv j a)) (t * (2 * π)) (x, ξ) θ
  set bound : CoordinateSpace n → ℝ := fun θ ↦
    (∑ j, C j * (1 + ‖ξ‖ ^ 2) ^ ((m - 1) / 2)) * (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  have hint (j : Fin n) : Integrable fun θ ↦ (-Complex.I) •
      leftIntegrand (spatialDerivSnd j (frequencyDeriv j a)) (t₀ * (2 * π)) (x, ξ) θ :=
    ((hb j).integrable_leftIntegrand _ _).fun_smul _
  have hmeas : ∀ᶠ t in nhds t₀, AEStronglyMeasurable (leftIntegrand a (t * (2 * π)) (x, ξ))
      (volume : Measure (CoordinateSpace n)) :=
    .of_forall fun t ↦ (ha.continuous_leftIntegrand _ _).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable (F' t₀) (volume : Measure (CoordinateSpace n)) :=
    (continuous_finsetSum _ fun j _ ↦
      ((hb j).continuous_leftIntegrand _ _).const_smul (-Complex.I)).aestronglyMeasurable
  have hbound : ∀ᵐ θ ∂(volume : Measure (CoordinateSpace n)), ∀ t ∈ Metric.ball t₀ 1,
      ‖F' t θ‖ ≤ bound θ := .of_forall fun θ t ht ↦ by
    simp only [F', bound, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
    exact hC j _ (hball t ht) x rfl ξ θ
  have hdiff : ∀ᵐ θ ∂(volume : Measure (CoordinateSpace n)), ∀ t ∈ Metric.ball t₀ 1,
      HasDerivAt (fun t ↦ leftIntegrand a (t * (2 * π)) (x, ξ) θ) (F' t θ) t :=
    .of_forall fun θ t _ ↦ hasDerivAt_leftIntegrand ha t x ξ θ
  obtain ⟨-, h⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds t₀ one_pos) hmeas (ha.integrable_leftIntegrand _ _) hF'meas
    hbound ((integrable_rpow_neg_one_add_norm_sq (r := n + 1) (by simp)).const_mul _) hdiff
  refine h.congr_deriv ?_
  simp only [F']
  rw [integral_finsetSum _ fun j _ ↦ hint j]
  simp only [integral_smul, scaledLeft]

end Scaled

/-! ### The remainder of the expansion along the family -/

section Remainder

variable {a : Amplitude n V W m}

variable (a) in
/-- The remainder `c_t(a) - ∑_{k < N} t^k leftTerm a k` of the expansion along the interpolating
family. -/
private def remainderAt (N : ℕ) (t : ℝ) (x ξ : CoordinateSpace n) : V →L[ℂ] W :=
  scaledLeft a t x ξ - ∑ k ∈ range N, t ^ k • (a.leftTerm k).coefficient (x, ξ)

/-- The derivative of the polynomial part `∑_{k < N + 1} t^k leftTerm a k` is given by the
recursion defining `leftTerm`. -/
private theorem hasDerivAt_sum_pow_smul_leftTerm (N : ℕ) (a : Amplitude n V W m)
    (x ξ : CoordinateSpace n) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ ∑ k ∈ range (N + 1), t ^ k • (a.leftTerm k).coefficient (x, ξ))
      (∑ k ∈ range N, t ^ k • ((-Complex.I) •
        ∑ j, ((spatialDerivSnd j (frequencyDeriv j a)).leftTerm k).coefficient (x, ξ))) t := by
  have h := HasDerivAt.fun_sum (u := range (N + 1)) fun k _ ↦
    (hasDerivAt_pow k t).smul_const ((a.leftTerm k).coefficient (x, ξ))
  refine h.congr_deriv ?_
  rw [Finset.sum_range_succ']
  simp only [CharP.cast_eq_zero, zero_mul, zero_smul, add_zero]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [coefficient_leftTerm_succ, Nat.add_sub_cancel, mul_comm, mul_smul]
  congr 1
  rw [← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  field_simp

/-- The derivative in `t` of the remainder with `N + 1` terms is `-i ∑ⱼ` the remainders with `N`
terms of `∂_{y_j} ∂_{ξ_j} a`. -/
private theorem hasDerivAt_remainderAt (ha : a.HasCompactInputSupport) (N : ℕ) {t : ℝ}
    (ht : |t| ≤ 1) (x ξ : CoordinateSpace n) :
    HasDerivAt (fun t ↦ remainderAt a (N + 1) t x ξ)
      ((-Complex.I) • ∑ j, remainderAt (spatialDerivSnd j (frequencyDeriv j a)) N t x ξ) t := by
  refine ((hasDerivAt_scaledLeft ha ht x ξ).fun_sub
    (hasDerivAt_sum_pow_smul_leftTerm N a x ξ t)).congr_deriv ?_
  simp only [remainderAt, smul_sub, Finset.smul_sum, Finset.sum_sub_distrib, smul_comm (t ^ _)]
  rw [Finset.sum_comm]

/-- The remainder vanishes at `t = 0`. -/
private theorem remainderAt_zero [CompleteSpace W] (ha : a.HasCompactInputSupport) (N : ℕ)
    (x ξ : CoordinateSpace n) :
    remainderAt a (N + 1) 0 x ξ = 0 := by
  rw [remainderAt, scaledLeft_zero ha, Finset.sum_range_succ']
  simp

/-- **The remainder estimate.** `‖c_t(a) - ∑_{k < N} t^k leftTerm a k‖ ≤ C ⟨ξ⟩ ^ (m - N)`,
uniformly for `t ∈ [0, 1]` and positions in a compact set. -/
private theorem exists_norm_remainderAt_le [CompleteSpace W] (N : ℕ) :
    ∀ {m : ℝ} {a : Amplitude n V W m}, a.HasCompactInputSupport →
      ∀ {K : Set (CoordinateSpace n)}, IsCompact K → ∃ C, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ x ∈ K, ∀ ξ, ‖remainderAt a N t x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - N) / 2) := by
  induction N with
  | zero =>
    intro m a ha K hK
    obtain ⟨C, hC0, hC⟩ := exists_norm_scaledLeft_le ha hK
    refine ⟨C, hC0, fun t ht x hx ξ ↦ ?_⟩
    have ht2 : |t| ≤ 2 := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa [remainderAt] using hC t ht2 x hx ξ
  | succ N ih =>
    intro m a ha K hK
    choose C hC0 hC using fun j ↦ ih ((ha.frequencyDeriv j).spatialDerivSnd j) hK
    refine ⟨∑ j, C j, Finset.sum_nonneg fun j _ ↦ hC0 j, fun t ht x hx ξ ↦ ?_⟩
    have hw : (1 + ‖ξ‖ ^ 2) ^ ((m - 1 - N) / 2) =
        (1 + ‖ξ‖ ^ 2) ^ ((m - ((N + 1 : ℕ) : ℝ)) / 2) := by
      congr 1
      push_cast
      ring
    have hbound : ∀ s ∈ Set.Ico (0 : ℝ) 1,
        ‖(-Complex.I) • ∑ j, remainderAt (spatialDerivSnd j (frequencyDeriv j a)) N s x ξ‖ ≤
          (∑ j, C j) * (1 + ‖ξ‖ ^ 2) ^ ((m - ((N + 1 : ℕ) : ℝ)) / 2) := by
      intro s hs
      rw [norm_smul, norm_neg, Complex.norm_I, one_mul, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
      rw [← hw]
      exact hC j s (Set.Ico_subset_Icc_self hs) x hx ξ
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s hs ↦ (hasDerivAt_remainderAt ha N (abs_le.2 ⟨by linarith [hs.1], hs.2⟩) x
        ξ).hasDerivWithinAt) hbound t ht
    rw [remainderAt_zero ha, sub_zero, sub_zero] at hmv
    have hB : 0 ≤ (∑ j, C j) * (1 + ‖ξ‖ ^ 2) ^ ((m - ((N + 1 : ℕ) : ℝ)) / 2) :=
      mul_nonneg (Finset.sum_nonneg fun j _ ↦ hC0 j) (by positivity)
    exact hmv.trans (mul_le_of_le_one_right hB ht.2)

end Remainder

/-! ### The remainder symbol -/

section Symbol

variable {a : Amplitude n V W m}

/-- The remainder `c - ∑_{k < N} leftTerm a k`, as a symbol of order `m`. -/
private def remainderSymbol (ha : a.HasCompactInputSupport) (N : ℕ) : Symbol n V W m :=
  a.leftSymbol ha -
    ∑ k ∈ range N, Symbol.inclusion (sub_le_self _ (Nat.cast_nonneg k)) (a.leftTerm k)

private theorem coefficient_remainderSymbol (ha : a.HasCompactInputSupport) (N : ℕ)
    (x ξ : CoordinateSpace n) :
    (remainderSymbol ha N).coefficient (x, ξ) = remainderAt a N 1 x ξ := by
  simp [remainderSymbol, remainderAt, scaledLeft_one ha]

private theorem spatialDeriv_remainderSymbol (ha : a.HasCompactInputSupport) (N : ℕ)
    (j : Fin n) :
    Symbol.spatialDeriv j (remainderSymbol ha N) =
      remainderSymbol (ha.spatialDerivFst j) N + remainderSymbol (ha.spatialDerivSnd j) N := by
  simp only [remainderSymbol, map_sub, map_sum, spatialDeriv_leftSymbol,
    Symbol.spatialDeriv_inclusion, spatialDeriv_leftTerm, map_add, Finset.sum_add_distrib]
  abel

private theorem coefficient_frequencyDeriv_remainderSymbol (ha : a.HasCompactInputSupport)
    (N : ℕ) (j : Fin n) :
    (Symbol.frequencyDeriv j (remainderSymbol ha N)).coefficient =
      (remainderSymbol (ha.frequencyDeriv j) N).coefficient := by
  funext p
  simp only [remainderSymbol, map_sub, map_sum, Symbol.coefficient_sub, Symbol.coefficient_sum,
    Symbol.frequencyDeriv_inclusion, Symbol.coefficient_inclusion, Pi.sub_apply, Finset.sum_apply,
    frequencyDeriv_leftSymbol, coefficient_frequencyDeriv_leftTerm]

/-- The symbol estimates of order `m - N` for the remainder, from the Leibniz rules. -/
private theorem exists_bound_remainderSymbol [CompleteSpace W] (ha : a.HasCompactInputSupport)
    (N : ℕ) (α β : List (Fin n)) {K : Set (CoordinateSpace n)} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ‖mixedDeriv α β (remainderSymbol ha N).coefficient x ξ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m - N - β.length) / 2) :=
  exists_norm_mixedDeriv_le_of_leibniz N HasCompactInputSupport
    (fun ha j ↦ ha.spatialDerivFst j) (fun ha j ↦ ha.spatialDerivSnd j)
    (fun ha j ↦ ha.frequencyDeriv j) (fun _ ha ↦ (remainderSymbol ha N).coefficient)
    (fun _ ha ↦ (remainderSymbol ha N).contDiff_coefficient)
    (fun _ ha j x ξ ↦ by
      rw [← Symbol.coefficient_spatialDeriv, spatialDeriv_remainderSymbol, Symbol.coefficient_add,
        Pi.add_apply])
    (fun _ ha j x ξ ↦ by
      rw [← Symbol.coefficient_frequencyDeriv, coefficient_frequencyDeriv_remainderSymbol])
    (fun _ ha _ hK ↦ by
      obtain ⟨C, hC0, hC⟩ := exists_norm_remainderAt_le N ha hK
      exact ⟨C, hC0, fun x hx ξ ↦ by
        simpa [coefficient_remainderSymbol] using hC 1 ⟨zero_le_one, le_rfl⟩ x hx ξ⟩)
    a ha α β hK

variable [CompleteSpace W]

variable (a) in
/-- The remainder `c - ∑_{k < N} leftTerm a k` of the expansion of the left symbol `c` of `a`
after `N` terms, a symbol of order `m - N` (`leftSymbol_eq_sum_leftTerm_add_leftRemainder`). -/
def leftRemainder (ha : a.HasCompactInputSupport) (N : ℕ) : Symbol n V W (m - N) where
  coefficient := (remainderSymbol ha N).coefficient
  contDiff_coefficient := (remainderSymbol ha N).contDiff_coefficient
  exists_bound _ hK α β := exists_bound_remainderSymbol ha N α β hK

@[simp]
theorem coefficient_leftRemainder (ha : a.HasCompactInputSupport) (N : ℕ) :
    (a.leftRemainder ha N).coefficient =
      (a.leftSymbol ha).coefficient - ∑ k ∈ range N, (a.leftTerm k).coefficient := by
  simp [leftRemainder, remainderSymbol]

/-- **The asymptotic expansion of the left symbol of an amplitude.** For an amplitude `a` of order
`m` with compact input support and every `N`,
`a.leftSymbol ha = ∑_{k < N} leftTerm a k + leftRemainder a ha N`, where `leftTerm a k` is the
term `((-i)^k / k!) ∑_{|w| = k} (∂_y^w ∂_ξ^w a)(x, x, ξ)` of order `m - k` and the remainder is a
symbol of order `m - N`. -/
theorem leftSymbol_eq_sum_leftTerm_add_leftRemainder (ha : a.HasCompactInputSupport) (N : ℕ) :
    a.leftSymbol ha =
      ∑ k ∈ range N, Symbol.inclusion (sub_le_self _ (Nat.cast_nonneg k)) (a.leftTerm k) +
        Symbol.inclusion (sub_le_self _ (Nat.cast_nonneg N)) (a.leftRemainder ha N) := by
  ext1
  simp

/-- The left symbol of an amplitude `a` agrees with its restriction `a(x, x, ξ)` to the diagonal
up to a symbol of order `m - 1`. -/
theorem leftSymbol_eq_diagonal_add_leftRemainder_one (ha : a.HasCompactInputSupport) :
    a.leftSymbol ha = a.diagonal + Symbol.inclusion (by simp) (a.leftRemainder ha 1) := by
  ext1
  funext p
  simp [leftTerm_zero]

/-- The left symbol of an amplitude `a` is an asymptotic sum of the terms `leftTerm a k` of order
`m - k`. -/
theorem isAsymptoticSum_leftSymbol (ha : a.HasCompactInputSupport) :
    (Symbol.inclusion (by simp) (a.leftSymbol ha) :
      Symbol n V W (m - ((0 : ℕ) : ℝ))).IsAsymptoticSum a.leftTerm :=
  Symbol.isAsymptoticSum_iff.2 fun N ↦ ⟨a.leftRemainder ha N, by simp⟩

end Symbol

end Amplitude

end TauCeti
