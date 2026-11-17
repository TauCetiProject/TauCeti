/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Basic

import Mathlib.Analysis.Calculus.SmoothSeries
import TauCeti.Analysis.Fourier.Monomial

/-!
# The derivative on the circle Sobolev spaces

Differentiating the Fourier monomial `e^{2πinx/T}` on the circle `AddCircle T` multiplies it by
`2πin/T`. On the Fourier-coefficient Sobolev spaces `H^s` of
`TauCeti/Analysis/Sobolev/Circle/Basic.lean`, differentiation is therefore the operator that
multiplies the `n`-th coefficient by `2πin/T`. Since `|n| (1 + |n|) ^ s ≤ (1 + |n|) ^ (s + 1)`, it
is a bounded operator `H^t → H^s` as soon as `s + 1 ≤ t`: differentiation costs exactly one order
of regularity, for every real order, including fractional and negative orders.

For `s > 1/2` the elements of `H^s` are continuous functions. If moreover `s + 1 ≤ t`, then the
continuous representative of `a ∈ H^t` is differentiable in the classical sense, and its derivative
is the continuous representative of the element of `H^s` given by this operator. The loss of one
order is what governs the differentiability of reparametrizations of boundary maps (see
`TauCeti/Analysis/Sobolev/Circle/Rotation.lean`).

## Main definitions

* `TauCeti.CircleSobolev.derivative T h`: for `h : s + 1 ≤ t`, the bounded operator
  `H^t → H^s` multiplying the `n`-th Fourier coefficient by `2πin/T`.

## Main statements

* `TauCeti.CircleSobolev.norm_derivative_le`: `‖derivative T h a‖ ≤ 2π/T ‖a‖`.
* `TauCeti.CircleSobolev.norm_sq_le_of_derivative`: conversely, the `H^(s + 1)` norm is
  controlled by the `H^s` norms of a function and of its derivative.
* `TauCeti.CircleSobolev.derivative_eq_zero_iff`: the kernel of the derivative consists of the
  constant functions.
* `TauCeti.CircleSobolev.bijective_derivative_add_inclusion`: `ζ ↦ ζ' + ζ` is a bijection
  `H^(s + 1) → H^s`, since it multiplies the `n`-th Fourier coefficient by the nonvanishing factor
  `1 + 2πin/T`; `TauCeti.CircleSobolev.derivativeAddInclusionEquiv` is the resulting continuous
  linear equivalence, whose inverse divides the coefficients by that factor
  (`TauCeti.CircleSobolev.coeff_derivativeAddInclusionEquiv_symm`).
* `TauCeti.CircleSobolev.hasDerivAt_toContinuousMap`: for `s > 1/2`, the continuous representative
  of `a ∈ H^t` is differentiable, with derivative the continuous representative of
  `derivative T h a`.
* `TauCeti.CircleSobolev.inner_derivative_inclusion`: integration by parts, `⟪a', b⟫ = -⟪a, b'⟫`
  in `H^s`.

## References

* M. E. Taylor, *Partial Differential Equations I*, Chapter 3 (Sobolev spaces on the torus via
  Fourier series).
-/

public section

noncomputable section

open Complex Filter Topology Real

namespace TauCeti

namespace CircleSobolev

variable {s t : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (T : ℝ) [hT : Fact (0 < T)]

/-- The derivative factor costs one order of regularity: for `s + 1 ≤ t`,
`(1 + |n|) ^ s |2πin/T| ≤ 2π/T (1 + |n|) ^ t`. -/
private theorem weight_mul_norm_derivFactor_le (h : s + 1 ≤ t) (n : ℤ) (x : E) :
    weight s n * ‖(2 * π * I * n / T : ℂ) • x‖ ≤ 2 * π / T * (weight t n * ‖x‖) := by
  have hw : weight s n * |(n : ℝ)| ≤ weight t n := by
    calc weight s n * |(n : ℝ)| ≤ weight s n * (1 + |(n : ℝ)|) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (weight_nonneg s n)
      _ = weight (s + 1) n := by rw [weight_add, weight_def 1, Real.rpow_one]
      _ ≤ weight t n := weight_le_weight h n
  have hc : 0 ≤ 2 * π / T := div_nonneg (by positivity) hT.out.le
  rw [norm_smul, norm_two_pi_I_mul_intCast_div hT.out]
  calc weight s n * (2 * π / T * |(n : ℝ)| * ‖x‖)
        = 2 * π / T * (weight s n * |(n : ℝ)| * ‖x‖) := by ring
    _ ≤ 2 * π / T * (weight t n * ‖x‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw (norm_nonneg x)) hc

/-- For `s + 1 ≤ t`, the derivative `H^t → H^s` on the circle `AddCircle T`: it multiplies the
`n`-th Fourier coefficient by `2πin/T`, the factor by which differentiation multiplies the
monomial `e^{2πinx/T}`. -/
def derivative (h : s + 1 ≤ t) : CircleSobolev t E →L[ℂ] CircleSobolev s E :=
  LinearMap.mkContinuous
    { toFun a := ⟨fun n ↦ (2 * π * I * n / T : ℂ) • a.coeff n,
        memℓp_of_forall_le fun n ↦ weight_mul_norm_derivFactor_le T h n (a.coeff n)⟩
      map_add' a b := CircleSobolev.ext (funext fun n ↦ smul_add _ (a.coeff n) (b.coeff n))
      map_smul' c a := CircleSobolev.ext (funext fun n ↦ smul_comm _ c (a.coeff n)) }
    (2 * π / T) fun a ↦ norm_le_of_forall_le (C := 2 * π / T)
      fun n ↦ weight_mul_norm_derivFactor_le T h n (a.coeff n)

@[simp]
theorem coeff_derivative (h : s + 1 ≤ t) (a : CircleSobolev t E) (n : ℤ) :
    (derivative T h a).coeff n = (2 * π * I * n / T : ℂ) • a.coeff n :=
  (rfl)

/-- Differentiation costs one order of regularity: `‖derivative T h a‖ ≤ 2π/T ‖a‖`. -/
theorem norm_derivative_le (h : s + 1 ≤ t) (a : CircleSobolev t E) :
    ‖derivative T h a‖ ≤ 2 * π / T * ‖a‖ :=
  norm_le_of_forall_le fun n ↦ weight_mul_norm_derivFactor_le T h n (a.coeff n)

theorem opNorm_derivative_le (h : s + 1 ≤ t) :
    ‖(derivative T h : CircleSobolev t E →L[ℂ] CircleSobolev s E)‖ ≤ 2 * π / T :=
  ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (by positivity) hT.out.le)
    (norm_derivative_le T h)

/-- Conversely, for `t = s + 1` the norm of `H^t` is controlled by the `H^s` norms of a function
and of its derivative: `‖a‖² ≤ 2 ‖a‖²_{H^s} + 2 (T/2π)² ‖a'‖²_{H^s}`. -/
theorem norm_sq_le_of_derivative (h : s + 1 = t) (a : CircleSobolev t E) :
    ‖a‖ ^ 2 ≤ 2 * ‖inclusion (show s ≤ t by linarith) a‖ ^ 2 +
      2 * (T / (2 * π)) ^ 2 * ‖derivative T h.le a‖ ^ 2 := by
  subst h
  refine hasSum_le (fun n ↦ ?_) (hasSum_sq_weight_mul_norm_coeff a)
    (((hasSum_sq_weight_mul_norm_coeff (inclusion (show s ≤ s + 1 by linarith) a)).mul_left 2).add
      ((hasSum_sq_weight_mul_norm_coeff (derivative T le_rfl a)).mul_left
        (2 * (T / (2 * π)) ^ 2)))
  have hk : T / (2 * π) * (2 * π / T) = 1 := by
    field_simp [hT.out.ne']
  rw [coeff_inclusion, coeff_derivative, norm_smul, norm_two_pi_I_mul_intCast_div hT.out,
    weight_add, weight_def 1, Real.rpow_one]
  calc (weight s n * (1 + |(n : ℝ)|) * ‖a.coeff n‖) ^ 2
      = (weight s n * ‖a.coeff n‖) ^ 2 * (1 + |(n : ℝ)|) ^ 2 := by ring
    _ ≤ (weight s n * ‖a.coeff n‖) ^ 2 * (2 * (1 + |(n : ℝ)| ^ 2)) := by
        gcongr
        nlinarith [sq_nonneg (1 - |(n : ℝ)|)]
    _ = 2 * (weight s n * ‖a.coeff n‖) ^ 2 + 2 * (T / (2 * π)) ^ 2 *
          (weight s n * (2 * π / T * |(n : ℝ)| * ‖a.coeff n‖)) ^ 2 := by
        linear_combination (-2 * (weight s n * ‖a.coeff n‖) ^ 2 * |(n : ℝ)| ^ 2 *
          (T / (2 * π) * (2 * π / T) + 1)) * hk

@[simp]
theorem derivative_single (h : s + 1 ≤ t) (n : ℤ) (x : E) :
    derivative T h (single n x) = single n ((2 * π * I * n / T : ℂ) • x) :=
  CircleSobolev.ext (funext fun m ↦ by
    rcases eq_or_ne m n with rfl | hm
    · simp
    · simp [hm])

@[simp]
theorem derivative_inclusion {u : ℝ} (h : s + 1 ≤ t) (htu : t ≤ u) (a : CircleSobolev u E) :
    derivative T h (inclusion htu a) = derivative T (h.trans htu) a :=
  CircleSobolev.ext (funext fun n ↦ by simp)

@[simp]
theorem inclusion_derivative {r : ℝ} (hrs : r ≤ s) (h : s + 1 ≤ t) (a : CircleSobolev t E) :
    inclusion hrs (derivative T h a) = derivative T (by linarith) a :=
  CircleSobolev.ext (funext fun n ↦ by simp)

/-- The kernel of the derivative consists of the constant functions: `derivative T h a = 0`
exactly when every Fourier coefficient of `a` other than the zeroth one vanishes. -/
theorem derivative_eq_zero_iff (h : s + 1 ≤ t) (a : CircleSobolev t E) :
    derivative T h a = 0 ↔ a = single 0 (a.coeff 0) := by
  refine ⟨fun ha ↦ CircleSobolev.ext (funext fun n ↦ ?_), fun ha ↦ ?_⟩
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hc : (2 * π * I * n / T : ℂ) ≠ 0 := by
        have := hT.out.ne'
        simp [hn, Real.pi_ne_zero, I_ne_zero, this]
      have := congr_arg (fun b : CircleSobolev s E ↦ b.coeff n) ha
      simpa [hn, hc] using this
  · rw [ha, derivative_single]
    simp

/-- Conversely, an element of `H^s` whose formal derivative lies in `H^s` lies in `H^(s + 1)`: if
the sequence `2πin/T • a.coeff n` is the coefficient sequence of some `b ∈ H^s`, then `a` comes from
an element of `H^(s + 1)` whose derivative is `b`. -/
theorem exists_inclusion_eq_and_derivative_eq (a b : CircleSobolev s E)
    (hb : ∀ n, b.coeff n = (2 * π * I * n / T : ℂ) • a.coeff n) :
    ∃ c : CircleSobolev (s + 1) E, inclusion (by linarith) c = a ∧ derivative T le_rfl c = b := by
  have _ : 0 < 2 * π / T := div_pos (by positivity) hT.out
  -- `(1 + |n|) ^ (s + 1) ‖a_n‖ = (1 + |n|) ^ s ‖a_n‖ + (1 + |n|) ^ s |n| ‖a_n‖`, and the last
  -- term is `T / 2π` times `(1 + |n|) ^ s ‖b_n‖`.
  have hle (n : ℤ) : weight (s + 1) n * ‖a.coeff n‖ ≤
      weight s n * ‖a.coeff n‖ + (2 * π / T)⁻¹ * (weight s n * ‖b.coeff n‖) := by
    rw [hb, norm_smul, norm_two_pi_I_mul_intCast_div hT.out, weight_add, weight_def 1,
      Real.rpow_one]
    refine le_of_eq ?_
    field_simp [hT.out.ne']
  have hsum : Summable fun n ↦ (weight (s + 1) n * ‖a.coeff n‖) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun n ↦ sq_nonneg _) (fun n ↦ ?_)
      (((hasSum_sq_weight_mul_norm_coeff a).summable.mul_left 2).add
        ((hasSum_sq_weight_mul_norm_coeff b).summable.mul_left (2 * ((2 * π / T)⁻¹) ^ 2)))
    have h0 : 0 ≤ weight (s + 1) n * ‖a.coeff n‖ :=
      mul_nonneg (weight_nonneg _ n) (norm_nonneg _)
    nlinarith [hle n, sq_nonneg (weight s n * ‖a.coeff n‖ -
      (2 * π / T)⁻¹ * (weight s n * ‖b.coeff n‖))]
  refine ⟨⟨a.coeff, (memℓp_weight_smul_iff _).2 hsum⟩, CircleSobolev.ext (by simp),
    CircleSobolev.ext (funext fun n ↦ ?_)⟩
  rw [coeff_derivative, hb]

omit hT in
/-- The Fourier multiplier `1 + 2πin/T` of `ζ ↦ ζ' + ζ` does not vanish: its real part is `1`. -/
private theorem one_add_derivFactor_ne_zero (n : ℤ) : (1 + 2 * π * I * n / T : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [Complex.div_re] at this

omit hT in
/-- The Fourier multiplier `1 + 2πin/T` has modulus at least `1`. -/
private theorem one_le_norm_one_add_derivFactor (n : ℤ) : 1 ≤ ‖(1 + 2 * π * I * n / T : ℂ)‖ := by
  refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
  simp [Complex.div_re]

/-- **`ζ ↦ ζ' + ζ` is a bijection `H^(s + 1) → H^s`.** It multiplies the `n`-th Fourier
coefficient by `1 + 2πin/T`, which never vanishes. -/
theorem bijective_derivative_add_inclusion (h : s + 1 = t) :
    Function.Bijective
      (derivative T h.le + inclusion (by linarith) :
        CircleSobolev t E →L[ℂ] CircleSobolev s E) := by
  subst h
  refine ⟨fun a b hab ↦ CircleSobolev.ext (funext fun n ↦ ?_), fun b ↦ ?_⟩
  · have hn := congrArg (fun c : CircleSobolev s E ↦ c.coeff n) hab
    simp only [add_apply, coeff_add, Pi.add_apply, coeff_derivative, coeff_inclusion] at hn
    refine smul_right_injective E (one_add_derivFactor_ne_zero T n) ?_
    simp only [add_smul, one_smul]
    rw [add_comm (a.coeff n), hn, add_comm]
  · -- Divide the coefficients of `b` by `1 + 2πin/T`, then recover one order of regularity.
    set c : ℤ → ℂ := fun n ↦ (1 + 2 * π * I * n / T : ℂ)⁻¹
    have hc (n : ℤ) : ‖c n‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ (one_le_norm_one_add_derivFactor T n)
    let a : CircleSobolev s E := ⟨fun n ↦ c n • b.coeff n, memℓp_of_forall_le (C := 1) fun n ↦ by
      rw [norm_smul, one_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) (hc n))
        (weight_nonneg s n)⟩
    obtain ⟨d, hda, hdb⟩ := exists_inclusion_eq_and_derivative_eq T a (b - a) fun n ↦ by
      have hne := one_add_derivFactor_ne_zero T n
      simp only [coeff_sub, Pi.sub_apply, a, c, smul_smul]
      have key : (1 : ℂ) - (1 + 2 * π * I * n / T)⁻¹ =
          2 * π * I * n / T * (1 + 2 * π * I * n / T)⁻¹ := by
        field_simp
        ring
      rw [← key, sub_smul, one_smul]
    refine ⟨d, ?_⟩
    rw [add_apply, hdb, hda, sub_add_cancel]

/-- `ζ ↦ ζ' + ζ`, as a continuous linear equivalence `H^(s + 1) ≃ H^s`. -/
def derivativeAddInclusionEquiv [CompleteSpace E] (h : s + 1 = t) :
    CircleSobolev t E ≃L[ℂ] CircleSobolev s E :=
  ContinuousLinearEquiv.ofBijective (derivative T h.le + inclusion (by linarith))
    (LinearMap.ker_eq_bot.2 (bijective_derivative_add_inclusion T h).injective)
    (LinearMap.range_eq_top.2 (bijective_derivative_add_inclusion T h).surjective)

@[simp]
theorem coe_derivativeAddInclusionEquiv [CompleteSpace E] (h : s + 1 = t) :
    (derivativeAddInclusionEquiv (E := E) T h : CircleSobolev t E →L[ℂ] CircleSobolev s E) =
      derivative T h.le + inclusion (by linarith) :=
  ContinuousLinearEquiv.coe_ofBijective _ _ _

@[simp]
theorem derivativeAddInclusionEquiv_apply [CompleteSpace E] (h : s + 1 = t)
    (a : CircleSobolev t E) :
    derivativeAddInclusionEquiv T h a = derivative T h.le a + inclusion (by linarith) a :=
  (rfl)

/-- The inverse of `ζ ↦ ζ' + ζ` divides the `n`-th Fourier coefficient by `1 + 2πin/T`. -/
@[simp]
theorem coeff_derivativeAddInclusionEquiv_symm [CompleteSpace E] (h : s + 1 = t)
    (b : CircleSobolev s E) (n : ℤ) :
    ((derivativeAddInclusionEquiv T h).symm b).coeff n =
      (1 + 2 * π * I * n / T : ℂ)⁻¹ • b.coeff n := by
  have hb := congrArg (fun c : CircleSobolev s E ↦ c.coeff n)
    ((derivativeAddInclusionEquiv T h).apply_symm_apply b)
  simp only [derivativeAddInclusionEquiv_apply, coeff_add, Pi.add_apply, coeff_derivative,
    coeff_inclusion] at hb
  rw [eq_inv_smul_iff₀ (one_add_derivFactor_ne_zero T n), ← hb, add_smul, one_smul, add_comm]

/-- For `s > 1/2` and `s + 1 ≤ t`, the continuous representative `x ↦ a(x)` of `a ∈ H^t` is
differentiable as a function of `x : ℝ`, and its derivative is the continuous representative of
`derivative T h a`. -/
theorem hasDerivAt_toContinuousMap [CompleteSpace E] (hs : 1 / 2 < s) (h : s + 1 ≤ t)
    (a : CircleSobolev t E) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ toContinuousMap T (by linarith) a y)
      (toContinuousMap T hs (derivative T h a) x) x := by
  have ht : 1 / 2 < t := by linarith
  simp_rw [toContinuousMap_apply]
  have hder (n : ℤ) (y : ℝ) : HasDerivAt (fun z : ℝ ↦ fourier n (z : AddCircle T) • a.coeff n)
      ((2 * π * I * n / T * fourier n (y : AddCircle T)) • a.coeff n) y :=
    (hasDerivAt_fourier T n y).smul_const (a.coeff n)
  have hbound (n : ℤ) (y : ℝ) :
      ‖(2 * π * I * n / T * fourier n (y : AddCircle T)) • a.coeff n‖ ≤
        ‖(derivative T h a).coeff n‖ := by
    rw [coeff_derivative, mul_comm, ← smul_smul, norm_smul, fourier_apply, Circle.norm_coe,
      one_mul]
  convert hasDerivAt_tsum (y₀ := 0) (summable_norm_coeff hs (derivative T h a)) hder hbound
    ((summable_norm_coeff ht a).of_norm_bounded fun n ↦ by
      rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]) x using 1
  exact tsum_congr fun n ↦ by rw [coeff_derivative, smul_smul, mul_comm]

/-- **Integration by parts on the circle.** The derivative is skew-adjoint for the inner product
of `H^s`: `⟪a', b⟫ = -⟪a, b'⟫` for `a, b ∈ H^t` with `s + 1 ≤ t`, both regarded in `H^s`. On the
Fourier side, the factor `2πin/T` of the derivative is purely imaginary. -/
theorem inner_derivative_inclusion {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (h : s + 1 ≤ t) (a b : CircleSobolev t F) :
    inner ℂ (derivative T h a) (inclusion (by linarith) b) =
      -inner ℂ (inclusion (by linarith) a) (derivative T h b) := by
  rw [inner_eq_tsum, inner_eq_tsum, ← tsum_neg]
  refine tsum_congr fun n ↦ ?_
  simp only [coeff_derivative, coeff_inclusion, inner_smul_left, inner_smul_right, map_div₀,
    map_mul, map_ofNat, conj_ofReal, conj_I, map_intCast]
  ring

end CircleSobolev

end TauCeti
