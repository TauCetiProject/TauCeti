/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Derivative
public import TauCeti.Analysis.Sobolev.Circle.FourierMultiplier

/-!
# The Laplacian on the circle Sobolev spaces

On the circle `AddCircle T`, the Laplacian `Δ = -∂²` multiplies the Fourier monomial
`e^{2πinx/T}` by `λₙ = (2πn/T)²`. On the Fourier-coefficient Sobolev spaces `H^s` of
`TauCeti/Analysis/Sobolev/Circle/Basic.lean` it is therefore the operator `H^(s + 2) → H^s`
multiplying the `n`-th Fourier coefficient by `λₙ`, for every real order `s`. This file develops
its elliptic theory on the whole Sobolev scale. It is the simplest closed manifold on which the
statements of the elliptic theory on compact manifolds can be tested, including the features
that a correct general statement must reproduce: the kernel, the solvability condition, and the
lower-order term in the elliptic estimate.

* *Symbol and elliptic multiplier structure.* The symbol `λₙ = (2πn/T)²`
  (`CircleSobolev.laplacianSymbol`), which is `n²` on the circle of length `2π`, is elliptic of
  order `2` for every `T ≠ 0` (`CircleSobolev.isTheta_laplacianSymbol`), so `Δ` and its Green
  operator `G` are the elliptic Fourier multipliers of
  `TauCeti/Analysis/Sobolev/Circle/FourierMultiplier.lean` with symbols `λₙ` and `λₙ⁻¹`
  (`CircleSobolev.laplacian_eq_fourierMultiplier`,
  `CircleSobolev.greenOperator_eq_fourierMultiplier`), whose zero-mode projection is the
  projection onto the constants (`CircleSobolev.indicator_setOf_laplacianSymbol_eq_zero`).
  Note that `Δ = -∂²` here, so `λₙ ≥ 0` has the opposite sign to `TauCeti.laplacianSymbol`.
* *Kernel.* For `T ≠ 0`, `Δ a = 0` exactly when `a` is constant
  (`CircleSobolev.laplacian_eq_zero_iff`).
* *Green operator.* The Fourier multiplier `G` with symbol `λₙ⁻¹` for `n ≠ 0` and `0` for
  `n = 0` (`CircleSobolev.greenOperator`) gains two orders and, for `T ≠ 0`, inverts `Δ` up to
  the projection `Π a = single 0 (a.coeff 0)` onto the constants: `Δ G b = b - Π b` and
  `G Δ a = a - Π a`.
* *Solvability.* For `T ≠ 0`, `Δ a = b` has a solution `a ∈ H^(s + 2)` exactly when `b ∈ H^s`
  has mean zero, that is `b.coeff 0 = 0` (`CircleSobolev.exists_laplacian_eq_iff`). The constant
  mode is the obstruction: `Δ a = 1` has no solution (`CircleSobolev.laplacian_ne_single_zero`).
* *The invertible operator `1 + Δ = 1 - ∂²`.* For `T ≠ 0`, it multiplies the `n`-th coefficient
  by `1 + λₙ ≥ 1`, so it is an isomorphism `H^(s + 2) ≃ H^s` for every `s`, whose inverse has
  symbol `(1 + λₙ)⁻¹` on every mode, including `n = 0`
  (`CircleSobolev.laplacianAddInclusionEquiv`).
* *Fredholm property.* For finite-dimensional `E` and `T ≠ 0`, `Δ : H^(s + 2) → H^s` is a
  Fredholm operator as an elliptic Fourier multiplier (`CircleSobolev.isFredholm_laplacian`). For
  `T ≠ 0`, its kernel (the constants) and cokernel (detected by the mean) are both copies of `E`,
  so `finrank (ker Δ) = finrank (coker Δ)` and `Δ` has index zero
  (`CircleSobolev.index_laplacian`, which also holds at the degenerate value `T = 0` since
  `H^(s + 2) ≃ₗ H^s`). For finite-dimensional `E` and `T ≠ 0` this is the Fredholm index
  `dim E - dim E = 0`; for infinite-dimensional `E` both finranks are `0` by convention.
* *Elliptic estimate.* For `T ≠ 0`, `‖a‖_{H^(s+2)} ≤ (T/π)² ‖Δ a‖_{H^s} + ‖a‖_{H^r}` for every
  `r ≤ s + 2` (`CircleSobolev.norm_le_mul_norm_laplacian_add_norm_inclusion`). The lower-order
  term cannot be dropped, since constants are killed by `Δ`
  (`CircleSobolev.not_exists_forall_norm_le_mul_norm_laplacian`), but it can on the complement
  of the kernel, the elements of mean zero
  (`CircleSobolev.norm_le_mul_norm_laplacian_of_coeff_zero_eq_zero`).
* *Elliptic regularity.* For `T ≠ 0`, if `a ∈ H^t` and `Δ a ∈ H^s`, then `a ∈ H^(s + 2)`
  (`CircleSobolev.exists_inclusion_eq_of_laplacian_eq_inclusion`).

## Main definitions

* `TauCeti.CircleSobolev.laplacianSymbol T n = (2πn/T)²`: the symbol of `Δ`.
* `TauCeti.CircleSobolev.laplacian T h`: for `h : s + 2 ≤ t`, the Laplacian `-∂²` as a bounded
  operator `H^t → H^s`.
* `TauCeti.CircleSobolev.greenOperator T`: the Green operator `H^s → H^(s + 2)`.
* `TauCeti.CircleSobolev.laplacianAddInclusionEquiv T hT`: for `hT : T ≠ 0`, the isomorphism
  `1 + Δ : H^(s + 2) ≃ H^s`, written `Δ + inclusion` between the two spaces.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 3, §1
  (Fourier series), Chapter 4, §1 (Sobolev spaces on the torus) and Chapter 5 (linear elliptic
  equations).
-/

public section

noncomputable section

open Asymptotics Complex Filter Real

namespace TauCeti

namespace CircleSobolev

variable {T : ℝ}

/-! ### The Laplacian symbol -/

/-- The symbol `(2πn/T)²` of the Laplacian `Δ = -∂²` on `AddCircle T`: the factor by which `Δ`
multiplies the Fourier monomial `e^{2πinx/T}`. With the sign convention `Δ = -∂²` of this file
it is nonnegative, the opposite sign to `TauCeti.laplacianSymbol`. -/
def laplacianSymbol (T : ℝ) (n : ℤ) : ℂ := (((2 * π * n / T) ^ 2 : ℝ) : ℂ)

theorem laplacianSymbol_def (T : ℝ) (n : ℤ) :
    laplacianSymbol T n = (((2 * π * n / T) ^ 2 : ℝ) : ℂ) :=
  (rfl)

/-- On the circle of length `2π` the Laplacian symbol is `n²`. -/
@[simp]
theorem laplacianSymbol_two_pi (n : ℤ) : laplacianSymbol (2 * π) n = (n : ℂ) ^ 2 := by
  rw [laplacianSymbol_def, mul_div_cancel_left₀ _ (by positivity : (2 * π : ℝ) ≠ 0)]
  norm_cast

@[simp]
theorem laplacianSymbol_eq_zero_iff (hT : T ≠ 0) (n : ℤ) :
    laplacianSymbol T n = 0 ↔ n = 0 := by
  simp [laplacianSymbol_def, Real.pi_ne_zero, hT]

theorem setOf_laplacianSymbol_eq_zero (hT : T ≠ 0) : {n | laplacianSymbol T n = 0} = {0} :=
  Set.ext (laplacianSymbol_eq_zero_iff hT)

private theorem norm_laplacianSymbol (T : ℝ) (n : ℤ) :
    ‖laplacianSymbol T n‖ = (2 * π / T) ^ 2 * |(n : ℝ)| ^ 2 := by
  rw [laplacianSymbol_def, norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_abs]
  ring

private theorem norm_laplacianSymbol_le (T : ℝ) (n : ℤ) :
    ‖laplacianSymbol T n‖ ≤ (2 * π / T) ^ 2 * weight 2 n := by
  rw [norm_laplacianSymbol, weight_ofNat]
  gcongr
  linarith [abs_nonneg (n : ℝ)]

/-- The Laplacian symbol is elliptic of order `2`: for `T ≠ 0`, `(2πn/T)²` is comparable to
`(1 + |n|)²` at every frequency `n ≠ 0`. -/
theorem isTheta_laplacianSymbol (hT : T ≠ 0) : laplacianSymbol T =Θ[cofinite] weight 2 := by
  refine ⟨IsBigO.of_bound ((2 * π / T) ^ 2) (Eventually.of_forall fun n ↦ by
      rw [norm_weight]
      exact norm_laplacianSymbol_le T n),
    IsBigO.of_bound (4 * ((2 * π / T) ^ 2)⁻¹)
      ((Set.finite_singleton (0 : ℤ)).eventually_cofinite_notMem.mono fun n hn ↦ ?_)⟩
  rw [norm_laplacianSymbol, norm_weight, weight_ofNat]
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (by simpa using hn)
  have hmul :
      4 * ((2 * π / T) ^ 2)⁻¹ * ((2 * π / T) ^ 2 * |(n : ℝ)| ^ 2) = 4 * |(n : ℝ)| ^ 2 := by
    field_simp [Real.pi_ne_zero, hT]
  rw [hmul]
  nlinarith

variable {r s t : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The frequency projection onto the zero modes of the Laplacian is the projection onto the
constants. -/
theorem indicator_setOf_laplacianSymbol_eq_zero (hT : T ≠ 0) (a : CircleSobolev s E) :
    indicator {n | laplacianSymbol T n = 0} a = single 0 (a.coeff 0) := by
  rw [setOf_laplacianSymbol_eq_zero hT]
  exact CircleSobolev.ext (funext fun n ↦ by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn])

/-- The elements supported off the zero modes of the Laplacian are the mean-zero elements. -/
theorem mem_supported_compl_setOf_laplacianSymbol_eq_zero_iff (hT : T ≠ 0)
    (a : CircleSobolev s E) :
    a ∈ supported s E {n | laplacianSymbol T n = 0}ᶜ ↔ a.coeff 0 = 0 := by
  rw [setOf_laplacianSymbol_eq_zero hT, mem_supported']
  simp

/-! ### The Laplacian -/

/-- The Laplacian symbol costs two orders of regularity: for `s + 2 ≤ t`,
`(1 + |n|) ^ s (2πn/T)² ≤ (2π/T)² (1 + |n|) ^ t`. -/
private theorem weight_mul_norm_laplacianSymbol_le (T : ℝ) (h : s + 2 ≤ t) (n : ℤ) :
    weight s n * ‖laplacianSymbol T n‖ ≤ (2 * π / T) ^ 2 * weight t n := by
  calc weight s n * ‖laplacianSymbol T n‖
      ≤ weight s n * ((2 * π / T) ^ 2 * weight 2 n) :=
        mul_le_mul_of_nonneg_left (norm_laplacianSymbol_le T n) (weight_nonneg s n)
    _ = (2 * π / T) ^ 2 * weight (s + 2) n := by rw [weight_add]; ring
    _ ≤ (2 * π / T) ^ 2 * weight t n :=
        mul_le_mul_of_nonneg_left (weight_le_weight h n) (sq_nonneg _)

/-- The **Laplacian** `Δ = -∂²` on the circle `AddCircle T`, as a bounded operator `H^t → H^s`
for `s + 2 ≤ t`: the Fourier multiplier with symbol `(2πn/T)²`
(`CircleSobolev.coeff_laplacian`). It is minus the second derivative
(`CircleSobolev.laplacian_apply`). -/
def laplacian (T : ℝ) (h : s + 2 ≤ t) : CircleSobolev t E →L[ℂ] CircleSobolev s E :=
  fourierMultiplierOfBound (laplacianSymbol T) (weight_mul_norm_laplacianSymbol_le T h)

/-- The Laplacian multiplies the `n`-th Fourier coefficient by `(2πn/T)²`. -/
@[simp]
theorem coeff_laplacian (T : ℝ) (h : s + 2 ≤ t) (a : CircleSobolev t E) (n : ℤ) :
    (laplacian T h a).coeff n = (((2 * π * n / T) ^ 2 : ℝ) : ℂ) • a.coeff n :=
  coeff_fourierMultiplierOfBound _ a n

@[simp]
theorem laplacian_single (T : ℝ) (h : s + 2 ≤ t) (n : ℤ) (x : E) :
    laplacian T h (single n x) = single n ((((2 * π * n / T) ^ 2 : ℝ) : ℂ) • x) :=
  fourierMultiplierOfBound_single _ n x

@[simp]
theorem laplacian_inclusion (T : ℝ) {u : ℝ} (h : s + 2 ≤ t) (htu : t ≤ u)
    (a : CircleSobolev u E) :
    laplacian T h (inclusion htu a) = laplacian T (h.trans htu) a :=
  CircleSobolev.ext (funext fun n ↦ by simp)

@[simp]
theorem inclusion_laplacian (T : ℝ) (hrs : r ≤ s) (h : s + 2 ≤ t) (a : CircleSobolev t E) :
    inclusion hrs (laplacian T h a) = laplacian T (by linarith) a :=
  CircleSobolev.ext (funext fun n ↦ by simp)

/-- The constant Fourier coefficient of `Δ a` vanishes: `Δ a` has mean zero. -/
theorem coeff_zero_laplacian (T : ℝ) (h : s + 2 ≤ t) (a : CircleSobolev t E) :
    (laplacian T h a).coeff 0 = 0 := by
  simp

/-- The Laplacian is the Fourier multiplier with the elliptic symbol `laplacianSymbol T` of order
`2`, so the general results on elliptic Fourier multipliers apply to it. -/
theorem laplacian_eq_fourierMultiplier (hT : T ≠ 0) (h : s + 2 ≤ t) :
    (laplacian T h : CircleSobolev t E →L[ℂ] CircleSobolev s E) =
      fourierMultiplier (laplacianSymbol T) (isTheta_laplacianSymbol hT).isBigO h :=
  ContinuousLinearMap.ext fun a ↦ CircleSobolev.ext (funext fun n ↦ by
    rw [coeff_laplacian, coeff_fourierMultiplier, laplacianSymbol_def])

/-- The Laplacian is minus the square of the derivative, through any intermediate order. -/
theorem laplacian_eq_neg_derivative_comp_derivative (T : ℝ) [Fact (0 < T)] {u : ℝ}
    (h₁ : s + 1 ≤ u) (h₂ : u + 1 ≤ t) :
    laplacian T (by linarith) =
      -(derivative T h₁).comp (derivative T h₂ : CircleSobolev t E →L[ℂ] _) := by
  refine ContinuousLinearMap.ext fun a ↦ CircleSobolev.ext (funext fun n ↦ ?_)
  rw [coeff_laplacian, neg_apply, ContinuousLinearMap.comp_apply, coeff_neg,
    Pi.neg_apply, coeff_derivative, coeff_derivative, smul_smul, ← neg_smul]
  congr 1
  push_cast
  linear_combination ((2 * π * n / T : ℂ) ^ 2) * I_sq

/-- The Laplacian is minus the second derivative: `Δ a = -(a'')`. -/
theorem laplacian_apply (T : ℝ) [Fact (0 < T)] (h : s + 2 ≤ t) (a : CircleSobolev t E) :
    laplacian T h a = -derivative T (le_refl (s + 1)) (derivative T (by linarith) a) :=
  congrArg (fun f ↦ f a)
    (laplacian_eq_neg_derivative_comp_derivative T (le_refl (s + 1)) (by linarith))

/-- **The kernel of the Laplacian consists of the constants**: for `T ≠ 0`, `Δ a = 0` exactly
when every Fourier coefficient of `a` other than the zeroth one vanishes. -/
theorem laplacian_eq_zero_iff (hT : T ≠ 0) (h : s + 2 ≤ t) (a : CircleSobolev t E) :
    laplacian T h a = 0 ↔ a = single 0 (a.coeff 0) := by
  rw [CircleSobolev.ext_iff, CircleSobolev.ext_iff, funext_iff, funext_iff]
  refine forall_congr' fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [hn, hT, Real.pi_ne_zero]

/-! ### The Green operator -/

/-- The symbol `(T/(2πn))²` of the Green operator gains two orders of regularity:
`(1 + |n|) ^ (s + 2) (T/(2πn))² ≤ (T/π)² (1 + |n|) ^ s`. At `n = 0` the symbol is `0`. -/
private theorem weight_mul_norm_greenSymbol_le (T : ℝ) (n : ℤ) :
    weight (s + 2) n * ‖(((T / (2 * π * n)) ^ 2 : ℝ) : ℂ)‖ ≤
      (T / π) ^ 2 * weight s n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using sq_nonneg (T / π)
  have hn1 : 1 ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have hsq : (1 + |(n : ℝ)|) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith [sq_abs (n : ℝ)]
  rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), weight_add_two]
  calc weight s n * (1 + |(n : ℝ)|) ^ 2 * (T / (2 * π * n)) ^ 2
      = (T / π) ^ 2 * ((1 + |(n : ℝ)|) ^ 2 / (4 * (n : ℝ) ^ 2)) * weight s n := by
        field_simp
        ring
    _ ≤ (T / π) ^ 2 * 1 * weight s n :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (div_le_one_of_le₀ hsq (by positivity)) (sq_nonneg _)) (weight_nonneg s n)
    _ = (T / π) ^ 2 * weight s n := by ring

/-- The **Green operator** of the circle Laplacian, `H^s → H^(s + 2)`: the Fourier multiplier
with symbol `(T/(2πn))² = (2πn/T)⁻²` for `n ≠ 0` and `0` for `n = 0`. For `T ≠ 0`, it inverts
the Laplacian on the functions of mean zero and vanishes on the constants
(`CircleSobolev.laplacian_greenOperator`, `CircleSobolev.greenOperator_laplacian`). -/
def greenOperator (T : ℝ) : CircleSobolev s E →L[ℂ] CircleSobolev (s + 2) E :=
  fourierMultiplierOfBound (fun n ↦ (((T / (2 * π * n)) ^ 2 : ℝ) : ℂ))
    (weight_mul_norm_greenSymbol_le T)

/-- The Green operator multiplies the `n`-th Fourier coefficient by `(T/(2πn))²`, which is `0`
for `n = 0`. -/
@[simp]
theorem coeff_greenOperator (T : ℝ) (b : CircleSobolev s E) (n : ℤ) :
    (greenOperator T b).coeff n = (((T / (2 * π * n)) ^ 2 : ℝ) : ℂ) • b.coeff n :=
  coeff_fourierMultiplierOfBound _ b n

@[simp]
theorem greenOperator_single (T : ℝ) (n : ℤ) (x : E) :
    greenOperator T (single (s := s) n x) =
      single n ((((T / (2 * π * n)) ^ 2 : ℝ) : ℂ) • x) :=
  fourierMultiplierOfBound_single _ n x

/-- The Green operator gains two orders, with norm at most `(T/π)²`. -/
theorem norm_greenOperator_le (T : ℝ) (b : CircleSobolev s E) :
    ‖greenOperator T b‖ ≤ (T / π) ^ 2 * ‖b‖ :=
  norm_fourierMultiplierOfBound_le _ b

@[simp]
theorem greenOperator_inclusion (T : ℝ) (hrs : r ≤ s) (b : CircleSobolev s E) :
    greenOperator T (inclusion hrs b) = inclusion (by linarith) (greenOperator T b) :=
  CircleSobolev.ext (funext fun n ↦ by simp)

/-- The Green operator is the Fourier multiplier with the inverse symbol `(laplacianSymbol T)⁻¹`
of order `-2`, the parametrix of the general theory. -/
theorem greenOperator_eq_fourierMultiplier (hT : T ≠ 0) :
    (greenOperator T : CircleSobolev s E →L[ℂ] CircleSobolev (s + 2) E) =
      fourierMultiplier (fun n ↦ (laplacianSymbol T n)⁻¹)
        (isBigO_inv (isTheta_laplacianSymbol hT).isBigO_symm) (by linarith) :=
  ContinuousLinearMap.ext fun b ↦ CircleSobolev.ext (funext fun n ↦ by
    rw [coeff_greenOperator, coeff_fourierMultiplier, laplacianSymbol_def, ← ofReal_inv,
      ← inv_pow, inv_div])

/-- **The Green operator is a right inverse of the Laplacian up to the constants**: for `T ≠ 0`,
`Δ G b = b - Π b`, where `Π b` is the constant term of `b`. -/
theorem laplacian_greenOperator (hT : T ≠ 0) (b : CircleSobolev s E) :
    laplacian T le_rfl (greenOperator T b) = b - single 0 (b.coeff 0) := by
  rw [laplacian_eq_fourierMultiplier hT, greenOperator_eq_fourierMultiplier hT,
    fourierMultiplier_fourierMultiplier_inv (isTheta_laplacianSymbol hT) rfl,
    indicator_setOf_laplacianSymbol_eq_zero hT]

/-- **The Green operator is a left inverse of the Laplacian up to the constants**: for `T ≠ 0`,
`G Δ a = a - Π a`, where `Π a` is the constant term of `a`. -/
theorem greenOperator_laplacian (hT : T ≠ 0) (h : s + 2 ≤ t) (a : CircleSobolev t E) :
    greenOperator T (laplacian T h a) = inclusion h (a - single 0 (a.coeff 0)) := by
  rw [← laplacian_inclusion T le_rfl h, laplacian_eq_fourierMultiplier hT,
    greenOperator_eq_fourierMultiplier hT,
    fourierMultiplier_inv_fourierMultiplier (isTheta_laplacianSymbol hT) rfl,
    indicator_setOf_laplacianSymbol_eq_zero hT, coeff_inclusion, map_sub, inclusion_single]

/-! ### Solvability -/

/-- **Solvability of `Δ a = b`.** For `T ≠ 0`, an element `b ∈ H^s` is the Laplacian of some
`a ∈ H^(s + 2)` exactly when its mean, the constant Fourier coefficient, vanishes. A solution is
`G b`. -/
theorem exists_laplacian_eq_iff (hT : T ≠ 0) (b : CircleSobolev s E) :
    (∃ a : CircleSobolev (s + 2) E, laplacian T le_rfl a = b) ↔ b.coeff 0 = 0 := by
  refine ⟨fun ⟨a, ha⟩ ↦ ha ▸ coeff_zero_laplacian T le_rfl a,
    fun hb ↦ ⟨greenOperator T b, ?_⟩⟩
  rw [laplacian_greenOperator hT, hb, map_zero, sub_zero]

/-- A nonzero constant is not a Laplacian: the equation `Δ a = x`, `x ≠ 0` constant, has no
solution in any `H^t`, since its right-hand side does not have mean zero. -/
theorem laplacian_ne_single_zero (T : ℝ) (h : s + 2 ≤ t) (a : CircleSobolev t E) {x : E}
    (hx : x ≠ 0) :
    laplacian T h a ≠ single 0 x := by
  intro ha
  have := coeff_zero_laplacian T h a
  rw [ha] at this
  exact hx (by simpa using this)

/-! ### The isomorphism `1 + Δ` -/

/-- For `T ≠ 0`, the symbol `1 + (2πn/T)²` of `1 + Δ` is elliptic of order `2`. -/
private theorem isTheta_one_add_laplacianSymbol (hT : T ≠ 0) :
    (fun n ↦ 1 + laplacianSymbol T n) =Θ[cofinite] weight 2 := by
  have h1 : (fun _ : ℤ ↦ (1 : ℂ)) =O[cofinite] weight 2 :=
    IsBigO.of_bound 1 (Eventually.of_forall fun n ↦ by
      rw [norm_one, norm_weight, weight_ofNat, one_mul]
      have : (1 : ℝ) ≤ 1 + |(n : ℝ)| := le_add_of_nonneg_right (abs_nonneg _)
      nlinarith)
  have hle (n : ℤ) : ‖laplacianSymbol T n‖ ≤ ‖1 + laplacianSymbol T n‖ := by
    rw [laplacianSymbol_def, ← ofReal_one, ← ofReal_add, norm_real, norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (by positivity)]
    linarith
  exact ⟨h1.add (isTheta_laplacianSymbol hT).1,
    (isTheta_laplacianSymbol hT).2.trans
      (IsBigO.of_bound 1 (Eventually.of_forall fun n ↦ by simpa using hle n))⟩

/-- The symbol `1 + (2πn/T)²` of `1 + Δ` never vanishes. -/
private theorem one_add_laplacianSymbol_ne_zero (T : ℝ) (n : ℤ) :
    1 + laplacianSymbol T n ≠ 0 := by
  rw [laplacianSymbol_def, ← ofReal_one, ← ofReal_add]
  exact_mod_cast (by positivity : (0 : ℝ) < 1 + (2 * π * n / T) ^ 2).ne'

/-- **`1 + Δ = 1 - ∂²` is an isomorphism `H^(s + 2) ≃ H^s`** for every real `s` and `T ≠ 0`,
written `Δ + inclusion` since its two summands act between different spaces. It multiplies the
`n`-th Fourier coefficient by `1 + (2πn/T)² ≥ 1`, and its inverse multiplies it by
`(1 + (2πn/T)²)⁻¹` (`CircleSobolev.coeff_laplacianAddInclusionEquiv_symm`), on every mode
including the constant one. -/
def laplacianAddInclusionEquiv (T : ℝ) (hT : T ≠ 0) :
    CircleSobolev (s + 2) E ≃L[ℂ] CircleSobolev s E :=
  fourierMultiplierEquiv (isTheta_one_add_laplacianSymbol hT)
    (one_add_laplacianSymbol_ne_zero T) rfl

@[simp]
theorem laplacianAddInclusionEquiv_apply (hT : T ≠ 0) (a : CircleSobolev (s + 2) E) :
    laplacianAddInclusionEquiv T hT a = laplacian T le_rfl a + inclusion (by linarith) a :=
  CircleSobolev.ext (funext fun n ↦ by
    simp [laplacianAddInclusionEquiv, laplacianSymbol_def, add_smul, add_comm])

/-- The inverse of `1 + Δ` multiplies the `n`-th Fourier coefficient by `(1 + (2πn/T)²)⁻¹`. -/
@[simp]
theorem coeff_laplacianAddInclusionEquiv_symm (hT : T ≠ 0) (b : CircleSobolev s E) (n : ℤ) :
    ((laplacianAddInclusionEquiv T hT).symm b).coeff n =
      (((1 + (2 * π * n / T) ^ 2)⁻¹ : ℝ) : ℂ) • b.coeff n := by
  simp [laplacianAddInclusionEquiv, laplacianSymbol_def]

/-! ### The Fredholm property -/

/-- **The circle Laplacian is Fredholm**: for finite-dimensional `E` and `T ≠ 0`,
`Δ : H^(s + 2) → H^s` is a Fredholm operator for every real `s`, as an elliptic Fourier
multiplier of order `2`. -/
theorem isFredholm_laplacian [FiniteDimensional ℂ E] (hT : T ≠ 0) :
    (laplacian T le_rfl : CircleSobolev (s + 2) E →L[ℂ] CircleSobolev s E).IsFredholm := by
  rw [laplacian_eq_fourierMultiplier hT]
  exact isFredholm_fourierMultiplier (isTheta_laplacianSymbol hT) rfl

/-- For `T ≠ 0`, the range of `Δ : H^(s + 2) → H^s` consists of the elements of mean zero: it
is the kernel of the constant Fourier coefficient. -/
theorem range_laplacian (hT : T ≠ 0) :
    (laplacian T le_rfl : CircleSobolev (s + 2) E →L[ℂ] CircleSobolev s E).range =
      (coeffCLM 0 : CircleSobolev s E →L[ℂ] E).ker := by
  ext b
  simpa using exists_laplacian_eq_iff hT b

/-- **The circle Laplacian has index zero**: for `T ≠ 0`, the kernel of `Δ : H^(s + 2) → H^s`
(the constants) and its cokernel (detected by the mean) are both identified with `E`; at `T = 0`,
`Δ = 0` and `H^(s + 2) ≃ₗ H^s` gives equality of finranks directly. For finite-dimensional `E`
and `T ≠ 0` this is the Fredholm index `dim E - dim E` of the Fredholm operator `Δ`
(`CircleSobolev.isFredholm_laplacian`); for infinite-dimensional `E` both finranks are `0` by
convention, and the statement carries no information. -/
theorem index_laplacian (T : ℝ) :
    (laplacian T le_rfl : CircleSobolev (s + 2) E →L[ℂ] CircleSobolev s E).index = 0 := by
  rw [ContinuousLinearMap.index_def, LinearMap.index_eq_finrank_sub, sub_eq_zero]
  rcases eq_or_ne T 0 with rfl | hT
  · have h0 : (laplacian 0 le_rfl : CircleSobolev (s + 2) E →L[ℂ] CircleSobolev s E) = 0 :=
      ContinuousLinearMap.ext fun a ↦ CircleSobolev.ext (funext fun n ↦ by simp)
    rw [h0, ContinuousLinearMap.toLinearMap_zero, LinearMap.ker_zero, LinearMap.range_zero,
      Submodule.topEquiv.finrank_eq, (Submodule.quotEquivOfEqBot _ rfl).finrank_eq,
      (toℓ2.trans toℓ2.symm).finrank_eq]
  · -- The constant term identifies the kernel with `E`.
    let eker : (laplacian T le_rfl : CircleSobolev (s + 2) E →L[ℂ]
        CircleSobolev s E).ker ≃ₗ[ℂ] E :=
      { toFun a := a.val.coeff 0
        invFun x := ⟨single 0 x, by simp⟩
        map_add' _ _ := by simp
        map_smul' _ _ := by simp
        left_inv a := Subtype.ext ((laplacian_eq_zero_iff hT le_rfl a.val).1 a.property).symm
        right_inv x := by simp }
    -- The mean identifies the cokernel with `E`.
    have hsurj : Function.Surjective (coeffCLM 0 : CircleSobolev s E →L[ℂ] E) :=
      fun x ↦ ⟨single 0 x, by simp⟩
    let ecoker := (Submodule.quotEquivOfEq _ _ (range_laplacian hT)).trans
      ((coeffCLM 0 : CircleSobolev s E →L[ℂ] E).toLinearMap.quotKerEquivOfSurjective hsurj)
    rw [eker.finrank_eq, ecoker.finrank_eq]

/-! ### The elliptic estimate and elliptic regularity -/

/-- **The elliptic estimate for the circle Laplacian**: for `T ≠ 0`,
`‖a‖_{H^(s+2)} ≤ (T/π)² ‖Δ a‖_{H^s} + ‖a‖_{H^r}` for every `r ≤ s + 2`. The lower-order term
controls the constant term of `a`, on which `Δ` vanishes. -/
theorem norm_le_mul_norm_laplacian_add_norm_inclusion (hT : T ≠ 0) (hr : r ≤ s + 2)
    (a : CircleSobolev (s + 2) E) :
    ‖a‖ ≤ (T / π) ^ 2 * ‖laplacian T le_rfl a‖ + ‖inclusion hr a‖ := by
  have ha : a = greenOperator T (laplacian T le_rfl a) + single 0 (a.coeff 0) := by
    rw [greenOperator_laplacian hT, inclusion_refl, sub_add_cancel]
  have h0 : ‖a.coeff 0‖ ≤ ‖inclusion hr a‖ := by
    simpa using norm_coeff_le (inclusion hr a) 0
  calc ‖a‖
      ≤ ‖greenOperator T (laplacian T le_rfl a)‖ + ‖single (s := s + 2) 0 (a.coeff 0)‖ := by
        conv_lhs => rw [ha]
        exact norm_add_le _ _
    _ ≤ (T / π) ^ 2 * ‖laplacian T le_rfl a‖ + ‖inclusion hr a‖ := by
        rw [norm_single, weight_zero_right, one_mul]
        exact add_le_add (norm_greenOperator_le T _) h0

/-- **Without the lower-order term the elliptic estimate fails**: if `E` is nontrivial, no
constant `C` satisfies `‖a‖_{H^t} ≤ C ‖Δ a‖_{H^s}` for all `a`, since `Δ` kills the nonzero
constants. -/
theorem not_exists_forall_norm_le_mul_norm_laplacian (T : ℝ) [Nontrivial E] (h : s + 2 ≤ t) :
    ¬∃ C : ℝ, ∀ a : CircleSobolev t E, ‖a‖ ≤ C * ‖laplacian T h a‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  exact hx (by simpa [norm_single] using hC (single 0 x))

/-- **On the complement of the kernel the lower-order term can be dropped**: for `T ≠ 0`, an
element `a` of mean zero satisfies `‖a‖_{H^(s+2)} ≤ (T/π)² ‖Δ a‖_{H^s}`. -/
theorem norm_le_mul_norm_laplacian_of_coeff_zero_eq_zero (hT : T ≠ 0)
    {a : CircleSobolev (s + 2) E} (ha : a.coeff 0 = 0) :
    ‖a‖ ≤ (T / π) ^ 2 * ‖laplacian T le_rfl a‖ := by
  have hG : greenOperator T (laplacian T le_rfl a) = a := by
    rw [greenOperator_laplacian hT, ha, map_zero, sub_zero, inclusion_refl]
  calc ‖a‖ = ‖greenOperator T (laplacian T le_rfl a)‖ := by rw [hG]
    _ ≤ (T / π) ^ 2 * ‖laplacian T le_rfl a‖ := norm_greenOperator_le T _

/-- **Elliptic regularity for the circle Laplacian**: for `T ≠ 0`, if `a ∈ H^t` and `Δ a ∈ H^r`
lies in the smaller space `H^s`, then `a ∈ H^(s + 2)`. Explicitly `a = G (Δ a) + Π a`. -/
theorem exists_inclusion_eq_of_laplacian_eq_inclusion (hT : T ≠ 0) (h : r + 2 ≤ t)
    (hts : t ≤ s + 2) (a : CircleSobolev t E) (b : CircleSobolev s E)
    (hab : laplacian T h a = inclusion (by linarith) b) :
    ∃ c : CircleSobolev (s + 2) E, inclusion hts c = a := by
  -- Applying `G` to `Δ a = b` gives `a - Π a = G b`.
  have hG : inclusion h (a - single 0 (a.coeff 0)) =
      inclusion (by linarith) (greenOperator T b) := by
    rw [← greenOperator_laplacian hT, hab, greenOperator_inclusion]
  have hcoeff := congrArg coeff hG
  rw [coeff_inclusion, coeff_inclusion] at hcoeff
  refine ⟨greenOperator T b + single 0 (a.coeff 0), CircleSobolev.ext ?_⟩
  rw [coeff_inclusion, coeff_add, ← hcoeff, coeff_sub]
  simp

end CircleSobolev

end TauCeti
