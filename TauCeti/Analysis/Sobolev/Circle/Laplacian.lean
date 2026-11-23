/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Analysis.Sobolev.Circle.Derivative
public import TauCeti.Analysis.Sobolev.Circle.FourierMultiplier
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index

import TauCeti.Analysis.Fredholm.CompactPerturbation

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

* *Kernel.* `Δ a = 0` exactly when `a` is constant (`CircleSobolev.laplacian_eq_zero_iff`).
* *Solvability.* `Δ a = b` has a solution `a ∈ H^(s + 2)` exactly when `b ∈ H^s` has mean zero,
  that is `b.coeff 0 = 0` (`CircleSobolev.exists_laplacian_eq_iff`). The constant mode is the
  obstruction: `Δ a = 1` has no solution (`CircleSobolev.laplacian_ne_single_zero`).
* *Green operator.* The Fourier multiplier `G` with symbol `λₙ⁻¹` for `n ≠ 0` and `0` for `n = 0`
  (`CircleSobolev.greenOperator`) gains two orders and inverts `Δ` up to the projection
  `Π a = single 0 (a.coeff 0)` onto the constants: `Δ G b = b - Π b` and `G Δ a = a - Π a`.
* *The invertible operator `1 + Δ = 1 - ∂²`.* It multiplies the `n`-th coefficient by
  `1 + λₙ ≥ 1`, so it is an isomorphism `H^(s + 2) ≃ H^s` for every `s`, whose inverse has
  symbol `(1 + λₙ)⁻¹` on every mode, including `n = 0`
  (`CircleSobolev.laplacianAddInclusionEquiv`).
* *Fredholm property.* The kernel of `Δ : H^(s + 2) → H^s` (the constants) and its cokernel
  (detected by the mean) are both copies of `E`, so `finrank (ker Δ) = finrank (coker Δ)`
  (`CircleSobolev.index_laplacian`). For finite-dimensional `E` this says that the Fredholm index
  `dim E - dim E` of `Δ` is zero; for infinite-dimensional `E` both finranks are `0` by convention
  and the statement carries no information. For finite-dimensional `E`, `Δ = (1 + Δ) - 1`
  differs from the isomorphism `1 + Δ` by the inclusion `H^(s + 2) → H^s`, which is compact by
  Rellich's theorem, so `Δ` is a Fredholm operator (`CircleSobolev.isFredholm_laplacian`).
* *Elliptic estimate.* `‖a‖_{H^(s+2)} ≤ (T/π)² ‖Δ a‖_{H^s} + ‖a‖_{H^r}` for every `r ≤ s + 2`
  (`CircleSobolev.norm_le_mul_norm_laplacian_add_norm_inclusion`). The lower-order term cannot be
  dropped, since constants are killed by `Δ`
  (`CircleSobolev.not_exists_forall_norm_le_mul_norm_laplacian`), but it can on the complement
  of the kernel, the elements of mean zero
  (`CircleSobolev.norm_le_mul_norm_laplacian_of_coeff_zero_eq_zero`).
* *Elliptic regularity.* If `a ∈ H^t` and `Δ a ∈ H^s`, then `a ∈ H^(s + 2)`
  (`CircleSobolev.exists_inclusion_eq_of_laplacian_eq_inclusion`).
* *The general theory.* The symbol `λₙ = (2πn/T)²` (`CircleSobolev.laplacianSymbol`), which is
  `n²` on the circle of length `2π`, is elliptic of order `2`
  (`CircleSobolev.isTheta_laplacianSymbol`), so `Δ` and `G` are the elliptic Fourier multipliers
  of `TauCeti/Analysis/Sobolev/Circle/FourierMultiplier.lean` with symbols `λₙ` and `λₙ⁻¹`
  (`CircleSobolev.laplacian_eq_fourierMultiplier`,
  `CircleSobolev.greenOperator_eq_fourierMultiplier`), whose zero-mode projection is the
  projection onto the constants (`CircleSobolev.indicator_setOf_laplacianSymbol_eq_zero`).
  Note that `Δ = -∂²` here, so `λₙ ≥ 0` has the opposite sign to `TauCeti.laplacianSymbol`.

## Main definitions

* `TauCeti.CircleSobolev.laplacian T h`: for `h : s + 2 ≤ t`, the Laplacian `-∂²` as a bounded
  operator `H^t → H^s`.
* `TauCeti.CircleSobolev.greenOperator T`: the Green operator `H^s → H^(s + 2)`.
* `TauCeti.CircleSobolev.laplacianAddInclusionEquiv T`: the isomorphism
  `1 + Δ : H^(s + 2) ≃ H^s`, written `Δ + inclusion` between the two spaces.
* `TauCeti.CircleSobolev.laplacianSymbol T n = (2πn/T)²`: the symbol of `Δ`.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 3, §1
  (Fourier series), Chapter 4, §1 (Sobolev spaces on the torus) and Chapter 5 (linear elliptic
  equations).
-/

public section

noncomputable section

open Complex Real

namespace TauCeti

namespace CircleSobolev

variable {r s t : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (T : ℝ) [hT : Fact (0 < T)]

/-! ### The Laplacian -/

omit hT in
/-- The Laplacian symbol costs two orders of regularity: for `s + 2 ≤ t`,
`(1 + |n|) ^ s (2πn/T)² ≤ (2π/T)² (1 + |n|) ^ t`. -/
private theorem weight_mul_norm_laplacianSymbol_le (h : s + 2 ≤ t) (n : ℤ) :
    weight s n * ‖(((2 * π * n / T) ^ 2 : ℝ) : ℂ)‖ ≤ (2 * π / T) ^ 2 * weight t n := by
  have hn : (n : ℝ) ^ 2 ≤ (1 + |(n : ℝ)|) ^ 2 := by
    nlinarith [sq_abs (n : ℝ), abs_nonneg (n : ℝ)]
  rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc weight s n * (2 * π * n / T) ^ 2 = (2 * π / T) ^ 2 * (weight s n * (n : ℝ) ^ 2) := by ring
    _ ≤ (2 * π / T) ^ 2 * weight t n := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        calc weight s n * (n : ℝ) ^ 2 ≤ weight s n * (1 + |(n : ℝ)|) ^ 2 :=
              mul_le_mul_of_nonneg_left hn (weight_nonneg s n)
          _ = weight (s + 2) n := (weight_add_two s n).symm
          _ ≤ weight t n := weight_le_weight h n

/-- The **Laplacian** `Δ = -∂²` on the circle `AddCircle T`, as a bounded operator `H^t → H^s`
for `s + 2 ≤ t`: the Fourier multiplier with symbol `(2πn/T)²` (`CircleSobolev.coeff_laplacian`).
It is minus the second derivative (`CircleSobolev.laplacian_apply`). -/
def laplacian (h : s + 2 ≤ t) : CircleSobolev t E →L[ℂ] CircleSobolev s E :=
  fourierMultiplierOfBound (fun n ↦ (((2 * π * n / T) ^ 2 : ℝ) : ℂ))
    (weight_mul_norm_laplacianSymbol_le T h)

omit hT in
/-- The Laplacian multiplies the `n`-th Fourier coefficient by `(2πn/T)²`. -/
@[simp]
theorem coeff_laplacian (h : s + 2 ≤ t) (a : CircleSobolev t E) (n : ℤ) :
    (laplacian T h a).coeff n = (((2 * π * n / T) ^ 2 : ℝ) : ℂ) • a.coeff n :=
  coeff_fourierMultiplierOfBound _ a n

/-- The Laplacian is minus the second derivative: `Δ a = -(a'')`. -/
theorem laplacian_apply (h : s + 2 ≤ t) (a : CircleSobolev t E) :
    laplacian T h a = -derivative T (le_refl (s + 1)) (derivative T (by linarith) a) := by
  refine CircleSobolev.ext (funext fun n ↦ ?_)
  rw [coeff_laplacian, coeff_neg, Pi.neg_apply, coeff_derivative, coeff_derivative, smul_smul,
    ← neg_smul]
  congr 1
  push_cast
  linear_combination ((2 * π * n / T : ℂ) ^ 2) * I_sq

omit hT in
@[simp]
theorem laplacian_single (h : s + 2 ≤ t) (n : ℤ) (x : E) :
    laplacian T h (single n x) = single n ((((2 * π * n / T) ^ 2 : ℝ) : ℂ) • x) :=
  fourierMultiplierOfBound_single _ n x

omit hT in
@[simp]
theorem laplacian_inclusion {u : ℝ} (h : s + 2 ≤ t) (htu : t ≤ u) (a : CircleSobolev u E) :
    laplacian T h (inclusion htu a) = laplacian T (h.trans htu) a :=
  CircleSobolev.ext (funext fun n ↦ by simp)

omit hT in
@[simp]
theorem inclusion_laplacian (hrs : r ≤ s) (h : s + 2 ≤ t) (a : CircleSobolev t E) :
    inclusion hrs (laplacian T h a) = laplacian T (by linarith) a :=
  CircleSobolev.ext (funext fun n ↦ by simp)

omit hT in
/-- The constant Fourier coefficient of `Δ a` vanishes: `Δ a` has mean zero. -/
theorem coeff_zero_laplacian (h : s + 2 ≤ t) (a : CircleSobolev t E) :
    (laplacian T h a).coeff 0 = 0 := by
  simp

/-- **The kernel of the Laplacian consists of the constants**: `Δ a = 0` exactly when every
Fourier coefficient of `a` other than the zeroth one vanishes. -/
theorem laplacian_eq_zero_iff (h : s + 2 ≤ t) (a : CircleSobolev t E) :
    laplacian T h a = 0 ↔ a = single 0 (a.coeff 0) := by
  refine ⟨fun ha ↦ ?_, fun ha ↦ ?_⟩
  · -- `Δ a = -(a'')`, and `a'' = 0` forces `a'` constant, hence zero since it has no mean.
    rw [laplacian_apply, neg_eq_zero, derivative_eq_zero_iff, coeff_derivative] at ha
    rw [← derivative_eq_zero_iff T (show s + 1 + 1 ≤ t by linarith), ha]
    simp
  · rw [ha, laplacian_single]
    simp

/-! ### The Green operator -/

omit hT in
/-- The symbol `(T/(2πn))²` of the Green operator gains two orders of regularity:
`(1 + |n|) ^ (s + 2) (T/(2πn))² ≤ (T/π)² (1 + |n|) ^ s`. At `n = 0` the symbol is `0`. -/
private theorem weight_mul_norm_greenSymbol_le (n : ℤ) :
    weight (s + 2) n * ‖((((T / (2 * π * n)) ^ 2 : ℝ)) : ℂ)‖ ≤ (T / π) ^ 2 * weight s n := by
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
with symbol `(T/(2πn))² = (2πn/T)⁻²` for `n ≠ 0` and `0` for `n = 0`. It inverts the Laplacian
on the functions of mean zero and vanishes on the constants
(`CircleSobolev.laplacian_greenOperator`, `CircleSobolev.greenOperator_laplacian`). -/
def greenOperator : CircleSobolev s E →L[ℂ] CircleSobolev (s + 2) E :=
  fourierMultiplierOfBound (fun n ↦ ((((T / (2 * π * n)) ^ 2 : ℝ)) : ℂ))
    (weight_mul_norm_greenSymbol_le T)

omit hT in
/-- The Green operator multiplies the `n`-th Fourier coefficient by `(T/(2πn))²`, which is `0`
for `n = 0`. -/
@[simp]
theorem coeff_greenOperator (b : CircleSobolev s E) (n : ℤ) :
    (greenOperator T b).coeff n = ((((T / (2 * π * n)) ^ 2 : ℝ)) : ℂ) • b.coeff n :=
  coeff_fourierMultiplierOfBound _ b n

omit hT in
@[simp]
theorem greenOperator_single (n : ℤ) (x : E) :
    greenOperator T (single (s := s) n x) = single n ((((T / (2 * π * n)) ^ 2 : ℝ) : ℂ) • x) :=
  fourierMultiplierOfBound_single _ n x

omit hT in
/-- The Green operator gains two orders, with norm at most `(T/π)²`. -/
theorem norm_greenOperator_le (b : CircleSobolev s E) :
    ‖greenOperator T b‖ ≤ (T / π) ^ 2 * ‖b‖ :=
  norm_fourierMultiplierOfBound_le _ b

omit hT in
/-- The product of the Laplacian eigenvalue and the Green symbol is `1` off the constant mode. -/
private theorem green_mul_eigenvalue (hT0 : T ≠ 0) {n : ℤ} (hn : n ≠ 0) :
    ((((T / (2 * π * n)) ^ 2 : ℝ)) : ℂ) * (((2 * π * n / T) ^ 2 : ℝ) : ℂ) = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [← ofReal_mul, ← mul_pow, ofReal_eq_one]
  field_simp

/-- **The Green operator is a right inverse of the Laplacian up to the constants**:
`Δ G b = b - Π b`, where `Π b` is the constant term of `b`. -/
theorem laplacian_greenOperator (b : CircleSobolev s E) :
    laplacian T le_rfl (greenOperator T b) = b - single 0 (b.coeff 0) := by
  refine CircleSobolev.ext (funext fun n ↦ ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [coeff_laplacian, coeff_greenOperator, smul_smul, mul_comm,
      green_mul_eigenvalue T hT.out.ne' hn]
    simp [hn]

/-- **The Green operator is a left inverse of the Laplacian up to the constants**:
`G Δ a = a - Π a`, where `Π a` is the constant term of `a`. -/
theorem greenOperator_laplacian (h : s + 2 ≤ t) (a : CircleSobolev t E) :
    greenOperator T (laplacian T h a) = inclusion h (a - single 0 (a.coeff 0)) := by
  refine CircleSobolev.ext (funext fun n ↦ ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [coeff_greenOperator, coeff_laplacian, smul_smul, green_mul_eigenvalue T hT.out.ne' hn]
    simp [hn]

omit hT in
@[simp]
theorem greenOperator_inclusion (hrs : r ≤ s) (b : CircleSobolev s E) :
    greenOperator T (inclusion hrs b) = inclusion (by linarith) (greenOperator T b) :=
  CircleSobolev.ext (funext fun n ↦ by simp)

/-! ### Solvability -/

/-- **Solvability of `Δ a = b`.** An element `b ∈ H^s` is the Laplacian of some `a ∈ H^(s + 2)`
exactly when its mean, the constant Fourier coefficient, vanishes. A solution is `G b`. -/
theorem exists_laplacian_eq_iff (b : CircleSobolev s E) :
    (∃ a : CircleSobolev (s + 2) E, laplacian T le_rfl a = b) ↔ b.coeff 0 = 0 := by
  refine ⟨fun ⟨a, ha⟩ ↦ ha ▸ coeff_zero_laplacian T le_rfl a, fun hb ↦ ⟨greenOperator T b, ?_⟩⟩
  rw [laplacian_greenOperator, hb, map_zero, sub_zero]

omit hT in
/-- A nonzero constant is not a Laplacian: the equation `Δ a = x`, `x ≠ 0` constant, has no
solution in any `H^t`, since its right-hand side does not have mean zero. -/
theorem laplacian_ne_single_zero (h : s + 2 ≤ t) (a : CircleSobolev t E) {x : E} (hx : x ≠ 0) :
    laplacian T h a ≠ single 0 x := by
  intro ha
  have := coeff_zero_laplacian T h a
  rw [ha] at this
  exact hx (by simpa using this)

/-! ### The isomorphism `1 + Δ` -/

omit hT in
/-- The inverse symbol `(1 + (2πn/T)²)⁻¹` of `1 + Δ` gains two orders of regularity. -/
private theorem weight_mul_norm_resolventSymbol_le (hT0 : T ≠ 0) (n : ℤ) :
    weight (s + 2) n * ‖((((1 + (2 * π * n / T) ^ 2)⁻¹ : ℝ)) : ℂ)‖ ≤
      2 * (1 + (T / (2 * π)) ^ 2) * weight s n := by
  have hpos : 0 < 1 + (2 * π * n / T) ^ 2 := by positivity
  -- `(1 + |n|)² ≤ 2 (1 + n²)` and `1 + n² ≤ (1 + (T/2π)²) (1 + (2πn/T)²)`.
  have hprod : (T / (2 * π)) ^ 2 * (2 * π * n / T) ^ 2 = (n : ℝ) ^ 2 := by
    field_simp
  have hle : (1 + |(n : ℝ)|) ^ 2 ≤
      2 * (1 + (T / (2 * π)) ^ 2) * (1 + (2 * π * n / T) ^ 2) := by
    nlinarith [sq_abs (n : ℝ), sq_nonneg (1 - |(n : ℝ)|), sq_nonneg (T / (2 * π)),
      sq_nonneg (2 * π * n / T)]
  rw [norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos), weight_add_two]
  calc weight s n * (1 + |(n : ℝ)|) ^ 2 * (1 + (2 * π * n / T) ^ 2)⁻¹
      = weight s n * ((1 + |(n : ℝ)|) ^ 2 * (1 + (2 * π * n / T) ^ 2)⁻¹) := by ring
    _ ≤ weight s n * (2 * (1 + (T / (2 * π)) ^ 2)) :=
        mul_le_mul_of_nonneg_left ((mul_inv_le_iff₀ hpos).2 hle) (weight_nonneg s n)
    _ = 2 * (1 + (T / (2 * π)) ^ 2) * weight s n := by ring

omit hT in
/-- The operator `1 + Δ = 1 - ∂²` multiplies the `n`-th Fourier coefficient by
`1 + (2πn/T)²`. -/
private theorem coeff_laplacian_add_inclusion (a : CircleSobolev (s + 2) E) (n : ℤ) :
    ((laplacian T le_rfl + inclusion (by linarith) : CircleSobolev (s + 2) E →L[ℂ]
      CircleSobolev s E) a).coeff n = (((1 + (2 * π * n / T) ^ 2 : ℝ)) : ℂ) • a.coeff n := by
  simp only [add_apply, coeff_add, Pi.add_apply, coeff_laplacian, coeff_inclusion, ofReal_add,
    ofReal_one, add_smul, one_smul]
  abel

omit hT in
/-- The symbol `1 + (2πn/T)²` of `1 + Δ` times its inverse is `1`. -/
private theorem inv_mul_one_add_eigenvalue (n : ℤ) :
    ((((1 + (2 * π * n / T) ^ 2)⁻¹ : ℝ)) : ℂ) * (((1 + (2 * π * n / T) ^ 2 : ℝ)) : ℂ) = 1 := by
  rw [← ofReal_mul, inv_mul_cancel₀ (by positivity), ofReal_one]

/-- **`1 + Δ = 1 - ∂²` is an isomorphism `H^(s + 2) ≃ H^s`** for every real `s`, written
`Δ + inclusion` since its two summands act between different spaces. It multiplies the `n`-th
Fourier coefficient by `1 + (2πn/T)² ≥ 1`, and its inverse multiplies it by `(1 + (2πn/T)²)⁻¹`
(`CircleSobolev.coeff_laplacianAddInclusionEquiv_symm`), on every mode including the constant
one. -/
def laplacianAddInclusionEquiv : CircleSobolev (s + 2) E ≃L[ℂ] CircleSobolev s E :=
  ContinuousLinearEquiv.ofContinuousLinearMap (laplacian T le_rfl + inclusion (by linarith))
    (fourierMultiplierOfBound (fun n ↦ ((((1 + (2 * π * n / T) ^ 2)⁻¹ : ℝ)) : ℂ))
      (weight_mul_norm_resolventSymbol_le T hT.out.ne'))
    (ContinuousLinearMap.ext fun b ↦ CircleSobolev.ext (funext fun n ↦ by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        coeff_laplacian_add_inclusion, coeff_fourierMultiplierOfBound, smul_smul, mul_comm,
        inv_mul_one_add_eigenvalue, one_smul]))
    (ContinuousLinearMap.ext fun a ↦ CircleSobolev.ext (funext fun n ↦ by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        coeff_fourierMultiplierOfBound, coeff_laplacian_add_inclusion, smul_smul,
        inv_mul_one_add_eigenvalue, one_smul]))

@[simp]
theorem laplacianAddInclusionEquiv_apply (a : CircleSobolev (s + 2) E) :
    laplacianAddInclusionEquiv T a = laplacian T le_rfl a + inclusion (by linarith) a :=
  congrFun (ContinuousLinearEquiv.coe_ofContinuousLinearMap _ _ _ _) a

/-- The inverse of `1 + Δ` multiplies the `n`-th Fourier coefficient by `(1 + (2πn/T)²)⁻¹`. -/
@[simp]
theorem coeff_laplacianAddInclusionEquiv_symm (b : CircleSobolev s E) (n : ℤ) :
    ((laplacianAddInclusionEquiv T).symm b).coeff n =
      ((((1 + (2 * π * n / T) ^ 2)⁻¹ : ℝ)) : ℂ) • b.coeff n :=
  coeff_fourierMultiplierOfBound _ b n

/-! ### The Fredholm property -/

/-- The Laplacian is `1 + Δ` minus the inclusion `H^(s + 2) → H^s`. -/
private theorem laplacian_eq_laplacianAddInclusionEquiv_sub :
    (laplacian T le_rfl : CircleSobolev (s + 2) E →L[ℂ] CircleSobolev s E) =
      (laplacianAddInclusionEquiv (s := s) (E := E) T :
        CircleSobolev (s + 2) E →L[ℂ] CircleSobolev s E) + -inclusion (by linarith) := by
  ext a : 1
  simp

/-- **The circle Laplacian is Fredholm**: for finite-dimensional `E`, `Δ : H^(s + 2) → H^s` is a
Fredholm operator for every real `s`. It differs from the isomorphism `1 + Δ` by the inclusion
`H^(s + 2) → H^s`, which is compact by Rellich's theorem. -/
theorem isFredholm_laplacian [FiniteDimensional ℂ E] :
    (laplacian T le_rfl : CircleSobolev (s + 2) E →L[ℂ] CircleSobolev s E).IsFredholm := by
  have := FiniteDimensional.completeSpace ℂ E
  rw [laplacian_eq_laplacianAddInclusionEquiv_sub]
  exact (laplacianAddInclusionEquiv T).isFredholm.add_of_isCompactOperator
    (isCompactOperator_inclusion (by linarith)).neg

/-- The range of `Δ : H^(s + 2) → H^s` consists of the elements of mean zero: it is the kernel of
the constant Fourier coefficient. -/
theorem range_laplacian :
    (laplacian T le_rfl : CircleSobolev (s + 2) E →L[ℂ] CircleSobolev s E).toLinearMap.range =
      (coeffCLM 0 : CircleSobolev s E →L[ℂ] E).toLinearMap.ker := by
  ext b
  simpa using exists_laplacian_eq_iff T b

/-- **The circle Laplacian has index zero**: the kernel of `Δ : H^(s + 2) → H^s`, the constants,
and its cokernel, detected by the mean, are both identified with `E`. For finite-dimensional `E`
this is the Fredholm index `dim E - dim E` of the Fredholm operator `Δ`
(`CircleSobolev.isFredholm_laplacian`); for infinite-dimensional `E` both finranks are `0` by
convention, and the statement carries no information. -/
theorem index_laplacian :
    (laplacian T le_rfl : CircleSobolev (s + 2) E →L[ℂ] CircleSobolev s E).index = 0 := by
  rw [ContinuousLinearMap.index_def, LinearMap.index_eq_finrank_sub, sub_eq_zero]
  -- The constant term identifies the kernel with `E`.
  let eker : LinearMap.ker (laplacian T le_rfl : CircleSobolev (s + 2) E →L[ℂ]
      CircleSobolev s E).toLinearMap ≃ₗ[ℂ] E :=
    { toFun a := a.val.coeff 0
      invFun x := ⟨single 0 x, by simp⟩
      map_add' _ _ := by simp
      map_smul' _ _ := by simp
      left_inv a := Subtype.ext ((laplacian_eq_zero_iff T le_rfl a.val).1 a.property).symm
      right_inv x := by simp }
  -- The mean identifies the cokernel with `E`.
  have hsurj : Function.Surjective (coeffCLM 0 : CircleSobolev s E →L[ℂ] E) :=
    fun x ↦ ⟨single 0 x, by simp⟩
  let ecoker := (Submodule.quotEquivOfEq _ _ (range_laplacian T)).trans
    ((coeffCLM 0 : CircleSobolev s E →L[ℂ] E).toLinearMap.quotKerEquivOfSurjective hsurj)
  rw [eker.finrank_eq, ecoker.finrank_eq]

/-! ### The elliptic estimate and elliptic regularity -/

/-- **The elliptic estimate for the circle Laplacian**:
`‖a‖_{H^(s+2)} ≤ (T/π)² ‖Δ a‖_{H^s} + ‖a‖_{H^r}` for every `r ≤ s + 2`. The lower-order term
controls the constant term of `a`, on which `Δ` vanishes. -/
theorem norm_le_mul_norm_laplacian_add_norm_inclusion (hr : r ≤ s + 2)
    (a : CircleSobolev (s + 2) E) :
    ‖a‖ ≤ (T / π) ^ 2 * ‖laplacian T le_rfl a‖ + ‖inclusion hr a‖ := by
  have ha : a = greenOperator T (laplacian T le_rfl a) + single 0 (a.coeff 0) := by
    rw [greenOperator_laplacian, inclusion_refl, sub_add_cancel]
  have h0 : ‖a.coeff 0‖ ≤ ‖inclusion hr a‖ := by
    simpa using norm_coeff_le (inclusion hr a) 0
  calc ‖a‖ ≤ ‖greenOperator T (laplacian T le_rfl a)‖ + ‖single (s := s + 2) 0 (a.coeff 0)‖ := by
        conv_lhs => rw [ha]
        exact norm_add_le _ _
    _ ≤ (T / π) ^ 2 * ‖laplacian T le_rfl a‖ + ‖inclusion hr a‖ := by
        rw [norm_single, weight_zero_right, one_mul]
        exact add_le_add (norm_greenOperator_le T _) h0

omit hT in
/-- **Without the lower-order term the elliptic estimate fails**: if `E` is nontrivial, no
constant `C` satisfies `‖a‖_{H^t} ≤ C ‖Δ a‖_{H^s}` for all `a`, since `Δ` kills the nonzero
constants. -/
theorem not_exists_forall_norm_le_mul_norm_laplacian [Nontrivial E] (h : s + 2 ≤ t) :
    ¬∃ C : ℝ, ∀ a : CircleSobolev t E, ‖a‖ ≤ C * ‖laplacian T h a‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  exact hx (by simpa [norm_single] using hC (single 0 x))

/-- **On the complement of the kernel the lower-order term can be dropped**: an element `a` of
mean zero satisfies `‖a‖_{H^(s+2)} ≤ (T/π)² ‖Δ a‖_{H^s}`. -/
theorem norm_le_mul_norm_laplacian_of_coeff_zero_eq_zero {a : CircleSobolev (s + 2) E}
    (ha : a.coeff 0 = 0) : ‖a‖ ≤ (T / π) ^ 2 * ‖laplacian T le_rfl a‖ := by
  have hG : greenOperator T (laplacian T le_rfl a) = a := by
    rw [greenOperator_laplacian, ha, map_zero, sub_zero, inclusion_refl]
  calc ‖a‖ = ‖greenOperator T (laplacian T le_rfl a)‖ := by rw [hG]
    _ ≤ (T / π) ^ 2 * ‖laplacian T le_rfl a‖ := norm_greenOperator_le T _

/-- **Elliptic regularity for the circle Laplacian**: if `a ∈ H^t` and `Δ a ∈ H^r` lies in the
smaller space `H^s`, then `a ∈ H^(s + 2)`. Explicitly `a = G (Δ a) + Π a`. -/
theorem exists_inclusion_eq_of_laplacian_eq_inclusion (h : r + 2 ≤ t) (hts : t ≤ s + 2)
    (a : CircleSobolev t E) (b : CircleSobolev s E)
    (hab : laplacian T h a = inclusion (by linarith) b) :
    ∃ c : CircleSobolev (s + 2) E, inclusion hts c = a := by
  -- Applying `G` to `Δ a = b` gives `a - Π a = G b`.
  have hG : inclusion h (a - single 0 (a.coeff 0)) =
      inclusion (by linarith) (greenOperator T b) := by
    rw [← greenOperator_laplacian T, hab, greenOperator_inclusion]
  have hcoeff := congr_arg coeff hG
  rw [coeff_inclusion, coeff_inclusion] at hcoeff
  refine ⟨greenOperator T b + single 0 (a.coeff 0), CircleSobolev.ext ?_⟩
  rw [coeff_inclusion, coeff_add, ← hcoeff, coeff_sub]
  simp

/-! ### The Laplacian as an elliptic Fourier multiplier -/

section Symbol

open Asymptotics Filter

/-- The symbol `(2πn/T)²` of the Laplacian `Δ = -∂²` on `AddCircle T`: the factor by which `Δ`
multiplies the Fourier monomial `e^{2πinx/T}`. With the sign convention `Δ = -∂²` of this file it
is nonnegative, the opposite sign to `TauCeti.laplacianSymbol`. -/
def laplacianSymbol (n : ℤ) : ℂ := (((2 * π * n / T) ^ 2 : ℝ) : ℂ)

omit hT in
theorem laplacianSymbol_def (n : ℤ) : laplacianSymbol T n = (((2 * π * n / T) ^ 2 : ℝ) : ℂ) :=
  (rfl)

omit hT in
/-- On the circle of length `2π` the Laplacian symbol is `n²`. -/
@[simp]
theorem laplacianSymbol_two_pi (n : ℤ) : laplacianSymbol (2 * π) n = (n : ℂ) ^ 2 := by
  rw [laplacianSymbol_def, mul_div_cancel_left₀ _ (by positivity : (2 * π : ℝ) ≠ 0)]
  push_cast
  rfl

@[simp]
theorem laplacianSymbol_eq_zero_iff (n : ℤ) : laplacianSymbol T n = 0 ↔ n = 0 := by
  have := hT.out.ne'
  simp [laplacianSymbol_def, Real.pi_ne_zero, this]

theorem setOf_laplacianSymbol_eq_zero : {n | laplacianSymbol T n = 0} = {0} :=
  Set.ext fun n ↦ laplacianSymbol_eq_zero_iff T n

omit hT in
private theorem norm_laplacianSymbol (n : ℤ) :
    ‖laplacianSymbol T n‖ = (2 * π / T) ^ 2 * |(n : ℝ)| ^ 2 := by
  rw [laplacianSymbol_def, norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_abs]
  ring

/-- The Laplacian symbol is elliptic of order `2`: `(2πn/T)²` is comparable to `(1 + |n|)²` at
every frequency `n ≠ 0`. -/
theorem isTheta_laplacianSymbol : laplacianSymbol T =Θ[cofinite] weight 2 := by
  have hk : 0 < 2 * π / T := div_pos (by positivity) hT.out
  refine ⟨IsBigO.of_bound ((2 * π / T) ^ 2) (Eventually.of_forall fun n ↦ ?_),
    IsBigO.of_bound (4 * ((2 * π / T) ^ 2)⁻¹)
      ((Set.finite_singleton (0 : ℤ)).eventually_cofinite_notMem.mono fun n hn ↦ ?_)⟩
  · rw [norm_laplacianSymbol, norm_weight, weight_ofNat]
    have : |(n : ℝ)| ^ 2 ≤ (1 + |(n : ℝ)|) ^ 2 := by
      gcongr
      linarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  · rw [norm_laplacianSymbol, norm_weight, weight_ofNat]
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (by simpa using hn)
    rw [show 4 * ((2 * π / T) ^ 2)⁻¹ * ((2 * π / T) ^ 2 * |(n : ℝ)| ^ 2) = 4 * |(n : ℝ)| ^ 2 by
      field_simp [hk.ne', hT.out.ne']]
    nlinarith

/-- The Laplacian is minus the square of the derivative, through any intermediate order. -/
theorem laplacian_eq_neg_derivative_comp_derivative {u : ℝ} (h₁ : s + 1 ≤ u) (h₂ : u + 1 ≤ t) :
    laplacian T (by linarith) =
      -(derivative T h₁).comp (derivative T h₂ : CircleSobolev t E →L[ℂ] _) := by
  refine ContinuousLinearMap.ext fun a ↦ CircleSobolev.ext (funext fun n ↦ ?_)
  rw [coeff_laplacian, neg_apply, ContinuousLinearMap.comp_apply, coeff_neg,
    Pi.neg_apply, coeff_derivative, coeff_derivative, smul_smul, ← neg_smul]
  congr 1
  push_cast
  linear_combination ((2 * π * n / T : ℂ) ^ 2) * I_sq

/-- The Laplacian is the Fourier multiplier with the elliptic symbol `laplacianSymbol T` of order
`2`, so the general results on elliptic Fourier multipliers apply to it. -/
theorem laplacian_eq_fourierMultiplier (h : s + 2 ≤ t) :
    (laplacian T h : CircleSobolev t E →L[ℂ] CircleSobolev s E) =
      fourierMultiplier (laplacianSymbol T) (isTheta_laplacianSymbol T).isBigO h :=
  ContinuousLinearMap.ext fun a ↦ CircleSobolev.ext (funext fun n ↦ by
    rw [coeff_laplacian, coeff_fourierMultiplier, laplacianSymbol_def])

/-- The Green operator is the Fourier multiplier with the inverse symbol `(laplacianSymbol T)⁻¹`
of order `-2`, the parametrix of the general theory. -/
theorem greenOperator_eq_fourierMultiplier :
    (greenOperator T : CircleSobolev s E →L[ℂ] CircleSobolev (s + 2) E) =
      fourierMultiplier (fun n ↦ (laplacianSymbol T n)⁻¹)
        (isBigO_inv (isTheta_laplacianSymbol T).isBigO_symm) (by linarith) :=
  ContinuousLinearMap.ext fun b ↦ CircleSobolev.ext (funext fun n ↦ by
    rw [coeff_greenOperator, coeff_fourierMultiplier, laplacianSymbol_def, ← ofReal_inv,
      ← inv_pow, inv_div])

/-- The frequency projection onto the zero modes of the Laplacian is the projection onto the
constants. -/
theorem indicator_setOf_laplacianSymbol_eq_zero (a : CircleSobolev s E) :
    indicator {n | laplacianSymbol T n = 0} a = single 0 (a.coeff 0) := by
  rw [setOf_laplacianSymbol_eq_zero]
  exact CircleSobolev.ext (funext fun n ↦ by
    rcases eq_or_ne n 0 with rfl | hn <;> simp [*])

/-- The elements supported off the zero modes of the Laplacian are the mean-zero elements. -/
theorem mem_supported_compl_setOf_laplacianSymbol_eq_zero_iff (a : CircleSobolev s E) :
    a ∈ supported s E {n | laplacianSymbol T n = 0}ᶜ ↔ a.coeff 0 = 0 := by
  rw [setOf_laplacianSymbol_eq_zero, mem_supported']
  simp

end Symbol

end CircleSobolev

end TauCeti
