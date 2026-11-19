/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Derivative
public import TauCeti.Analysis.Sobolev.Circle.FourierMultiplier

/-!
# The Laplacian on the circle

On the circle `AddCircle T` the nonnegative Laplacian `Δ = -∂²` multiplies the Fourier monomial
`e^{2πinx/T}` by `(2πn/T)²` (`TauCeti.CircleSobolev.laplacianSymbol`); for `T = 2π` this is `n²`.
It is an elliptic Fourier multiplier of order `2`, so the elliptic theory of
`TauCeti/Analysis/Sobolev/Circle/FourierMultiplier.lean` applies to it, and it shows what that
theory does and does not give when the operator has a kernel.

* The kernel of `Δ : H^t → H^s` consists of the constants, and `Δ` is Fredholm of index zero.
* `Δ a = b` is solvable exactly when `b` has mean zero, that is `b.coeff 0 = 0`; in particular
  `Δ u = 1` has no solution.
* Since `Δ 1 = 0` while `1 ≠ 0`, no estimate `‖a‖_{H^t} ≤ C ‖Δ a‖_{H^s}` holds on all of `H^t`;
  it does hold on the mean-zero elements.
* The multiplier `G` with symbol `(2πn/T)⁻²` for `n ≠ 0` and `0` for `n = 0`, the Green operator,
  satisfies `Δ G = G Δ = 1 - Π₀`, where `Π₀ a = a.coeff 0` is the projection onto the constants.
* `1 + Δ = 1 - ∂²` has no kernel: it multiplies `e^{2πinx/T}` by `1 + (2πn/T)²`, which does not
  vanish even at `n = 0`, and it is an isomorphism `H^(s + 2) ≃ H^s` whose inverse divides by
  this factor (`TauCeti.CircleSobolev.oneAddLaplacianEquiv`).

## Main definitions

* `TauCeti.CircleSobolev.laplacianSymbol T n = (2πn/T)²`.
* `TauCeti.CircleSobolev.laplacian T h`: the Laplacian `-∂²` as a bounded operator `H^t → H^s`
  for `s + 2 ≤ t`.
* `TauCeti.CircleSobolev.oneAddLaplacianEquiv T h`: the isomorphism `1 - ∂² : H^t ≃ H^s` for
  `s + 2 = t`.

## Main statements

* `TauCeti.CircleSobolev.laplacian_eq_neg_derivative_comp_derivative`: `Δ = -∂ ∘ ∂`.
* `TauCeti.CircleSobolev.laplacian_eq_zero_iff`, `TauCeti.CircleSobolev.mem_range_laplacian_iff`:
  the kernel is the constants and the range is the mean-zero elements.
* `TauCeti.CircleSobolev.single_zero_notMem_range_laplacian`: `Δ u = 1` has no solution.
* `TauCeti.CircleSobolev.not_exists_norm_le_laplacian` and
  `TauCeti.CircleSobolev.exists_norm_le_laplacian_of_coeff_zero_eq_zero`: the estimate without a
  lower-order term fails on `H^t`, and holds on the mean-zero elements.
* `TauCeti.CircleSobolev.laplacian_greenOperator`,
  `TauCeti.CircleSobolev.greenOperator_laplacian`: `Δ G = G Δ = 1 - Π₀`.
* `TauCeti.CircleSobolev.isFredholm_laplacian`, `TauCeti.CircleSobolev.index_laplacian`.

## References

* M. E. Taylor, *Partial Differential Equations I*, Chapter 3, §1 (the Laplacian on the torus
  via Fourier series) and Chapter 5, §1.
-/

public section

noncomputable section

open Asymptotics Filter Real

namespace TauCeti

namespace CircleSobolev

variable {s t : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (T : ℝ) [hT : Fact (0 < T)]

/-- The symbol `(2πn/T)²` of the nonnegative Laplacian `-∂²` on `AddCircle T`: the factor by
which `-∂²` multiplies the Fourier monomial `e^{2πinx/T}`. -/
def laplacianSymbol (n : ℤ) : ℂ := ((2 * π * n / T) ^ 2 : ℝ)

omit hT in
theorem laplacianSymbol_def (n : ℤ) : laplacianSymbol T n = ((2 * π * n / T) ^ 2 : ℝ) :=
  (rfl)

omit hT in
/-- On the circle of length `2π` the Laplacian symbol is `n²`. -/
@[simp]
theorem laplacianSymbol_two_pi (n : ℤ) : laplacianSymbol (2 * π) n = (n : ℂ) ^ 2 := by
  rw [laplacianSymbol_def, mul_div_cancel_left₀ _ (by positivity : (2 * π : ℝ) ≠ 0)]
  push_cast
  ring

theorem laplacianSymbol_eq_zero_iff (n : ℤ) : laplacianSymbol T n = 0 ↔ n = 0 := by
  have := hT.out.ne'
  simp [laplacianSymbol_def, Real.pi_ne_zero, this]

theorem setOf_laplacianSymbol_eq_zero : {n | laplacianSymbol T n = 0} = {0} :=
  Set.ext fun n ↦ laplacianSymbol_eq_zero_iff T n

omit hT in
private theorem norm_laplacianSymbol (n : ℤ) :
    ‖laplacianSymbol T n‖ = (2 * π / T) ^ 2 * |(n : ℝ)| ^ 2 := by
  rw [laplacianSymbol_def, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    sq_abs]
  ring

private theorem weight_two (n : ℤ) : weight 2 n = (1 + |(n : ℝ)|) ^ 2 := by
  rw [weight_def, ← Real.rpow_natCast]
  norm_num

/-- The Laplacian symbol is elliptic of order `2`: `(2πn/T)²` is comparable to `(1 + |n|)²` at
every frequency `n ≠ 0`. -/
theorem isTheta_laplacianSymbol : laplacianSymbol T =Θ[cofinite] weight 2 := by
  have hk : 0 < 2 * π / T := div_pos (by positivity) hT.out
  refine ⟨IsBigO.of_bound ((2 * π / T) ^ 2) (Eventually.of_forall fun n ↦ ?_),
    IsBigO.of_bound (4 * ((2 * π / T) ^ 2)⁻¹)
      ((Set.finite_singleton (0 : ℤ)).eventually_cofinite_notMem.mono fun n hn ↦ ?_)⟩
  · rw [norm_laplacianSymbol, norm_weight, weight_two]
    have : |(n : ℝ)| ^ 2 ≤ (1 + |(n : ℝ)|) ^ 2 := by
      gcongr
      linarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  · rw [norm_laplacianSymbol, norm_weight, weight_two]
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (by simpa using hn)
    rw [show 4 * ((2 * π / T) ^ 2)⁻¹ * ((2 * π / T) ^ 2 * |(n : ℝ)| ^ 2) = 4 * |(n : ℝ)| ^ 2 by
      field_simp [hk.ne', hT.out.ne']]
    nlinarith

/-- The nonnegative Laplacian `Δ = -∂²` on the circle `AddCircle T`, as a bounded operator
`H^t → H^s` for `s + 2 ≤ t`: it multiplies the `n`-th Fourier coefficient by `(2πn/T)²`. -/
def laplacian (h : s + 2 ≤ t) : CircleSobolev t E →L[ℂ] CircleSobolev s E :=
  fourierMultiplier (laplacianSymbol T) (isTheta_laplacianSymbol T).1 h

@[simp]
theorem coeff_laplacian (h : s + 2 ≤ t) (a : CircleSobolev t E) (n : ℤ) :
    (laplacian T h a).coeff n = laplacianSymbol T n • a.coeff n :=
  coeff_fourierMultiplier _ h a n

@[simp]
theorem laplacian_single (h : s + 2 ≤ t) (n : ℤ) (x : E) :
    laplacian T h (single n x) = single n (laplacianSymbol T n • x) :=
  fourierMultiplier_single _ h n x

/-- The Laplacian is minus the square of the derivative. -/
theorem laplacian_eq_neg_derivative_comp_derivative {u : ℝ} (h₁ : s + 1 ≤ u) (h₂ : u + 1 ≤ t) :
    laplacian T (by linarith) =
      -(derivative T h₁).comp (derivative T h₂ : CircleSobolev t E →L[ℂ] _) := by
  refine ContinuousLinearMap.ext fun a ↦ CircleSobolev.ext (funext fun n ↦ ?_)
  simp only [coeff_laplacian, FunLike.coe_neg, Pi.neg_apply,
    ContinuousLinearMap.comp_apply, coeff_neg, coeff_derivative, smul_smul, ← neg_smul,
    laplacianSymbol_def]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The kernel of the Laplacian is the constants**: `Δ a = 0` exactly when every Fourier
coefficient of `a` other than the zeroth one vanishes. -/
theorem laplacian_eq_zero_iff (h : s + 2 ≤ t) (a : CircleSobolev t E) :
    laplacian T h a = 0 ↔ a = single 0 (a.coeff 0) := by
  rw [laplacian, fourierMultiplier_eq_zero_iff]
  refine ⟨fun ha ↦ CircleSobolev.ext (funext fun n ↦ ?_), fun ha n hn ↦ ?_⟩
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn, ha n ((laplacianSymbol_eq_zero_iff T n).not.2 hn)]
  · rw [ha]
    simp [(laplacianSymbol_eq_zero_iff T n).not.1 hn]

/-- **Solvability of `Δ a = b`**: for `s + 2 = t`, an element `b ∈ H^s` is `Δ a` for some
`a ∈ H^t` exactly when it has mean zero, `b.coeff 0 = 0`. -/
theorem mem_range_laplacian_iff (h : s + 2 = t) (b : CircleSobolev s E) :
    b ∈ (laplacian T h.le : CircleSobolev t E →L[ℂ] CircleSobolev s E).range ↔ b.coeff 0 = 0 := by
  rw [laplacian, mem_range_fourierMultiplier_iff (isTheta_laplacianSymbol T) h]
  exact ⟨fun hb ↦ hb 0 ((laplacianSymbol_eq_zero_iff T 0).2 rfl),
    fun hb n hn ↦ (laplacianSymbol_eq_zero_iff T n).1 hn ▸ hb⟩

/-- **`Δ u = 1` has no solution**: a nonzero constant is not in the range of the Laplacian,
since it does not have mean zero. -/
theorem single_zero_notMem_range_laplacian (h : s + 2 = t) {x : E} (hx : x ≠ 0) :
    single 0 x ∉ (laplacian T h.le : CircleSobolev t E →L[ℂ] CircleSobolev s E).range := by
  rw [mem_range_laplacian_iff T h]
  simpa using hx

/-- **The estimate without a lower-order term fails**: since `Δ 1 = 0` while `‖1‖_{H^t} > 0`, no
bound `‖a‖_{H^t} ≤ C ‖Δ a‖_{H^s}` holds on all of `H^t`. -/
theorem not_exists_norm_le_laplacian [Nontrivial E] (h : s + 2 ≤ t) :
    ¬ ∃ C, ∀ a : CircleSobolev t E, ‖a‖ ≤ C * ‖laplacian T h a‖ :=
  not_exists_norm_le_of_eq_zero _ h ((laplacianSymbol_eq_zero_iff T 0).2 rfl)

/-- **The estimate on the mean-zero elements**: for `s + 2 = t` there is `C` with
`‖a‖_{H^t} ≤ C ‖Δ a‖_{H^s}` for every `a ∈ H^t` of mean zero. -/
theorem exists_norm_le_laplacian_of_coeff_zero_eq_zero (h : s + 2 = t) :
    ∃ C, ∀ a : CircleSobolev t E, a.coeff 0 = 0 → ‖a‖ ≤ C * ‖laplacian T h.le a‖ := by
  obtain ⟨C, hC⟩ := exists_norm_sub_modeProjection_le (E := E) (isTheta_laplacianSymbol T) h
  refine ⟨C, fun a ha ↦ ?_⟩
  have hproj : modeProjection {n | laplacianSymbol T n = 0} a = 0 := by
    rw [setOf_laplacianSymbol_eq_zero]
    exact CircleSobolev.ext (funext fun n ↦ by
      rcases eq_or_ne n 0 with rfl | hn <;> simp [*])
  simpa [laplacian, hproj] using hC a

/-- The projection onto the zero modes of the Laplacian is the projection onto the constants. -/
theorem modeProjection_setOf_laplacianSymbol_eq_zero (a : CircleSobolev s E) :
    modeProjection {n | laplacianSymbol T n = 0} a = single 0 (a.coeff 0) := by
  rw [setOf_laplacianSymbol_eq_zero]
  exact CircleSobolev.ext (funext fun n ↦ by
    rcases eq_or_ne n 0 with rfl | hn <;> simp [*])

/-- **The Green operator of the Laplacian**: the multiplier `G` with symbol `(2πn/T)⁻²` for
`n ≠ 0` and `0` for `n = 0` satisfies `Δ G b = b - b.coeff 0`. -/
theorem laplacian_greenOperator (h : s + 2 = t) (b : CircleSobolev s E) :
    laplacian T h.le (fourierMultiplier (fun n ↦ (laplacianSymbol T n)⁻¹)
        (isBigO_inv (isTheta_laplacianSymbol T).2) (show t + -2 ≤ s by linarith) b) =
      b - single 0 (b.coeff 0) := by
  rw [laplacian, fourierMultiplier_fourierMultiplier_inv (isTheta_laplacianSymbol T) h,
    modeProjection_setOf_laplacianSymbol_eq_zero]

/-- **The Green operator of the Laplacian** is also a left inverse up to the constants:
`G Δ a = a - a.coeff 0`. -/
theorem greenOperator_laplacian (h : s + 2 = t) (a : CircleSobolev t E) :
    fourierMultiplier (fun n ↦ (laplacianSymbol T n)⁻¹)
        (isBigO_inv (isTheta_laplacianSymbol T).2) (show t + -2 ≤ s by linarith)
        (laplacian T h.le a) =
      a - single 0 (a.coeff 0) := by
  rw [laplacian, fourierMultiplier_inv_fourierMultiplier (isTheta_laplacianSymbol T) h,
    modeProjection_setOf_laplacianSymbol_eq_zero]

/-- The Laplacian `H^t → H^s`, `s + 2 = t`, is a Fredholm operator. -/
theorem isFredholm_laplacian [FiniteDimensional ℂ E] (h : s + 2 = t) :
    (laplacian T h.le : CircleSobolev t E →L[ℂ] CircleSobolev s E).IsFredholm :=
  isFredholm_fourierMultiplier (isTheta_laplacianSymbol T) h

/-- The Laplacian has index zero: its kernel and cokernel are both the constants. -/
@[simp]
theorem index_laplacian [FiniteDimensional ℂ E] (h : s + 2 = t) :
    (laplacian T h.le : CircleSobolev t E →L[ℂ] CircleSobolev s E).index = 0 :=
  index_fourierMultiplier (isTheta_laplacianSymbol T) h

/-! ### The operator `1 - ∂²` -/

/-- The symbol `1 + (2πn/T)²` of `1 + Δ = 1 - ∂²` is elliptic of order `2`. -/
theorem isTheta_one_add_laplacianSymbol :
    (fun n ↦ 1 + laplacianSymbol T n) =Θ[cofinite] weight 2 := by
  have hk : 0 < 2 * π / T := div_pos (by positivity) hT.out
  have hnorm (n : ℤ) : ‖1 + laplacianSymbol T n‖ = 1 + (2 * π / T) ^ 2 * |(n : ℝ)| ^ 2 := by
    rw [laplacianSymbol_def, ← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity), ← sq_abs (2 * π * n / T), abs_div,
      abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), abs_of_pos hT.out]
    ring
  refine ⟨IsBigO.of_bound (1 + (2 * π / T) ^ 2) (Eventually.of_forall fun n ↦ ?_),
    IsBigO.of_bound (2 * (1 + ((2 * π / T) ^ 2)⁻¹)) (Eventually.of_forall fun n ↦ ?_)⟩
  · rw [hnorm, norm_weight, weight_two]
    have h0 : 0 ≤ |(n : ℝ)| := abs_nonneg _
    nlinarith [sq_nonneg (2 * π / T)]
  · rw [hnorm, norm_weight, weight_two]
    have hk2 : 0 < (2 * π / T) ^ 2 := by positivity
    have hinv : ((2 * π / T) ^ 2)⁻¹ * (2 * π / T) ^ 2 = 1 := inv_mul_cancel₀ hk2.ne'
    nlinarith [sq_nonneg (|(n : ℝ)| - 1), mul_nonneg (inv_nonneg.2 hk2.le) (sq_nonneg |(n : ℝ)|),
      mul_nonneg hk2.le (sq_nonneg |(n : ℝ)|)]

omit hT in
/-- The symbol `1 + (2πn/T)²` of `1 - ∂²` vanishes nowhere, not even at `n = 0`. -/
theorem one_add_laplacianSymbol_ne_zero (n : ℤ) : 1 + laplacianSymbol T n ≠ 0 := by
  rw [laplacianSymbol_def, ← Complex.ofReal_one, ← Complex.ofReal_add, Complex.ofReal_ne_zero]
  positivity

/-- **`1 - ∂²` is an isomorphism** `H^t ≃ H^s` for `s + 2 = t`: it multiplies the `n`-th Fourier
coefficient by `1 + (2πn/T)²` and its inverse, which gains two orders of regularity, divides by
it. -/
def oneAddLaplacianEquiv (h : s + 2 = t) : CircleSobolev t E ≃L[ℂ] CircleSobolev s E :=
  fourierMultiplierEquiv (isTheta_one_add_laplacianSymbol T) (one_add_laplacianSymbol_ne_zero T) h

@[simp]
theorem coeff_oneAddLaplacianEquiv (h : s + 2 = t) (a : CircleSobolev t E) (n : ℤ) :
    (oneAddLaplacianEquiv T h a).coeff n = (1 + laplacianSymbol T n) • a.coeff n := by
  simp [oneAddLaplacianEquiv]

@[simp]
theorem coeff_oneAddLaplacianEquiv_symm (h : s + 2 = t) (b : CircleSobolev s E) (n : ℤ) :
    ((oneAddLaplacianEquiv T h).symm b).coeff n = (1 + laplacianSymbol T n)⁻¹ • b.coeff n := by
  simp [oneAddLaplacianEquiv]

/-- `1 - ∂²` is the sum of the inclusion and the Laplacian. -/
theorem oneAddLaplacianEquiv_apply (h : s + 2 = t) (a : CircleSobolev t E) :
    oneAddLaplacianEquiv T h a = inclusion (by linarith) a + laplacian T h.le a :=
  CircleSobolev.ext (funext fun n ↦ by simp [add_smul])

end CircleSobolev

end TauCeti
