/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs

import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Fourier.Decay

/-!
# Multiplication operators on the Sobolev spaces of the circle

On Fourier coefficients, multiplying a function on the circle by the monomial `e^{imθ}` shifts the
coefficients by `m`, and multiplying by `g = ∑ₘ gₘ e^{imθ}` convolves them with `(gₘ)`. This file
constructs these operators on the Fourier-coefficient Sobolev spaces `H^s` of
`TauCeti/Analysis/Sobolev/Circle/Basic.lean`, for every real order `s`, including negative and
fractional orders where elements of `H^s` are not functions.

By Peetre's inequality (`CircleSobolev.weight_add_le`), the shift by `m` has norm at most
`(1 + |m|) ^ |s|` on `H^s`. The multiplication operator by the coefficient sequence `g` is then
the operator-norm convergent series `∑ₘ gₘ • shift m`, as soon as
`∑ₘ (1 + |m|) ^ |s| ‖gₘ‖ < ∞`. A smooth function on the circle has rapidly decaying Fourier
coefficients, so it satisfies this for every `s`: multiplication by a smooth function is a bounded
operator on every `H^s`, and it is invertible when the function vanishes nowhere. Such multipliers
are needed to patch boundary estimates with smooth partitions of unity and cutoffs.

## Main definitions

* `TauCeti.CircleSobolev.shift m`: multiplication by `e^{imθ}`, shifting the Fourier coefficients
  by `m`.
* `TauCeti.CircleSobolev.multiplier g`: multiplication by the function with Fourier coefficients
  `g`, defined as `∑ₘ g m • shift m`.
* `TauCeti.CircleSobolev.multiplierEquiv`: for a smooth nowhere-vanishing function `f`,
  multiplication by `f` as a continuous linear automorphism of `H^s`.

## Main statements

* `TauCeti.CircleSobolev.norm_shift_le`: `‖shift m a‖ ≤ (1 + |m|) ^ |s| ‖a‖`.
* `TauCeti.CircleSobolev.norm_multiplier_le`: the operator norm of `multiplier g` on `H^s` is at
  most `∑ₘ (1 + |m|) ^ |s| ‖g m‖`.
* `TauCeti.CircleSobolev.coeff_multiplier`: the Fourier coefficients of `multiplier g a` are the
  convolution `∑ₘ g m • a.coeff (n - m)`.
* `TauCeti.CircleSobolev.toContinuousMap_multiplier_fourierCoeff`: for `s > 1/2`, the operator
  `multiplier (fourierCoeff f)` is pointwise multiplication by `f` on continuous representatives.
* `TauCeti.CircleSobolev.summable_weight_mul_norm_fourierCoeff`: a `C^k` function on the circle
  satisfies the summability hypothesis of `multiplier` on `H^s` for `|s| < k - 1`, so a smooth
  function satisfies it for every order.
* `TauCeti.CircleSobolev.multiplier_fourierCoeff_comp`: for smooth `f` and `g`, multiplication by
  `f` after multiplication by `g` is multiplication by `f * g`.

## References

* M. E. Taylor, *Partial Differential Equations I*, Chapter 3 (Sobolev spaces on the torus via
  Fourier series, and multiplication by smooth functions).
-/

public section

noncomputable section

open scoped ContDiff

namespace TauCeti

namespace CircleSobolev

variable {s t : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### Shifts of the Fourier coefficients -/

/-- Peetre's inequality bounds the weighted coefficients of a shift by the reindexed weighted
coefficients. -/
private theorem weight_mul_norm_coeff_sub_le (m : ℤ) (a : CircleSobolev s E) (n : ℤ) :
    weight s n * ‖a.coeff (n - m)‖ ≤ weight |s| m * (weight s (n - m) * ‖a.coeff (n - m)‖) := by
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  simpa using weight_add_le s m (n - m)

private theorem memℓp_shift (m : ℤ) (a : CircleSobolev s E) :
    Memℓp (fun n ↦ weight s n • a.coeff (n - m)) 2 := by
  have h : Memℓp (fun n ↦ weight s (n - m) • a.coeff (n - m)) 2 := by
    have ha := a.memℓp_weight_smul_coeff
    rw [memℓp_gen_iff (by norm_num)] at ha ⊢
    exact (Equiv.subRight m).summable_iff.2 ha
  refine (h.const_smul (weight |s| m)).mono' fun n ↦ ?_
  simp only [Pi.smul_apply, norm_smul, norm_weight]
  exact weight_mul_norm_coeff_sub_le m a n

private theorem norm_shift_le' (m : ℤ) (a : CircleSobolev s E) :
    ‖(⟨fun n ↦ a.coeff (n - m), memℓp_shift m a⟩ : CircleSobolev s E)‖ ≤ weight |s| m * ‖a‖ := by
  have ha : HasSum (fun n ↦ (weight s (n - m) * ‖a.coeff (n - m)‖) ^ 2) (‖a‖ ^ 2) :=
    (Equiv.subRight m).hasSum_iff.2 (hasSum_sq_weight_mul_norm_coeff a)
  have hle : ‖(⟨fun n ↦ a.coeff (n - m), memℓp_shift m a⟩ : CircleSobolev s E)‖ ^ 2 ≤
      (weight |s| m * ‖a‖) ^ 2 := by
    rw [mul_pow]
    refine hasSum_le (fun n ↦ ?_) (hasSum_sq_weight_mul_norm_coeff _) (ha.mul_left _)
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg (weight_nonneg s n) (norm_nonneg _))
      (weight_mul_norm_coeff_sub_le m a n) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (weight_nonneg _ _) (norm_nonneg _)) two_ne_zero).1 hle

/-- Multiplication by the Fourier monomial `e^{imθ}`, which shifts the Fourier coefficients by
`m`. -/
def shift (m : ℤ) : CircleSobolev s E →L[ℂ] CircleSobolev s E :=
  LinearMap.mkContinuous
    { toFun a := ⟨fun n ↦ a.coeff (n - m), memℓp_shift m a⟩
      map_add' _ _ := (rfl)
      map_smul' _ _ := (rfl) }
    (weight |s| m) (norm_shift_le' m)

@[simp]
theorem coeff_shift (m : ℤ) (a : CircleSobolev s E) (n : ℤ) :
    (shift m a).coeff n = a.coeff (n - m) :=
  (rfl)

/-- The shift by `m` changes the `H^s` norm by at most the factor `(1 + |m|) ^ |s|`. -/
theorem norm_shift_le (m : ℤ) (a : CircleSobolev s E) : ‖shift m a‖ ≤ weight |s| m * ‖a‖ :=
  norm_shift_le' m a

theorem opNorm_shift_le (m : ℤ) : ‖(shift m : CircleSobolev s E →L[ℂ] _)‖ ≤ weight |s| m :=
  ContinuousLinearMap.opNorm_le_bound _ (weight_nonneg _ _) (norm_shift_le m)

@[simp]
theorem shift_zero (a : CircleSobolev s E) : shift 0 a = a :=
  CircleSobolev.ext (funext fun n ↦ by simp)

@[simp]
theorem shift_shift (m k : ℤ) (a : CircleSobolev s E) : shift m (shift k a) = shift (m + k) a :=
  CircleSobolev.ext (funext fun n ↦ by simp [sub_sub])

@[simp]
theorem shift_single (m n : ℤ) (x : E) :
    shift m (single (s := s) n x) = single (m + n) x := by
  refine CircleSobolev.ext (funext fun p ↦ ?_)
  simp only [coeff_shift, coeff_single, Pi.single_apply, sub_eq_iff_eq_add']

@[simp]
theorem inclusion_shift (h : t ≤ s) (m : ℤ) (a : CircleSobolev s E) :
    inclusion h (shift m a) = shift m (inclusion h a) :=
  CircleSobolev.ext (funext fun n ↦ by simp)

/-- For `s > 1/2`, the shift by `m` is multiplication by `e^{2πimx/T}` on continuous
representatives. -/
theorem toContinuousMap_shift (T : ℝ) [Fact (0 < T)] [CompleteSpace E] (hs : 1 / 2 < s) (m : ℤ)
    (a : CircleSobolev s E) (x : AddCircle T) :
    toContinuousMap T hs (shift m a) x = fourier m x • toContinuousMap T hs a x := by
  rw [toContinuousMap_apply, toContinuousMap_apply, ← tsum_const_smul'',
    ← (Equiv.addRight m).tsum_eq]
  refine tsum_congr fun n ↦ ?_
  simp [mul_comm, mul_smul]

/-! ### Multiplication operators -/

variable {g : ℤ → ℂ}

/-- The operator of multiplication by the function with Fourier coefficients `g`, defined as the
series `∑ₘ g m • shift m`. This is a pointwise multiplier, not a Fourier multiplier: on
coefficients it acts by convolution with `g` (`coeff_multiplier`). The series converges in
operator norm on `H^s` when `∑ₘ (1 + |m|) ^ |s| ‖g m‖ < ∞` (`hasSum_multiplier`), in particular
when `g` is the sequence of Fourier coefficients of a sufficiently smooth function
(`summable_weight_mul_norm_fourierCoeff`). -/
def multiplier (g : ℤ → ℂ) : CircleSobolev s E →L[ℂ] CircleSobolev s E :=
  ∑' m, g m • shift m

private theorem norm_smul_shift_le (m : ℤ) :
    ‖g m • (shift m : CircleSobolev s E →L[ℂ] CircleSobolev s E)‖ ≤ weight |s| m * ‖g m‖ := by
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right (opNorm_shift_le m) (norm_nonneg _)

/-- The operator norm of `multiplier g` on `H^s` is at most `∑ₘ (1 + |m|) ^ |s| ‖g m‖`. -/
theorem norm_multiplier_le (hg : Summable fun m ↦ weight |s| m * ‖g m‖) :
    ‖(multiplier g : CircleSobolev s E →L[ℂ] CircleSobolev s E)‖ ≤
      ∑' m, weight |s| m * ‖g m‖ :=
  tsum_of_norm_bounded hg.hasSum norm_smul_shift_le

variable [CompleteSpace E]

/-- The series defining `multiplier g` converges in operator norm when the coefficients `g` are
summable against the weights of order `|s|`. -/
theorem hasSum_multiplier (hg : Summable fun m ↦ weight |s| m * ‖g m‖) :
    HasSum (fun m ↦ g m • (shift m : CircleSobolev s E →L[ℂ] CircleSobolev s E))
      (multiplier g) :=
  (Summable.of_norm_bounded hg norm_smul_shift_le).hasSum

theorem hasSum_multiplier_apply (hg : Summable fun m ↦ weight |s| m * ‖g m‖)
    (a : CircleSobolev s E) : HasSum (fun m ↦ g m • shift m a) (multiplier g a) :=
  (hasSum_multiplier hg).mapL (ContinuousLinearMap.apply ℂ _ a)

/-- The Fourier coefficients of `multiplier g a` are the convolution of `g` with those of `a`. -/
theorem coeff_multiplier (hg : Summable fun m ↦ weight |s| m * ‖g m‖) (a : CircleSobolev s E)
    (n : ℤ) : (multiplier g a).coeff n = ∑' m, g m • a.coeff (n - m) := by
  have h := (hasSum_multiplier_apply hg a).mapL (coeffCLM n)
  simp only [coeffCLM_apply, coeff_smul, coeff_shift, Pi.smul_apply] at h
  exact h.tsum_eq.symm

/-- Multiplication operators commute with the inclusions between the Sobolev spaces. -/
theorem inclusion_multiplier (h : t ≤ s) (hgs : Summable fun m ↦ weight |s| m * ‖g m‖)
    (hgt : Summable fun m ↦ weight |t| m * ‖g m‖) (a : CircleSobolev s E) :
    inclusion h (multiplier g a) = multiplier g (inclusion h a) :=
  CircleSobolev.ext (funext fun n ↦ by simp [coeff_multiplier hgs, coeff_multiplier hgt])

section Continuous

variable (T : ℝ) [Fact (0 < T)]

/-- For `s > 1/2`, `multiplier g` is pointwise multiplication by `∑ₘ g m e^{2πimx/T}` on continuous
representatives. -/
theorem toContinuousMap_multiplier (hs : 1 / 2 < s) (hg : Summable fun m ↦ weight |s| m * ‖g m‖)
    (a : CircleSobolev s E) (x : AddCircle T) :
    toContinuousMap T hs (multiplier g a) x =
      (∑' m, g m * fourier m x) • toContinuousMap T hs a x := by
  have hsum : Summable fun m ↦ g m * fourier m x :=
    Summable.of_norm_bounded hg fun m ↦ by
      simpa [fourier_apply] using le_mul_of_one_le_left (norm_nonneg (g m))
        (one_le_weight (abs_nonneg s) m)
  refine ((hasSum_multiplier_apply hg a).mapL
    ((ContinuousMap.evalCLM ℂ x).comp (toContinuousMap T hs))).unique ?_
  simpa [toContinuousMap_shift, mul_smul] using hsum.hasSum.smul_const (toContinuousMap T hs a x)

/-- For a continuous function `f` on the circle whose Fourier coefficients are summable against
the weights of order `|s|`, with `s > 1/2`, the operator `multiplier (fourierCoeff f)` is
pointwise multiplication by `f` on continuous representatives. -/
theorem toContinuousMap_multiplier_fourierCoeff (hs : 1 / 2 < s) {f : AddCircle T → ℂ}
    (hfc : Continuous f) (hf : Summable fun m ↦ weight |s| m * ‖fourierCoeff f m‖)
    (a : CircleSobolev s E) (x : AddCircle T) :
    toContinuousMap T hs (multiplier (fourierCoeff f) a) x = f x • toContinuousMap T hs a x := by
  have hsum : Summable (fourierCoeff (⟨f, hfc⟩ : C(AddCircle T, ℂ))) :=
    Summable.of_norm_bounded hf fun m ↦
      le_mul_of_one_le_left (norm_nonneg _) (one_le_weight (abs_nonneg s) m)
  rw [toContinuousMap_multiplier T hs hf]
  congr 1
  simpa using (has_pointwise_sum_fourier_series_of_summable hsum x).tsum_eq

end Continuous

/-! ### Multiplication by smooth functions -/

section Smooth

variable {T : ℝ} [Fact (0 < T)]

/-- The Fourier coefficients of a `C^k` function on the circle are summable against the weights
`(1 + |n|) ^ r` of every order `r < k - 1`. In particular, multiplication by a `C^k` function is
bounded on `H^s` whenever `|s| < k - 1` (`norm_multiplier_le`). -/
theorem summable_weight_mul_norm_fourierCoeff {f : AddCircle T → ℂ} {k : ℕ}
    (hf : ContDiff ℝ k fun x : ℝ ↦ f x) {r : ℝ} (hr : r + 1 < k) :
    Summable fun n ↦ weight r n * ‖fourierCoeff f n‖ := by
  obtain ⟨C₀, hC₀⟩ := exists_abs_pow_mul_norm_fourierCoeff_le (k := 0) (hf.of_le (by simp))
  obtain ⟨C, hC⟩ := exists_abs_pow_mul_norm_fourierCoeff_le hf
  have hC₀' : ∀ n, ‖fourierCoeff f n‖ ≤ C₀ := fun n ↦ by simpa using hC₀ n
  have hbound (n : ℤ) : (1 + |(n : ℝ)|) ^ k * ‖fourierCoeff f n‖ ≤ 2 ^ k * max C₀ C := by
    rcases eq_or_ne n 0 with rfl | hn
    · simpa using (hC₀' 0).trans ((le_max_left C₀ C).trans (le_mul_of_one_le_left
        ((norm_nonneg _).trans ((hC₀' 0).trans (le_max_left C₀ C))) (one_le_pow₀ one_le_two)))
    · have h1 : 1 ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hn
      calc (1 + |(n : ℝ)|) ^ k * ‖fourierCoeff f n‖
          ≤ (2 * |(n : ℝ)|) ^ k * ‖fourierCoeff f n‖ := by gcongr; linarith
        _ = 2 ^ k * (|(n : ℝ)| ^ k * ‖fourierCoeff f n‖) := by ring
        _ ≤ 2 ^ k * max C₀ C := by gcongr; exact (hC n).trans (le_max_right _ _)
  refine Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (weight_nonneg _ _) (norm_nonneg _))
    (fun n ↦ ?_) ((summable_weight (r := r - k) (by linarith)).mul_left (2 ^ k * max C₀ C))
  have hw : weight r n = weight (r - k) n * (1 + |(n : ℝ)|) ^ k := by
    rw [← Real.rpow_natCast, ← weight_def, ← weight_add, sub_add_cancel]
  rw [hw, mul_assoc, mul_comm]
  exact mul_le_mul_of_nonneg_right (hbound n) (weight_nonneg _ _)

private theorem summable_weight_mul_norm_fourierCoeff_of_contDiff {f : AddCircle T → ℂ}
    (hf : ContDiff ℝ ∞ fun x : ℝ ↦ f x) (r : ℝ) :
    Summable fun n ↦ weight r n * ‖fourierCoeff f n‖ :=
  summable_weight_mul_norm_fourierCoeff (k := ⌈r⌉₊ + 2) (hf.of_le (by simp)) (by
    have := Nat.le_ceil r
    push_cast
    linarith)

/-- For `s > 1/2`, multiplication by a smooth function `f` on `H^s` is pointwise multiplication by
`f` on continuous representatives. -/
private theorem toContinuousMap_multiplier_fourierCoeff_of_contDiff (hs : 1 / 2 < s)
    {f : AddCircle T → ℂ} (hf : ContDiff ℝ ∞ fun x : ℝ ↦ f x) (a : CircleSobolev s E)
    (x : AddCircle T) :
    toContinuousMap T hs (multiplier (fourierCoeff f) a) x = f x • toContinuousMap T hs a x :=
  toContinuousMap_multiplier_fourierCoeff T hs
    ((QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 hf.continuous)
    (summable_weight_mul_norm_fourierCoeff_of_contDiff hf _) a x

/-- Multiplication by the smooth function `g` followed by multiplication by the smooth function
`f` is multiplication by `f * g`, on `H^s` for every real `s`. -/
theorem multiplier_fourierCoeff_comp {f g : AddCircle T → ℂ} (hf : ContDiff ℝ ∞ fun x : ℝ ↦ f x)
    (hg : ContDiff ℝ ∞ fun x : ℝ ↦ g x) :
    (multiplier (fourierCoeff f)).comp
        (multiplier (fourierCoeff g) : CircleSobolev s E →L[ℂ] CircleSobolev s E) =
      multiplier (fourierCoeff fun x ↦ f x * g x) := by
  -- Compare on Fourier monomials, which lie in `H^u` for `u = max s 1 > 1/2`, where the
  -- multipliers act on continuous representatives by pointwise multiplication.
  set u := max s 1
  have hu : 1 / 2 < u := by norm_num [u]
  have hsu : s ≤ u := le_max_left s 1
  have key {h : AddCircle T → ℂ} (hh : ContDiff ℝ ∞ fun x : ℝ ↦ h x) (y : CircleSobolev u E) :
      multiplier (fourierCoeff h) (inclusion hsu y) =
        inclusion hsu (multiplier (fourierCoeff h) y) :=
    (inclusion_multiplier hsu (summable_weight_mul_norm_fourierCoeff_of_contDiff hh _)
      (summable_weight_mul_norm_fourierCoeff_of_contDiff hh _) y).symm
  refine continuousLinearMap_ext_single fun n x ↦ ?_
  rw [ContinuousLinearMap.comp_apply, ← inclusion_single hsu, key hg, key hf, key (hf.mul hg)]
  congr 1
  refine toContinuousMap_injective T hu (ContinuousMap.ext fun y ↦ ?_)
  rw [toContinuousMap_multiplier_fourierCoeff_of_contDiff hu hf,
    toContinuousMap_multiplier_fourierCoeff_of_contDiff hu hg,
    toContinuousMap_multiplier_fourierCoeff_of_contDiff hu (hf.mul hg), smul_smul]

omit [CompleteSpace E] in
/-- Multiplication by the constant function `1` is the identity. -/
@[simp]
theorem multiplier_fourierCoeff_one :
    (multiplier (fourierCoeff fun _ : AddCircle T ↦ (1 : ℂ)) :
      CircleSobolev s E →L[ℂ] CircleSobolev s E) = ContinuousLinearMap.id ℂ _ := by
  have h : fourierCoeff (fun _ : AddCircle T ↦ (1 : ℂ)) = Pi.single 0 1 := by
    rw [← fourierCoeff_fourier (T := T) 0]
    congr 1
    funext x
    simp
  rw [h, multiplier, tsum_eq_single 0 fun m hm ↦ by simp [hm]]
  ext a : 1
  simp

/-- For a smooth function `f` on the circle that vanishes nowhere, multiplication by `f` as a
continuous linear automorphism of `H^s`, for every real `s`; its inverse is multiplication by
`f⁻¹`. -/
def multiplierEquiv (f : AddCircle T → ℂ) (hf : ContDiff ℝ ∞ fun x : ℝ ↦ f x)
    (hf₀ : ∀ x, f x ≠ 0) : CircleSobolev s E ≃L[ℂ] CircleSobolev s E :=
  have hinv : ContDiff ℝ ∞ fun x : ℝ ↦ (f x)⁻¹ := hf.inv fun x ↦ hf₀ x
  ContinuousLinearEquiv.equivOfInverse (multiplier (fourierCoeff f))
    (multiplier (fourierCoeff fun x ↦ (f x)⁻¹))
    (fun a ↦ by
      rw [← ContinuousLinearMap.comp_apply, multiplier_fourierCoeff_comp hinv hf]
      simp [inv_mul_cancel₀ (hf₀ _)])
    (fun a ↦ by
      rw [← ContinuousLinearMap.comp_apply, multiplier_fourierCoeff_comp hf hinv]
      simp [mul_inv_cancel₀ (hf₀ _)])

@[simp]
theorem coe_multiplierEquiv (f : AddCircle T → ℂ) (hf : ContDiff ℝ ∞ fun x : ℝ ↦ f x)
    (hf₀ : ∀ x, f x ≠ 0) :
    ⇑(multiplierEquiv (s := s) (E := E) f hf hf₀) = multiplier (fourierCoeff f) :=
  (rfl)

@[simp]
theorem coe_multiplierEquiv_symm (f : AddCircle T → ℂ) (hf : ContDiff ℝ ∞ fun x : ℝ ↦ f x)
    (hf₀ : ∀ x, f x ≠ 0) :
    ⇑(multiplierEquiv (s := s) (E := E) f hf hf₀).symm =
      multiplier (fourierCoeff fun x ↦ (f x)⁻¹) :=
  (rfl)

end Smooth

end CircleSobolev

end TauCeti
