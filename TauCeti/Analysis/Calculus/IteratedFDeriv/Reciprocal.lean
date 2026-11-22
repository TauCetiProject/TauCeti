/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.RCLike.Basic

/-!
# Iterated derivatives of reciprocals

This file computes and bounds the iterated derivatives that appear when dividing by a real or
complex function `p` that does not vanish: a coordinate `t` divided by a positive period `p`, as in
the normalized time `t / p` of a circle of period `p`, or a cutoff divided by an elliptic symbol,
as in microlocal elliptic regularity.

In one variable, the `k`-th derivative of `x ↦ c / x` is `(-1)^k k! c / x^(k+1)`
(`TauCeti.iteratedDeriv_const_div`), so the norm of the `k`-th iterated derivative of `x ↦ x⁻¹`
is `k! / ‖x‖^(k+1)` (`TauCeti.norm_iteratedFDeriv_inv`); on `𝕜 = ℝ` or `ℂ`, so is that of its
real iterated derivative (`TauCeti.norm_iteratedFDeriv_real_inv`). Consequently, for `|c| ≤ R` and
`ε ≤ |x|`, the `k`-th derivative of `x ↦ c / x` is at most `k! R / ε^(k+1)`, and its derivative
in `c` is at most `k! / ε^(k+1)` (`TauCeti.norm_iteratedDeriv_const_div_le`,
`TauCeti.norm_deriv_iteratedDeriv_const_div_le`). The `k`-th derivative is linear in `c`, so all
of its derivatives of order at least two in `c` vanish
(`TauCeti.iteratedDeriv_add_two_iteratedDeriv_const_div`).

For a real or complex function `p` of class `C^k` with `ε ≤ ‖p x‖`, `0 < ε ≤ 1` and
`‖D^i p x‖ ≤ C` for `1 ≤ i ≤ k`, where `1 ≤ C`, Faà di Bruno's bound (Mathlib's
`norm_iteratedFDerivWithin_comp_le`, applied on the open set where `p` does not vanish) gives
`‖D^k (p⁻¹) x‖ ≤ (k!)^2 C^k / ε^(k+1)` (`TauCeti.norm_iteratedFDeriv_inv_comp_le`). Rescaling,
if the derivatives of order at most `n` of `p` are bounded by `A t` and `c t ≤ ‖p y‖` for a scale
`t > 0`, then those of `p⁻¹` are bounded by `Q / t` with `Q` depending only on `n`, `A` and `c`
(`TauCeti.exists_norm_iteratedFDeriv_inv_le_div`).

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (angle variables of a family of tori whose periods
  vary with the action variables).
-/

public section

open scoped Nat

namespace TauCeti

section OneVariable

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The `k`-th derivative of `x ↦ c / x` is `(-1)^k k! c / x^(k+1)`. At `x = 0` both sides
vanish, with the conventions `0⁻¹ = 0` and `c / 0 = 0`. -/
@[simp]
theorem iteratedDeriv_const_div (k : ℕ) (c x : 𝕜) :
    iteratedDeriv k (fun y ↦ c / y) x = (-1) ^ k * k ! * c / x ^ (k + 1) := by
  simp_rw [div_eq_mul_inv c, iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate,
    iter_deriv_inv]
  rw [show (-1 - k : ℤ) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  ring

/-- The `k`-th derivative of `x ↦ c / x ^ m` is
`(-1)^k (∏ i ∈ Finset.range k, (m + i)) c / x ^ (m + k)`. At `x = 0` with `m + k > 0` both sides
vanish, with the conventions `0⁻¹ = 0` and `c / 0 = 0`. -/
theorem iteratedDeriv_const_div_pow (k m : ℕ) (c x : 𝕜) :
    iteratedDeriv k (fun y ↦ c / y ^ m) x =
      (-1) ^ k * (∏ i ∈ Finset.range k, ((m + i : ℕ) : 𝕜)) * c / x ^ (m + k) := by
  have heq : (fun y : 𝕜 ↦ c / y ^ m) = fun y ↦ c * y ^ (-(m : ℤ)) := by
    ext y
    rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
  rw [heq, iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_zpow]
  have hprod : ∏ i ∈ Finset.range k, ((-(m : ℤ) : 𝕜) - i) =
      (-1) ^ k * ∏ i ∈ Finset.range k, ((m + i : ℕ) : 𝕜) := by
    have hneg : ∏ i ∈ Finset.range k, ((-(m : ℤ) : 𝕜) - i) =
        ∏ i ∈ Finset.range k, ((-1 : 𝕜) * ((m + i : ℕ) : 𝕜)) :=
      Finset.prod_congr rfl fun i _ ↦ by push_cast; ring
    rw [hneg, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  simp only [Int.cast_neg, Int.cast_natCast] at hprod ⊢
  have hexp : -(m : ℤ) - k = -((m + k : ℕ) : ℤ) := by omega
  rw [hprod, hexp, zpow_neg, zpow_natCast]
  ring

/-- The `k`-th derivative of `x ↦ c / x` at a fixed point `x` is linear in `c`. -/
private theorem iteratedDeriv_const_div_eq_mul (k : ℕ) (x : 𝕜) :
    (fun c ↦ iteratedDeriv k (fun y ↦ c / y) x) =
      fun c ↦ c * ((-1) ^ k * k ! / x ^ (k + 1)) := by
  funext c
  rw [iteratedDeriv_const_div]
  ring

/-- The derivative in `c` of the `k`-th derivative of `x ↦ c / x` is `(-1)^k k! / x^(k+1)`. -/
theorem deriv_iteratedDeriv_const_div (k : ℕ) (c x : 𝕜) :
    deriv (fun c' ↦ iteratedDeriv k (fun y ↦ c' / y) x) c = (-1) ^ k * k ! / x ^ (k + 1) := by
  rw [iteratedDeriv_const_div_eq_mul]
  simp

/-- The `k`-th derivative of `x ↦ c / x` is linear in `c`, so its derivatives of order at least
two in `c` vanish. -/
theorem iteratedDeriv_add_two_iteratedDeriv_const_div (j k : ℕ) (c x : 𝕜) :
    iteratedDeriv (j + 2) (fun c' ↦ iteratedDeriv k (fun y ↦ c' / y) x) c = 0 := by
  rw [iteratedDeriv_const_div_eq_mul, iteratedDeriv_succ', iteratedDeriv_succ']
  simp

end OneVariable

section OneVariableBound

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The `k`-th iterated derivative of `x ↦ x⁻¹` has norm `k! / ‖x‖^(k+1)`. -/
@[simp]
theorem norm_iteratedFDeriv_inv (k : ℕ) (x : 𝕜) :
    ‖iteratedFDeriv 𝕜 k (fun y : 𝕜 ↦ y⁻¹) x‖ = k ! / ‖x‖ ^ (k + 1) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := iteratedDeriv_const_div k (1 : 𝕜) x
  simp only [one_div, mul_one] at h
  rw [h]
  simp [norm_pow]

/-- For `‖c‖ ≤ R` and `ε ≤ ‖x‖` with `0 < ε`, the `k`-th derivative of `x ↦ c / x` is at most
`k! R / ε^(k+1)`. -/
theorem norm_iteratedDeriv_const_div_le (k : ℕ) {c x : 𝕜} {R ε : ℝ} (hc : ‖c‖ ≤ R)
    (hε : 0 < ε) (hx : ε ≤ ‖x‖) :
    ‖iteratedDeriv k (fun y ↦ c / y) x‖ ≤ k ! * R / ε ^ (k + 1) := by
  rw [iteratedDeriv_const_div]
  simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    RCLike.norm_natCast]
  have hR : 0 ≤ R := (norm_nonneg c).trans hc
  gcongr

/-- For `ε ≤ ‖x‖` with `0 < ε`, the derivative in `c` of the `k`-th derivative of
`x ↦ c / x` is at most `k! / ε^(k+1)`. -/
theorem norm_deriv_iteratedDeriv_const_div_le (k : ℕ) (c : 𝕜) {x : 𝕜} {ε : ℝ} (hε : 0 < ε)
    (hx : ε ≤ ‖x‖) :
    ‖deriv (fun c' ↦ iteratedDeriv k (fun y ↦ c' / y) x) c‖ ≤ k ! / ε ^ (k + 1) := by
  rw [deriv_iteratedDeriv_const_div]
  simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    RCLike.norm_natCast]
  gcongr

end OneVariableBound

section Reciprocal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `k`-th real iterated derivative of `z ↦ z⁻¹` on `𝕜 = ℝ` or `ℂ` has norm `k! / ‖z‖^(k+1)`
away from `0`: it is the `k`-th complex derivative with the scalars restricted to `ℝ`. -/
theorem norm_iteratedFDeriv_real_inv {𝕜 : Type*} [RCLike 𝕜] (k : ℕ) {z : 𝕜} (hz : z ≠ 0) :
    ‖iteratedFDeriv ℝ k (fun y : 𝕜 ↦ y⁻¹) z‖ = k ! / ‖z‖ ^ (k + 1) := by
  rw [← ContDiffAt.restrictScalars_iteratedFDeriv (𝕜 := ℝ) (contDiffAt_inv 𝕜 hz (n := k)),
    Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_inv]

/-- **Derivative bounds for the reciprocal of a function.** Let `p : E → 𝕜`, with `𝕜 = ℝ` or `ℂ`,
be a function of class `C^k`. If `ε ≤ ‖p x‖` with `0 < ε ≤ 1`, and `‖D^i p x‖ ≤ C` for
`1 ≤ i ≤ k` with `1 ≤ C`, then `‖D^k (p⁻¹) x‖ ≤ (k!)^2 C^k / ε^(k+1)`. -/
theorem norm_iteratedFDeriv_inv_comp_le {𝕜 : Type*} [RCLike 𝕜] {p : E → 𝕜} {k : ℕ}
    (hp : ContDiff ℝ k p) {x : E} {ε C : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hx : ε ≤ ‖p x‖)
    (hC : 1 ≤ C) (hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i p x‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (fun y ↦ (p y)⁻¹) x‖ ≤ (k ! : ℝ) ^ 2 * C ^ k / ε ^ (k + 1) := by
  -- Work on the open set where `p` does not vanish, which contains `x`.
  set s : Set E := p ⁻¹' {0}ᶜ
  have hsopen : IsOpen s := isOpen_compl_singleton.preimage hp.continuous
  have hpx : 0 < ‖p x‖ := hε.trans_le hx
  have hxs : x ∈ s := norm_pos_iff.1 hpx
  have hinv : ContDiffOn ℝ k (fun y : 𝕜 ↦ y⁻¹) {0}ᶜ := contDiffOn_inv ℝ
  have hbound : ∀ i, i ≤ k →
      ‖iteratedFDerivWithin ℝ i (fun y : 𝕜 ↦ y⁻¹) {0}ᶜ (p x)‖ ≤ (k ! : ℝ) / ε ^ (k + 1) := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i isOpen_compl_singleton hxs,
      norm_iteratedFDeriv_real_inv i hxs]
    calc (i ! : ℝ) / ‖p x‖ ^ (i + 1) ≤ i ! / ε ^ (i + 1) := by gcongr
      _ ≤ k ! / ε ^ (i + 1) := by gcongr
      _ ≤ k ! / ε ^ (k + 1) := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_of_le_one hε.le hε₁ (by omega))
  have hpow : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDerivWithin ℝ i p s x‖ ≤ C ^ i := fun i hi₁ hi ↦ by
    rw [iteratedFDerivWithin_of_isOpen i hsopen hxs]
    exact (hD i hi₁ hi).trans (le_self_pow₀ hC (by omega))
  have h := norm_iteratedFDerivWithin_comp_le hinv hp.contDiffOn le_rfl
    isOpen_compl_singleton.uniqueDiffOn hsopen.uniqueDiffOn (fun y hy ↦ hy) hxs hbound hpow
  rw [iteratedFDerivWithin_of_isOpen k hsopen hxs] at h
  calc ‖iteratedFDeriv ℝ k (fun y ↦ (p y)⁻¹) x‖ ≤ k ! * (k ! / ε ^ (k + 1)) * C ^ k := h
    _ = (k ! : ℝ) ^ 2 * C ^ k / ε ^ (k + 1) := by ring

/-- **Derivative bounds for the reciprocal of a large function.** Let `t > 0` be a scale. If
`p : E → 𝕜`, with `𝕜 = ℝ` or `ℂ`, is of class `C^n`, its derivatives of order at most `n` at `y`
are bounded by `A t` and `c t ≤ ‖p y‖` with `c > 0`, then the derivatives of order at most `n` of
`p⁻¹` at `y` are bounded by `Q / t`, where `Q` depends only on `n`, `A` and `c`. This is how a
cutoff is divided by an elliptic symbol of size `t = (1 + ‖η‖) ^ M`. -/
theorem exists_norm_iteratedFDeriv_inv_le_div {𝕜 : Type*} [RCLike 𝕜] (n : ℕ)
    (A : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ Q, 0 ≤ Q ∧ ∀ (p : E → 𝕜) (t : ℝ) (y : E), 0 < t → ContDiff ℝ n p →
      (∀ j ≤ n, ‖iteratedFDeriv ℝ j p y‖ ≤ A * t) → c * t ≤ ‖p y‖ →
        ∀ j ≤ n, ‖iteratedFDeriv ℝ j (fun z ↦ (p z)⁻¹) y‖ ≤ Q / t := by
  set ε := min c 1
  set C := max A 1
  have hε : 0 < ε := lt_min hc one_pos
  refine ⟨(n ! : ℝ) ^ 2 * C ^ n / ε ^ (n + 1), by positivity,
    fun p t y ht hp hA hpy j hj ↦ ?_⟩
  -- Normalize: `p = t p'` with `p'` of size one.
  set p' : E → 𝕜 := fun z ↦ (t : 𝕜)⁻¹ • p z
  have hnt : ‖(t : 𝕜)⁻¹‖ = t⁻¹ := by rw [norm_inv, RCLike.norm_ofReal, abs_of_pos ht]
  have hp' : ContDiff ℝ n p' := hp.const_smul _
  have hD (i : ℕ) (hi : i ≤ n) : ‖iteratedFDeriv ℝ i p' y‖ = ‖iteratedFDeriv ℝ i p y‖ / t := by
    rw [iteratedFDeriv_const_smul_apply' (hp.contDiffAt.of_le (by exact_mod_cast hi)), norm_smul,
      hnt, inv_mul_eq_div]
  have hpy' : ε ≤ ‖p' y‖ := by
    rw [norm_smul, hnt, inv_mul_eq_div, le_div_iff₀ ht]
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) ht.le).trans hpy
  have hinv := norm_iteratedFDeriv_inv_comp_le (k := j) (hp'.of_le (by exact_mod_cast hj)) hε
    (min_le_right _ _) hpy' (le_max_right A 1) fun i _ hi ↦ by
      rw [hD i (hi.trans hj), div_le_iff₀ ht]
      exact (hA i (hi.trans hj)).trans (by gcongr; exact le_max_left _ _)
  have hpy0 : p' y ≠ 0 := norm_pos_iff.1 (hε.trans_le hpy')
  have hrec : (fun z ↦ (p z)⁻¹) = fun z ↦ (t : 𝕜)⁻¹ • p'⁻¹ z := by
    ext z
    simp only [p', Pi.inv_apply, smul_eq_mul, mul_inv, inv_inv]
    rw [inv_mul_cancel_left₀ (RCLike.ofReal_ne_zero.2 ht.ne')]
  have hsmul := iteratedFDeriv_const_smul_apply' (a := (t : 𝕜)⁻¹)
    (((hp'.contDiffAt.of_le (by exact_mod_cast hj)).inv hpy0 :
      ContDiffAt ℝ j (fun z ↦ (p' z)⁻¹) y))
  rw [hrec, hsmul, norm_smul, hnt, inv_mul_eq_div]
  gcongr
  have hC : 1 ≤ C := le_max_right _ _
  have hε1 : ε ≤ 1 := min_le_right _ _
  calc ‖iteratedFDeriv ℝ j p'⁻¹ y‖ ≤ (j ! : ℝ) ^ 2 * C ^ j / ε ^ (j + 1) := hinv
    _ ≤ (n ! : ℝ) ^ 2 * C ^ n / ε ^ (j + 1) := by gcongr
    _ ≤ (n ! : ℝ) ^ 2 * C ^ n / ε ^ (n + 1) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_of_le_one hε.le hε1 (by omega))

end Reciprocal

end TauCeti
