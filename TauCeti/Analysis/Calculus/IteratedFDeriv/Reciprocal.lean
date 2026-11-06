/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Iterated derivatives of reciprocals and of linear-times-function products

This file computes and bounds the iterated derivatives that appear when a coordinate `t` is
divided by a positive function `p`, as in the normalized time `t / p` of a circle of period `p`.

In one variable, the `k`-th derivative of `x ↦ c / x` is `(-1)^k k! c / x^(k+1)`
(`TauCeti.iteratedDeriv_const_div`), so the norm of the `k`-th iterated derivative of `x ↦ x⁻¹`
is `k! / ‖x‖^(k+1)` (`TauCeti.norm_iteratedFDeriv_inv`). Consequently, for `|c| ≤ R` and
`ε ≤ |x|`, the `k`-th derivative of `x ↦ c / x` is at most `k! R / ε^(k+1)`, and its derivative
in `c` is at most `k! / ε^(k+1)` (`TauCeti.norm_iteratedDeriv_const_div_le`,
`TauCeti.norm_deriv_iteratedDeriv_const_div_le`). The `k`-th derivative is linear in `c`, so all
of its derivatives of order at least two in `c` vanish
(`TauCeti.iteratedDeriv_add_two_iteratedDeriv_const_div`).

For a function `g` on a normed space `E` and a normed algebra `A`, the product
`z ↦ z.2 * g z.1` on `E × A` is linear in its second variable. By the Leibniz rule, its `k`-th
iterated derivative has norm at most `‖z.2‖ ‖D^k g (z.1)‖ + k ‖D^(k-1) g (z.1)‖`
(`TauCeti.norm_iteratedFDeriv_snd_mul_comp_fst_le`). For a positive function `p` with
`ε ≤ p x`, `ε ≤ 1` and `‖D^i p x‖ ≤ C` for `1 ≤ i ≤ k`, where `1 ≤ C`, Faà di Bruno's bound
(Mathlib's `norm_iteratedFDeriv_comp_le'`) gives
`‖D^k (p⁻¹) x‖ ≤ (k!)^2 C^k / ε^(k+1)` (`TauCeti.norm_iteratedFDeriv_inv_comp_le`).

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
theorem iteratedDeriv_const_div (k : ℕ) (c x : 𝕜) :
    iteratedDeriv k (fun y ↦ c / y) x = (-1) ^ k * k ! * c / x ^ (k + 1) := by
  simp_rw [div_eq_mul_inv c, iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate,
    iter_deriv_inv]
  rw [show (-1 - k : ℤ) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
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

section Product

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]

/-- **Leibniz bound for a product linear in one variable.** For `g : E → A` of class `C^k`, the
`k`-th iterated derivative of `z ↦ z.2 * g z.1` on `E × A` has norm at most
`‖z.2‖ ‖D^k g (z.1)‖ + k ‖D^(k-1) g (z.1)‖`. -/
theorem norm_iteratedFDeriv_snd_mul_comp_fst_le {g : E → A} {k : ℕ} (hg : ContDiff 𝕜 k g)
    (z : E × A) :
    ‖iteratedFDeriv 𝕜 k (fun w : E × A ↦ w.2 * g w.1) z‖ ≤
      ‖z.2‖ * ‖iteratedFDeriv 𝕜 k g z.1‖ + k * ‖iteratedFDeriv 𝕜 (k - 1) g z.1‖ := by
  have hsnd : ContDiff 𝕜 k (Prod.snd : E × A → A) := contDiff_snd
  have hgf : ContDiff 𝕜 k (g ∘ Prod.fst : E × A → A) := hg.comp contDiff_fst
  have hle (i : ℕ) (hi : i ≤ k) :
      ‖iteratedFDeriv 𝕜 i (g ∘ Prod.fst : E × A → A) z‖ ≤ ‖iteratedFDeriv 𝕜 i g z.1‖ :=
    norm_iteratedFDeriv_comp_fst_le hg z (by exact_mod_cast hi)
  refine (norm_iteratedFDeriv_mul_le hsnd hgf z le_rfl).trans ?_
  rcases k with _ | m
  · simp
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hrest : ∑ i ∈ Finset.range m, ((m + 1).choose (i + 1 + 1) : ℝ) *
      ‖iteratedFDeriv 𝕜 (i + 1 + 1) (Prod.snd : E × A → A) z‖ *
      ‖iteratedFDeriv 𝕜 (m + 1 - (i + 1 + 1)) (g ∘ Prod.fst : E × A → A) z‖ = 0 :=
    Finset.sum_eq_zero fun i _ ↦ by
      have h : iteratedFDeriv 𝕜 (i + 1 + 1) (Prod.snd : E × A → A) z = 0 :=
        (ContinuousLinearMap.snd 𝕜 E A).iteratedFDeriv_add_two i z
      simp [h]
  have h1 : ‖iteratedFDeriv 𝕜 1 (Prod.snd : E × A → A) z‖ ≤ 1 := by
    rw [norm_iteratedFDeriv_one, fderiv_snd]
    exact ContinuousLinearMap.norm_snd_le 𝕜 E A
  rw [hrest, zero_add]
  refine le_of_le_of_eq (add_le_add ?_ ?_) (add_comm _ _)
  · simp only [zero_add, Nat.choose_one_right]
    calc ((m + 1 : ℕ) : ℝ) * ‖iteratedFDeriv 𝕜 1 (Prod.snd : E × A → A) z‖ *
          ‖iteratedFDeriv 𝕜 m (g ∘ Prod.fst : E × A → A) z‖
        ≤ ((m + 1 : ℕ) : ℝ) * 1 * ‖iteratedFDeriv 𝕜 m g z.1‖ := by
          gcongr
          exact hle m (Nat.le_succ m)
      _ = ((m + 1 : ℕ) : ℝ) * ‖iteratedFDeriv 𝕜 m g z.1‖ := by ring
  · simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
      norm_iteratedFDeriv_zero]
    gcongr
    exact hle _ le_rfl

end Product

section Reciprocal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Derivative bounds for the reciprocal of a positive function.** Let `p : E → ℝ` be a
positive function of class `C^k`. If `ε ≤ p x` with `0 < ε ≤ 1`, and `‖D^i p x‖ ≤ C` for
`1 ≤ i ≤ k` with `1 ≤ C`, then `‖D^k (p⁻¹) x‖ ≤ (k!)^2 C^k / ε^(k+1)`. -/
theorem norm_iteratedFDeriv_inv_comp_le {p : E → ℝ} {k : ℕ} (hp : ContDiff ℝ k p)
    (hpos : ∀ y, 0 < p y) {x : E} {ε C : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hx : ε ≤ p x)
    (hC : 1 ≤ C) (hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i p x‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (fun y ↦ (p y)⁻¹) x‖ ≤ (k ! : ℝ) ^ 2 * C ^ k / ε ^ (k + 1) := by
  have hinv : ContDiffOn ℝ k (fun y : ℝ ↦ y⁻¹) (Set.Ioi 0) :=
    contDiffOn_id.inv fun y hy ↦ (Set.mem_Ioi.mp hy).ne'
  have hrange : Set.range p ⊆ Set.Ioi 0 := Set.range_subset_iff.mpr hpos
  have hbound : ∀ i, i ≤ k →
      ‖iteratedFDerivWithin ℝ i (fun y : ℝ ↦ y⁻¹) (Set.Ioi 0) (p x)‖ ≤
        (k ! : ℝ) / ε ^ (k + 1) := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioi (hpos x), norm_iteratedFDeriv_inv,
      Real.norm_of_nonneg (hpos x).le]
    calc (i ! : ℝ) / p x ^ (i + 1) ≤ i ! / ε ^ (i + 1) := by gcongr
      _ ≤ k ! / ε ^ (i + 1) := by gcongr
      _ ≤ k ! / ε ^ (k + 1) := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_of_le_one hε.le hε₁ (by omega))
  have hpow : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i p x‖ ≤ C ^ i := fun i hi₁ hi ↦
    (hD i hi₁ hi).trans (le_self_pow₀ hC (by omega))
  have h := norm_iteratedFDeriv_comp_le' hrange (uniqueDiffOn_Ioi 0) hinv hp le_rfl x hbound hpow
  calc ‖iteratedFDeriv ℝ k (fun y ↦ (p y)⁻¹) x‖ ≤ k ! * (k ! / ε ^ (k + 1)) * C ^ k := h
    _ = (k ! : ℝ) ^ 2 * C ^ k / ε ^ (k + 1) := by ring

end Reciprocal

end TauCeti
