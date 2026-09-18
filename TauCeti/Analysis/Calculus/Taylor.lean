/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Taylor polynomials: sign of the remainder and the derivatives of `f(x) / x`

Two facts about Mathlib's Taylor polynomials `taylorWithinEval f n s x₀ x`.

* **Sign of the remainder.** As a function of the expansion point, the derivative of
  `x₀ ↦ taylorWithinEval f n s x₀ x` is `(x - x₀)ⁿ / n! · f⁽ⁿ⁺¹⁾(x₀)`. If `(-1)ⁿ f⁽ⁿ⁺¹⁾ ≥ 0`
  on `[x, y]`, this derivative is nonnegative there, so the Taylor polynomial of order `n`
  expanded at `y` and evaluated at the left endpoint `x` dominates `f x`: the Taylor remainder
  has a sign.
* **Derivatives of `f(x) / x`.** By the Leibniz rule and `dᵐ/dxᵐ x⁻¹ = (-1)ᵐ m! x⁻ᵐ⁻¹`,

  `dⁿ/dtⁿ (f(t) / t) = (-1)ⁿ n! t⁻ⁿ⁻¹ · Σ_{k ≤ n} f⁽ᵏ⁾(t) (0 - t)ᵏ / k!`,

  the last factor being the Taylor polynomial of order `n` of `f` expanded at `t` and evaluated
  at `0`.

Combined, they show that the iterated derivatives of `f(t) / t` alternate in sign whenever `f` is
nonnegative and the derivatives of `f'` alternate in sign — the statement that a Bernstein
function divided by its parameter is completely monotone.

## Main declarations

* `TauCeti.le_taylorWithinEval_of_neg_one_pow_mul_iteratedDerivWithin_nonneg`: if
  `(-1)ⁿ f⁽ⁿ⁺¹⁾ ≥ 0` on `[x, y]`, then `f x` is at most the Taylor polynomial of order `n` at `y`,
  evaluated at `x`.
* `TauCeti.iteratedDeriv_div_id`: the formula for the `n`-th derivative of `t ↦ f t / t`.
-/

public section

open Set Filter
open scoped ContDiff Topology Nat

namespace TauCeti

/-- **The Taylor remainder has a sign.** Let `f` be `C^(n+1)` on an open set `s` containing
`[x, y]`, with `(-1)ⁿ f⁽ⁿ⁺¹⁾ ≥ 0` on `[x, y]`. Then the Taylor polynomial of order `n` of `f`
expanded at `y` and evaluated at `x` is at least `f x`. -/
theorem le_taylorWithinEval_of_neg_one_pow_mul_iteratedDerivWithin_nonneg {f : ℝ → ℝ} {s : Set ℝ}
    {n : ℕ} {x y : ℝ} (hs : IsOpen s) (hxy : x ≤ y) (hsub : Icc x y ⊆ s)
    (hf : ContDiffOn ℝ (n + 1) f s)
    (hsign : ∀ z ∈ Icc x y, 0 ≤ (-1) ^ n * iteratedDerivWithin (n + 1) f s z) :
    f x ≤ taylorWithinEval f n s y x := by
  -- The Taylor polynomial is nondecreasing in its expansion point on `[x, y]`.
  have hderiv : ∀ z ∈ s, HasDerivAt (fun w => taylorWithinEval f n s w x)
      (((n ! : ℝ)⁻¹ * (x - z) ^ n) • iteratedDerivWithin (n + 1) f s z) z := fun z hz =>
    (hasDerivWithinAt_taylorWithinEval hs.uniqueDiffOn self_mem_nhdsWithin hz subset_rfl
      hf.of_succ ((hf.differentiableOn_iteratedDerivWithin (mod_cast n.lt_succ_self)
        hs.uniqueDiffOn) z hz)).hasDerivAt (hs.mem_nhds hz)
  have hmono : MonotoneOn (fun w => taylorWithinEval f n s w x) (Icc x y) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x y)
      (fun z hz => (hderiv z (hsub hz)).continuousAt.continuousWithinAt)
      (fun z hz => (hderiv z (hsub (interior_subset hz))).hasDerivWithinAt) fun z hz => ?_
    have hz := interior_subset hz
    have hpow : (x - z) ^ n = (-1) ^ n * (z - x) ^ n := by rw [← mul_pow]; ring
    rw [smul_eq_mul, hpow]
    have := hsign z hz
    have : 0 ≤ (z - x) ^ n := pow_nonneg (sub_nonneg.mpr hz.1) n
    calc (0 : ℝ) ≤ (n ! : ℝ)⁻¹ * (z - x) ^ n * ((-1) ^ n * iteratedDerivWithin (n + 1) f s z) := by
          positivity
      _ = _ := by ring
  simpa using hmono (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy

/-- **The derivatives of `f(t) / t`.** If `f` is `C^n` on an open set `s` containing `t ≠ 0`,
then `dⁿ/dtⁿ (f(t) / t) = (-1)ⁿ n! t⁻ⁿ⁻¹ · T(0)`, where `T` is the Taylor polynomial of order `n`
of `f` expanded at `t`. -/
theorem iteratedDeriv_div_id {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {t : ℝ} (hs : IsOpen s)
    (ht : t ∈ s) (ht0 : t ≠ 0) (hf : ContDiffOn ℝ n f s) :
    iteratedDeriv n (fun x => f x / x) t =
      (-1) ^ n * n ! * (t ^ (n + 1))⁻¹ * taylorWithinEval f n s t 0 := by
  have hfun : (fun x => f x / x) = f * Inv.inv := by
    funext x
    simp [div_eq_mul_inv]
  have hinv : ContDiffWithinAt ℝ n (Inv.inv : ℝ → ℝ) s t :=
    (contDiffAt_inv ℝ ht0).contDiffWithinAt
  rw [hfun, ← iteratedDerivWithin_of_isOpen hs ht,
    iteratedDerivWithin_mul ht hs.uniqueDiffOn (hf.contDiffWithinAt ht) hinv,
    taylor_within_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  rw [Nat.add_sub_cancel_left,
    iteratedDerivWithin_of_isOpen (f := (Inv.inv : ℝ → ℝ)) (n := m) hs ht, iteratedDeriv_eq_iterate,
    iter_deriv_inv, smul_eq_mul]
  have hz : (-1 - (m : ℤ)) = -((m + 1 : ℕ) : ℤ) := by push_cast; ring
  have hchoose : ((k + m).choose k : ℝ) * k ! * m ! = (k + m)! := by
    rw [Nat.choose_symm_add]
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial k m
  have htk : t ^ (k + m + 1) = t ^ k * t ^ (m + 1) := by ring
  rw [hz, zpow_neg, zpow_natCast, ← hchoose, zero_sub, neg_pow t k, htk,
    pow_add (-1 : ℝ) k m]
  field_simp
  rw [← pow_mul, mul_comm k 2, pow_mul, neg_one_sq, one_pow, mul_one]

end TauCeti
