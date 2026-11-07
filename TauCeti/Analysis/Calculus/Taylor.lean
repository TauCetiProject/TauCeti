/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Taylor polynomials: size and sign of the remainder, and the derivatives of `f(x) / x`

Three facts about Mathlib's Taylor polynomials `taylorWithinEval f n s x₀ x`.

* **Size of the remainder.** From the Lagrange form of the remainder, if `|f⁽ⁿ⁺¹⁾| ≤ M` between
  `x₀` and `x`, then `|f x - T(x)| ≤ M |x - x₀|ⁿ⁺¹ / (n+1)!`, where `T` is the Taylor polynomial
  of order `n` expanded at `x₀`.
* **Sign of the remainder.** As a function of the expansion point, the derivative of
  `x₀ ↦ taylorWithinEval f n s x₀ x` is `(x - x₀)ⁿ / n! · f⁽ⁿ⁺¹⁾(x₀)`. If `(-1)ⁿ f⁽ⁿ⁺¹⁾ ≥ 0`
  on `(x, y)`, this derivative is nonnegative there, so the Taylor polynomial of order `n`
  expanded at `y` and evaluated at the left endpoint `x` dominates `f x`: the Taylor remainder
  has a sign.
* **Derivatives of `f(x) / x`.** By the Leibniz rule and `dᵐ/dxᵐ x⁻¹ = (-1)ᵐ m! x⁻ᵐ⁻¹`,

  `dⁿ/dtⁿ (f(t) / t) = (-1)ⁿ n! t⁻ⁿ⁻¹ · Σ_{k ≤ n} f⁽ᵏ⁾(t) (0 - t)ᵏ / k!`,

  the last factor being the Taylor polynomial of order `n` of `f` expanded at `t` and evaluated
  at `0`.

The last two combined show that the iterated derivatives of `f(t) / t` alternate in sign whenever
`f` is nonnegative and the derivatives of `f'` alternate in sign — the statement that a Bernstein
function divided by its parameter is completely monotone.

## Main declarations

* `TauCeti.abs_sub_taylorWithinEval_le`: a bound on the Taylor remainder when the next derivative
  is bounded, with the error proportional to `|x - x₀|^(n+1)`.
* `TauCeti.le_taylorWithinEval_of_neg_one_pow_mul_iteratedDerivWithin_nonneg`: if
  `(-1)ⁿ f⁽ⁿ⁺¹⁾ ≥ 0` on `(x, y)`, then `f x` is at most the Taylor polynomial of order `n` at `y`,
  evaluated at `x`.
* `TauCeti.iteratedDeriv_div_id`: the formula for the `n`-th derivative of `t ↦ f t / t`.
-/

public section

open Set Filter
open scoped ContDiff Topology Nat

namespace TauCeti

/-- **Taylor's theorem with a bounded remainder.** If `f` is `C^(n+1)` and its `(n+1)`st
derivative is bounded in absolute value by `M` strictly between `x₀` and `x`, then its Taylor
polynomial of order `n` about `x₀` approximates `f x` with error at most
`M * |x - x₀|^(n+1) / (n+1)!`. -/
theorem abs_sub_taylorWithinEval_le {f : ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ (n + 1) f)
    {M : ℝ} {x₀ x : ℝ} (hM : ∀ t ∈ uIoo x₀ x, |iteratedDeriv (n + 1) f t| ≤ M) :
    |f x - taylorWithinEval f n univ x₀ x| ≤ M * |x - x₀| ^ (n + 1) / (n + 1)! := by
  rcases eq_or_ne x₀ x with rfl | hx
  · simp
  obtain ⟨y, hy, hfy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hx hf.contDiffOn
  have htay : taylorWithinEval f n (uIcc x₀ x) x₀ x = taylorWithinEval f n univ x₀ x := by
    simp only [taylor_within_apply, iteratedDerivWithin_univ]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx)
      (hf.of_le (mod_cast by grind)).contDiffAt left_mem_uIcc]
  rw [← htay, hfy, abs_div, abs_mul, abs_pow, Nat.abs_cast]
  gcongr
  exact hM y hy

/-- **The Taylor remainder has a sign.** Let `f` be `C^(n+1)` on a set `s` of unique
differentiability containing `[x, y]`, with `(-1)ⁿ f⁽ⁿ⁺¹⁾ ≥ 0` on `(x, y)`. Then the Taylor
polynomial of order `n` of `f` expanded at `y` and evaluated at `x` is at least `f x`. -/
theorem le_taylorWithinEval_of_neg_one_pow_mul_iteratedDerivWithin_nonneg {f : ℝ → ℝ} {s : Set ℝ}
    {n : ℕ} {x y : ℝ} (hs : UniqueDiffOn ℝ s) (hxy : x ≤ y) (hsub : Icc x y ⊆ s)
    (hf : ContDiffOn ℝ (n + 1) f s)
    (hsign : ∀ z ∈ Ioo x y, 0 ≤ (-1) ^ n * iteratedDerivWithin (n + 1) f s z) :
    f x ≤ taylorWithinEval f n s y x := by
  -- The Taylor polynomial is nondecreasing in its expansion point on `[x, y]`.
  have hmono : MonotoneOn (fun w => taylorWithinEval f n s w x) (Icc x y) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x y)
      (f' := fun z => ((n ! : ℝ)⁻¹ * (x - z) ^ n) • iteratedDerivWithin (n + 1) f s z)
      ((continuousOn_taylorWithinEval hs hf.of_succ).mono hsub) (fun z hz => ?_) fun z hz => ?_
    all_goals rw [interior_Icc] at hz
    · have hzs : s ∈ 𝓝 z :=
        mem_of_superset (isOpen_Ioo.mem_nhds hz) (Ioo_subset_Icc_self.trans hsub)
      exact ((hasDerivWithinAt_taylorWithinEval hs self_mem_nhdsWithin (mem_of_mem_nhds hzs)
        subset_rfl hf.of_succ ((hf.differentiableOn_iteratedDerivWithin (mod_cast n.lt_succ_self)
          hs) z (mem_of_mem_nhds hzs))).hasDerivAt hzs).hasDerivWithinAt
    · have := hsign z hz
      have : 0 ≤ (z - x) ^ n := pow_nonneg (sub_nonneg.mpr hz.1.le) n
      calc 0 ≤ (n ! : ℝ)⁻¹ * (z - x) ^ n * ((-1) ^ n * iteratedDerivWithin (n + 1) f s z) := by
            positivity
        _ = _ := by rw [smul_eq_mul, ← neg_sub z x, neg_pow (z - x)]; ring
  simpa using hmono (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy

/-- **The derivatives of `f(t) / t`.** If `f` is `C^n` at `t ≠ 0` and `s` is an open set
containing `t`, then `dⁿ/dtⁿ (f(t) / t) = (-1)ⁿ n! t⁻ⁿ⁻¹ · T(0)`, where `T` is the Taylor
polynomial of order `n` of `f` expanded at `t` (within `s`). -/
theorem iteratedDeriv_div_id {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {t : ℝ} (hs : IsOpen s)
    (ht : t ∈ s) (ht0 : t ≠ 0) (hf : ContDiffAt ℝ n f t) :
    iteratedDeriv n (fun x => f x / x) t =
      (-1) ^ n * n ! * (t ^ (n + 1))⁻¹ * taylorWithinEval f n s t 0 := by
  have hfun : (fun x => f x / x) = f * Inv.inv := by
    funext x
    simp [div_eq_mul_inv]
  have hinv : ContDiffWithinAt ℝ n (Inv.inv : ℝ → ℝ) s t :=
    (contDiffAt_inv ℝ ht0).contDiffWithinAt
  rw [hfun, ← iteratedDerivWithin_of_isOpen hs ht,
    iteratedDerivWithin_mul ht hs.uniqueDiffOn hf.contDiffWithinAt hinv,
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
  simp [pow_right_comm _ k 2]

end TauCeti
