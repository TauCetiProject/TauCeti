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
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Taylor polynomials and remainder estimates

Remainder bounds and identities for Mathlib's Taylor polynomials `taylorWithinEval f n s x₀ x`,
including a uniform second-order estimate for functions C² near a compact interval.
Two further applications are:

* **Sign of the remainder.** As a function of the expansion point, the derivative of
  `x₀ ↦ taylorWithinEval f n s x₀ x` is `(x - x₀)ⁿ / n! · f⁽ⁿ⁺¹⁾(x₀)`. If `(-1)ⁿ f⁽ⁿ⁺¹⁾ ≥ 0`
  on `(x, y)`, this derivative is nonnegative there, so the Taylor polynomial of order `n`
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
  `(-1)ⁿ f⁽ⁿ⁺¹⁾ ≥ 0` on `(x, y)`, then `f x` is at most the Taylor polynomial of order `n` at `y`,
  evaluated at `x`.
* `TauCeti.iteratedDeriv_div_id`: the formula for the `n`-th derivative of `t ↦ f t / t`.
* `TauCeti.abs_sub_taylorWithinEval_le`: a bound on the Taylor remainder when the next derivative
  is bounded, with the error proportional to `|x - x₀|^(n+1)`.
-/

public section

open Set Filter
open scoped ContDiff Topology Nat

namespace TauCeti

/-- **Taylor's theorem with a bounded remainder.** If `f` is `C^(n+1)` and its `(n+1)`st
derivative is bounded in absolute value by `M`, then its Taylor polynomial of order `n` about `x₀`
approximates `f x` with error at most `M * |x - x₀|^(n+1) / (n+1)!`. -/
theorem abs_sub_taylorWithinEval_le {f : ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ (n + 1) f)
    {M : ℝ} (hM : ∀ t, |iteratedDeriv (n + 1) f t| ≤ M) (x₀ x : ℝ) :
    |f x - taylorWithinEval f n Set.univ x₀ x| ≤ M * |x - x₀| ^ (n + 1) / (n + 1)! := by
  rcases eq_or_ne x x₀ with rfl | hx
  · simp
  obtain ⟨y, -, hy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (x₀ := x₀) (x := x)
    hx.symm (hf.contDiffOn)
  have htay : taylorWithinEval f n (Set.uIcc x₀ x) x₀ x =
      taylorWithinEval f n Set.univ x₀ x := by
    simp only [taylor_within_apply]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx.symm)
      ((hf.of_le (by norm_cast; simp at hk; omega)).contDiffAt) Set.left_mem_uIcc]
    simp only [iteratedDerivWithin_univ]
  rw [htay] at hy
  rw [hy, abs_div, abs_mul, abs_pow, Nat.abs_cast]
  gcongr
  exact hM y

/-- The quadratic Taylor polynomial on the whole line, written using ordinary derivatives.
No regularity hypothesis is needed for this algebraic identity. -/
theorem taylorWithinEval_univ_two (f : ℝ → ℝ) (x y : ℝ) :
    taylorWithinEval f 2 univ x y =
      f x + deriv f x * (y - x) + 1 / 2 * deriv (deriv f) x * (y - x) ^ 2 := by
  simp only [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_univ,
    iteratedDeriv_succ, iteratedDeriv_zero, Nat.factorial_zero, Nat.factorial_one,
    Nat.cast_one, Nat.cast_zero, zero_add, one_mul, inv_one, pow_one, smul_eq_mul]
  ring

/-- Uniform second-order Taylor remainder estimate for a function C² near a compact interval.
The coefficient of the squared increment can be made arbitrarily small. -/
theorem exists_pos_forall_abs_sub_taylorWithinEval_two_le {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ z ∈ Icc a b, ContDiffAt ℝ 2 f z) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |y - x| < δ →
      |f y - taylorWithinEval f 2 univ x y| ≤ ε * (y - x) ^ 2 := by
  have hu : UniformContinuousOn (iteratedDeriv 2 f) (Icc a b) := by
    apply isCompact_Icc.uniformContinuousOn_of_continuous
    intro z hz
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      (((hf z hz).derivWithin (m := 1) (by norm_num)).derivWithin
        (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.1 hu ε hε
  refine ⟨δ, hδ, fun x hx y hy hxy ↦ ?_⟩
  by_cases h : x = y
  · subst y
    simp
  obtain ⟨z, hz, hTaylor⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) h (fun t ht ↦ (hf t (uIcc_subset_Icc hx hy ht)).contDiffWithinAt)
  have hz' : z ∈ Icc a b := uIcc_subset_Icc hx hy (uIoo_subset_uIcc_self hz)
  have hzx : dist z x < δ := lt_of_le_of_lt
    (by simpa [Real.dist_eq] using abs_sub_left_of_mem_uIcc (uIoo_subset_uIcc_self hz)) hxy
  have hd : |iteratedDeriv 2 f z - iteratedDeriv 2 f x| < ε := by
    simpa [Real.dist_eq] using hδf z hz' x hx hzx
  have hpoly : taylorWithinEval f 1 (uIcc x y) x y =
      f x + deriv f x * (y - x) := by
    rw [taylorWithinEval_succ, taylor_within_zero_eval,
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc h)
        ((hf x hx).of_le (by norm_num)) left_mem_uIcc]
    simp [iteratedDeriv_one, smul_eq_mul, mul_comm]
  rw [hpoly] at hTaylor
  have heq : f y - taylorWithinEval f 2 univ x y =
      (iteratedDeriv 2 f z - iteratedDeriv 2 f x) * (y - x) ^ 2 / 2 := by
    rw [taylorWithinEval_univ_two]
    have hTaylor' : f y - (f x + deriv f x * (y - x)) =
        iteratedDeriv 2 f z * (y - x) ^ 2 / 2 := by
      simpa only [Nat.reduceAdd, Nat.factorial_two, Nat.cast_ofNat] using hTaylor
    rw [iteratedDeriv_succ, iteratedDeriv_one] at hTaylor' ⊢
    linarith
  rw [heq]
  calc
    _ = |iteratedDeriv 2 f z - iteratedDeriv 2 f x| / 2 * (y - x) ^ 2 := by
      rw [abs_div, abs_mul, abs_pow, sq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring
    _ ≤ ε * (y - x) ^ 2 := by
      gcongr
      linarith [abs_nonneg (iteratedDeriv 2 f z - iteratedDeriv 2 f x)]

/-- **The Taylor remainder has a sign.** Let `f` be `C^(n+1)` on an open set `s` containing
`[x, y]`, with `(-1)ⁿ f⁽ⁿ⁺¹⁾ ≥ 0` on `(x, y)`. Then the Taylor polynomial of order `n` of `f`
expanded at `y` and evaluated at `x` is at least `f x`. -/
theorem le_taylorWithinEval_of_neg_one_pow_mul_iteratedDerivWithin_nonneg {f : ℝ → ℝ} {s : Set ℝ}
    {n : ℕ} {x y : ℝ} (hs : IsOpen s) (hxy : x ≤ y) (hsub : Icc x y ⊆ s)
    (hf : ContDiffOn ℝ (n + 1) f s)
    (hsign : ∀ z ∈ Ioo x y, 0 ≤ (-1) ^ n * iteratedDerivWithin (n + 1) f s z) :
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
    have hzIoo : z ∈ Ioo x y := by simpa only [interior_Icc] using hz
    have hpow : (x - z) ^ n = (-1) ^ n * (z - x) ^ n := by rw [← mul_pow]; ring
    rw [smul_eq_mul, hpow]
    have := hsign z hzIoo
    have : 0 ≤ (z - x) ^ n := pow_nonneg (sub_nonneg.mpr hzIoo.1.le) n
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
