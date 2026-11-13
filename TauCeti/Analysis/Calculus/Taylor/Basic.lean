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
including uniform second-order estimates for functions C² near compact sets.
The file provides:

* **Uniform second-order remainder.** For a function C² near a compact set, the
  second-order Taylor remainder is bounded by `ε * (y - x)²` whenever the increment is
  sufficiently small, uniformly over endpoints in the set.
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

* `TauCeti.taylorWithinEval_univ_two`: the quadratic Taylor polynomial expressed using ordinary
  derivatives.
* `TauCeti.exists_pos_forall_abs_sub_taylorWithinEval_two_le`: a uniform small-coefficient
  second-order remainder estimate on a compact interval. The variant
  `TauCeti.exists_pos_forall_abs_sub_taylorWithinEval_two_le_of_isCompact` applies to any
  compact set, without smoothness in the gaps between its points.
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

/-- On a nondegenerate unordered interval, the Taylor polynomial at its first endpoint agrees
with that computed on the whole line whenever the function is sufficiently smooth there. -/
theorem taylorWithinEval_uIcc_eq_univ {f : ℝ → ℝ} {n : ℕ} {x y : ℝ}
    (hxy : x ≠ y) (hf : ContDiffAt ℝ n f x) :
    taylorWithinEval f n (uIcc x y) x y = taylorWithinEval f n univ x y := by
  simp only [taylor_within_apply, iteratedDerivWithin_univ]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hxy)
    (hf.of_le (mod_cast Nat.le_of_lt_succ (Finset.mem_range.1 hk))) left_mem_uIcc]

/-- **Taylor's theorem with a bounded remainder.** If `f` is `C^(n+1)` near each point between
`x₀` and `x`, including the endpoints, and its `(n+1)`st derivative is bounded in absolute
value by `M` strictly between `x₀` and `x`, then its Taylor
polynomial of order `n` about `x₀` approximates `f x` with error at most
`M * |x - x₀|^(n+1) / (n+1)!`. -/
theorem abs_sub_taylorWithinEval_le {f : ℝ → ℝ} {n : ℕ} {M x₀ x : ℝ}
    (hf : ∀ t ∈ uIcc x₀ x, ContDiffAt ℝ (n + 1) f t)
    (hM : ∀ t ∈ uIoo x₀ x, |iteratedDeriv (n + 1) f t| ≤ M) :
    |f x - taylorWithinEval f n univ x₀ x| ≤ M * |x - x₀| ^ (n + 1) / (n + 1)! := by
  rcases eq_or_ne x₀ x with rfl | hx
  · simp
  obtain ⟨y, hy, hfy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hx
    (fun t ht ↦ (hf t ht).contDiffWithinAt)
  rw [taylorWithinEval_uIcc_eq_univ hx ((hf x₀ left_mem_uIcc).of_le
    (mod_cast n.le_succ))] at hfy
  rw [hfy, abs_div, abs_mul, abs_pow, Nat.abs_cast]
  gcongr
  exact hM y hy

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
    rw [taylorWithinEval_uIcc_eq_univ h ((hf x hx).of_le (by norm_num))]
    simp [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDeriv_one,
      smul_eq_mul, mul_comm]
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

/-- Uniform second-order Taylor remainder estimate for a function C² near a compact set.
Only smoothness at the points of the set is required, even when the set is disconnected. -/
theorem exists_pos_forall_abs_sub_taylorWithinEval_two_le_of_isCompact {f : ℝ → ℝ}
    {s : Set ℝ} (hf : ∀ z ∈ s, ContDiffAt ℝ 2 f z) (hs : IsCompact s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ s, ∀ y ∈ s, |y - x| < δ →
      |f y - taylorWithinEval f 2 univ x y| ≤ ε * (y - x) ^ 2 := by
  have hlocal (z : s) : ∃ U : Set ℝ, IsOpen U ∧ (z : ℝ) ∈ U ∧
      ∀ x ∈ U, ∀ y ∈ U,
        |f y - taylorWithinEval f 2 univ x y| ≤ ε * (y - x) ^ 2 := by
    obtain ⟨a, b, _, hab, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds
      ((hf z z.property).eventually (by norm_num))
    obtain ⟨η, hη, hTaylor⟩ := exists_pos_forall_abs_sub_taylorWithinEval_two_le
      (fun x hx ↦ hsub hx) hε
    refine ⟨interior (Icc a b) ∩ Metric.ball (z : ℝ) (η / 2),
      isOpen_interior.inter Metric.isOpen_ball,
      ⟨mem_interior_iff_mem_nhds.2 hab, Metric.mem_ball_self (half_pos hη)⟩, ?_⟩
    intro x hx y hy
    apply hTaylor x (interior_subset hx.1) y (interior_subset hy.1)
    rw [← Real.dist_eq]
    have hx' := Metric.mem_ball.1 hx.2
    have hy' := Metric.mem_ball.1 hy.2
    have := dist_triangle y (z : ℝ) x
    rw [dist_comm (z : ℝ) x] at this
    linarith
  choose U hU hz hTaylor using hlocal
  obtain ⟨δ, hδ, hcover⟩ := lebesgue_number_lemma_of_metric hs hU
    (fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, hz ⟨x, hx⟩⟩)
  refine ⟨δ, hδ, fun x hx y _ hxy ↦ ?_⟩
  obtain ⟨z, hball⟩ := hcover x hx
  exact hTaylor z x (hball (Metric.mem_ball_self hδ)) y
    (hball (by simpa only [Metric.mem_ball, Real.dist_eq] using hxy))

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

/-- **The derivatives of `f(t) / t`.** If `f` is `C^n` at `t ≠ 0` and `s` is a set of unique
differentiability containing `t` (for instance an open set, or an interval with `t` an endpoint),
then `dⁿ/dtⁿ (f(t) / t) = (-1)ⁿ n! t⁻ⁿ⁻¹ · T(0)`, where `T` is the Taylor polynomial of order `n`
of `f` expanded at `t` (within `s`). -/
theorem iteratedDeriv_div_id {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {t : ℝ}
    (hs : UniqueDiffOn ℝ s) (ht : t ∈ s) (ht0 : t ≠ 0) (hf : ContDiffAt ℝ n f t) :
    iteratedDeriv n (fun x => f x / x) t =
      (-1) ^ n * n ! * (t ^ (n + 1))⁻¹ * taylorWithinEval f n s t 0 := by
  have hfun : (fun x => f x / x) = f * Inv.inv := by
    funext x
    simp [div_eq_mul_inv]
  have hinv {m : ℕ} : ContDiffAt ℝ m (Inv.inv : ℝ → ℝ) t := contDiffAt_inv ℝ ht0
  rw [hfun, ← iteratedDerivWithin_eq_iteratedDeriv (f := f * Inv.inv) hs (hf.mul hinv) ht,
    iteratedDerivWithin_mul ht hs hf.contDiffWithinAt hinv.contDiffWithinAt,
    taylor_within_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  rw [Nat.add_sub_cancel_left,
    iteratedDerivWithin_eq_iteratedDeriv hs hinv ht, iteratedDeriv_eq_iterate,
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
