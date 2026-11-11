/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Polynomials with converging coefficients

Let `P i` be polynomials over a normed field, indexed along a filter `l`, whose coefficients
converge to those of a polynomial `P₀`, and whose degrees are eventually at most a fixed `N`.
This file records the estimates which make such a family behave uniformly:

* on every closed ball, `P i → P₀` uniformly
  (`Polynomial.tendstoUniformlyOn_eval_closedBall_of_tendsto_coeff`);
* the derivatives have the same property, since their coefficients converge as well
  (`Polynomial.tendsto_coeff_derivative`);
* the values grow at most like `(1 + ‖z‖) ^ N`, with a constant independent of `i`
  (`Polynomial.exists_eventually_forall_norm_eval_le`);
* if the degrees are eventually at most `deg P₀` and `P₀ ≠ 0`, the values also grow at least like
  `‖z‖ ^ deg P₀` outside a fixed ball, again with constants independent of `i`
  (`Polynomial.exists_eventually_forall_mul_pow_le_norm_eval`). In particular, if `deg P₀ ≥ 1`,
  then eventually `‖P i‖ ≥ 1` outside a fixed ball
  (`Polynomial.exists_eventually_forall_one_le_norm_eval`);
* in any case the degree can only jump up in the limit: eventually `deg P₀ ≤ deg P i`
  (`Polynomial.eventually_natDegree_le_natDegree_of_tendsto_coeff`).

The degree bound cannot be dropped: `z + z ^ 2 / i` has coefficients converging to those of `z`,
but a root at `-i`, which escapes to infinity.

When `P₀` has degree at least one, these bounds give the uniform decay
`(1 + ‖P i‖²)⁻¹ ≤ A / (1 + ‖z‖) ^ 2`
(`Polynomial.exists_eventually_forall_inv_one_add_norm_eval_sq_le`) and the uniform comparison
`‖(P i)'‖² ≤ B (1 + ‖P i‖²)` (`Polynomial.exists_eventually_forall_norm_derivative_eval_sq_le`).
These are the uniform versions, along a converging family, of the decay statements of
`TauCeti.Analysis.Polynomial.AtInfinity`.
-/

public section

namespace Polynomial

open Filter Finset Metric Topology

variable {𝕜 ι : Type*} [NormedField 𝕜] {l : Filter ι} {P : ι → Polynomial 𝕜} {P₀ : Polynomial 𝕜}

/-- If the coefficients of `P i` converge to those of `P₀`, so do the coefficients of their
derivatives. -/
theorem tendsto_coeff_derivative (hP : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (P₀.coeff k)))
    (k : ℕ) :
    Tendsto (fun i ↦ (derivative (P i)).coeff k) l (𝓝 ((derivative P₀).coeff k)) := by
  simp only [coeff_derivative]
  exact (hP (k + 1)).mul_const _

/-- The norm of the value of a polynomial of degree less than `n` at `z` is at most the sum of
the norms of its first `n` coefficients times `‖z‖ ^ k`. -/
theorem norm_eval_le_sum_norm_coeff_mul_pow {p : Polynomial 𝕜} {n : ℕ} (hn : p.natDegree < n)
    (z : 𝕜) :
    ‖p.eval z‖ ≤ ∑ k ∈ range n, ‖p.coeff k‖ * ‖z‖ ^ k := by
  rw [eval_eq_sum_range' hn]
  refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun k _ ↦ ?_))
  rw [norm_mul, norm_pow]

/-- **Uniform convergence on balls.** If the degrees of `P i` are eventually at most `N`, the
degree of `P₀` is at most `N`, and the coefficients converge, then `P i → P₀` uniformly on every
closed ball. -/
theorem tendstoUniformlyOn_eval_closedBall_of_tendsto_coeff {N : ℕ}
    (hN : ∀ᶠ i in l, (P i).natDegree ≤ N) (hN₀ : P₀.natDegree ≤ N)
    (hP : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (P₀.coeff k))) (R : ℝ) :
    TendstoUniformlyOn (fun i z ↦ (P i).eval z) P₀.eval l (closedBall 0 R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- The coefficientwise errors, weighted by `R ^ k`, sum to a quantity tending to zero.
  have hsum : Tendsto (fun i ↦ ∑ k ∈ range (N + 1), ‖(P i).coeff k - P₀.coeff k‖ * |R| ^ k) l
      (𝓝 (∑ k ∈ range (N + 1), ‖P₀.coeff k - P₀.coeff k‖ * |R| ^ k)) :=
    tendsto_finsetSum _ fun k _ ↦ (((hP k).sub_const _).norm).mul_const _
  simp only [sub_self, norm_zero, zero_mul, sum_const_zero] at hsum
  filter_upwards [hN, hsum.eventually (gt_mem_nhds hε)] with i hi hlt z hz
  have hz' : ‖z‖ ≤ |R| := (mem_closedBall_zero_iff.mp hz).trans (le_abs_self R)
  rw [dist_eq_norm, ← eval_sub]
  refine lt_of_le_of_lt ((norm_eval_le_sum_norm_coeff_mul_pow
    ((natDegree_sub_le _ _).trans_lt (Nat.lt_succ_of_le (max_le hN₀ hi))) z).trans
    (sum_le_sum fun k _ ↦ ?_)) hlt
  rw [coeff_sub, norm_sub_rev]
  gcongr

/-- **A uniform polynomial growth bound.** If the degrees of `P i` are eventually at most `N` and
the coefficients converge, then `‖P i z‖ ≤ C (1 + ‖z‖) ^ N` for all `z`, eventually in `i`, with
`C` independent of `i`. -/
theorem exists_eventually_forall_norm_eval_le {N : ℕ} (hN : ∀ᶠ i in l, (P i).natDegree ≤ N)
    (hP : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (P₀.coeff k))) :
    ∃ C : ℝ, ∀ᶠ i in l, ∀ z, ‖(P i).eval z‖ ≤ C * (1 + ‖z‖) ^ N := by
  refine ⟨∑ k ∈ range (N + 1), (‖P₀.coeff k‖ + 1), ?_⟩
  have hb : ∀ k ∈ range (N + 1), ∀ᶠ i in l, ‖(P i).coeff k‖ < ‖P₀.coeff k‖ + 1 := fun k _ ↦
    (hP k).norm.eventually (gt_mem_nhds (lt_add_one _))
  filter_upwards [hN, (eventually_all_finset _).2 hb] with i hi hlt z
  rw [sum_mul]
  refine (norm_eval_le_sum_norm_coeff_mul_pow (Nat.lt_succ_of_le hi) z).trans
    (sum_le_sum fun k hk ↦ ?_)
  have h1 : (1 : ℝ) ≤ 1 + ‖z‖ := le_add_of_nonneg_right (norm_nonneg z)
  have hzk : ‖z‖ ^ k ≤ (1 + ‖z‖) ^ N :=
    (pow_le_pow_left₀ (norm_nonneg z) (le_add_of_nonneg_left zero_le_one) k).trans
      (pow_le_pow_right₀ h1 (Nat.lt_succ_iff.mp (mem_range.mp hk)))
  exact mul_le_mul (hlt k hk).le hzk (by positivity) (by positivity)

/-- **A uniform lower growth bound outside a ball.** If `P₀ ≠ 0`, the degrees of `P i` are
eventually at most that of `P₀`, and the coefficients converge, then there are `c > 0` and `R ≥ 1`
such that `c ‖z‖ ^ deg P₀ ≤ ‖P i z‖` whenever `R ≤ ‖z‖`, eventually in `i`. -/
theorem exists_eventually_forall_mul_pow_le_norm_eval (hP₀ : P₀ ≠ 0)
    (hN : ∀ᶠ i in l, (P i).natDegree ≤ P₀.natDegree)
    (hP : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (P₀.coeff k))) :
    ∃ c > 0, ∃ R ≥ 1, ∀ᶠ i in l, ∀ z, R ≤ ‖z‖ → c * ‖z‖ ^ P₀.natDegree ≤ ‖(P i).eval z‖ := by
  set N := P₀.natDegree
  set a := ‖P₀.leadingCoeff‖
  have ha : 0 < a := norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hP₀)
  set S := ∑ k ∈ range N, (‖P₀.coeff k‖ + 1)
  have hS : 0 ≤ S := sum_nonneg fun k _ ↦ by positivity
  refine ⟨a / 4, by positivity, max 1 (4 * S / a), le_max_left _ _, ?_⟩
  have hb : ∀ k ∈ range N, ∀ᶠ i in l, ‖(P i).coeff k‖ < ‖P₀.coeff k‖ + 1 := fun k _ ↦
    (hP k).norm.eventually (gt_mem_nhds (lt_add_one _))
  have hlead : ∀ᶠ i in l, a / 2 < ‖(P i).coeff N‖ :=
    (hP N).norm.eventually (lt_mem_nhds (by rw [coeff_natDegree]; linarith))
  filter_upwards [hN, (eventually_all_finset _).2 hb, hlead] with i hi hlt hl z hz
  have hz1 : 1 ≤ ‖z‖ := (le_max_left _ _).trans hz
  have hzS : 4 * S / a ≤ ‖z‖ := (le_max_right _ _).trans hz
  -- Split off the top coefficient: `P i z = ∑_{k < N} cₖ z ^ k + c_N z ^ N`.
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hi), sum_range_succ]
  -- The lower terms are at most `S ‖z‖ ^ N / ‖z‖ ≤ (a / 4) ‖z‖ ^ N`.
  have hlow : ‖∑ k ∈ range N, (P i).coeff k * z ^ k‖ * ‖z‖ ≤ S * ‖z‖ ^ N := by
    refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (norm_nonneg z)).trans ?_
    rw [sum_mul, sum_mul]
    refine sum_le_sum fun k hk ↦ ?_
    have hkN : k + 1 ≤ N := mem_range.mp hk
    rw [norm_mul, norm_pow, mul_assoc, ← pow_succ]
    exact mul_le_mul (hlt k hk).le (pow_le_pow_right₀ hz1 hkN) (by positivity) (by positivity)
  have hlow' : ‖∑ k ∈ range N, (P i).coeff k * z ^ k‖ ≤ a / 4 * ‖z‖ ^ N := by
    have hzpos : 0 < ‖z‖ := zero_lt_one.trans_le hz1
    have h4 : S ≤ a / 4 * ‖z‖ := by
      rw [div_le_iff₀ ha] at hzS
      linarith
    have := hlow.trans (mul_le_mul_of_nonneg_right h4 (by positivity))
    rw [mul_right_comm] at this
    exact le_of_mul_le_mul_right this hzpos
  have htop : a / 2 * ‖z‖ ^ N ≤ ‖(P i).coeff N * z ^ N‖ := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right hl.le (by positivity)
  have := norm_sub_norm_le ((P i).coeff N * z ^ N) (-∑ k ∈ range N, (P i).coeff k * z ^ k)
  rw [norm_neg, sub_neg_eq_add, add_comm] at this
  linarith

/-- **The degree is lower semicontinuous.** If the coefficients of `P i` converge to those of
`P₀`, then eventually `deg P₀ ≤ deg P i`. -/
theorem eventually_natDegree_le_natDegree_of_tendsto_coeff
    (hP : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (P₀.coeff k))) :
    ∀ᶠ i in l, P₀.natDegree ≤ (P i).natDegree := by
  rcases eq_or_ne P₀ 0 with rfl | hP₀
  · exact Eventually.of_forall fun i ↦ by simp
  have hlead : P₀.coeff P₀.natDegree ≠ 0 := by
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hP₀
  filter_upwards [(hP P₀.natDegree).eventually_ne hlead] with i hi
  exact le_natDegree_of_ne_zero hi

/-- **Uniform modulus at least one outside a ball.** If `P₀` has degree at least one, the degrees
of `P i` are eventually at most that of `P₀`, and the coefficients converge, then there is a radius
`R` such that eventually `1 ≤ ‖P i z‖` for every `z` outside the closed ball of radius `R`. -/
theorem exists_eventually_forall_one_le_norm_eval (hm : 0 < P₀.natDegree)
    (hN : ∀ᶠ i in l, (P i).natDegree ≤ P₀.natDegree)
    (hP : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (P₀.coeff k))) :
    ∃ R : ℝ, ∀ᶠ i in l, ∀ z ∉ closedBall (0 : 𝕜) R, 1 ≤ ‖(P i).eval z‖ := by
  obtain ⟨c, hc, R, hR, hb⟩ :=
    exists_eventually_forall_mul_pow_le_norm_eval (ne_zero_of_natDegree_gt hm) hN hP
  refine ⟨max R c⁻¹, ?_⟩
  filter_upwards [hb] with i hi z hz
  rw [mem_closedBall_zero_iff, not_le] at hz
  have hzR : R ≤ ‖z‖ := (le_max_left _ _).trans hz.le
  have hz1 : 1 ≤ ‖z‖ := hR.trans hzR
  calc (1 : ℝ) = c * c⁻¹ := (mul_inv_cancel₀ hc.ne').symm
    _ ≤ c * ‖z‖ ^ P₀.natDegree := by
        gcongr
        exact ((le_max_right _ _).trans hz.le).trans (le_self_pow₀ hz1 hm.ne')
    _ ≤ ‖(P i).eval z‖ := hi z hzR

/-- **Uniform decay of `(1 + ‖P‖²)⁻¹`.** If `P₀` has degree at least one, the degrees of `P i` are
eventually at most that of `P₀`, and the coefficients converge, then
`(1 + ‖P i z‖²)⁻¹ ≤ A / (1 + ‖z‖) ^ 2` for all `z`, eventually in `i`, with `A` independent of
`i`. -/
theorem exists_eventually_forall_inv_one_add_norm_eval_sq_le (hm : 0 < P₀.natDegree)
    (hN : ∀ᶠ i in l, (P i).natDegree ≤ P₀.natDegree)
    (hP : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (P₀.coeff k))) :
    ∃ A : ℝ, ∀ᶠ i in l, ∀ z, (1 + ‖(P i).eval z‖ ^ 2)⁻¹ ≤ A / (1 + ‖z‖) ^ 2 := by
  obtain ⟨c, hc, R, hR, hb⟩ :=
    exists_eventually_forall_mul_pow_le_norm_eval (ne_zero_of_natDegree_gt hm) hN hP
  refine ⟨max (4 / c ^ 2) ((1 + R) ^ 2), ?_⟩
  filter_upwards [hb] with i hi z
  rw [inv_le_iff_one_le_mul₀ (by positivity), div_mul_eq_mul_div, le_div_iff₀ (by positivity),
    one_mul]
  by_cases hz : R ≤ ‖z‖
  · -- Far out, `‖P i z‖ ≥ c ‖z‖ ^ m ≥ c ‖z‖` and `1 + ‖z‖ ≤ 2 ‖z‖`.
    have hz1 : 1 ≤ ‖z‖ := hR.trans hz
    have hPz : c * ‖z‖ ≤ ‖(P i).eval z‖ :=
      (mul_le_mul_of_nonneg_left (le_self_pow₀ hz1 hm.ne') hc.le).trans (hi z hz)
    have h2 : (1 + ‖z‖) ^ 2 ≤ 4 / c ^ 2 * (c * ‖z‖) ^ 2 := by
      rw [mul_pow, ← mul_assoc, div_mul_cancel₀ _ (by positivity)]
      nlinarith
    calc (1 + ‖z‖) ^ 2 ≤ 4 / c ^ 2 * (c * ‖z‖) ^ 2 := h2
      _ ≤ 4 / c ^ 2 * (1 + ‖(P i).eval z‖ ^ 2) := by
          gcongr
          nlinarith [pow_le_pow_left₀ (by positivity) hPz 2]
      _ ≤ max (4 / c ^ 2) ((1 + R) ^ 2) * (1 + ‖(P i).eval z‖ ^ 2) := by
          gcongr
          exact le_max_left _ _
  · -- On the ball, `(1 + ‖z‖) ^ 2 ≤ (1 + R) ^ 2`.
    calc (1 + ‖z‖) ^ 2 ≤ (1 + R) ^ 2 * 1 := by
          rw [mul_one]
          gcongr
          exact (not_le.mp hz).le
      _ ≤ max (4 / c ^ 2) ((1 + R) ^ 2) * (1 + ‖(P i).eval z‖ ^ 2) := by
          gcongr
          · exact le_max_right _ _
          · exact le_add_of_nonneg_right (by positivity)

/-- **The derivative is uniformly dominated.** If `P₀` has degree at least one, the degrees of
`P i` are eventually at most that of `P₀`, and the coefficients converge, then
`‖(P i)' z‖² ≤ B (1 + ‖P i z‖²)` for all `z`, eventually in `i`, with `B` independent of `i`. -/
theorem exists_eventually_forall_norm_derivative_eval_sq_le (hm : 0 < P₀.natDegree)
    (hN : ∀ᶠ i in l, (P i).natDegree ≤ P₀.natDegree)
    (hP : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (P₀.coeff k))) :
    ∃ B : ℝ, ∀ᶠ i in l, ∀ z,
      ‖(derivative (P i)).eval z‖ ^ 2 ≤ B * (1 + ‖(P i).eval z‖ ^ 2) := by
  set m := P₀.natDegree
  obtain ⟨c, hc, R, hR, hb⟩ :=
    exists_eventually_forall_mul_pow_le_norm_eval (ne_zero_of_natDegree_gt hm) hN hP
  obtain ⟨D, hD⟩ := exists_eventually_forall_norm_eval_le (N := m)
    (hN.mono fun i hi ↦ (natDegree_derivative_le _).trans (Nat.sub_le_of_le_add (by omega)))
    (tendsto_coeff_derivative hP)
  refine ⟨(D * 2 ^ m / c) ^ 2 + (D * (1 + R) ^ m) ^ 2, ?_⟩
  filter_upwards [hb, hD] with i hi hDi z
  have hP2 : 0 ≤ ‖(P i).eval z‖ ^ 2 := by positivity
  have hd := hDi z
  by_cases hz : R ≤ ‖z‖
  · -- Far out, `(1 + ‖z‖) ^ m ≤ 2 ^ m ‖z‖ ^ m ≤ (2 ^ m / c) ‖P i z‖`.
    have hz1 : 1 ≤ ‖z‖ := hR.trans hz
    have h1 : (1 + ‖z‖) ^ m ≤ 2 ^ m / c * ‖(P i).eval z‖ := by
      calc (1 + ‖z‖) ^ m ≤ (2 * ‖z‖) ^ m := by gcongr; linarith
        _ = 2 ^ m / c * (c * ‖z‖ ^ m) := by
            rw [mul_pow, ← mul_assoc, div_mul_cancel₀ _ hc.ne']
        _ ≤ 2 ^ m / c * ‖(P i).eval z‖ := by gcongr; exact hi z hz
    have h2 : ‖(derivative (P i)).eval z‖ ≤ D * 2 ^ m / c * ‖(P i).eval z‖ := by
      have hD0 : 0 ≤ D :=
        nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hd) (by positivity)
      calc ‖(derivative (P i)).eval z‖ ≤ D * (2 ^ m / c * ‖(P i).eval z‖) :=
            hd.trans (mul_le_mul_of_nonneg_left h1 hD0)
        _ = D * 2 ^ m / c * ‖(P i).eval z‖ := by ring
    have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    rw [mul_pow] at h3
    nlinarith [sq_nonneg (D * (1 + R) ^ m), sq_nonneg (D * 2 ^ m / c)]
  · -- On the ball, `‖(P i)' z‖ ≤ D (1 + R) ^ m`.
    have h1 : ‖(derivative (P i)).eval z‖ ≤ D * (1 + R) ^ m := by
      have hD0 : 0 ≤ D :=
        nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hd) (by positivity)
      refine hd.trans (mul_le_mul_of_nonneg_left ?_ hD0)
      gcongr
      exact (not_le.mp hz).le
    have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (D * (1 + R) ^ m), sq_nonneg (D * 2 ^ m / c)]

end Polynomial
