/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: the Tau Ceti contributors
-/
module

public import TauCeti.Data.Matrix.Sinkhorn.Basic

/-!
# Explicit rates for the Sinkhorn iteration

Let `K` be a kernel with strictly positive entries, let `a` and `b` be strictly positive row and
column sums, and let `P` be the Sinkhorn–Knopp scaling `u i * K i j * v j` of `K` with these
marginals. The linear convergence theorems of `TauCeti.Data.Matrix.Sinkhorn.Basic` measure the
error after `n` steps against the Hilbert distance from the initial row factors `u₀` to the unknown
factors `u`. This file removes that dependence: the rates here involve only the kernel, through
its projective diameter `Δ(K)`, the step count `n` and, for the objective, the total mass.

The point is that a half-step `x ↦ c / (A *ᵥ x)` lands within `Δ(A)` of every other half-step,
whatever its input (`Matrix.hilbertProjectiveDist_sinkhornUpdate_le_projectiveDiameter`). So the
column factors of the iteration are within `Δ(K)` of `v` before any contraction has taken place,
and within `tanh (Δ(K) / 4) ^ (2 * n) * Δ(K)` after `n` steps; the row factors are within
`tanh (Δ(K) / 4) ^ (2 * n + 1) * Δ(K)` of `u` after `n + 1` steps. If the entries of `K` lie
between `m > 0` and `M`, then `Δ(K) ≤ 2 * log (M / m)` and `tanh (Δ(K) / 4) ≤ (M - m) / (M + m)`
(`Matrix.projectiveDiameter_le_two_mul_log_div`, `Matrix.tanh_projectiveDiameter_div_four_le`).
Since the Hilbert distance between positive vectors is the oscillation of the difference of their
logarithms, these are rates for the dual potentials `log u` and `log v` modulo constants.

With `δ n = tanh (Δ(K) / 4) ^ (2 * n) * Δ(K)`, the Sinkhorn plan after `n` steps agrees with `P`
entrywise up to the factor `exp (δ n)`, so the error of its column sums, whose row sums are
exactly `a`, is at most `(exp (δ n) - 1) * ∑ j, b j` in `ℓ¹`.

The objective is measured through duality. The minimisation of `Matrix.relEntropy · K` over the
nonnegative matrices with row sums `a` and column sums `b` has the concave dual objective
`Matrix.relEntropyDual K a b f g = ∑ i, a i * f i + ∑ j, b j * g j + ∑ i, a i -
∑ i, ∑ j, exp (f i) * K i j * exp (g j)`, the Lagrangian dual written in potentials shifted so
that the optimal ones are `log u` and `log v`. Every dual value is at most every primal value
(`Matrix.relEntropyDual_le_relEntropy`), and the two meet at `P`
(`Matrix.IsDiagonalScaling.relEntropyDual_eq_relEntropy`). Each half-step of the Sinkhorn
iteration maximises this concave objective in one block of potentials, which is why its values
measure the progress of the iteration; that maximisation property is not used here. The gap
between the minimum `relEntropy P K` and the dual value at the logarithms of the factors of the
Sinkhorn plan after `n` steps is the relative entropy of `P` against that plan, hence at most
`(∑ i, a i) * δ n`.

## Main results

* `Matrix.hilbertProjectiveDist_sinkhornUpdate_iterate_le_mul_projectiveDiameter` and
  `Matrix.hilbertProjectiveDist_sinkhornStep_iterate_succ_le_mul_projectiveDiameter`: from any
  two strictly positive initial vectors, the column factors after `n` steps are within
  `tanh (Δ(K) / 4) ^ (2 * n) * Δ(K)` of each other, and the row factors after `n + 1` steps within
  `tanh (Δ(K) / 4) ^ (2 * n + 1) * Δ(K)`.
* `IsDiagonalScaling.hilbertProjectiveDist_sinkhornUpdate_iterate_le_mul_projectiveDiameter` and
  `IsDiagonalScaling.hilbertProjectiveDist_sinkhornStep_iterate_succ_le_mul_projectiveDiameter`
  (in the `Matrix` namespace): the same rates towards the factors of the Sinkhorn–Knopp scaling.
* `Matrix.sinkhornPlan_iterate_apply_le_exp_mul_projectiveDiameter_mul` and
  `Matrix.le_exp_mul_projectiveDiameter_mul_sinkhornPlan_iterate_apply`: the entries of the
  Sinkhorn plan after `n` steps agree with those of the scaling up to the factor `exp (δ n)`.
* `Matrix.abs_sum_sinkhornPlan_iterate_apply_sub_le` and
  `Matrix.sum_abs_sum_sinkhornPlan_iterate_apply_sub_le`: the column-sum residual after `n` steps.
* `Matrix.IsDiagonalScaling.relEntropy_sub_relEntropyDual_iterate_le`: the objective gap of the
  Sinkhorn iteration after `n` steps is at most `(∑ i, a i) * δ n`.

## References

* J. Franklin and J. Lorenz, *On the scaling of multidimensional matrices*, Linear Algebra Appl.
  114/115 (1989), 717--735, for the contraction rate of the Sinkhorn iteration in Hilbert's
  projective metric and its expression through the entries of the kernel.
* I. Csiszár, *I-divergence geometry of probability distributions and minimization problems*,
  Ann. Probab. 3 (1975), 146--158, for the relative-entropy identities behind the duality gap.
* G. Peyré and M. Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11 (2019),
  Sections 4.2 and 4.4, for the dual of the entropic problem and Sinkhorn's algorithm as block
  coordinate ascent on it.
-/

public section

open Real TauCeti

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### Potentials -/

/-- From any two strictly positive initial row factors, the column factors of the Sinkhorn iteration
after `n` steps are within `tanh (K.projectiveDiameter / 4) ^ (2 * n) * K.projectiveDiameter` of
each other in Hilbert's projective metric. -/
theorem hilbertProjectiveDist_sinkhornUpdate_iterate_le_mul_projectiveDiameter
    {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j) {a : ι → ℝ} (ha : ∀ i, 0 < a i) {b : κ → ℝ}
    (hb : ∀ j, 0 < b j) {x y : ι → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (n : ℕ) :
    hilbertProjectiveDist (Kᵀ.sinkhornUpdate b ((K.sinkhornStep a b)^[n] x))
        (Kᵀ.sinkhornUpdate b ((K.sinkhornStep a b)^[n] y)) ≤
      tanh (K.projectiveDiameter / 4) ^ (2 * n) * K.projectiveDiameter := by
  have ht := tanh_projectiveDiameter_div_four_nonneg K
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- without rows all row factors coincide
    rw [Subsingleton.elim ((K.sinkhornStep a b)^[n] x) ((K.sinkhornStep a b)^[n] y),
      hilbertProjectiveDist_self]
    exact mul_nonneg (pow_nonneg ht _) (projectiveDiameter_nonneg K)
  have hKt : ∀ j i, 0 < Kᵀ j i := fun j i ↦ by simpa using hK i j
  -- the column factors follow the Sinkhorn iteration of `Kᵀ` from the first column update
  have hsemi : Function.Semiconj (Kᵀ.sinkhornUpdate b) (K.sinkhornStep a b)
      (Kᵀ.sinkhornStep b a) := fun z ↦ by simp [sinkhornStep_def]
  rw [hsemi.iterate_right, hsemi.iterate_right]
  have h := hilbertProjectiveDist_sinkhornStep_iterate_le hKt hb ha (sinkhornUpdate_pos hKt hb hx)
    (sinkhornUpdate_pos hKt hb hy) n
  have h0 := hilbertProjectiveDist_sinkhornUpdate_le_projectiveDiameter hKt (fun j ↦ (hb j).ne')
    (fun i ↦ (hx i).le) (fun i ↦ (hy i).le)
  rw [projectiveDiameter_transpose] at h h0
  exact h.trans (mul_le_mul_of_nonneg_left h0 (pow_nonneg ht _))

/-- From any two strictly positive initial row factors, the row factors of the Sinkhorn iteration
after `n + 1` steps are within
`tanh (K.projectiveDiameter / 4) ^ (2 * n + 1) * K.projectiveDiameter` of each other in Hilbert's
projective metric. -/
theorem hilbertProjectiveDist_sinkhornStep_iterate_succ_le_mul_projectiveDiameter
    {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j) {a : ι → ℝ} (ha : ∀ i, 0 < a i) {b : κ → ℝ}
    (hb : ∀ j, 0 < b j) {x y : ι → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (n : ℕ) :
    hilbertProjectiveDist ((K.sinkhornStep a b)^[n + 1] x) ((K.sinkhornStep a b)^[n + 1] y) ≤
      tanh (K.projectiveDiameter / 4) ^ (2 * n + 1) * K.projectiveDiameter := by
  have ht := tanh_projectiveDiameter_div_four_nonneg K
  have hrate := mul_nonneg (pow_nonneg ht (2 * n + 1)) (projectiveDiameter_nonneg K)
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply', sinkhornStep_def,
    sinkhornStep_def]
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · -- without columns all column factors coincide
    rw [Subsingleton.elim (Kᵀ.sinkhornUpdate b _) (Kᵀ.sinkhornUpdate b _),
      hilbertProjectiveDist_self]
    exact hrate
  rcases isEmpty_or_nonempty ι with hι | hι
  · simpa [hilbertProjectiveDist_def] using hrate
  have hKt : ∀ j i, 0 < Kᵀ j i := fun j i ↦ by simpa using hK i j
  calc _ ≤ tanh (K.projectiveDiameter / 4) *
        (tanh (K.projectiveDiameter / 4) ^ (2 * n) * K.projectiveDiameter) :=
      (hilbertProjectiveDist_sinkhornUpdate_le hK (fun i ↦ (ha i).ne')
        (sinkhornUpdate_pos hKt hb (sinkhornStep_iterate_pos hK ha hb hx n))
        (sinkhornUpdate_pos hKt hb (sinkhornStep_iterate_pos hK ha hb hy n))).trans
        (mul_le_mul_of_nonneg_left
          (hilbertProjectiveDist_sinkhornUpdate_iterate_le_mul_projectiveDiameter hK ha hb hx hy n)
          ht)
    _ = tanh (K.projectiveDiameter / 4) ^ (2 * n + 1) * K.projectiveDiameter := by ring

/-- **Rate of the column potentials**: if `P` is the diagonal scaling of a strictly positive `K` by
strictly positive factors `u` and `v` with row sums `a` and column sums `b`, then from every
strictly positive `u₀` the column factors of the Sinkhorn iteration after `n` steps are within
`tanh (K.projectiveDiameter / 4) ^ (2 * n) * K.projectiveDiameter` of `v` in Hilbert's projective
metric. -/
theorem IsDiagonalScaling.hilbertProjectiveDist_sinkhornUpdate_iterate_le_mul_projectiveDiameter
    {P K : Matrix ι κ ℝ} {u : ι → ℝ} {v : κ → ℝ} (hP : IsDiagonalScaling P K u v) {a : ι → ℝ}
    {b : κ → ℝ} (hPm : HasMarginals P a b) (hK : ∀ i j, 0 < K i j) (ha : ∀ i, 0 < a i)
    (hb : ∀ j, 0 < b j) (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) {u₀ : ι → ℝ}
    (hu₀ : ∀ i, 0 < u₀ i) (n : ℕ) :
    hilbertProjectiveDist (Kᵀ.sinkhornUpdate b ((K.sinkhornStep a b)^[n] u₀)) v ≤
      tanh (K.projectiveDiameter / 4) ^ (2 * n) * K.projectiveDiameter := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simpa [hilbertProjectiveDist_def] using mul_nonneg
      (pow_nonneg (tanh_projectiveDiameter_div_four_nonneg K) (2 * n)) (projectiveDiameter_nonneg K)
  obtain ⟨j⟩ := id hκ
  have : Nonempty ι := hPm.nonempty_of_col_sum_ne_zero (hb j).ne'
  have hv' : Kᵀ.sinkhornUpdate b ((K.sinkhornStep a b)^[n] u) = v := by
    rw [Function.iterate_fixed (hP.sinkhornStep_eq hPm hK hu hv)]
    exact hP.sinkhornUpdate_transpose_eq ((hasMarginals_def P a b).1 hPm).2 hK hu
  rw [← hv']
  exact Matrix.hilbertProjectiveDist_sinkhornUpdate_iterate_le_mul_projectiveDiameter hK ha hb hu₀
    hu n

/-- **Rate of the row potentials**: in the setting of
`Matrix.IsDiagonalScaling.hilbertProjectiveDist_sinkhornUpdate_iterate_le_mul_projectiveDiameter`,
the row factors of the Sinkhorn iteration after `n + 1` steps from every strictly positive `u₀` are
within `tanh (K.projectiveDiameter / 4) ^ (2 * n + 1) * K.projectiveDiameter` of `u` in Hilbert's
projective metric. -/
theorem IsDiagonalScaling.hilbertProjectiveDist_sinkhornStep_iterate_succ_le_mul_projectiveDiameter
    {P K : Matrix ι κ ℝ} {u : ι → ℝ} {v : κ → ℝ} (hP : IsDiagonalScaling P K u v) {a : ι → ℝ}
    {b : κ → ℝ} (hPm : HasMarginals P a b) (hK : ∀ i j, 0 < K i j) (ha : ∀ i, 0 < a i)
    (hb : ∀ j, 0 < b j) (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) {u₀ : ι → ℝ}
    (hu₀ : ∀ i, 0 < u₀ i) (n : ℕ) :
    hilbertProjectiveDist ((K.sinkhornStep a b)^[n + 1] u₀) u ≤
      tanh (K.projectiveDiameter / 4) ^ (2 * n + 1) * K.projectiveDiameter := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simpa [hilbertProjectiveDist_def] using mul_nonneg
      (pow_nonneg (tanh_projectiveDiameter_div_four_nonneg K) (2 * n + 1))
      (projectiveDiameter_nonneg K)
  obtain ⟨i⟩ := id hι
  have : Nonempty κ := hPm.nonempty_of_row_sum_ne_zero (ha i).ne'
  have h := Matrix.hilbertProjectiveDist_sinkhornStep_iterate_succ_le_mul_projectiveDiameter hK ha
    hb hu₀ hu n
  rwa [Function.iterate_fixed (hP.sinkhornStep_eq hPm hK hu hv)] at h

/-! ### Plans and marginals -/

/-- **Linear convergence of the Sinkhorn iteration from any initial factors**, upper bound: if `P`
is the diagonal scaling of a strictly positive `K` by strictly positive factors with row sums `a`
and column sums `b`, then every entry of the Sinkhorn plan after `n` steps from a strictly positive
`u₀` is at most `exp (tanh (K.projectiveDiameter / 4) ^ (2 * n) * K.projectiveDiameter)` times the
corresponding entry of `P`. -/
theorem sinkhornPlan_iterate_apply_le_exp_mul_projectiveDiameter_mul {K : Matrix ι κ ℝ}
    (hK : ∀ i j, 0 < K i j) {a : ι → ℝ} (ha : ∀ i, 0 < a i) {b : κ → ℝ} (hb : ∀ j, 0 < b j)
    {P : Matrix ι κ ℝ} {u : ι → ℝ} {v : κ → ℝ} (hP : IsDiagonalScaling P K u v)
    (hPm : HasMarginals P a b) (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) {u₀ : ι → ℝ}
    (hu₀ : ∀ i, 0 < u₀ i) (n : ℕ) (i : ι) (j : κ) :
    K.sinkhornPlan a b ((K.sinkhornStep a b)^[n] u₀) i j ≤
      exp (tanh (K.projectiveDiameter / 4) ^ (2 * n) * K.projectiveDiameter) * P i j := by
  have : Nonempty κ := ⟨j⟩
  refine (hP.sinkhornPlan_apply_le_exp_mul hK (fun i ↦ (ha i).le) hb
    ((hasMarginals_def P a b).1 hPm).1 hv (sinkhornStep_iterate_pos hK ha hb hu₀ n) i j).trans ?_
  exact mul_le_mul_of_nonneg_right (exp_le_exp.2
    (hP.hilbertProjectiveDist_sinkhornUpdate_iterate_le_mul_projectiveDiameter hPm hK ha hb hu hv
      hu₀ n)) (hP.pos hK hu hv i j).le

/-- **Linear convergence of the Sinkhorn iteration from any initial factors**, lower bound: in the
setting of `Matrix.sinkhornPlan_iterate_apply_le_exp_mul_projectiveDiameter_mul`, every entry of `P`
is at most `exp (tanh (K.projectiveDiameter / 4) ^ (2 * n) * K.projectiveDiameter)` times the
corresponding entry of the Sinkhorn plan after `n` steps. -/
theorem le_exp_mul_projectiveDiameter_mul_sinkhornPlan_iterate_apply {K : Matrix ι κ ℝ}
    (hK : ∀ i j, 0 < K i j) {a : ι → ℝ} (ha : ∀ i, 0 < a i) {b : κ → ℝ} (hb : ∀ j, 0 < b j)
    {P : Matrix ι κ ℝ} {u : ι → ℝ} {v : κ → ℝ} (hP : IsDiagonalScaling P K u v)
    (hPm : HasMarginals P a b) (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) {u₀ : ι → ℝ}
    (hu₀ : ∀ i, 0 < u₀ i) (n : ℕ) (i : ι) (j : κ) :
    P i j ≤ exp (tanh (K.projectiveDiameter / 4) ^ (2 * n) * K.projectiveDiameter) *
      K.sinkhornPlan a b ((K.sinkhornStep a b)^[n] u₀) i j := by
  have : Nonempty ι := ⟨i⟩
  have : Nonempty κ := ⟨j⟩
  have hun := sinkhornStep_iterate_pos hK ha hb hu₀ n
  refine (hP.le_exp_mul_sinkhornPlan_apply hK hb ((hasMarginals_def P a b).1 hPm).1
    (fun i ↦ (hu i).le) hv hun i j).trans ?_
  exact mul_le_mul_of_nonneg_right (exp_le_exp.2
    (hP.hilbertProjectiveDist_sinkhornUpdate_iterate_le_mul_projectiveDiameter hPm hK ha hb hu hv
      hu₀ n))
    ((isDiagonalScaling_sinkhornPlan K a b _).pos hK (sinkhornStep_pos hK ha hb hun)
      (sinkhornUpdate_pos (fun j i ↦ by simpa using hK i j) hb hun) i j).le

/-- **Column residual of the Sinkhorn iteration**: in the setting of
`Matrix.sinkhornPlan_iterate_apply_le_exp_mul_projectiveDiameter_mul`, the `j`-th column sum of
the Sinkhorn plan after `n` steps differs from `b j` by at most
`(exp (tanh (K.projectiveDiameter / 4) ^ (2 * n) * K.projectiveDiameter) - 1) * b j`. -/
theorem abs_sum_sinkhornPlan_iterate_apply_sub_le {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j)
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) {b : κ → ℝ} (hb : ∀ j, 0 < b j) {P : Matrix ι κ ℝ}
    {u : ι → ℝ} {v : κ → ℝ} (hP : IsDiagonalScaling P K u v) (hPm : HasMarginals P a b)
    (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) {u₀ : ι → ℝ} (hu₀ : ∀ i, 0 < u₀ i) (n : ℕ)
    (j : κ) :
    |∑ i, K.sinkhornPlan a b ((K.sinkhornStep a b)^[n] u₀) i j - b j| ≤
      (exp (tanh (K.projectiveDiameter / 4) ^ (2 * n) * K.projectiveDiameter) - 1) * b j := by
  set E := exp (tanh (K.projectiveDiameter / 4) ^ (2 * n) * K.projectiveDiameter)
  have hb' := ((hasMarginals_def P a b).1 hPm).2 j
  have hup : ∑ i, K.sinkhornPlan a b ((K.sinkhornStep a b)^[n] u₀) i j ≤ E * b j := by
    rw [← hb', Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦
      sinkhornPlan_iterate_apply_le_exp_mul_projectiveDiameter_mul hK ha hb hP hPm hu hv hu₀ n i j
  have hlow : b j ≤ E * ∑ i, K.sinkhornPlan a b ((K.sinkhornStep a b)^[n] u₀) i j := by
    rw [← hb', Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦
      le_exp_mul_projectiveDiameter_mul_sinkhornPlan_iterate_apply hK ha hb hP hPm hu hv hu₀ n i j
  -- `b j ≤ E * s` gives `b j - s ≤ (1 - E⁻¹) * b j`, and `1 - E⁻¹ ≤ E - 1`
  have hE : 0 < E := exp_pos _
  rw [abs_sub_le_iff]
  constructor
  · linarith
  · nlinarith [mul_nonneg (hb j).le (sq_nonneg (E - 1))]

/-- **ℓ¹ column residual of the Sinkhorn iteration**: in the setting of
`Matrix.sinkhornPlan_iterate_apply_le_exp_mul_projectiveDiameter_mul`, the column sums of the
Sinkhorn plan after `n` steps differ from `b` in `ℓ¹` by at most
`(exp (tanh (K.projectiveDiameter / 4) ^ (2 * n) * K.projectiveDiameter) - 1) * ∑ j, b j`. Its row
sums are exactly `a`. -/
theorem sum_abs_sum_sinkhornPlan_iterate_apply_sub_le {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j)
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) {b : κ → ℝ} (hb : ∀ j, 0 < b j) {P : Matrix ι κ ℝ}
    {u : ι → ℝ} {v : κ → ℝ} (hP : IsDiagonalScaling P K u v) (hPm : HasMarginals P a b)
    (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) {u₀ : ι → ℝ} (hu₀ : ∀ i, 0 < u₀ i) (n : ℕ) :
    ∑ j, |∑ i, K.sinkhornPlan a b ((K.sinkhornStep a b)^[n] u₀) i j - b j| ≤
      (exp (tanh (K.projectiveDiameter / 4) ^ (2 * n) * K.projectiveDiameter) - 1) *
        ∑ j, b j := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ ↦
    abs_sum_sinkhornPlan_iterate_apply_sub_le hK ha hb hP hPm hu hv hu₀ n j

/-! ### The objective -/

/-- **Objective gap of the Sinkhorn iteration**: if `P` is the diagonal scaling of a strictly
positive `K` by strictly positive factors with row sums `a` and column sums `b`, so that
`relEntropy P K` is the minimum of the relative entropy against `K` with these marginals, then the
dual objective at the logarithms of the row and column factors of the Sinkhorn plan after `n` steps
from a strictly positive `u₀` falls short of that minimum by at most
`(∑ i, a i) * (tanh (K.projectiveDiameter / 4) ^ (2 * n) * K.projectiveDiameter)`. By
`Matrix.relEntropyDual_le_relEntropy` the shortfall is nonnegative. -/
theorem IsDiagonalScaling.relEntropy_sub_relEntropyDual_iterate_le {P K : Matrix ι κ ℝ}
    {u : ι → ℝ} {v : κ → ℝ} (hP : IsDiagonalScaling P K u v) {a : ι → ℝ} {b : κ → ℝ}
    (hPm : HasMarginals P a b) (hK : ∀ i j, 0 < K i j) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) {u₀ : ι → ℝ} (hu₀ : ∀ i, 0 < u₀ i) (n : ℕ) :
    relEntropy P K - K.relEntropyDual a b
        (fun i ↦ log (K.sinkhornStep a b ((K.sinkhornStep a b)^[n] u₀) i))
        (fun j ↦ log (Kᵀ.sinkhornUpdate b ((K.sinkhornStep a b)^[n] u₀) j)) ≤
      (∑ i, a i) * (tanh (K.projectiveDiameter / 4) ^ (2 * n) * K.projectiveDiameter) := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · -- a positive row sum needs a column, so there are no rows either
    have : IsEmpty ι := ⟨fun i ↦ hκ.false (hPm.nonempty_of_row_sum_ne_zero (ha i).ne').some⟩
    simp [relEntropy_def, relEntropyDual_def]
  obtain ⟨j⟩ := id hκ
  have : Nonempty ι := hPm.nonempty_of_col_sum_ne_zero (hb j).ne'
  set x := (K.sinkhornStep a b)^[n] u₀
  have hx : ∀ i, 0 < x i := sinkhornStep_iterate_pos hK ha hb hu₀ n
  have hrow := sinkhornStep_pos hK ha hb hx
  have hcol := sinkhornUpdate_pos (fun j i ↦ by simpa using hK i j) hb hx
  have hR := isDiagonalScaling_sinkhornPlan K a b x
  have hRpos := hR.pos hK hrow hcol
  -- the gap is the relative entropy of `P` against the Sinkhorn plan, of the same mass
  have hRsum : ∑ i, ∑ j, K.sinkhornPlan a b x i j = ∑ i, a i :=
    Finset.sum_congr rfl fun i _ ↦ sum_sinkhornPlan_apply hK a hb hx i
  rw [hR.relEntropy_sub_relEntropyDual (fun i j ↦ (hK i j).ne') hrow hcol hPm, hRsum,
    add_sub_cancel_right, ← hPm.sum_sum_eq, Finset.sum_mul, relEntropy_def]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  -- cell by cell, `P i j ≤ exp δ * R i j` bounds `log (P i j) - log (R i j)` by `δ`
  have hle := le_exp_mul_projectiveDiameter_mul_sinkhornPlan_iterate_apply hK ha hb hP hPm hu hv
    hu₀ n i j
  have hPpos := hP.pos hK hu hv i j
  have hlog : log (P i j) ≤ tanh (K.projectiveDiameter / 4) ^ (2 * n) * K.projectiveDiameter +
      log (K.sinkhornPlan a b x i j) := by
    rw [← log_exp (tanh (K.projectiveDiameter / 4) ^ (2 * n) * K.projectiveDiameter),
      ← log_mul (exp_pos _).ne' (hRpos i j).ne']
    exact log_le_log hPpos hle
  have := mul_le_mul_of_nonneg_left hlog hPpos.le
  linarith

end Matrix
