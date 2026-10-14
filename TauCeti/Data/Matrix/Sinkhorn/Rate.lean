/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: the Tau Ceti contributors
-/
module

public import TauCeti.Data.Matrix.Sinkhorn.Basic
import TauCeti.Analysis.SpecialFunctions.Log.MulLog

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

## Main definitions

* `Matrix.relEntropyDual K a b f g`: the dual objective of the entropy minimisation with marginals
  `a` and `b` against `K`, at the potentials `f` and `g`.

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
* `Matrix.IsDiagonalScaling.relEntropy_sub_relEntropyDual`: the duality gap at the potentials of a
  diagonal scaling `R` of `K` is the relative entropy against `R` plus the mass excess of `R`.
* `Matrix.relEntropyDual_le_relEntropy` and `Matrix.IsDiagonalScaling.relEntropyDual_eq_relEntropy`:
  weak duality, and strong duality with attainment at the Sinkhorn–Knopp scaling.
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
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simpa [hilbertProjectiveDist_def] using
      mul_nonneg (pow_nonneg ht (2 * n)) (projectiveDiameter_nonneg K)
  have hKt : ∀ j i, 0 < Kᵀ j i := fun j i ↦ by simpa using hK i j
  induction n with
  | zero =>
    simpa using hilbertProjectiveDist_sinkhornUpdate_le_projectiveDiameter hKt
      (fun j ↦ (hb j).ne') (fun i ↦ (hx i).le) (fun i ↦ (hy i).le)
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', sinkhornStep_def,
      sinkhornStep_def]
    -- the column factors after `n` steps, and the two half-steps that lead to the next ones
    set c := Kᵀ.sinkhornUpdate b ((K.sinkhornStep a b)^[n] x)
    set c' := Kᵀ.sinkhornUpdate b ((K.sinkhornStep a b)^[n] y)
    have hc : ∀ j, 0 < c j := sinkhornUpdate_pos hKt hb (sinkhornStep_iterate_pos hK ha hb hx n)
    have hc' : ∀ j, 0 < c' j :=
      sinkhornUpdate_pos hKt hb (sinkhornStep_iterate_pos hK ha hb hy n)
    have hcol := hilbertProjectiveDist_sinkhornUpdate_le hKt (fun j ↦ (hb j).ne')
      (sinkhornUpdate_pos hK ha hc) (sinkhornUpdate_pos hK ha hc')
    rw [projectiveDiameter_transpose] at hcol
    calc _ ≤ tanh (K.projectiveDiameter / 4) *
          hilbertProjectiveDist (K.sinkhornUpdate a c) (K.sinkhornUpdate a c') := hcol
      _ ≤ tanh (K.projectiveDiameter / 4) * (tanh (K.projectiveDiameter / 4) *
          (tanh (K.projectiveDiameter / 4) ^ (2 * n) * K.projectiveDiameter)) :=
        mul_le_mul_of_nonneg_left ((hilbertProjectiveDist_sinkhornUpdate_le hK
          (fun i ↦ (ha i).ne') hc hc').trans (mul_le_mul_of_nonneg_left ih ht)) ht
      _ = tanh (K.projectiveDiameter / 4) ^ (2 * (n + 1)) * K.projectiveDiameter := by ring

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
  -- a positive column sum needs a row
  have : Nonempty ι := Finset.univ_nonempty_iff.1 (Finset.nonempty_of_sum_ne_zero
    ((((hasMarginals_def P a b).1 hPm).2 j).trans_ne (hb j).ne'))
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
  -- a positive row sum needs a column
  have : Nonempty κ := Finset.univ_nonempty_iff.1 (Finset.nonempty_of_sum_ne_zero
    ((((hasMarginals_def P a b).1 hPm).1 i).trans_ne (ha i).ne'))
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

/-! ### The dual objective -/

/-- The dual objective of the minimisation of `Matrix.relEntropy · K` over the nonnegative matrices
with row sums `a` and column sums `b`, at the row potentials `f` and the column potentials `g`:
`∑ i, a i * f i + ∑ j, b j * g j + ∑ i, a i - ∑ i, ∑ j, exp (f i) * K i j * exp (g j)`.

This is the Lagrangian dual of the minimisation, with the potentials shifted by one so that the
optimal potentials of a diagonal scaling `u i * K i j * v j` are `log u` and `log v`. It is at most
every primal value (`Matrix.relEntropyDual_le_relEntropy`), with equality at the minimiser
(`Matrix.IsDiagonalScaling.relEntropyDual_eq_relEntropy`). -/
noncomputable def relEntropyDual (K : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ) (f : ι → ℝ)
    (g : κ → ℝ) : ℝ :=
  ∑ i, a i * f i + ∑ j, b j * g j + ∑ i, a i - ∑ i, ∑ j, exp (f i) * K i j * exp (g j)

/-- The defining formula of the dual objective. -/
theorem relEntropyDual_def (K : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ) (f : ι → ℝ) (g : κ → ℝ) :
    K.relEntropyDual a b f g =
      ∑ i, a i * f i + ∑ j, b j * g j + ∑ i, a i - ∑ i, ∑ j, exp (f i) * K i j * exp (g j) :=
  (rfl)

/-- **The duality gap at a diagonal scaling**: if `R` is the diagonal scaling of a strictly positive
`K` by strictly positive factors `u` and `v`, then for every `Q` with row sums `a` and column sums
`b`, the gap between `relEntropy Q K` and the dual objective at the potentials `log u` and `log v`
is `relEntropy Q R` plus the excess `∑ i, ∑ j, R i j - ∑ i, a i` of the mass of `R` over that
of `Q`. -/
theorem IsDiagonalScaling.relEntropy_sub_relEntropyDual {R K : Matrix ι κ ℝ} {u : ι → ℝ}
    {v : κ → ℝ} (hR : IsDiagonalScaling R K u v) (hK : ∀ i j, 0 < K i j) (hu : ∀ i, 0 < u i)
    (hv : ∀ j, 0 < v j) {a : ι → ℝ} {b : κ → ℝ} {Q : Matrix ι κ ℝ} (hQ : HasMarginals Q a b) :
    relEntropy Q K - K.relEntropyDual a b (fun i ↦ log (u i)) (fun j ↦ log (v j)) =
      relEntropy Q R + ∑ i, ∑ j, R i j - ∑ i, a i := by
  rw [isDiagonalScaling_def] at hR
  have hlog : ∀ i j, log (R i j) = log (K i j) + (log (u i) + log (v j)) := fun i j ↦ by
    rw [hR i j, log_mul (mul_pos (hu i) (hK i j)).ne' (hv j).ne', log_mul (hu i).ne' (hK i j).ne']
    ring
  have hQK : relEntropy Q K =
      relEntropy Q R + ∑ i, ∑ j, Q i j * (log (u i) + log (v j)) := by
    simp only [relEntropy_def, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hlog]
    ring
  have hRsum : ∑ i, ∑ j, exp (log (u i)) * K i j * exp (log (v j)) = ∑ i, ∑ j, R i j := by
    simp only [exp_log (hu _), exp_log (hv _), hR]
  rw [relEntropyDual_def, hRsum, hQK, hQ.sum_sum_mul_add]
  ring

/-- **Weak duality** for the entropy minimisation: against a strictly positive `K`, the dual
objective at any potentials `f` and `g` is at most the relative entropy of every nonnegative `Q`
with row sums `a` and column sums `b`. -/
theorem relEntropyDual_le_relEntropy {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j) {a : ι → ℝ}
    {b : κ → ℝ} {Q : Matrix ι κ ℝ} (hQ0 : ∀ i j, 0 ≤ Q i j) (hQ : HasMarginals Q a b)
    (f : ι → ℝ) (g : κ → ℝ) : K.relEntropyDual a b f g ≤ relEntropy Q K := by
  -- the diagonal scaling `R` of `K` by `exp f` and `exp g`, whose potentials are `f` and `g`
  set R : Matrix ι κ ℝ := of fun i j ↦ exp (f i) * K i j * exp (g j)
  have hR : IsDiagonalScaling R K (fun i ↦ exp (f i)) (fun j ↦ exp (g j)) :=
    (isDiagonalScaling_def _ _ _ _).2 fun i j ↦ of_apply _ i j
  have hRpos := hR.pos hK (fun i ↦ exp_pos (f i)) (fun j ↦ exp_pos (g j))
  have hgap := hR.relEntropy_sub_relEntropyDual hK (fun i ↦ exp_pos (f i))
    (fun j ↦ exp_pos (g j)) hQ
  simp only [log_exp] at hgap
  -- Gibbs' inequality for unequal masses: `∑ (Q - R) ≤ relEntropy Q R`, cell by cell
  have hcell : ∑ i, ∑ j, (Q i j - R i j) ≤ relEntropy Q R := by
    rw [relEntropy_def]
    exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ by
      linarith [mul_log_sub_mul_log_ge (R i j) (Q i j) (hRpos i j) (hQ0 i j)]
  have hmass : ∑ i, ∑ j, Q i j = ∑ i, a i :=
    Finset.sum_congr rfl fun i _ ↦ ((hasMarginals_def Q a b).1 hQ).1 i
  simp only [Finset.sum_sub_distrib, hmass] at hcell
  linarith

/-- **Strong duality** for the entropy minimisation: if `P` is the diagonal scaling of a strictly
positive `K` by strictly positive factors `u` and `v`, with row sums `a` and column sums `b`, the
dual objective at the potentials `log u` and `log v` is `relEntropy P K`. With
`Matrix.relEntropyDual_le_relEntropy`, these potentials maximise the dual objective, and its maximum
is the minimum of the relative entropy. -/
theorem IsDiagonalScaling.relEntropyDual_eq_relEntropy {P K : Matrix ι κ ℝ} {u : ι → ℝ}
    {v : κ → ℝ} (hP : IsDiagonalScaling P K u v) (hK : ∀ i j, 0 < K i j) (hu : ∀ i, 0 < u i)
    (hv : ∀ j, 0 < v j) {a : ι → ℝ} {b : κ → ℝ} (hPm : HasMarginals P a b) :
    K.relEntropyDual a b (fun i ↦ log (u i)) (fun j ↦ log (v j)) = relEntropy P K := by
  have hgap := hP.relEntropy_sub_relEntropyDual hK hu hv hPm
  have hmass : ∑ i, ∑ j, P i j = ∑ i, a i :=
    Finset.sum_congr rfl fun i _ ↦ ((hasMarginals_def P a b).1 hPm).1 i
  have hself : relEntropy P P = 0 := by simp [relEntropy_def]
  linarith

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
  rw [hasMarginals_def] at hPm
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · -- a positive row sum needs a column, so there are no rows either
    have : IsEmpty ι := ⟨fun i ↦ (ha i).ne' (by simpa using (hPm.1 i).symm)⟩
    simp [relEntropy_def, relEntropyDual_def]
  obtain ⟨j⟩ := id hκ
  -- a positive column sum needs a row
  have : Nonempty ι :=
    Finset.univ_nonempty_iff.1 (Finset.nonempty_of_sum_ne_zero ((hPm.2 j).trans_ne (hb j).ne'))
  set x := (K.sinkhornStep a b)^[n] u₀
  have hx : ∀ i, 0 < x i := sinkhornStep_iterate_pos hK ha hb hu₀ n
  have hrow := sinkhornStep_pos hK ha hb hx
  have hcol := sinkhornUpdate_pos (fun j i ↦ by simpa using hK i j) hb hx
  have hR := isDiagonalScaling_sinkhornPlan K a b x
  have hRpos := hR.pos hK hrow hcol
  -- the gap is the relative entropy of `P` against the Sinkhorn plan, of the same mass
  have hRsum : ∑ i, ∑ j, K.sinkhornPlan a b x i j = ∑ i, a i :=
    Finset.sum_congr rfl fun i _ ↦ sum_sinkhornPlan_apply hK a hb hx i
  have hPsum : ∑ i, a i = ∑ i, ∑ j, P i j := Finset.sum_congr rfl fun i _ ↦ (hPm.1 i).symm
  rw [hR.relEntropy_sub_relEntropyDual hK hrow hcol ((hasMarginals_def P a b).2 hPm), hRsum,
    add_sub_cancel_right, hPsum, Finset.sum_mul, relEntropy_def]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  -- cell by cell, `P i j ≤ exp δ * R i j` bounds `log (P i j) - log (R i j)` by `δ`
  have hle := le_exp_mul_projectiveDiameter_mul_sinkhornPlan_iterate_apply hK ha hb hP
    ((hasMarginals_def P a b).2 hPm) hu hv hu₀ n i j
  have hPpos := hP.pos hK hu hv i j
  have hlog : log (P i j) ≤ tanh (K.projectiveDiameter / 4) ^ (2 * n) * K.projectiveDiameter +
      log (K.sinkhornPlan a b x i j) := by
    rw [← log_exp (tanh (K.projectiveDiameter / 4) ^ (2 * n) * K.projectiveDiameter),
      ← log_mul (exp_pos _).ne' (hRpos i j).ne']
    exact log_le_log hPpos hle
  nlinarith

end Matrix
