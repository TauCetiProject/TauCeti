/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: the Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import TauCeti.Data.Matrix.BirkhoffContraction
public import TauCeti.Data.Matrix.Scaling

/-!
# Linear convergence of the Sinkhorn iteration

Let `K : Matrix ι κ ℝ` be a kernel with strictly positive entries, and let `a : ι → ℝ` and
`b : κ → ℝ` be strictly positive row and column sums. The Sinkhorn iteration (iterative
proportional fitting) looks for the diagonal scaling `u i * K i j * v j` of `K` with these row and
column sums by alternately enforcing them: from row factors `u` it takes the column factors
`v = b / Kᵀ u` that give the column sums `b`, and then the row factors `a / K v` that give the row
sums `a`.

Both half-steps have the form `x ↦ c / (A *ᵥ x)` for a positive matrix `A`, which is a contraction
for Hilbert's projective metric: rescaling by `c` and taking reciprocals are Hilbert isometries,
and `A` contracts by the factor `tanh (Δ(A) / 4)` by Birkhoff's theorem. A matrix and its transpose
have the same projective diameter, so a full Sinkhorn step contracts Hilbert's projective metric
between row factors by `tanh (Δ(K) / 4) ^ 2`. The factors of the Sinkhorn–Knopp scaling are a fixed
point, so the row factors of the iteration converge to them linearly in Hilbert's projective
metric, and so, one half-step later, do the column factors.

Two diagonal scalings of `K` with the same row sums differ entrywise at most by the factor
`exp d`, where `d` is the Hilbert distance between their column factors
(`Matrix.IsDiagonalScaling.apply_le_exp_hilbertProjectiveDist_mul`). The matrices produced by
the iteration therefore converge linearly, in the ratio of every entry, to the Sinkhorn–Knopp
scaling, and their column sums converge to `b` at the same rate; their row sums are exactly `a`.

Since the Hilbert distance between strictly positive vectors is the oscillation
`max (log x - log y) - min (log x - log y)`, the convergence of the factors in Hilbert's projective
metric is the convergence of the dual potentials `log u` and `log v` modulo additive constants.

## Main definitions

* `Matrix.sinkhornUpdate K a v`: the row factors `a / (K *ᵥ v)` that give the diagonal scaling of
  `K` by `v` the row sums `a`; `Kᵀ.sinkhornUpdate b u` is the column update.
* `Matrix.sinkhornStep K a b u`: one full Sinkhorn step, a column update followed by a row update.
* `Matrix.sinkhornPlan K a b u`: the diagonal scaling of `K` produced by the Sinkhorn step from
  `u`, whose row sums are `a`.

## Main results

* `Matrix.hilbertProjectiveDist_sinkhornUpdate_le` and
  `Matrix.hilbertProjectiveDist_sinkhornStep_le`: each half-step contracts Hilbert's projective
  metric by `tanh (Δ(K) / 4)`, and a full step by its square.
* `Matrix.IsDiagonalScaling.sinkhornStep_eq`: the row factors of a diagonal scaling with the
  prescribed row and column sums are a fixed point of the Sinkhorn step.
* `Matrix.IsDiagonalScaling.hilbertProjectiveDist_sinkhornStep_iterate_le` and
  `Matrix.IsDiagonalScaling.hilbertProjectiveDist_sinkhornUpdate_iterate_le`: the linear
  convergence of the row and the column factors to those of the Sinkhorn–Knopp scaling.
* `Matrix.sinkhornPlan_iterate_apply_le_exp_mul`, `Matrix.le_exp_mul_sinkhornPlan_iterate_apply`
  and the column-sum bounds `Matrix.sum_sinkhornPlan_iterate_apply_le_exp_mul` and
  `Matrix.le_exp_mul_sum_sinkhornPlan_iterate_apply`: linear convergence of the matrices and of
  their column sums.
* `Matrix.tendsto_sinkhornPlan_iterate`: the Sinkhorn iteration converges to the Sinkhorn–Knopp
  scaling from every strictly positive initial vector.

## References

* J. Franklin and J. Lorenz, *On the scaling of multidimensional matrices*, Linear Algebra Appl.
  114/115 (1989), 717--735.
* G. Peyré and M. Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11 (2019),
  Section 4.2 and Theorem 4.2.
-/

public section

open Filter Real Topology TauCeti

namespace Matrix

variable {ι κ : Type*} [Fintype κ]

/-! ### The half-step -/

/-- The row update of the Sinkhorn iteration: the row factors `a i / ∑ j, K i j * v j`, which give
the diagonal scaling `u i * K i j * v j` of `K` the row sums `a`.

The column update of the iteration is the row update of the transpose, `Kᵀ.sinkhornUpdate b u`. -/
noncomputable def sinkhornUpdate (K : Matrix ι κ ℝ) (a : ι → ℝ) (v : κ → ℝ) : ι → ℝ :=
  a / (K *ᵥ v)

/-- The defining formula of the row update. -/
theorem sinkhornUpdate_def (K : Matrix ι κ ℝ) (a : ι → ℝ) (v : κ → ℝ) :
    K.sinkhornUpdate a v = a / (K *ᵥ v) :=
  (rfl)

/-- The entries of the row update. -/
@[simp]
theorem sinkhornUpdate_apply (K : Matrix ι κ ℝ) (a : ι → ℝ) (v : κ → ℝ) (i : ι) :
    K.sinkhornUpdate a v i = a i / (K *ᵥ v) i :=
  (rfl)

/-- The row update of a strictly positive vector by a strictly positive kernel, towards strictly
positive row sums, is strictly positive. -/
theorem sinkhornUpdate_pos [Nonempty κ] {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j) {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) {v : κ → ℝ} (hv : ∀ j, 0 < v j) (i : ι) :
    0 < K.sinkhornUpdate a v i := by
  rw [sinkhornUpdate_apply, mulVec_apply_eq_sum]
  exact div_pos (ha i) (Finset.sum_pos (fun j _ ↦ mul_pos (hK i j) (hv j)) Finset.univ_nonempty)

/-- The row update enforces the row sums: the diagonal scaling of `K` by the row factors
`K.sinkhornUpdate a v` and the column factors `v` has row sum `a i` wherever `(K *ᵥ v) i ≠ 0`. -/
theorem sum_sinkhornUpdate_mul_mul (K : Matrix ι κ ℝ) (a : ι → ℝ) (v : κ → ℝ) {i : ι}
    (h : (K *ᵥ v) i ≠ 0) : ∑ j, K.sinkhornUpdate a v i * K i j * v j = a i := by
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [sinkhornUpdate_apply, ← mulVec_apply_eq_sum]
  exact div_mul_cancel₀ (a i) h

/-- The row factors of a diagonal scaling are the row update of its column factors towards its
row sums. -/
theorem IsDiagonalScaling.sinkhornUpdate_eq {P K : Matrix ι κ ℝ} {u : ι → ℝ} {v : κ → ℝ}
    (hP : IsDiagonalScaling P K u v) {a : ι → ℝ} (ha : ∀ i, ∑ j, P i j = a i)
    (hKv : ∀ i, (K *ᵥ v) i ≠ 0) : K.sinkhornUpdate a v = u := by
  rw [isDiagonalScaling_def] at hP
  funext i
  rw [sinkhornUpdate_apply, div_eq_iff (hKv i), ← ha i, mulVec_apply_eq_sum]
  simp only [hP i, mul_assoc, ← Finset.mul_sum]

/-- **Each half-step of the Sinkhorn iteration is a contraction**: the row update by a strictly
positive kernel `K` contracts Hilbert's projective metric between strictly positive column factors
by the factor `tanh (K.projectiveDiameter / 4)`. -/
theorem hilbertProjectiveDist_sinkhornUpdate_le [Finite ι] {K : Matrix ι κ ℝ}
    (hK : ∀ i j, 0 < K i j) {a : ι → ℝ} (ha : ∀ i, a i ≠ 0) {x y : κ → ℝ} (hx : ∀ j, 0 < x j)
    (hy : ∀ j, 0 < y j) :
    hilbertProjectiveDist (K.sinkhornUpdate a x) (K.sinkhornUpdate a y) ≤
      tanh (K.projectiveDiameter / 4) * hilbertProjectiveDist x y := by
  rw [sinkhornUpdate_def, sinkhornUpdate_def, div_eq_mul_inv, div_eq_mul_inv,
    hilbertProjectiveDist_mul_left ha, hilbertProjectiveDist_inv]
  exact hilbertProjectiveDist_mulVec_le hK hx hy

/-! ### The full step -/

variable [Fintype ι]

/-- One full step of the Sinkhorn iteration from the row factors `u`: the column update
`Kᵀ.sinkhornUpdate b u` towards the column sums `b`, followed by the row update towards the row
sums `a`. -/
noncomputable def sinkhornStep (K : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ) (u : ι → ℝ) : ι → ℝ :=
  K.sinkhornUpdate a (Kᵀ.sinkhornUpdate b u)

/-- The defining formula of the Sinkhorn step. -/
theorem sinkhornStep_def (K : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ) (u : ι → ℝ) :
    K.sinkhornStep a b u = K.sinkhornUpdate a (Kᵀ.sinkhornUpdate b u) :=
  (rfl)

/-- The Sinkhorn step keeps the row factors strictly positive. -/
theorem sinkhornStep_pos [Nonempty κ] {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j) {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) {b : κ → ℝ} (hb : ∀ j, 0 < b j) {u : ι → ℝ} (hu : ∀ i, 0 < u i)
    (i : ι) : 0 < K.sinkhornStep a b u i :=
  have : Nonempty ι := ⟨i⟩
  sinkhornUpdate_pos hK ha (sinkhornUpdate_pos (fun j i ↦ by simpa using hK i j) hb hu) i

/-- The iterates of the Sinkhorn step keep the row factors strictly positive. -/
theorem sinkhornStep_iterate_pos [Nonempty κ] {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j)
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) {b : κ → ℝ} (hb : ∀ j, 0 < b j) {u : ι → ℝ}
    (hu : ∀ i, 0 < u i) (n : ℕ) (i : ι) : 0 < (K.sinkhornStep a b)^[n] u i := by
  induction n generalizing i with
  | zero => exact hu i
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact sinkhornStep_pos hK ha hb ih i

/-- **A full Sinkhorn step is a contraction**: it contracts Hilbert's projective metric between
strictly positive row factors by the factor `tanh (K.projectiveDiameter / 4) ^ 2`. -/
theorem hilbertProjectiveDist_sinkhornStep_le {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j)
    {a : ι → ℝ} (ha : ∀ i, a i ≠ 0) {b : κ → ℝ} (hb : ∀ j, 0 < b j) {x y : ι → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    hilbertProjectiveDist (K.sinkhornStep a b x) (K.sinkhornStep a b y) ≤
      tanh (K.projectiveDiameter / 4) ^ 2 * hilbertProjectiveDist x y := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [hilbertProjectiveDist_def]
  have hKt : ∀ j i, 0 < Kᵀ j i := fun j i ↦ by simpa using hK i j
  have hcol := hilbertProjectiveDist_sinkhornUpdate_le hKt (fun j ↦ (hb j).ne') hx hy
  rw [projectiveDiameter_transpose] at hcol
  calc hilbertProjectiveDist (K.sinkhornStep a b x) (K.sinkhornStep a b y)
      ≤ tanh (K.projectiveDiameter / 4) *
          hilbertProjectiveDist (Kᵀ.sinkhornUpdate b x) (Kᵀ.sinkhornUpdate b y) :=
        hilbertProjectiveDist_sinkhornUpdate_le hK ha (sinkhornUpdate_pos hKt hb hx)
          (sinkhornUpdate_pos hKt hb hy)
    _ ≤ tanh (K.projectiveDiameter / 4) *
          (tanh (K.projectiveDiameter / 4) * hilbertProjectiveDist x y) :=
        mul_le_mul_of_nonneg_left hcol (tanh_projectiveDiameter_div_four_nonneg K)
    _ = tanh (K.projectiveDiameter / 4) ^ 2 * hilbertProjectiveDist x y := by ring

/-- The `n`-th iterates of the Sinkhorn step from two strictly positive vectors approach each other
in Hilbert's projective metric at the linear rate `tanh (K.projectiveDiameter / 4) ^ (2 * n)`. -/
theorem hilbertProjectiveDist_sinkhornStep_iterate_le {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j)
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) {b : κ → ℝ} (hb : ∀ j, 0 < b j) {x y : ι → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (n : ℕ) :
    hilbertProjectiveDist ((K.sinkhornStep a b)^[n] x) ((K.sinkhornStep a b)^[n] y) ≤
      tanh (K.projectiveDiameter / 4) ^ (2 * n) * hilbertProjectiveDist x y := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · -- without columns every Sinkhorn step lands on the same vector `a / 0`
    cases n with
    | zero => simp
    | succ n =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', sinkhornStep_def,
        sinkhornStep_def, Subsingleton.elim (Kᵀ.sinkhornUpdate b _) (Kᵀ.sinkhornUpdate b _),
        hilbertProjectiveDist_self]
      exact mul_nonneg (pow_nonneg (tanh_projectiveDiameter_div_four_nonneg K) _)
        (hilbertProjectiveDist_nonneg x y)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    calc _ ≤ tanh (K.projectiveDiameter / 4) ^ 2 *
          hilbertProjectiveDist ((K.sinkhornStep a b)^[n] x) ((K.sinkhornStep a b)^[n] y) :=
        hilbertProjectiveDist_sinkhornStep_le hK (fun i ↦ (ha i).ne') hb
          (sinkhornStep_iterate_pos hK ha hb hx n) (sinkhornStep_iterate_pos hK ha hb hy n)
      _ ≤ tanh (K.projectiveDiameter / 4) ^ 2 *
          (tanh (K.projectiveDiameter / 4) ^ (2 * n) * hilbertProjectiveDist x y) :=
        mul_le_mul_of_nonneg_left ih (pow_nonneg (tanh_projectiveDiameter_div_four_nonneg K) 2)
      _ = _ := by ring

/-! ### The fixed point -/

omit [Fintype κ] in
/-- The column factors of a diagonal scaling of a strictly positive kernel with column sums `b` and
strictly positive row factors are the column update of its row factors. -/
theorem IsDiagonalScaling.sinkhornUpdate_transpose_eq [Nonempty ι] {P K : Matrix ι κ ℝ}
    {u : ι → ℝ} {v : κ → ℝ} (hP : IsDiagonalScaling P K u v) {b : κ → ℝ}
    (hb : ∀ j, ∑ i, P i j = b j) (hK : ∀ i j, 0 < K i j) (hu : ∀ i, 0 < u i) :
    Kᵀ.sinkhornUpdate b u = v :=
  hP.transpose.sinkhornUpdate_eq (fun j ↦ by simpa using hb j) fun j ↦ by
    simpa [mulVec_apply_eq_sum] using
      (Finset.sum_pos (fun i _ ↦ mul_pos (hK i j) (hu i)) Finset.univ_nonempty).ne'

/-- The row factors of a diagonal scaling of a strictly positive kernel by strictly positive
factors, with row sums `a` and column sums `b`, are a fixed point of the Sinkhorn step. -/
theorem IsDiagonalScaling.sinkhornStep_eq [Nonempty κ] {P K : Matrix ι κ ℝ} {u : ι → ℝ}
    {v : κ → ℝ} (hP : IsDiagonalScaling P K u v) {a : ι → ℝ} {b : κ → ℝ}
    (hPm : HasMarginals P a b) (hK : ∀ i j, 0 < K i j) (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) :
    K.sinkhornStep a b u = u := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Subsingleton.elim _ _
  rw [hasMarginals_def] at hPm
  rw [sinkhornStep_def, hP.sinkhornUpdate_transpose_eq hPm.2 hK hu]
  refine hP.sinkhornUpdate_eq hPm.1 fun i ↦ ?_
  rw [mulVec_apply_eq_sum]
  exact (Finset.sum_pos (fun j _ ↦ mul_pos (hK i j) (hv j)) Finset.univ_nonempty).ne'

/-- **Linear convergence of the row factors** of the Sinkhorn iteration: if `u` and `v` are
strictly positive factors of a diagonal scaling of `K` with row sums `a` and column sums `b`, then
the `n`-th iterate of the Sinkhorn step from a strictly positive `u₀` is within
`tanh (K.projectiveDiameter / 4) ^ (2 * n)` times the initial distance of `u` in Hilbert's
projective metric. -/
theorem IsDiagonalScaling.hilbertProjectiveDist_sinkhornStep_iterate_le {P K : Matrix ι κ ℝ}
    {u : ι → ℝ} {v : κ → ℝ} (hP : IsDiagonalScaling P K u v) {a : ι → ℝ} {b : κ → ℝ}
    (hPm : HasMarginals P a b) (hK : ∀ i j, 0 < K i j) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) {u₀ : ι → ℝ} (hu₀ : ∀ i, 0 < u₀ i) (n : ℕ) :
    hilbertProjectiveDist ((K.sinkhornStep a b)^[n] u₀) u ≤
      tanh (K.projectiveDiameter / 4) ^ (2 * n) * hilbertProjectiveDist u₀ u := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
  · simp [hilbertProjectiveDist_def]
  -- a positive row sum needs a column
  have : Nonempty κ := Finset.univ_nonempty_iff.1 (Finset.nonempty_of_sum_ne_zero
    ((((hasMarginals_def P a b).1 hPm).1 i).trans_ne (ha i).ne'))
  have h := Matrix.hilbertProjectiveDist_sinkhornStep_iterate_le hK ha hb hu₀ hu n
  rwa [Function.iterate_fixed (hP.sinkhornStep_eq hPm hK hu hv)] at h

/-- **Linear convergence of the column factors** of the Sinkhorn iteration: in the setting of
`Matrix.IsDiagonalScaling.hilbertProjectiveDist_sinkhornStep_iterate_le`, the column update of the
`n`-th iterate is within `tanh (K.projectiveDiameter / 4) ^ (2 * n + 1)` times
`hilbertProjectiveDist u₀ u` of `v` in Hilbert's projective metric, that is the rate times the
initial distance of the row factors `u₀` from `u`. -/
theorem IsDiagonalScaling.hilbertProjectiveDist_sinkhornUpdate_iterate_le {P K : Matrix ι κ ℝ}
    {u : ι → ℝ} {v : κ → ℝ} (hP : IsDiagonalScaling P K u v) {a : ι → ℝ} {b : κ → ℝ}
    (hPm : HasMarginals P a b) (hK : ∀ i j, 0 < K i j) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) {u₀ : ι → ℝ} (hu₀ : ∀ i, 0 < u₀ i) (n : ℕ) :
    hilbertProjectiveDist (Kᵀ.sinkhornUpdate b ((K.sinkhornStep a b)^[n] u₀)) v ≤
      tanh (K.projectiveDiameter / 4) ^ (2 * n + 1) * hilbertProjectiveDist u₀ u := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · exact (by simp [hilbertProjectiveDist_def] : _ = (0 : ℝ)).trans_le
      (mul_nonneg (pow_nonneg (tanh_projectiveDiameter_div_four_nonneg K) _)
        (hilbertProjectiveDist_nonneg u₀ u))
  obtain ⟨j⟩ := id hκ
  rw [hasMarginals_def] at hPm
  -- a positive column sum needs a row
  have : Nonempty ι :=
    Finset.univ_nonempty_iff.1 (Finset.nonempty_of_sum_ne_zero ((hPm.2 j).trans_ne (hb j).ne'))
  have hKt : ∀ j i, 0 < Kᵀ j i := fun j i ↦ by simpa using hK i j
  have hcol := hilbertProjectiveDist_sinkhornUpdate_le hKt (fun j ↦ (hb j).ne')
    (sinkhornStep_iterate_pos hK ha hb hu₀ n) hu
  rw [projectiveDiameter_transpose, hP.sinkhornUpdate_transpose_eq hPm.2 hK hu] at hcol
  calc _ ≤ _ := hcol
    _ ≤ tanh (K.projectiveDiameter / 4) *
          (tanh (K.projectiveDiameter / 4) ^ (2 * n) * hilbertProjectiveDist u₀ u) :=
        mul_le_mul_of_nonneg_left (hP.hilbertProjectiveDist_sinkhornStep_iterate_le
          ((hasMarginals_def P a b).2 hPm) hK ha hb hu hv hu₀ n)
          (tanh_projectiveDiameter_div_four_nonneg K)
    _ = _ := by ring

/-! ### Convergence of the scaled matrices -/

/-- The matrix produced by the Sinkhorn step from the row factors `u`: the diagonal scaling of `K`
by the column factors `Kᵀ.sinkhornUpdate b u` and the row factors `K.sinkhornStep a b u` obtained
from them. Its row sums are `a` (`Matrix.sum_sinkhornPlan_apply`), and along the iteration its
column sums converge to `b`. -/
noncomputable def sinkhornPlan (K : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ) (u : ι → ℝ) :
    Matrix ι κ ℝ :=
  of fun i j ↦ K.sinkhornStep a b u i * K i j * Kᵀ.sinkhornUpdate b u j

/-- The entries of the Sinkhorn plan. -/
@[simp]
theorem sinkhornPlan_apply (K : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ) (u : ι → ℝ) (i : ι)
    (j : κ) :
    K.sinkhornPlan a b u i j = K.sinkhornStep a b u i * K i j * Kᵀ.sinkhornUpdate b u j :=
  (rfl)

/-- The Sinkhorn plan is the diagonal scaling of `K` by the factors of the Sinkhorn step. -/
theorem isDiagonalScaling_sinkhornPlan (K : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (u : ι → ℝ) :
    IsDiagonalScaling (K.sinkhornPlan a b u) K (K.sinkhornStep a b u) (Kᵀ.sinkhornUpdate b u) :=
  (isDiagonalScaling_def _ _ _ _).2 (sinkhornPlan_apply K a b u)

/-- The Sinkhorn plan from strictly positive row factors has row sums `a`. -/
theorem sum_sinkhornPlan_apply [Nonempty κ] {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j)
    (a : ι → ℝ) {b : κ → ℝ} (hb : ∀ j, 0 < b j) {u : ι → ℝ} (hu : ∀ i, 0 < u i) (i : ι) :
    ∑ j, K.sinkhornPlan a b u i j = a i := by
  have : Nonempty ι := ⟨i⟩
  simp only [sinkhornPlan_apply, sinkhornStep_def]
  refine sum_sinkhornUpdate_mul_mul K a _ ?_
  rw [mulVec_apply_eq_sum]
  exact (Finset.sum_pos (fun j _ ↦ mul_pos (hK i j)
    (sinkhornUpdate_pos (fun j i ↦ by simpa using hK i j) hb hu j)) Finset.univ_nonempty).ne'

/-- **Linear convergence of the Sinkhorn iteration**, upper bound: if `P` is the diagonal scaling
of `K` by strictly positive factors `u` and `v` with row sums `a` and column sums `b`, then every
entry of the Sinkhorn plan after `n` steps from a strictly positive `u₀` is at most
`exp (tanh (K.projectiveDiameter / 4) ^ (2 * n + 1) * hilbertProjectiveDist u₀ u)` times the
corresponding entry of `P`. -/
theorem sinkhornPlan_iterate_apply_le_exp_mul {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j)
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) {b : κ → ℝ} (hb : ∀ j, 0 < b j) {P : Matrix ι κ ℝ}
    {u : ι → ℝ} {v : κ → ℝ} (hP : IsDiagonalScaling P K u v) (hPm : HasMarginals P a b)
    (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) {u₀ : ι → ℝ} (hu₀ : ∀ i, 0 < u₀ i) (n : ℕ) (i : ι)
    (j : κ) :
    K.sinkhornPlan a b ((K.sinkhornStep a b)^[n] u₀) i j ≤
      exp (tanh (K.projectiveDiameter / 4) ^ (2 * n + 1) * hilbertProjectiveDist u₀ u) *
        P i j := by
  have : Nonempty ι := ⟨i⟩
  have : Nonempty κ := ⟨j⟩
  have hun := sinkhornStep_iterate_pos hK ha hb hu₀ n
  refine ((isDiagonalScaling_sinkhornPlan K a b _).apply_le_exp_hilbertProjectiveDist_mul hP (hK i)
    (sinkhornStep_pos hK ha hb hun i).le
    (sinkhornUpdate_pos (fun j i ↦ by simpa using hK i j) hb hun) hv
    ((sum_sinkhornPlan_apply hK a hb hun i).trans (((hasMarginals_def P a b).1 hPm).1 i).symm)
    j).trans ?_
  exact mul_le_mul_of_nonneg_right
    (exp_le_exp.2 (hP.hilbertProjectiveDist_sinkhornUpdate_iterate_le hPm hK ha hb hu hv hu₀ n))
    (hP.pos hK hu hv i j).le

/-- **Linear convergence of the Sinkhorn iteration**, lower bound: in the setting of
`Matrix.sinkhornPlan_iterate_apply_le_exp_mul`, every entry of `P` is at most
`exp (tanh (K.projectiveDiameter / 4) ^ (2 * n + 1) * hilbertProjectiveDist u₀ u)` times the
corresponding entry of the Sinkhorn plan after `n` steps. -/
theorem le_exp_mul_sinkhornPlan_iterate_apply {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j)
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) {b : κ → ℝ} (hb : ∀ j, 0 < b j) {P : Matrix ι κ ℝ}
    {u : ι → ℝ} {v : κ → ℝ} (hP : IsDiagonalScaling P K u v) (hPm : HasMarginals P a b)
    (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) {u₀ : ι → ℝ} (hu₀ : ∀ i, 0 < u₀ i) (n : ℕ) (i : ι)
    (j : κ) :
    P i j ≤
      exp (tanh (K.projectiveDiameter / 4) ^ (2 * n + 1) * hilbertProjectiveDist u₀ u) *
        K.sinkhornPlan a b ((K.sinkhornStep a b)^[n] u₀) i j := by
  have : Nonempty ι := ⟨i⟩
  have : Nonempty κ := ⟨j⟩
  have hun := sinkhornStep_iterate_pos hK ha hb hu₀ n
  have hw := sinkhornUpdate_pos (fun j i ↦ by simpa using hK i j) hb hun
  refine (hP.apply_le_exp_hilbertProjectiveDist_mul (isDiagonalScaling_sinkhornPlan K a b _) (hK i)
    (hu i).le hv hw ((((hasMarginals_def P a b).1 hPm).1 i).trans
      (sum_sinkhornPlan_apply hK a hb hun i).symm)
    j).trans ?_
  rw [hilbertProjectiveDist_comm]
  exact mul_le_mul_of_nonneg_right
    (exp_le_exp.2 (hP.hilbertProjectiveDist_sinkhornUpdate_iterate_le hPm hK ha hb hu hv hu₀ n))
    ((isDiagonalScaling_sinkhornPlan K a b _).pos hK (sinkhornStep_pos hK ha hb hun) hw i j).le

/-- The column sums of the Sinkhorn plan after `n` steps are at most
`exp (tanh (K.projectiveDiameter / 4) ^ (2 * n + 1) * hilbertProjectiveDist u₀ u)` times the
prescribed column sums `b`. -/
theorem sum_sinkhornPlan_iterate_apply_le_exp_mul {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j)
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) {b : κ → ℝ} (hb : ∀ j, 0 < b j) {P : Matrix ι κ ℝ}
    {u : ι → ℝ} {v : κ → ℝ} (hP : IsDiagonalScaling P K u v) (hPm : HasMarginals P a b)
    (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) {u₀ : ι → ℝ} (hu₀ : ∀ i, 0 < u₀ i) (n : ℕ)
    (j : κ) :
    ∑ i, K.sinkhornPlan a b ((K.sinkhornStep a b)^[n] u₀) i j ≤
      exp (tanh (K.projectiveDiameter / 4) ^ (2 * n + 1) * hilbertProjectiveDist u₀ u) * b j := by
  rw [← ((hasMarginals_def P a b).1 hPm).2 j, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦
    sinkhornPlan_iterate_apply_le_exp_mul hK ha hb hP hPm hu hv hu₀ n i j

/-- The prescribed column sums `b` are at most
`exp (tanh (K.projectiveDiameter / 4) ^ (2 * n + 1) * hilbertProjectiveDist u₀ u)` times the
column sums of the Sinkhorn plan after `n` steps. -/
theorem le_exp_mul_sum_sinkhornPlan_iterate_apply {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j)
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) {b : κ → ℝ} (hb : ∀ j, 0 < b j) {P : Matrix ι κ ℝ}
    {u : ι → ℝ} {v : κ → ℝ} (hP : IsDiagonalScaling P K u v) (hPm : HasMarginals P a b)
    (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) {u₀ : ι → ℝ} (hu₀ : ∀ i, 0 < u₀ i) (n : ℕ)
    (j : κ) :
    b j ≤ exp (tanh (K.projectiveDiameter / 4) ^ (2 * n + 1) * hilbertProjectiveDist u₀ u) *
      ∑ i, K.sinkhornPlan a b ((K.sinkhornStep a b)^[n] u₀) i j := by
  rw [← ((hasMarginals_def P a b).1 hPm).2 j, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦
    le_exp_mul_sinkhornPlan_iterate_apply hK ha hb hP hPm hu hv hu₀ n i j

/-- **Convergence of the Sinkhorn iteration**: for a strictly positive kernel `K`, if `P` is the
diagonal scaling of `K` by strictly positive factors with row sums `a > 0` and column sums `b > 0`
(the Sinkhorn–Knopp scaling, which exists by `Matrix.exists_sinkhorn_scaling` when `a` and `b` have
the same total mass), then the Sinkhorn plans along the iteration from any strictly positive
initial row factors converge to `P`. -/
theorem tendsto_sinkhornPlan_iterate {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j)
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) {b : κ → ℝ} (hb : ∀ j, 0 < b j) {P : Matrix ι κ ℝ}
    {u : ι → ℝ} {v : κ → ℝ} (hP : IsDiagonalScaling P K u v) (hPm : HasMarginals P a b)
    (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) {u₀ : ι → ℝ} (hu₀ : ∀ i, 0 < u₀ i) :
    Tendsto (fun n ↦ K.sinkhornPlan a b ((K.sinkhornStep a b)^[n] u₀)) atTop (𝓝 P) := by
  -- the rate `δ n = t ^ (2 * n + 1) * d`, with `t = tanh (K.projectiveDiameter / 4) < 1`
  have ht := tanh_projectiveDiameter_div_four_nonneg K
  have hδ : Tendsto (fun n : ℕ ↦ tanh (K.projectiveDiameter / 4) ^ (2 * n + 1) *
      hilbertProjectiveDist u₀ u) atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg _)
      (pow_lt_one₀ ht (tanh_lt_one _) two_ne_zero)).const_mul
        (tanh (K.projectiveDiameter / 4))).mul_const (hilbertProjectiveDist u₀ u)
    rw [mul_zero, zero_mul] at h
    exact h.congr fun n ↦ by ring
  refine tendsto_pi_nhds.2 fun i ↦ tendsto_pi_nhds.2 fun j ↦ ?_
  have hup := ((continuous_exp.tendsto' 0 1 exp_zero).comp hδ).mul_const (P i j)
  have hlow := ((continuous_exp.tendsto' (-0) 1 (by simp)).comp hδ.neg).mul_const (P i j)
  rw [one_mul] at hup hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun n ↦ ?_)
    fun n ↦ sinkhornPlan_iterate_apply_le_exp_mul hK ha hb hP hPm hu hv hu₀ n i j
  have h := le_exp_mul_sinkhornPlan_iterate_apply hK ha hb hP hPm hu hv hu₀ n i j
  simp only [Function.comp_apply, exp_neg, inv_mul_eq_div]
  rw [div_le_iff₀ (exp_pos _), mul_comm]
  exact h

end Matrix
