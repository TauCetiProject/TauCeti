/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import TauCeti.LinearAlgebra.Matrix.Metzler

import Mathlib.Analysis.SpecialFunctions.Exponential
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Analysis.Normed.Algebra.Exponential
import TauCeti.Analysis.Normed.Algebra.MatrixExponential

/-!
# The sign of the exponential of a Metzler matrix

For a real square matrix `B`, the exponential `exp (t • B)` has nonnegative entries for every
time `t ≥ 0` if and only if `B` is Metzler, that is, its off-diagonal entries are nonnegative
(`Matrix.exp_smul_nonneg_iff_isMetzler`). Consequently `exp (t • Q)` is a row-stochastic matrix
for every `t ≥ 0` if and only if `Q` is a Q-matrix (`Matrix.exp_smul_mem_rowStochastic_iff`):
the Q-matrices are exactly the matrices whose exponentials are the transition matrices
`P(t) = exp (t • Q)` of a continuous-time Markov chain on finitely many states.

If `B` is Metzler, then `B + c • 1` is entrywise nonnegative for a large enough `c`, every term of
its exponential series is nonnegative, and `exp B = exp (B + c • 1) * exp (-c • 1)` with
`exp (-c • 1) = e^(-c) • 1`. Conversely, an off-diagonal entry of `exp (t • B)` vanishes at `t = 0`
and has derivative `B i j` there, so it cannot stay nonnegative for small `t > 0` unless
`0 ≤ B i j`. The row sums are handled the same way: a matrix `M` with `M *ᵥ v = 0` has
`exp M *ᵥ v = v`, and conversely the derivative at `0` of the constant row sums of `exp (t • Q)` is
the row sum of `Q`.

## Main results

* `Matrix.exp_apply_nonneg_of_nonneg`: the exponential of an entrywise nonnegative real matrix is
  entrywise nonnegative.
* `Matrix.IsMetzler.exp_apply_nonneg`: the exponential of a Metzler matrix is entrywise
  nonnegative.
* `Matrix.exp_smul_nonneg_iff_isMetzler`: `exp (t • B)` is entrywise nonnegative for every
  `t ≥ 0` if and only if `B` is Metzler.
* `Matrix.IsQMatrix.exp_smul_mem_rowStochastic`: the exponential of a Q-matrix at a time `t ≥ 0`
  is row-stochastic.
* `Matrix.exp_smul_mem_rowStochastic_iff`: `exp (t • Q)` is row-stochastic for every `t ≥ 0` if
  and only if `Q` is a Q-matrix.

## References

* D. A. Levin and Y. Peres, *Markov Chains and Mixing Times*, second edition, American
  Mathematical Society, 2017, Section 20.1, equations (20.5) and (20.6), for the exponential of a
  Q-matrix as a stochastic matrix.
* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, Section 2.1.
-/

public section

open NormedSpace Filter Topology

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The exponential of an entrywise nonnegative real matrix is entrywise nonnegative. -/
theorem exp_apply_nonneg_of_nonneg {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j) (i j : n) :
    0 ≤ exp A i j :=
  (exp_series_hasSum_exp_apply A i j).nonneg fun k ↦ by
    rw [Rat.smul_def]
    exact mul_nonneg (by positivity) (pow_apply_nonneg hA k i j)

open scoped Matrix.Norms.Operator in
/-- The exponential of a Metzler matrix is entrywise nonnegative. -/
theorem IsMetzler.exp_apply_nonneg {B : Matrix n n ℝ} (hB : B.IsMetzler) (i j : n) :
    0 ≤ exp B i j := by
  obtain ⟨c, hc⟩ := isMetzler_iff_exists_add_smul_one_nonneg.mp hB
  have hcomm : Commute (B + c • 1) ((-c) • 1) := (Commute.one_right _).smul_right _
  have hexp : exp B = exp (B + c • 1) * exp ((-c) • (1 : Matrix n n ℝ)) := by
    rw [← exp_add_of_commute _ _ hcomm, add_assoc, ← add_smul, add_neg_cancel, zero_smul,
      add_zero]
  -- This typed specialization pins the operator-norm matrix ring instance.
  have hscalar : exp ((-c) • (1 : Matrix n n ℝ)) = Real.exp (-c) • 1 := exp_real_smul_one _
  rw [hexp, hscalar, mul_smul_comm, mul_one, Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg (Real.exp_pos _).le (exp_apply_nonneg_of_nonneg hc i j)

/-- **Positivity of the exponential of a Metzler matrix.** The exponential `exp (t • B)` of a
real square matrix is entrywise nonnegative at every time `t ≥ 0` if and only if `B` is
Metzler. -/
theorem exp_smul_nonneg_iff_isMetzler (B : Matrix n n ℝ) :
    (∀ t : ℝ, 0 ≤ t → ∀ i j, 0 ≤ exp (t • B) i j) ↔ B.IsMetzler := by
  refine ⟨fun h ↦ isMetzler_iff.mpr fun i j hij ↦ ?_, fun hB t ht ↦ (hB.smul ht).exp_apply_nonneg⟩
  -- The entry vanishes at `t = 0` and is nonnegative for `t ≥ 0`, so its right derivative
  -- `B i j` at `0` is nonnegative.
  refine IsLocalMinOn.hasDerivWithinAt_Ici_nonneg
    (eventually_mem_nhdsWithin.mono fun t (ht : 0 ≤ t) ↦ ?_)
    (hasDerivAt_exp_smul_apply B i j).hasDerivWithinAt
  rw [zero_smul, exp_zero, one_apply_ne hij]
  exact h t ht i j

/-- The exponential `exp (t • Q)` of a Q-matrix at a time `t ≥ 0` is a row-stochastic matrix. -/
theorem IsQMatrix.exp_smul_mem_rowStochastic {Q : Matrix n n ℝ} (hQ : Q.IsQMatrix) {t : ℝ}
    (ht : 0 ≤ t) : exp (t • Q) ∈ rowStochastic ℝ n :=
  mem_rowStochastic.mpr ⟨(hQ.isMetzler.smul ht).exp_apply_nonneg,
    exp_mulVec_eq_self_of_mulVec_eq_zero (by rw [smul_mulVec, hQ.mulVec_one_eq_zero, smul_zero])⟩

/-- **The exponential of a Q-matrix is stochastic.** The exponential `exp (t • Q)` of a real square
matrix is a row-stochastic matrix at every time `t ≥ 0` if and only if `Q` is a Q-matrix. -/
theorem exp_smul_mem_rowStochastic_iff (Q : Matrix n n ℝ) :
    (∀ t : ℝ, 0 ≤ t → exp (t • Q) ∈ rowStochastic ℝ n) ↔ Q.IsQMatrix := by
  refine ⟨fun h ↦ ⟨(exp_smul_nonneg_iff_isMetzler Q).mp fun t ht i j ↦
    nonneg_of_mem_rowStochastic (h t ht), fun i ↦ ?_⟩,
    fun hQ t ht ↦ hQ.exp_smul_mem_rowStochastic ht⟩
  -- The row sum `g t = ∑ j, exp (t • Q) i j` is constant on `[0, ∞)` and has right derivative
  -- `∑ j, Q i j` at `0`, which is therefore both nonnegative and nonpositive.
  have hd : HasDerivWithinAt (fun t : ℝ ↦ ∑ j, exp (t • Q) i j) (∑ j, Q i j) (Set.Ici 0) 0 :=
    (HasDerivAt.fun_sum fun j _ ↦ hasDerivAt_exp_smul_apply Q i j).hasDerivWithinAt
  have hconst : ∀ᶠ t in 𝓝[Set.Ici 0] (0 : ℝ),
      ∑ j, exp (t • Q) i j = ∑ j, exp ((0 : ℝ) • Q) i j :=
    eventually_mem_nhdsWithin.mono fun t (ht : 0 ≤ t) ↦ by
      rw [sum_row_of_mem_rowStochastic (h t ht), sum_row_of_mem_rowStochastic (h 0 le_rfl)]
  exact le_antisymm (IsLocalMaxOn.hasDerivWithinAt_Ici_nonpos (hconst.mono fun _ ht ↦ ht.le) hd)
    (IsLocalMinOn.hasDerivWithinAt_Ici_nonneg (hconst.mono fun _ ht ↦ ht.ge) hd)

end Matrix
