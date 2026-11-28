/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import TauCeti.LinearAlgebra.Matrix.Metzler

import TauCeti.Analysis.Normed.Algebra.Exponential

/-!
# Uniformization of a matrix exponential

Let `Q` be a real square matrix, `r ≠ 0` a real rate and `K = Matrix.uniformized Q r`, the matrix
`1 + r⁻¹ • Q`. For every real time `t`,

`exp (t • Q) = ∑ₖ e^(-r t) (r t)ᵏ / k! • Kᵏ`

(`Matrix.hasSum_uniformized_pow`, and entrywise `Matrix.hasSum_uniformized_pow_apply`). When `Q` is
a Q-matrix and `r > 0` is at least every total jump rate `-Q i i`, the matrix `K` is stochastic
(`Matrix.uniformized_mem_rowStochastic_iff`) and the weights `e^(-r t) (r t)ᵏ / k!` are the Poisson
probabilities of mean `r t`: the transition matrix `exp (t • Q)` of the continuous-time chain at a
time `t ≥ 0` is the average of the `k`-step transition matrices of the discrete chain `K` over a
Poisson number `k` of steps. This reduces questions about `exp (t • Q)`, such as its stationary
vectors and the positivity of its entries, to questions about the powers of `K`.

The identity is algebraic: `t • Q = (r t) • K - (r t) • 1`, the two terms commute, and
`exp (-(r t) • 1) = e^(-r t) • 1`, so `exp (t • Q) = e^(-r t) • exp ((r t) • K)`
(`Matrix.exp_smul_eq_smul_exp_smul_uniformized`); expanding the last exponential into its series
gives the sum. It holds for every `r ≠ 0` and every real `t`, with no sign condition on `Q`, `r` or
`t`. For `r = 0` the uniformized matrix is `1` (Lean's `0⁻¹ = 0`), the series then sums to `1`,
and the identity fails in general.

## Main results

* `Matrix.exp_smul_eq_smul_exp_smul_uniformized`: `exp (t • Q) = e^(-r t) • exp ((r t) • K)`.
* `Matrix.hasSum_uniformized_pow`: the series `∑ₖ e^(-r t) (r t)ᵏ / k! • Kᵏ` converges to
  `exp (t • Q)`.
* `Matrix.hasSum_uniformized_pow_apply`: the same identity at each entry.

## References

* D. A. Levin and Y. Peres, *Markov Chains and Mixing Times*, second edition, American
  Mathematical Society, 2017, Section 20.1, equations (20.5) and (20.6), p. 281.
-/

public section

open NormedSpace
open scoped Matrix.Norms.Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Uniformization, product form.** For a nonzero rate `r` and every real time `t`, the
exponential `exp (t • Q)` is `e^(-r t)` times the exponential of `(r t) • K`, where
`K = 1 + r⁻¹ • Q` is the uniformized matrix. -/
theorem exp_smul_eq_smul_exp_smul_uniformized (Q : Matrix n n ℝ) {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    exp (t • Q) = Real.exp (-(r * t)) • exp ((r * t) • Q.uniformized r) := by
  have hdecomp : t • Q = (r * t) • Q.uniformized r + (-(r * t)) • (1 : Matrix n n ℝ) := by
    rw [uniformized_def]
    match_scalars
    · field_simp
    · ring
  rw [hdecomp]
  exact exp_add_real_smul_one (A := Matrix n n ℝ) _ _

/-- **Uniformization.** For a real square matrix `Q`, a nonzero rate `r` and a real time `t`, the
exponential `exp (t • Q)` is the sum of the series `∑ₖ e^(-r t) (r t)ᵏ / k! • Kᵏ` of powers of the
uniformized matrix `K = 1 + r⁻¹ • Q`. For a Q-matrix, a rate `r > 0` at least every total jump
rate and a time `t ≥ 0`, `K` is stochastic and the coefficients are the Poisson probabilities of
mean `r t`. -/
theorem hasSum_uniformized_pow (Q : Matrix n n ℝ) {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    HasSum (fun k : ℕ ↦ (Real.exp (-(r * t)) * (r * t) ^ k / k.factorial) • Q.uniformized r ^ k)
      (exp (t • Q)) := by
  have hterm : (fun k : ℕ ↦
      (Real.exp (-(r * t)) * (r * t) ^ k / k.factorial) • Q.uniformized r ^ k) =
      fun k : ℕ ↦
        Real.exp (-(r * t)) • ((k.factorial⁻¹ : ℝ) • ((r * t) • Q.uniformized r) ^ k) := by
    funext k
    rw [smul_pow, smul_smul, smul_smul]
    congr 1
    ring
  rw [hterm, exp_smul_eq_smul_exp_smul_uniformized Q hr t]
  exact (exp_series_hasSum_exp' (𝕂 := ℝ) ((r * t) • Q.uniformized r)).const_smul _

/-- **Uniformization, entrywise.** For a real square matrix `Q`, a nonzero rate `r`, a real time
`t` and states `i, j`, the entry `exp (t • Q) i j` is the sum of the series
`∑ₖ e^(-r t) (r t)ᵏ / k! * (Kᵏ) i j`, where `K = 1 + r⁻¹ • Q` is the uniformized matrix. -/
theorem hasSum_uniformized_pow_apply (Q : Matrix n n ℝ) {r : ℝ} (hr : r ≠ 0) (t : ℝ) (i j : n) :
    HasSum (fun k : ℕ ↦ Real.exp (-(r * t)) * (r * t) ^ k / k.factorial * (Q.uniformized r ^ k) i j)
      (exp (t • Q) i j) :=
  Pi.hasSum.mp (Pi.hasSum.mp (hasSum_uniformized_pow Q hr t) i) j

end Matrix
