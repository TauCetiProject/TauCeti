/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Analysis.Matrix.Eigenvalues.OperatorNorm
import TauCeti.Probability.Moments.GrowingOrder

/-!
# Almost sure edge bounds from trace moments of growing order

The trace method bounds the edge of the spectrum of a random matrix through the expected trace
of a power of growing order. For a Hermitian matrix `A` and even `k`, `‖A‖ ^ k ≤ tr (A ^ k)`; for
a positive-semidefinite matrix this holds for every `k`, and `‖A‖` is its largest eigenvalue.
Hence a bound `E tr (A n ^ k n) ≤ C n ^ a c ^ k n` for every `c > L`, with orders `k n` growing
faster than `log n`, gives almost surely `limsup ‖A n‖ ≤ L`.

For Wigner matrices this is the upper half of the limit `‖Hₙ‖ → 2`, and for sample covariance
matrices it is the upper half of the limit `λ_max(XX*/n) → (1 + √y)²`. In both cases the lower
half follows from the global spectral law. The dimensions of the matrices may vary with `n` and
must be nonempty; the matrices at different sizes may have any coupling.

## Main statements

* `TauCeti.Probability.ae_forall_eventually_l2_opNorm_lt_of_integral_re_trace_pow_le`: Hermitian
  matrices and even orders.
* `TauCeti.Probability.ae_forall_eventually_eigenvalues₀_zero_lt_of_integral_re_trace_pow_le`:
  positive-semidefinite matrices, their largest eigenvalues, and orders of any parity.

## References

* Z. Bai and J. W. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*,
  2nd ed., Springer (2010), Chapter 5.
* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), §2.2.
-/

public section

open Filter MeasureTheory
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace TauCeti.Probability

variable {Ω 𝕜 : Type*} [MeasurableSpace Ω] {P : Measure Ω} [RCLike 𝕜]
  {d : ℕ → Type*} [∀ n, Fintype (d n)] [∀ n, DecidableEq (d n)] [∀ n, Nonempty (d n)]
  {k : ℕ → ℕ} {L : ℝ}

/-- **Trace method for the norm of Hermitian random matrices.** Let `A n` be random Hermitian
matrices and let the even orders `k n` grow faster than `log n`. If for every `c > L ≥ 0` there
are constants `C` and `a` with `E tr (A n ^ k n) ≤ C n ^ a c ^ k n` for all large `n`, then almost
surely the Euclidean operator norm of `A n` is eventually below every `c > L`. -/
theorem ae_forall_eventually_l2_opNorm_lt_of_integral_re_trace_pow_le
    {A : (n : ℕ) → Ω → Matrix (d n) (d n) 𝕜} (hA : ∀ n ω, (A n ω).IsHermitian)
    (hk_even : ∀ n, Even (k n)) (hk : Tendsto (fun n ↦ (k n : ℝ) / Real.log n) atTop atTop)
    (hint : ∀ n, Integrable (fun ω ↦ RCLike.re (A n ω ^ k n).trace) P) (hL : 0 ≤ L)
    (hmom : ∀ c > L, ∃ C : ℝ, ∃ a : ℕ, ∀ᶠ n : ℕ in atTop,
      ∫ ω, RCLike.re (A n ω ^ k n).trace ∂P ≤ C * n ^ a * c ^ k n) :
    ∀ᵐ ω ∂P, ∀ c > L, ∀ᶠ n in atTop, ‖A n ω‖ < c :=
  ae_forall_eventually_lt_of_integral_le_mul_pow hL
    (fun n ↦ .of_forall fun ω ↦ by
      simpa only [abs_norm] using (hA n ω).l2_opNorm_pow_le_re_trace_pow (hk_even n))
    hint hk hmom

/-- **Trace method for the largest eigenvalue of positive-semidefinite random matrices.** Let
`S n` be random positive-semidefinite matrices, such as sample covariance matrices, and let the
orders `k n` grow faster than `log n`. If for every `c > L ≥ 0` there are constants `C` and `a`
with `E tr (S n ^ k n) ≤ C n ^ a c ^ k n` for all large `n`, then almost surely the largest
eigenvalue of `S n` is eventually below every `c > L`. -/
theorem ae_forall_eventually_eigenvalues₀_zero_lt_of_integral_re_trace_pow_le
    {S : (n : ℕ) → Ω → Matrix (d n) (d n) 𝕜} (hS : ∀ n ω, (S n ω).PosSemidef)
    (hk : Tendsto (fun n ↦ (k n : ℝ) / Real.log n) atTop atTop)
    (hint : ∀ n, Integrable (fun ω ↦ RCLike.re (S n ω ^ k n).trace) P) (hL : 0 ≤ L)
    (hmom : ∀ c > L, ∃ C : ℝ, ∃ a : ℕ, ∀ᶠ n : ℕ in atTop,
      ∫ ω, RCLike.re (S n ω ^ k n).trace ∂P ≤ C * n ^ a * c ^ k n) :
    ∀ᵐ ω ∂P, ∀ c > L, ∀ᶠ n in atTop,
      (hS n ω).isHermitian.eigenvalues₀ ⟨0, Fintype.card_pos⟩ < c :=
  ae_forall_eventually_lt_of_integral_le_mul_pow hL
    (fun n ↦ .of_forall fun ω ↦ by
      rw [← (hS n ω).l2_opNorm_eq_eigenvalues₀_zero, abs_norm]
      exact (hS n ω).l2_opNorm_pow_le_re_trace_pow (k n))
    hint hk hmom

end TauCeti.Probability
