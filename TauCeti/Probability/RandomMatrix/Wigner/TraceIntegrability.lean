/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner.Basic
import TauCeti.LinearAlgebra.Matrix.Trace.Pow

/-!
# Integrability of traces of Wigner matrix powers

On a finite measure space, the trace of the `k`-th power of a Wigner matrix of size `n` is a finite
sum of products of `k` entries of the `n × n` corner. Hölder's inequality therefore puts it in
`Lᵖ` when the corner entries lie in `L^(p * k)`, and makes it integrable when they lie in `Lᵏ`.
Neither independence nor centering is needed.

## Main results

* `TauCeti.memLp_trace_pow_wignerMatrix`: on a finite measure space with corner entries in
  `L^(p * k)`, `(Hₙ ^ k).trace` lies in `Lᵖ`.
* `TauCeti.integrable_trace_pow_wignerMatrix`: on a finite measure space with corner entries in
  `Lᵏ`, `(Hₙ ^ k).trace` is integrable.
-/

public section

open MeasureTheory Matrix
open scoped ENNReal

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : StrictUpper → Ω → ℂ}
  {η : ℕ → Ω → ℝ}

/-- On a finite measure space, the trace of the `k`th power of a Wigner matrix of size `n` lies in
`Lᵖ` for every `p : ℝ≥0∞` whenever all coordinates of the `n × n` corner lie in `L^(p * k)`.
Neither independence nor centering is required, and `k = 0` is included. -/
theorem memLp_trace_pow_wignerMatrix [IsFiniteMeasure P] {p : ℝ≥0∞} {k n : ℕ}
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n → MemLp (ξ ij) (p * k) P)
    (hηp : ∀ i < n, MemLp (η i) (p * k) P) :
    MemLp (fun ω ↦ (wignerMatrix ξ η n ω ^ k).trace) p P := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [memLp_const]
  · simp_rw [trace_pow_eq_sum_prod _ hk]
    refine memLp_finsetSum Finset.univ fun w _ ↦ ?_
    have hk0 : (k : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hk
    have h := MemLp.fun_prod (s := (Finset.univ : Finset (Fin k)))
      (p := fun _ ↦ p * k)
      fun t _ ↦ memLp_wignerMatrix_apply hξp hηp (w t) (w (finRotate k t))
    have hexp : (∑ _t : Fin k, (p * k)⁻¹)⁻¹ = p := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top k)) (Or.inr hk0), mul_comm p⁻¹,
        ← mul_assoc, ENNReal.mul_inv_cancel hk0 (ENNReal.natCast_ne_top k), one_mul, inv_inv]
    rwa [hexp] at h

/-- On a finite measure space, the trace of the `k`th power of a Wigner matrix of size `n` is
integrable whenever all coordinates of the `n × n` corner lie in `Lᵏ`. Neither independence nor
centering is required, and `k = 0` is included. -/
theorem integrable_trace_pow_wignerMatrix [IsFiniteMeasure P] {k n : ℕ}
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → MemLp (ξ ij) k P)
    (hη : ∀ i < n, MemLp (η i) k P) :
    Integrable (fun ω ↦ (wignerMatrix ξ η n ω ^ k).trace) P := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · simp_rw [trace_pow_eq_sum_prod _ hk]
    exact integrable_finsetSum _ fun w _ ↦ integrable_prod_wignerMatrix_apply
      (fun ij hij ↦ by simpa using hξ ij hij) (fun i hi ↦ by simpa using hη i hi) _ _

end TauCeti
