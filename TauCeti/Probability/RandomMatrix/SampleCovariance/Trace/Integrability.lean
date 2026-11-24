/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SampleSecondMoment
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import TauCeti.Data.ENNReal.Inv
import TauCeti.Probability.RandomMatrix.Integrability

/-!
# Integrability of traces of sample covariance powers

Each entry of the sample covariance matrix `X Xᴴ / n` of a random rectangular matrix `X` is a
scaled sum of products of an entry of `X` and a conjugate entry. By Hölder's inequality these
entries lie in `L^(q * k)` when the entries of `X` lie in `L^(q * 2k)`, so the trace of the
`k`th power of the sample covariance matrix lies in `L^q` (`TauCeti.memLp_trace_pow`). Neither
independence nor centering is needed. The theorems assume a finite measure when `k = 0`.

## Main results

* `TauCeti.Probability.memLp_trace_pow_sampleCovariance`: with entries in `L^(q * 2k)`, the
  trace of the `k`th power of the sample covariance matrix lies in `L^q`.
* `TauCeti.Probability.integrable_trace_pow_sampleCovariance`: with entries in `L^(2k)`, it is
  integrable.
-/

public section

open MeasureTheory Matrix
open scoped ENNReal

namespace TauCeti.Probability

variable {Ω 𝕜 p n : Type*} [MeasurableSpace Ω] [RCLike 𝕜] {P : Measure Ω}
  {X : Ω → Matrix p n 𝕜} {k : ℕ}

/-- The trace of the `k`th power of the sample covariance matrix of `X` lies in `L^q` whenever all
entries of `X` lie in `L^(q * 2k)`. The measure is assumed finite when `k = 0`. Neither
independence nor centering is required. -/
theorem memLp_trace_pow_sampleCovariance [Fintype p] [Fintype n] [DecidableEq p] {q : ℝ≥0∞}
    (hP : k = 0 → IsFiniteMeasure P) (hX : ∀ a b, MemLp (fun ω ↦ X ω a b) (q * (2 * k : ℕ)) P) :
    MemLp (fun ω ↦ ((X ω).sampleCovariance ^ k).trace) q P := by
  -- Each entry is a scaled sum of products of two entries, which lie in `L^(q * k)` by Hölder.
  have hexp : ((q * (2 * k : ℕ))⁻¹ + (q * (2 * k : ℕ))⁻¹)⁻¹ = q * k := by
    have h2 : q * ((2 * k : ℕ) : ℝ≥0∞) = q * k * 2 := by
      push_cast
      ring
    rw [← two_mul, h2, ENNReal.inv_mul_inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]
  have : ENNReal.HolderTriple (q * (2 * k : ℕ)) (q * (2 * k : ℕ)) (q * k) :=
    hexp ▸ ENNReal.HolderTriple.of _ _
  refine memLp_trace_pow hP fun a b ↦ ?_
  simp only [sampleCovariance_apply]
  exact (memLp_finsetSum _ fun c _ ↦ (hX a c).mul (r := q * k) (hX b c).star).const_smul
    (1 / (Fintype.card n : ℝ))

/-- The trace of the `k`th power of the sample covariance matrix of `X` is integrable whenever all
entries of `X` lie in `L^(2k)`. The measure is assumed finite when `k = 0`. Neither independence
nor centering is required. -/
theorem integrable_trace_pow_sampleCovariance [Fintype p] [Fintype n] [DecidableEq p]
    (hP : k = 0 → IsFiniteMeasure P) (hX : ∀ a b, MemLp (fun ω ↦ X ω a b) (2 * k : ℕ) P) :
    Integrable (fun ω ↦ ((X ω).sampleCovariance ^ k).trace) P :=
  memLp_one_iff_integrable.mp (memLp_trace_pow_sampleCovariance hP (by simpa using hX))

end TauCeti.Probability
