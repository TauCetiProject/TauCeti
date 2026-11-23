/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner.Basic
import TauCeti.Probability.RandomMatrix.Integrability

/-!
# Integrability of traces of Wigner matrix powers

The trace of the `k`-th power of a Wigner matrix of size `n` lies in `Lᵖ` when the corner entries
lie in `L^(p * k)`, and is integrable when they lie in `Lᵏ`. These are the Wigner cases of
`TauCeti.memLp_trace_pow`, which needs only entrywise moments: neither independence nor centering
is needed. The measure is assumed finite when `k = 0`.

## Main results

* `TauCeti.memLp_trace_pow_wignerMatrix`: with corner entries in `L^(p * k)`, `(Hₙ ^ k).trace`
  lies in `Lᵖ`.
* `TauCeti.integrable_trace_pow_wignerMatrix`: with corner entries in `Lᵏ`, `(Hₙ ^ k).trace` is
  integrable.
-/

public section

open MeasureTheory Matrix
open scoped ENNReal

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : StrictUpper → Ω → ℂ}
  {η : ℕ → Ω → ℝ}

/-- The trace of the `k`th power of a Wigner matrix of size `n` lies in `Lᵖ` for every
`p : ℝ≥0∞` whenever all coordinates of the `n × n` corner lie in `L^(p * k)`. The measure is
assumed finite when `k = 0`. Neither independence nor centering is required. -/
theorem memLp_trace_pow_wignerMatrix {p : ℝ≥0∞} {k n : ℕ} (hP : k = 0 → IsFiniteMeasure P)
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n → MemLp (ξ ij) (p * k) P)
    (hηp : ∀ i < n, MemLp (η i) (p * k) P) :
    MemLp (fun ω ↦ (wignerMatrix ξ η n ω ^ k).trace) p P :=
  memLp_trace_pow hP (memLp_wignerMatrix_apply hξp hηp)

/-- The trace of the `k`th power of a Wigner matrix of size `n` is integrable whenever all
coordinates of the `n × n` corner lie in `Lᵏ`. The measure is assumed finite when `k = 0`.
Neither independence nor centering is required. -/
theorem integrable_trace_pow_wignerMatrix {k n : ℕ} (hP : k = 0 → IsFiniteMeasure P)
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → MemLp (ξ ij) k P)
    (hη : ∀ i < n, MemLp (η i) k P) :
    Integrable (fun ω ↦ (wignerMatrix ξ η n ω ^ k).trace) P :=
  memLp_one_iff_integrable.mp <| memLp_trace_pow_wignerMatrix hP
    (fun ij hij ↦ by simpa only [one_mul] using hξ ij hij)
    (fun i hi ↦ by simpa only [one_mul] using hη i hi)

end TauCeti
