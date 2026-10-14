/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder

/-!
# Integrability of dual pairings

Pointwise evaluation pairs dual-valued and vector-valued functions with Hölder conjugate
exponents to give an integrable scalar function. This supplies the integrability needed to
split integrals in weak integration-by-parts formulas. The result specializes Mathlib's
bilinear Hölder estimate `ContinuousLinearMap.memLp_of_bilin` to the dual pairing.
-/

public section

open scoped ENNReal

namespace MeasureTheory.MemLp

variable {α 𝕜 V : Type*} [MeasurableSpace α] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] {μ : Measure α} {p q : ℝ≥0∞}
  [p.HolderConjugate q] {f : α → StrongDual 𝕜 V} {g : α → V}

/-- Evaluating a dual-valued `Lᵖ` function on an `Lᑫ` function is integrable when the
exponents are Hölder conjugate. -/
theorem integrable_apply (hf : MemLp f p μ) (hg : MemLp g q μ) :
    Integrable (fun x ↦ f x (g x)) μ :=
  memLp_one_iff_integrable.1
    ((ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 V)).memLp_of_bilin 1 hf hg)

end MeasureTheory.MemLp
