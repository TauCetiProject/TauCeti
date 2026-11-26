/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import TauCeti.Analysis.InnerProductSpace.Covector

/-!
# Locally integrable covector fields

Evaluating a locally integrable Gram-normed covector field on a fixed tuple gives a locally
integrable scalar coefficient. This lets scalar test functions act on individual coefficients.
-/

public section

open TauCeti

namespace MeasureTheory

variable {X V : Type*} [TopologicalSpace X] [MeasurableSpace X] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {k : ℕ} {f : X → Covector V k}
  {s : Set X} {μ : Measure X}

/-- The coefficients obtained by evaluating a locally integrable covector field on a fixed
tuple are locally integrable on the same set. -/
theorem LocallyIntegrableOn.covector_coefficient (hf : LocallyIntegrableOn f s μ)
    (v : Fin k → V) : LocallyIntegrableOn (fun x ↦ (f x).ofCovector v) s μ := by
  simpa only [Function.comp_def, Covector.coefficientCLM_apply] using
    (Covector.coefficientCLM v).locallyIntegrableOn_comp hf

end MeasureTheory
