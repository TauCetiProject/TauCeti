/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithms of field norms

For a finite separable extension `L/K` and an algebraically closed normed extension field `E`
of `K`, the logarithm of the size in `E` of the field norm is the sum of the logarithmic sizes
at the `K`-embeddings of `L` into `E`. This turns bounds at individual embeddings into a bound
on the field norm. The identity also holds at zero under the convention `Real.log 0 = 0`.
-/

public section

open Finset

namespace Algebra

/-- For a finite separable extension `L/K` and an algebraically closed normed extension field
`E` of `K`, the logarithmic size in `E` of the field norm is the sum of the logarithmic sizes
under all `K`-embeddings of `L` into `E`. -/
theorem log_norm_norm_eq_sum_embeddings {K L E : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [NormedField E] [Algebra K E]
    [IsAlgClosed E] (x : L) :
    Real.log ‖algebraMap K E (norm K x)‖ = ∑ σ : L →ₐ[K] E, Real.log ‖σ x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [norm_eq_prod_embeddings K E x, norm_prod,
    Real.log_prod (f := fun σ : L →ₐ[K] E ↦ ‖σ x‖)
      (fun σ _ ↦ _root_.norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx))]

end Algebra
