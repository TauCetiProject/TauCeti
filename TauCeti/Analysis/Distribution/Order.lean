/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Distribution

/-!
# Local finite order of distributions

A distribution has finite order on each compact set: for a compact `K ⊆ Ω` its value on a test
function supported in `K` is bounded by a constant times a bound on the derivatives of the test
function up to some fixed order `N`.

## Main declarations

* `Distribution.exists_norm_apply_le`: a distribution has finite order on each compact set.

## References

* [L. Hörmander, *The Analysis of Linear Partial Differential Operators I*][hormander2003], §2.1.
-/

public section

open TopologicalSpace TestFunction
open scoped Distributions ContDiff

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E}

/-- **A distribution has finite order on each compact set.** For a compact `K ⊆ Ω` there are an
order `N` and a constant `C` such that `‖T φ‖ ≤ C * M` for every test function `φ` supported in
`K` whose derivatives of order at most `N` are all bounded by `M`. -/
theorem exists_norm_apply_le (T : 𝓓'(Ω, F)) {K : Compacts E} (hK : (K : Set E) ⊆ Ω) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ K → ∀ M, 0 ≤ M →
      (∀ i ≤ N, ∀ x, ‖iteratedFDeriv ℝ i φ x‖ ≤ M) → ‖T φ‖ ≤ C * M := by
  let T' : 𝓓_{K}(E, ℝ) →L[ℝ] F := (T : 𝓓(Ω, ℝ) →L[ℝ] F).comp (ofSupportedInCLM ℝ hK)
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℝ E ℝ ⊤ K) ((normSeminorm ℝ F).comp T'.toLinearMap)
    (continuous_norm.comp T'.continuous)
  refine ⟨s.sup id, C, C.2, fun φ hφ M hM hφM => ?_⟩
  let ψ : 𝓓_{K}(E, ℝ) := .of_support_subset φ.contDiff ((subset_tsupport _).trans hφ)
  have hψ : ofSupportedInCLM ℝ hK ψ = φ := by
    ext y
    simp [ψ]
  calc ‖T φ‖ = ‖T (ofSupportedInCLM ℝ hK ψ)‖ := by rw [hψ]
    -- `T'` is by definition `T` precomposed with the inclusion `ofSupportedInCLM ℝ hK`.
    _ = (normSeminorm ℝ F).comp T'.toLinearMap ψ := rfl
    _ ≤ (C • s.sup (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) ψ := hC ψ
    _ ≤ C * M := by
      rw [smul_apply, NNReal.smul_def, smul_eq_mul]
      gcongr
      refine Seminorm.finset_sup_apply_le hM fun i hi => ?_
      rw [ContDiffMapSupportedIn.seminorm_top_le_iff ℝ hM]
      exact fun x _ => hφM i (Finset.le_sup (f := id) hi) x

end Distribution
