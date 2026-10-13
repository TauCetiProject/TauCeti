/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.Diagonal
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Compact
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Approximation numbers of infinite diagonal operators

For bounded diagonal coefficients whose magnitudes decrease, the zero-based approximation
number at index `n` equals the magnitude of the `n`-th coefficient. Retaining the first `n`
coordinates attains the best rank-at-most-`n` approximation. The formula applies to all
sequence spaces `lp` with `1 ≤ p ≤ ∞`, in particular to real and complex `ℓ²`.

Over a complete locally compact scalar field, coefficients tending to zero give a compact
diagonal operator.

## References

* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), Chapter 2.
-/

public section

open scoped lp ENNReal NNReal Topology
open Filter

namespace lp

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The approximation numbers of a diagonal operator with decreasing coefficient magnitudes
are exactly those magnitudes. No convergence-to-zero assumption is needed. -/
@[simp]
theorem singularValue_diagonalCLM (d : ℓ^∞(ℕ, 𝕜))
    (hd : Antitone fun i ↦ ‖d i‖) (n : ℕ) :
    (diagonalCLM (p := p) d).singularValue n = ‖d n‖₊ := by
  have hp : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  refine le_antisymm ?_ ?_
  · refine ((diagonalCLM (p := p) d).singularValue_le_nnnorm_sub
      (by simpa using rank_diagonalTruncation_le (p := p) d (Finset.range n))).trans ?_
    exact_mod_cast norm_diagonalCLM_sub_diagonalTruncation_le (p := p) d (Finset.range n)
      (norm_nonneg _) (fun i hi ↦ hd (by simpa using hi))
  · let v : Fin (n + 1) → ℓ^p(ℕ, 𝕜) := fun i ↦ lp.single p (i : ℕ) 1
    have hv : LinearIndependent 𝕜 v := by
      apply LinearIndependent.of_comp (lpSubmodule 𝕜 (fun _ : ℕ ↦ 𝕜) p).subtype
      exact (Pi.linearIndependent_single_one ℕ 𝕜).comp _ Fin.val_injective
    have hsupp : ∀ x ∈ Submodule.span 𝕜 (Set.range v), ∀ i, n < i → x i = 0 := by
      intro x hx i hi
      have hle : Submodule.span 𝕜 (Set.range v) ≤
          LinearMap.ker (evalₗ (𝕜 := 𝕜) (fun _ : ℕ ↦ 𝕜) p i) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨j, rfl⟩
        exact lp.single_apply_ne (E := fun _ : ℕ ↦ 𝕜) p j 1 (by omega)
      exact hle hx
    exact_mod_cast (diagonalCLM (p := p) d).le_singularValue_of_linearIndependent hv (fun x hx ↦ by
      calc
        ‖d n‖ * ‖x‖ = ‖d n • x‖ := (norm_smul _ _).symm
        _ ≤ ‖diagonalCLM d x‖ := by
          refine norm_mono hp fun i ↦ ?_
          rcases le_or_gt i n with hi | hi
          · simpa [norm_mul] using
              mul_le_mul_of_nonneg_right (hd hi) (norm_nonneg (x i))
          · simp [hsupp x hx i hi])

/-- For decreasing diagonal magnitudes, retaining the first `n` coordinates attains the
approximation number at index `n`. -/
theorem nnnorm_diagonalCLM_sub_diagonalTruncation_range (d : ℓ^∞(ℕ, 𝕜))
    (hd : Antitone fun i ↦ ‖d i‖) (n : ℕ) :
    ‖diagonalCLM (p := p) d - diagonalTruncation d (Finset.range n)‖₊ = ‖d n‖₊ := by
  refine le_antisymm ?_ ?_
  · exact_mod_cast norm_diagonalCLM_sub_diagonalTruncation_le (p := p) d (Finset.range n)
      (norm_nonneg _) (fun i hi ↦ hd (by simpa using hi))
  · rw [← singularValue_diagonalCLM (p := p) d hd n]
    exact (diagonalCLM d).singularValue_le_nnnorm_sub
      (by simpa using rank_diagonalTruncation_le (p := p) d (Finset.range n))

/-- A diagonal operator with decreasing coefficient magnitudes tending to zero is compact. -/
theorem isCompactOperator_diagonalCLM [LocallyCompactSpace 𝕜] [CompleteSpace 𝕜]
    (d : ℓ^∞(ℕ, 𝕜)) (hd : Antitone fun i ↦ ‖d i‖)
    (hzero : Tendsto (fun i ↦ ‖d i‖₊) atTop (𝓝 0)) :
    IsCompactOperator (diagonalCLM (p := p) d) := by
  apply ContinuousLinearMap.isCompactOperator_of_tendsto_singularValue
  exact hzero.congr fun n ↦ (singularValue_diagonalCLM (p := p) d hd n).symm

end lp
