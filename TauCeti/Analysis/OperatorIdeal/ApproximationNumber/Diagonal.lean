/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.Diagonal
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax

/-!
# Approximation numbers of infinite diagonal operators

For bounded diagonal coefficients whose magnitudes decrease, the zero-based approximation
number at index `n` equals the magnitude of the `n`-th coefficient. Retaining the first `n`
coordinates attains the best rank-at-most-`n` approximation. The formula applies to all
sequence spaces `lp` with `1 ≤ p ≤ ∞`, in particular to real and complex `ℓ²`. Conversely, every
decreasing sequence of nonnegative reals is the approximation-number sequence of such a diagonal
operator (`lp.exists_singularValue_diagonalCLM_eq`).

The general compactness theorem `lp.isCompactOperator_diagonalCLM` in the multiplier module
shows that, over a locally compact scalar field, coefficients tending to zero give a
compact diagonal operator; monotonicity is not required.

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
  · exact ((diagonalCLM (p := p) d).singularValue_le_nnnorm_sub
      (rank_diagonalTruncation_range_le d n)).trans
        (nnnorm_diagonalCLM_sub_diagonalTruncation_range_le d hd n)
  · let v : Fin (n + 1) → ℓ^p(ℕ, 𝕜) := fun i ↦ lp.single p (i : ℕ) 1
    have hv : LinearIndependent 𝕜 v := by
      exact (linearIndependent_single_one (p := p) (𝕜 := 𝕜)).comp _ Fin.val_injective
    have hsupp : ∀ x ∈ Submodule.span 𝕜 (Set.range v), ∀ i, n < i → x i = 0 := by
      intro x hx i hi
      exact apply_eq_zero_of_mem_span_single (fun j : Fin (n + 1) ↦ (j : ℕ)) hx
        (by
          rintro ⟨j, hj⟩
          have hjlt := j.isLt
          simp only at hj
          omega)
    exact_mod_cast (diagonalCLM (p := p) d).le_singularValue_of_linearIndependent hv (fun x hx ↦ by
      calc
        ‖d n‖ * ‖x‖ = ‖d n • x‖ := (norm_smul _ _).symm
        _ ≤ ‖diagonalCLM d x‖ := by
          refine norm_mono hp fun i ↦ ?_
          rcases le_or_gt i n with hi | hi
          · simpa [norm_mul] using
              mul_le_mul_of_nonneg_right (hd hi) (norm_nonneg (x i))
          · simp [hsupp x hx i hi])

/-- The approximation numbers of a diagonal operator tend to zero when its decreasing
coefficient magnitudes do. -/
theorem tendsto_singularValue_diagonalCLM (d : ℓ^∞(ℕ, 𝕜))
    (hd : Antitone fun i ↦ ‖d i‖) (h0 : Tendsto (fun i ↦ ‖d i‖) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (diagonalCLM (p := p) d).singularValue n) atTop (𝓝 0) := by
  simpa only [singularValue_diagonalCLM d hd, ← NNReal.tendsto_coe, NNReal.coe_zero,
    coe_nnnorm] using h0

/-- For decreasing diagonal magnitudes, retaining the first `n` coordinates attains the
approximation number at index `n`. -/
theorem nnnorm_diagonalCLM_sub_diagonalTruncation_range (d : ℓ^∞(ℕ, 𝕜))
    (hd : Antitone fun i ↦ ‖d i‖) (n : ℕ) :
    ‖diagonalCLM (p := p) d - diagonalTruncation d (Finset.range n)‖₊ = ‖d n‖₊ := by
  refine le_antisymm ?_ ?_
  · exact nnnorm_diagonalCLM_sub_diagonalTruncation_range_le d hd n
  · rw [← singularValue_diagonalCLM (p := p) d hd n]
    exact (diagonalCLM d).singularValue_le_nnnorm_sub
      (rank_diagonalTruncation_range_le d n)

/-- Every decreasing sequence `c` of nonnegative reals is the approximation-number sequence of a
diagonal operator: the one with coefficients `c n`, which are bounded by `c 0`. -/
theorem exists_singularValue_diagonalCLM_eq {𝕜 : Type*} [RCLike 𝕜] {c : ℕ → ℝ≥0}
    (hc : Antitone c) : ∃ d : ℓ^∞(ℕ, 𝕜), (diagonalCLM (p := p) d).singularValue = c := by
  let d : ℓ^∞(ℕ, 𝕜) := ⟨fun n ↦ ((c n : ℝ) : 𝕜), memℓp_infty ⟨c 0, by
    rintro _ ⟨n, rfl⟩
    simpa using hc (Nat.zero_le n)⟩⟩
  refine ⟨d, funext fun n ↦ ?_⟩
  rw [singularValue_diagonalCLM d fun m k hmk ↦ by simpa [d] using hc hmk]
  ext
  simp [d]

end lp
