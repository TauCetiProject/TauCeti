/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.Diagonal.Basic
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax
import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Compact

/-!
# Approximation numbers of infinite diagonal operators

For bounded diagonal coefficients whose magnitudes decrease, the zero-based approximation
number at index `n` equals the magnitude of the `n`-th coefficient. Retaining the first `n`
coordinates attains the best rank-at-most-`n` approximation. The formula applies to all
sequence spaces `lp` with `1 ≤ p ≤ ∞`, in particular to real and complex `ℓ²`. Conversely, every
antitone `ℕ → ℝ≥0` sequence defines an `ℓ^∞` sequence (`lp.ofAntitone`) whose diagonal operator
has those approximation numbers (`lp.exists_singularValue_diagonalCLM_eq`). For coefficients in
any order and on any index type, if all coefficients outside a set of at most `n` indices have
norm at most `C`, then the approximation number at index `n` is at most `C`
(`lp.singularValue_diagonalCLM_le`). Dually, if all coefficients on a set of more than `n`
indices have norm at least `c`, then it is at least `c` (`lp.le_singularValue_diagonalCLM`),
since the diagonal operator has a left inverse of norm at most `c⁻¹` on the span of the
corresponding coordinate vectors.

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

variable {ι 𝕜 : Type*} [NontriviallyNormedField 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Upper bound for a diagonal operator.** If all coefficients outside a set of at most `n`
indices have norm at most `C`, then the approximation number at index `n` is at most `C`. -/
theorem singularValue_diagonalCLM_le (d : ℓ^∞(ι, 𝕜)) {n : ℕ} {s : Finset ι} (hs : s.card ≤ n)
    {C : ℝ≥0} (hC : ∀ i ∉ s, ‖d i‖₊ ≤ C) : (diagonalCLM (p := p) d).singularValue n ≤ C := by
  classical
  refine ((diagonalCLM (p := p) d).singularValue_le_nnnorm_sub
    ((rank_diagonalTruncation_le d s).trans (by exact_mod_cast hs))).trans ?_
  exact_mod_cast norm_diagonalCLM_sub_diagonalTruncation_le d s C.coe_nonneg fun i hi ↦ hC i hi

/-- **Lower bound for a diagonal operator.** If all coefficients on a set of more than `n`
indices have norm at least `c`, then the approximation number at index `n` is at least `c`. -/
theorem le_singularValue_diagonalCLM (d : ℓ^∞(ι, 𝕜)) {n : ℕ} {s : Finset ι} (hs : n < s.card)
    {c : ℝ≥0} (hc : ∀ i ∈ s, c ≤ ‖d i‖₊) : c ≤ (diagonalCLM (p := p) d).singularValue n := by
  rcases eq_zero_or_pos c with h | h
  · exact h ▸ zero_le
  obtain ⟨M, B, hM, hB, hBDA⟩ := exists_comp_diagonalCLM_comp_subtypeL_eq_id (p := p) d s h hc
  -- The left inverse `B` makes the diagonal operator `c`-coercive on `M`.
  refine NNReal.coe_le_coe.mp <| (diagonalCLM (p := p) d).le_singularValue_of_lt_rank
    (V := M) (by simpa [hM] using hs) fun x hx ↦ ?_
  have hBx : B (diagonalCLM d x) = ⟨x, hx⟩ := by simpa using congr($hBDA ⟨x, hx⟩)
  calc
    (c : ℝ) * ‖x‖ = c * ‖B (diagonalCLM d x)‖ := by rw [hBx, ← Submodule.norm_coe]
    _ ≤ c * ‖B‖ * ‖diagonalCLM (p := p) d x‖ := by
      rw [mul_assoc]
      gcongr
      exact B.le_opNorm _
    _ ≤ ‖diagonalCLM (p := p) d x‖ := mul_le_of_le_one_left (norm_nonneg _) (by exact_mod_cast hB)

/-- The approximation numbers of a diagonal operator with decreasing coefficient magnitudes
are exactly those magnitudes. No convergence-to-zero assumption is needed. -/
@[simp]
theorem singularValue_diagonalCLM (d : ℓ^∞(ℕ, 𝕜))
    (hd : Antitone fun i ↦ ‖d i‖) (n : ℕ) :
    (diagonalCLM (p := p) d).singularValue n = ‖d n‖₊ := by
  refine le_antisymm ?_ ?_
  · exact singularValue_diagonalCLM_le d (Finset.card_range n).le fun i hi ↦
      hd (by simpa using hi)
  · exact le_singularValue_diagonalCLM d (s := Finset.range (n + 1)) (by simp) fun i hi ↦
      hd (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- The approximation numbers of a diagonal operator tend to zero when its coefficient
magnitudes do. -/
theorem tendsto_singularValue_diagonalCLM (d : ℓ^∞(ℕ, 𝕜))
    (h0 : Tendsto (fun i ↦ ‖d i‖) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (diagonalCLM (p := p) d).singularValue n) atTop (𝓝 0) := by
  exact ContinuousLinearMap.tendsto_singularValue_nhds_zero_iff.2
    ⟨_, rank_diagonalTruncation_range_le d, tendsto_diagonalTruncation_range d h0⟩

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

/-- The approximation numbers of the diagonal operator associated to `lp.ofAntitone 𝕜 hc` recover
`c`. -/
@[simp]
theorem singularValue_diagonalCLM_ofAntitone {𝕜 : Type*} [RCLike 𝕜] {c : ℕ → ℝ≥0}
    (hc : Antitone c) (n : ℕ) :
    (diagonalCLM (p := p) (ofAntitone 𝕜 hc)).singularValue n = c n := by
  rw [singularValue_diagonalCLM (ofAntitone 𝕜 hc) fun m k hmk ↦ by simpa using hc hmk]
  ext
  simp

/-- The `k`-th Ky Fan prefix gauge of the diagonal operator associated to `lp.ofAntitone 𝕜 hc` is
`∑ j < k, c j`. -/
@[simp]
theorem kyFanGauge_diagonalCLM_ofAntitone {𝕜 : Type*} [RCLike 𝕜] {c : ℕ → ℝ≥0}
    (hc : Antitone c) (k : ℕ) :
    (diagonalCLM (p := p) (ofAntitone 𝕜 hc)).kyFanGauge k = ∑ j ∈ Finset.range k, c j := by
  simp [ContinuousLinearMap.kyFanGauge_def]

/-- Every decreasing sequence `c` of nonnegative reals is the approximation-number sequence of a
diagonal operator: the one with coefficients `c n`, which are bounded by `c 0`. -/
theorem exists_singularValue_diagonalCLM_eq {𝕜 : Type*} [RCLike 𝕜] {c : ℕ → ℝ≥0}
    (hc : Antitone c) : ∃ d : ℓ^∞(ℕ, 𝕜), (diagonalCLM (p := p) d).singularValue = c :=
  ⟨ofAntitone 𝕜 hc, funext (singularValue_diagonalCLM_ofAntitone hc)⟩

end lp
