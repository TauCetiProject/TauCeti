/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.CharPowerSeries.DominantMinor
public import TauCeti.Analysis.Normed.Operator.RowCompact

/-!
# Exact Fredholm coefficients of a row-compact operator with dominant minors

Let `u` be a row-compact endomorphism of `C₀(ℕ, K)` over a complete ultrametric normed field,
with matrix `aᵢⱼ`, and let `d : ℕ → K` have strictly decreasing norms with `‖aᵢⱼ‖ ≤ ‖d i‖`.
If every leading principal minor of the normalised matrix `(d i)⁻¹ aᵢⱼ` has norm one, then the
coefficients of the Fredholm series `det (1 - T u) = ∑ cₙ Tⁿ` have norms

`‖cₙ‖ = ∏ i ∈ range n, ‖d i‖`
(`ContinuousLinearMap.IsRowCompact.norm_charCoeff_matrixCoeff_eq_prod`).

Here no decay of `d` is assumed: row compactness supplies it. The normalisation of the leading
minors forces `‖d n‖` to be at most the row norm `rₙ(u)`
(`ContinuousLinearMap.norm_le_rowNorm_of_norm_principalMinor_eq_one`), and the row norms of a
row-compact operator tend to zero. The coefficient formula then follows from the matrix criterion
`Matrix.norm_charCoeff_eq_prod_of_norm_principalMinor_eq_one`.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §5.
-/

public section

open Filter Finset Topology
open scoped ZeroAtInfty

namespace ContinuousLinearMap

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {u : C₀(ℕ, K) →L[K] C₀(ℕ, K)}
  {d : ℕ → K}

/-- If row `n` of the matrix of `u` is bounded, the entries of row `i` are bounded by `‖d i‖` for
`i < n`, the `d i` with `i ≤ n` are nonzero, and the normalised matrix `(d i)⁻¹ aᵢⱼ` has a leading
principal minor of norm one on `range (n + 1)`, then `‖d n‖` is at most the row norm `rₙ(u)`. -/
theorem norm_le_rowNorm_of_norm_principalMinor_eq_one {n : ℕ} {C : ℝ}
    (hn : ∀ j, ‖u.matrixCoeff n j‖ ≤ C)
    (hd : ∀ i ∈ range (n + 1), d i ≠ 0) (hb : ∀ i < n, ∀ j, ‖u.matrixCoeff i j‖ ≤ ‖d i‖)
    (hminor : ‖(Matrix.of fun i j ↦ (d i)⁻¹ * u.matrixCoeff i j).principalMinor
      (range (n + 1))‖ = 1) :
    ‖d n‖ ≤ u.rowNorm n := by
  -- Bound row `n` by its row norm and the earlier rows by the norms of `d`.
  let r : ℕ → ℝ := Function.update (fun i ↦ ‖d i‖) n (u.rowNorm n)
  have hr (i j : ℕ) (hi : i ∈ range (n + 1)) : ‖u.matrixCoeff i j‖ ≤ r i := by
    rcases eq_or_ne i n with rfl | hin
    · simpa [r] using norm_matrixCoeff_le_rowNorm_of_le hn j
    · simpa [r, hin] using hb i (by grind) j
  have hle : ‖u.matrixCoeff.principalMinor (range (n + 1))‖ ≤ ∏ i ∈ range (n + 1), r i := by
    rw [Matrix.principalMinor_def, ← prod_coe_sort]
    exact Matrix.norm_det_le_prod_of_norm_le fun i j ↦ hr i j i.2
  have hprod : ∏ i ∈ range (n + 1), r i = (∏ i ∈ range n, ‖d i‖) * u.rowNorm n := by
    rw [prod_range_succ, prod_congr rfl fun i hi ↦ Function.update_of_ne
      (mem_range.1 hi).ne _ _]
    simp [r]
  rw [Matrix.norm_principalMinor_eq_prod hd hminor, hprod, prod_range_succ] at hle
  exact le_of_mul_le_mul_left hle <| prod_pos fun i hi ↦
    norm_pos_iff.2 (hd i (mem_range.2 (Nat.lt_succ_of_lt (mem_range.1 hi))))

/-- **Exact Fredholm coefficients.** Let `u` be a row-compact endomorphism of `C₀(ℕ, K)` over a
complete ultrametric normed field, and let the norms of `d : ℕ → K` decrease strictly, with
`‖aᵢⱼ‖ ≤ ‖d i‖` for the matrix `aᵢⱼ` of `u`. If every leading principal minor of the
normalised matrix `(d i)⁻¹ aᵢⱼ` has norm one, then the `n`-th coefficient of the Fredholm
series `det (1 - T u)` has norm `∏ i ∈ range n, ‖d i‖`. -/
theorem IsRowCompact.norm_charCoeff_matrixCoeff_eq_prod [CompleteSpace K] (hu : u.IsRowCompact)
    (hdec : StrictAnti fun i ↦ ‖d i‖) (hb : ∀ i j, ‖u.matrixCoeff i j‖ ≤ ‖d i‖)
    (hminor : ∀ n, ‖(Matrix.of fun i j ↦ (d i)⁻¹ * u.matrixCoeff i j).principalMinor
      (range n)‖ = 1) (n : ℕ) :
    ‖u.matrixCoeff.charCoeff n‖ = ∏ i ∈ range n, ‖d i‖ := by
  have hd (i : ℕ) : d i ≠ 0 := norm_pos_iff.1 ((norm_nonneg _).trans_lt (hdec i.lt_succ_self))
  -- The norms of `d` are squeezed between zero and the null row norms of `u`.
  have hd₀ : Tendsto (fun i ↦ ‖d i‖) atTop (𝓝 0) := by
    obtain ⟨C, hC⟩ := (isRowCompact_iff.1 hu).1
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_)
      (Nat.cofinite_eq_atTop ▸ hu.tendsto_rowNorm)
    exact norm_le_rowNorm_of_norm_principalMinor_eq_one (hC i) (fun i _ ↦ hd i)
      (fun i _ ↦ hb i) (hminor (i + 1))
  exact Matrix.norm_charCoeff_eq_prod_of_norm_principalMinor_eq_one hdec hd₀ hb (hminor n)

end ContinuousLinearMap
