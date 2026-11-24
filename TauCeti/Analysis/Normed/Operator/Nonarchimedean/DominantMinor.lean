/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.CharPowerSeries.DominantMinor
public import TauCeti.Analysis.Normed.Operator.RowCompact
import TauCeti.Analysis.Normed.Group.Basic

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
row-compact operator tend to zero, so `‖d i‖ → 0`
(`ContinuousLinearMap.IsRowCompact.tendsto_norm_of_norm_principalMinor_eq_one`). The coefficient
formula then follows from the matrix criterion
`Matrix.norm_charCoeff_eq_prod_of_norm_principalMinor_eq_one`.

If the norm is recovered from a real additive valuation `v` by `‖x‖ = b ^ (-v x)` with `b > 1`,
the coefficients have valuations `v (cₙ) = ∑ i < n, v (d i)`
(`ContinuousLinearMap.IsRowCompact.addValuation_charCoeff_matrixCoeff_eq_sum`), the Newton polygon
of the Fredholm series is `n ↦ ∑ i < n, v (d i)`
(`ContinuousLinearMap.IsRowCompact.newtonPolygon_charPowerSeries_matrixCoeff_eq_sum`), and its
slopes are the strictly increasing valuations `v (d i)`, each of multiplicity one
(`ContinuousLinearMap.IsRowCompact.newtonSlopeMultiplicity_charPowerSeries_matrixCoeff_eq_ncard`).
For instance, with `v ϖ = 1`, the choices `d i = ϖ ^ i` and `d i = ϖ ^ (2 * i + 1)` give the
slopes `i` and `2 * i + 1`, and `d i = π ^ (2 * i + 1)` with `v π = 1 / 2` gives the
nonintegral slopes `i + 1 / 2`.

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
    exact Matrix.norm_det_le_prod_of_norm_le fun i j ↦ hr i j i.property
  have hprod : ∏ i ∈ range (n + 1), r i = (∏ i ∈ range n, ‖d i‖) * u.rowNorm n := by
    rw [prod_range_succ, prod_congr rfl fun i hi ↦ Function.update_of_ne
      (mem_range.1 hi).ne _ _]
    simp [r]
  rw [Matrix.norm_principalMinor_eq_prod hd hminor, hprod, prod_range_succ] at hle
  exact le_of_mul_le_mul_left hle <| prod_pos fun i hi ↦
    norm_pos_iff.2 (hd i (mem_range.2 (Nat.lt_succ_of_lt (mem_range.1 hi))))

/-- If the leading principal minors of the normalised matrix `(d i)⁻¹ aᵢⱼ` of a row-compact
endomorphism `u` of `C₀(ℕ, K)` all have norm one, where `d i ≠ 0` and `‖aᵢⱼ‖ ≤ ‖d i‖`, then the
norms `‖d i‖` tend to zero: they are bounded by the null row norms of `u`. -/
theorem IsRowCompact.tendsto_norm_of_norm_principalMinor_eq_one (hu : u.IsRowCompact)
    (hd : ∀ i, d i ≠ 0) (hb : ∀ i j, ‖u.matrixCoeff i j‖ ≤ ‖d i‖)
    (hminor : ∀ n, ‖(Matrix.of fun i j ↦ (d i)⁻¹ * u.matrixCoeff i j).principalMinor
      (range n)‖ = 1) :
    Tendsto (fun i ↦ ‖d i‖) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := (isRowCompact_iff.1 hu).1
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_)
    (Nat.cofinite_eq_atTop ▸ hu.tendsto_rowNorm)
  exact norm_le_rowNorm_of_norm_principalMinor_eq_one (hC i) (fun i _ ↦ hd i)
    (fun i _ ↦ hb i) (hminor (i + 1))

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
  exact Matrix.norm_charCoeff_eq_prod_of_norm_principalMinor_eq_one hdec
    (hu.tendsto_norm_of_norm_principalMinor_eq_one (TauCeti.ne_zero_of_strictAnti_norm hdec) hb
      hminor) hb (hminor n)

section Valuation

variable [CompleteSpace K] (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- **Exact Fredholm coefficient valuations.** Under the hypotheses of
`ContinuousLinearMap.IsRowCompact.norm_charCoeff_matrixCoeff_eq_prod`, if the norm is recovered
from a real additive valuation `v` by `‖x‖ = b ^ (-v x)`, the `n`-th coefficient of the Fredholm
series `det (1 - T u)` has valuation `∑ i ∈ range n, v (d i)`. -/
theorem IsRowCompact.addValuation_charCoeff_matrixCoeff_eq_sum (hu : u.IsRowCompact)
    (hdec : StrictAnti fun i ↦ ‖d i‖) (hA : ∀ i j, ‖u.matrixCoeff i j‖ ≤ ‖d i‖)
    (hminor : ∀ n, ‖(Matrix.of fun i j ↦ (d i)⁻¹ * u.matrixCoeff i j).principalMinor
      (range n)‖ = 1) (n : ℕ) :
    v (u.matrixCoeff.charCoeff n) = ∑ i ∈ range n, v (d i) :=
  Matrix.addValuation_charCoeff_eq_sum_of_norm_principalMinor_eq_one v hb hv hdec
    (hu.tendsto_norm_of_norm_principalMinor_eq_one (TauCeti.ne_zero_of_strictAnti_norm hdec) hA
      hminor) hA (hminor n)

/-- **Exact Fredholm polygon.** Under the hypotheses of
`ContinuousLinearMap.IsRowCompact.norm_charCoeff_matrixCoeff_eq_prod`, if the norm is recovered
from a real additive valuation `v` by `‖x‖ = b ^ (-v x)`, the Newton polygon of the Fredholm
series `det (1 - T u)` is `n ↦ ∑ i ∈ range n, v (d i)`. -/
theorem IsRowCompact.newtonPolygon_charPowerSeries_matrixCoeff_eq_sum (hu : u.IsRowCompact)
    (hdec : StrictAnti fun i ↦ ‖d i‖) (hA : ∀ i j, ‖u.matrixCoeff i j‖ ≤ ‖d i‖)
    (hminor : ∀ n, ‖(Matrix.of fun i j ↦ (d i)⁻¹ * u.matrixCoeff i j).principalMinor
      (range n)‖ = 1) :
    u.matrixCoeff.charPowerSeries.newtonPolygon v = fun n ↦ ∑ i ∈ range n, v (d i) :=
  Matrix.newtonPolygon_charPowerSeries_eq_sum_of_norm_principalMinor_eq_one v hb hv hdec
    (hu.tendsto_norm_of_norm_principalMinor_eq_one (TauCeti.ne_zero_of_strictAnti_norm hdec) hA
      hminor) hA hminor

/-- **Exact Fredholm slopes.** Under the hypotheses of
`ContinuousLinearMap.IsRowCompact.norm_charCoeff_matrixCoeff_eq_prod`, if the norm is recovered
from a real additive valuation `v` by `‖x‖ = b ^ (-v x)`, the multiplicity of a slope `σ` of the
Fredholm series `det (1 - T u)` is the number of indices `i` with `v (d i) = σ`. Thus the slopes
are the strictly increasing valuations `v (d i)`, each of multiplicity one. -/
theorem IsRowCompact.newtonSlopeMultiplicity_charPowerSeries_matrixCoeff_eq_ncard
    (hu : u.IsRowCompact) (hdec : StrictAnti fun i ↦ ‖d i‖)
    (hA : ∀ i j, ‖u.matrixCoeff i j‖ ≤ ‖d i‖)
    (hminor : ∀ n, ‖(Matrix.of fun i j ↦ (d i)⁻¹ * u.matrixCoeff i j).principalMinor
      (range n)‖ = 1) (σ : ℝ) :
    u.matrixCoeff.charPowerSeries.newtonSlopeMultiplicity v σ = {i | v (d i) = σ}.ncard :=
  Matrix.newtonSlopeMultiplicity_charPowerSeries_eq_ncard_of_norm_principalMinor_eq_one v hb hv
    hdec (hu.tendsto_norm_of_norm_principalMinor_eq_one (TauCeti.ne_zero_of_strictAnti_norm hdec)
      hA hminor) hA hminor σ

end Valuation

end ContinuousLinearMap
