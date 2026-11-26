/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Slopes
import TauCeti.Algebra.Order.Floor.Semifield
import TauCeti.Analysis.Matrix.CharPowerSeries.RowHodge

/-!
# Slope counts from block row decay

Let `K` be a complete ultrametric field with a real additive valuation `v` and a base `b > 1`
such that `‖x‖ = b ^ (-v x)` for `x ≠ 0`. Consider an endomorphism `u` of the model space
`C₀(J × ℕ, K)`, for a finite nonempty type `J` with `H` elements, whose matrix decays along the
blocks `J × {k}`: for some `0 < s < 1`,

`‖u.matrixCoeff (j, k) x‖ ≤ s ^ k`.

This is the shape of a compact Hecke operator on `H` copies of the Tate algebra `K⟨z⟩` in the
monomial basis, when every row of degree `k` is divisible by `s ^ k`. Put `c = -logb b s > 0`.
Such an operator is row compact
(`ContinuousLinearMap.isRowCompact_of_norm_matrixCoeff_le_pow_snd`), and the counting of its
slopes reduces to the following steps.

* **Lower polygon.** The `n`-th coefficient of the principal-minor series has valuation at least
  `c ∑ i < n, ⌊i / H⌋` (`Matrix.norm_charCoeff_le_pow_sum_range_div`), and these heights form a
  convex sequence with slopes `c ⌊n / H⌋`: the slopes `0, …, 0, c, …, c, 2 c, …`, each repeated
  `H` times. So they lie below the Newton polygon
  (`Matrix.mul_sum_range_div_le_newtonPolygon_charPowerSeries`).
* **Slopes at most `σ`.** If the Fredholm polygon of a row-compact operator has `N` finite unit
  edges of slope at most `σ`, it lies at or below `σ N` at `N`
  (`ContinuousLinearMap.IsPrCompact.newtonPolygon_charPowerSeries_ncard_setOf_unitSlope_le_le`).
  With block decay, `c ∑ i < N, ⌊i / H⌋ ≤ N σ`
  (`ContinuousLinearMap.mul_sum_range_div_ncard_setOf_unitSlope_le_le`).
* **Explicit count.** The block sum is `H q (q - 1) / 2 + ρ q` for `N = H q + ρ`
  (`Finset.sum_range_div`), so the inequality forces `N < H (⌊2 σ / c⌋₊ + 2)`
  (`TauCeti.lt_mul_floor_add_two_of_mul_sum_range_div_le`,
  `ContinuousLinearMap.ncard_setOf_unitSlope_newtonPolygon_charPowerSeries_le_lt`). Over an
  algebraically closed `K` the edge count is the sum of the algebraic multiplicities of the
  eigenvalues of valuation at most `σ`, which is therefore bounded by the same number
  (`ContinuousLinearMap.finsum_finrank_maxGenEigenspace_lt`).

For `H = 1` and `s = |p|` over `ℚ_p` the lower polygon is `n (n - 1) / 2`, attained by
`diag (pⁱ)`, whose slopes `0, 1, 2, …` meet the count: exactly `⌊σ⌋₊ + 1` of them are at most
`σ ≥ 0`, fewer than `⌊2 σ⌋₊ + 2`. The bound controls the number of small slopes, not any single
slope.

The lower polygon, the bound at `N` and the explicit count hold in general and are proved in
`TauCeti.Analysis.Matrix.CharPowerSeries.RowHodge`,
`TauCeti.Analysis.Normed.Operator.Nonarchimedean.Slopes` and
`TauCeti.Algebra.Order.Floor.Semifield`; this file combines them under block row decay.

## Main results

* `ContinuousLinearMap.mul_sum_range_div_ncard_setOf_unitSlope_le_le`: under block row decay
  the block lower polygon at the number `N` of slopes at most `σ` is at most `σ N`.
* `ContinuousLinearMap.ncard_setOf_unitSlope_newtonPolygon_charPowerSeries_le_lt`: under block
  row decay fewer than `H (⌊2 σ / c⌋₊ + 2)` finite slopes are at most `σ`.
* `ContinuousLinearMap.finsum_finrank_maxGenEigenspace_lt`: the same bound for the total algebraic
  multiplicity of the eigenvalues of valuation at most `σ`.

## References

* K. Buzzard, *Eigenvarieties*, in *L-functions and Galois Representations*, LMS Lecture Note
  Series 320 (2007), §§11–12.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§5–7.
-/

public section

open Finset Filter TauCeti
open scoped ZeroAtInfty

namespace ContinuousLinearMap

section BlockDecay

variable {J K : Type*} [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J] [Finite J]
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (v : AddValuation K (WithTop ℝ)) {b s : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {u : C₀(J × ℕ, K) →L[K] C₀(J × ℕ, K)}

include hb hv

/-- **Slope counts under block row decay.** Let `0 < s < 1`, and let `u` be an endomorphism of
`C₀(J × ℕ, K)`, for a finite `J`, whose entries in a row indexed by `(j, k)` have norm at most
`s ^ k`. If `N` finite unit edges of the Fredholm polygon of `u` have slope at most `σ`, then
`-logb b s * ∑ i < N, ⌊i / #J⌋ ≤ N σ`. -/
theorem mul_sum_range_div_ncard_setOf_unitSlope_le_le (hs₀ : 0 < s) (hs₁ : s < 1)
    (hA : ∀ i j, ‖u.matrixCoeff i j‖ ≤ s ^ i.2) (σ : ℝ) :
    -Real.logb b s * (∑ i ∈ range {n | n ∈ finiteEdges (u.charPowerSeries.newtonPolygon v) ∧
      unitSlope (u.charPowerSeries.newtonPolygon v) n ≤ σ}.ncard, i / Nat.card J : ℕ) ≤
      {n | n ∈ finiteEdges (u.charPowerSeries.newtonPolygon v) ∧
        unitSlope (u.charPowerSeries.newtonPolygon v) n ≤ σ}.ncard * σ := by
  have hu := isRowCompact_of_norm_matrixCoeff_le_pow_snd hs₀.le hs₁ hA
  have hlow := Matrix.mul_sum_range_div_le_newtonPolygon_charPowerSeries hb hv hs₀ hs₁.le hA
  rw [← hu.charPowerSeries_eq_charPowerSeries_matrixCoeff] at hlow
  have h := (hlow _).trans <| IsPrCompact.newtonPolygon_charPowerSeries_ncard_setOf_unitSlope_le_le
    v hb hv (isPrCompact_iff_isRowCompact.2 hu : u.IsPrCompact) σ
  rw [WithTop.coe_le_coe, mul_comm σ] at h
  exact h

/-- **Explicit slope count under block row decay.** Let `0 < s < 1`, and let `u` be an
endomorphism of `C₀(J × ℕ, K)`, for a finite nonempty `J`, whose entries in a row indexed by
`(j, k)` have norm at most `s ^ k`. Fewer than `#J * (⌊2 σ / c⌋₊ + 2)` finite unit edges of the
Fredholm polygon of `u` have slope at most `σ`, where `c = -logb b s > 0`. -/
theorem ncard_setOf_unitSlope_newtonPolygon_charPowerSeries_le_lt [Nonempty J] (hs₀ : 0 < s)
    (hs₁ : s < 1) (hA : ∀ i j, ‖u.matrixCoeff i j‖ ≤ s ^ i.2) (σ : ℝ) :
    {n | n ∈ finiteEdges (u.charPowerSeries.newtonPolygon v) ∧
      unitSlope (u.charPowerSeries.newtonPolygon v) n ≤ σ}.ncard <
      Nat.card J * (⌊2 * σ / -Real.logb b s⌋₊ + 2) :=
  lt_mul_floor_add_two_of_mul_sum_range_div_le Nat.card_pos
    (neg_pos.mpr (Real.logb_neg hb hs₀ hs₁))
    (mul_sum_range_div_ncard_setOf_unitSlope_le_le v hb hv hs₀ hs₁ hA σ)

/-- **Slope summands under block row decay.** Over a complete algebraically closed ultrametric
field, let `0 < s < 1`, and let `u` be an endomorphism of `C₀(J × ℕ, K)`, for a finite nonempty
`J`, whose entries in a row indexed by `(j, k)` have norm at most `s ^ k`. The algebraic
multiplicities of the eigenvalues of `u` of valuation at most `σ` sum to less than
`#J * (⌊2 σ / c⌋₊ + 2)`, where `c = -logb b s > 0`. -/
theorem finsum_finrank_maxGenEigenspace_lt [IsAlgClosed K] [Nonempty J] (hs₀ : 0 < s)
    (hs₁ : s < 1) (hA : ∀ i j, ‖u.matrixCoeff i j‖ ≤ s ^ i.2) (σ : ℝ) :
    ∑ᶠ μ ∈ {μ : K | v μ ≤ σ}, Module.finrank K
        (Module.End.maxGenEigenspace (u : Module.End K C₀(J × ℕ, K)) μ) <
      Nat.card J * (⌊2 * σ / -Real.logb b s⌋₊ + 2) := by
  have hu : u.IsPrCompact := isPrCompact_iff_isRowCompact.2
    (isRowCompact_of_norm_matrixCoeff_le_pow_snd hs₀.le hs₁ hA)
  rw [← hu.ncard_setOf_unitSlope_newtonPolygon_charPowerSeries_le v hb hv σ]
  exact ncard_setOf_unitSlope_newtonPolygon_charPowerSeries_le_lt v hb hv hs₀ hs₁ hA σ

end BlockDecay

end ContinuousLinearMap
