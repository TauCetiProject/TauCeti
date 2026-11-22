/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Slopes
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Analysis.Matrix.CharPowerSeries.Weight

/-!
# Slope counts from block row decay

Let `K` be a complete ultrametric field with a real additive valuation `v` and a base `b > 1`
such that `‖x‖ = b ^ (-v x)` for `x ≠ 0`. Consider an endomorphism `u` of the model space
`C₀(J × ℕ, K)`, for a finite nonempty type `J` with `H` elements, whose matrix decays along the
blocks `J × {k}`: for some `0 < s < 1`,

`‖u.matrixCoeff (j, k) x‖ ≤ s ^ k`.

This is the shape of a compact Hecke operator on `H` copies of the Tate algebra `K⟨z⟩` in the
monomial basis, when every row of degree `k` is divisible by `s ^ k`. Put `c = -logb b s > 0`.
Such an operator is row compact, and the counting of its slopes reduces to the following steps.

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

## Main results

* `Matrix.mul_sum_range_div_le_newtonPolygon_charPowerSeries`: block row decay bounds the Newton
  polygon of the principal-minor series below.
* `ContinuousLinearMap.IsPrCompact.newtonPolygon_charPowerSeries_ncard_setOf_unitSlope_le_le`:
  the Fredholm polygon at the number `N` of slopes at most `σ` is at most `σ N`.
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

namespace TauCeti

/-- **Counting bound for the block lower polygon.** Let `H > 0` and `c > 0`. If
`c ∑ i < n, ⌊i / H⌋ ≤ n x`, then `n < H (⌊2 x / c⌋₊ + 2)`. Writing `n = H q + ρ` with `ρ < H`,
the sum is `H q (q - 1) / 2 + ρ q`, and the inequality forces `q - 1 ≤ 2 x / c`. -/
theorem lt_mul_floor_add_two_of_mul_sum_range_div_le {H n : ℕ} (hH : 0 < H) {c x : ℝ}
    (hc : 0 < c) (h : c * (∑ i ∈ range n, i / H : ℕ) ≤ n * x) :
    n < H * (⌊2 * x / c⌋₊ + 2) := by
  have hn := Nat.div_add_mod n H
  have hρ := Nat.mod_lt n hH
  rw [sum_range_div] at h
  set q := n / H
  set ρ := n % H
  rcases q.eq_zero_or_pos with hq | hq
  · rw [hq, Nat.mul_zero, Nat.zero_add] at hn
    rw [← hn]
    nlinarith
  -- The number of complete blocks is at most `⌊2 x / c⌋₊ + 1`.
  have key : ((q - 1 : ℕ) : ℝ) ≤ 2 * x / c := by
    rw [le_div_iff₀ hc]
    by_contra hlt
    rw [not_le] at hlt
    have hnR : (n : ℝ) = H * q + ρ := by exact_mod_cast hn.symm
    push_cast [Nat.cast_sub hq, Nat.cast_choose_two] at h hlt
    have hnpos : (0 : ℝ) < n := by
      rw [hnR]
      have : (1 : ℝ) ≤ H := by exact_mod_cast hH
      positivity
    -- `2 n x < n c (q - 1) ≤ 2 c (H q (q - 1) / 2 + ρ q) ≤ 2 n x`.
    have h₁ := mul_lt_mul_of_pos_left hlt hnpos
    have h₂ : 0 ≤ c * ρ * (q + 1) := by positivity
    have h₃ : (n : ℝ) * ((q - 1) * c) = c * H * q * (q - 1) + c * ρ * (q - 1) := by
      rw [hnR]
      ring
    linarith
  have hfl := Nat.le_floor key
  calc n = H * q + ρ := hn.symm
    _ < H * (q + 1) := by nlinarith
    _ ≤ H * (⌊2 * x / c⌋₊ + 2) := Nat.mul_le_mul_left _ (by omega)

end TauCeti

namespace Matrix

variable {J K : Type*} [Finite J] [DecidableEq J] [NormedField K] [IsUltrametricDist K]
  {v : AddValuation K (WithTop ℝ)} {b s : ℝ}

/-- **Block row decay bounds the Newton polygon.** Let `v` be a real additive valuation with
`‖x‖ = b ^ (-v x)` for `x ≠ 0`, where `b > 1`. If `0 < s ≤ 1` and every entry in a row indexed
by `(j, k)` of a matrix `A` on `J × ℕ` has norm at most `s ^ k`, then the heights
`-logb b s * ∑ i < n, ⌊i / #J⌋` lie below the Newton polygon of the principal-minor series
`A.charPowerSeries`, which is the Fredholm determinant `det (1 - T A)` when its principal-minor
families are summable. -/
theorem mul_sum_range_div_le_newtonPolygon_charPowerSeries (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) (hs₀ : 0 < s) (hs₁ : s ≤ 1)
    {A : Matrix (J × ℕ) (J × ℕ) K} (hA : ∀ i j, ‖A i j‖ ≤ s ^ i.2) :
    (fun n ↦ ((-Real.logb b s * (∑ i ∈ range n, i / Nat.card J : ℕ) : ℝ) : WithTop ℝ)) ≤
      A.charPowerSeries.newtonPolygon v := by
  have hc : 0 ≤ -Real.logb b s := neg_nonneg.mpr (Real.logb_nonpos hb hs₀.le hs₁)
  refine PowerSeries.le_newtonPolygon ⟨⟨fun _ _ _ _ _ _ ↦ WithTop.coe_ne_top⟩,
    fun i _ j _ hij ↦ ?_⟩ fun n ↦ ?_
  · -- The unit slopes `c ⌊n / #J⌋` are nondecreasing.
    simp only [unitSlope_def, WithTop.untop₀_coe, sum_range_succ, Nat.cast_add]
    have := Nat.div_le_div_right (c := Nat.card J) hij
    have : ((i / Nat.card J : ℕ) : ℝ) ≤ (j / Nat.card J : ℕ) := by exact_mod_cast this
    nlinarith
  · have key := norm_charCoeff_le_pow_sum_range_div hs₀.le hs₁ hA n
    rw [← coeff_charPowerSeries] at key
    have h := (PowerSeries.norm_coeff_mul_rpow_pow_le_iff A.charPowerSeries v hb hv n 0
      (-Real.logb b s * (∑ i ∈ range n, i / Nat.card J : ℕ))).mp <| by
      rwa [Real.rpow_zero, one_pow, mul_one, neg_mul, neg_neg, Real.rpow_mul
        (zero_lt_one.trans hb).le, Real.rpow_logb (zero_lt_one.trans hb) hb.ne' hs₀,
        Real.rpow_natCast]
    simpa only [zero_mul, add_zero] using h

end Matrix

namespace ContinuousLinearMap

section PrCompact

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (v : AddValuation K (WithTop ℝ)) {M : Type*} [SeminormedAddCommGroup M] [Module K M]
  {u : M →L[K] M} {b : ℝ} (hb : 1 < b) (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- **Slopes at most `σ` lie under the line of slope `σ`.** If the Fredholm polygon of a
row-compact endomorphism `u` of a module with property (Pr) has `N` finite unit edges of slope
at most `σ`, its height at `N` is at most `σ N`. Hence every lower bound of the polygon is at
most `σ N` at `N`. -/
theorem IsPrCompact.newtonPolygon_charPowerSeries_ncard_setOf_unitSlope_le_le
    (hu : u.IsPrCompact) (σ : ℝ) :
    u.charPowerSeries.newtonPolygon v {n | n ∈ finiteEdges (u.charPowerSeries.newtonPolygon v) ∧
      unitSlope (u.charPowerSeries.newtonPolygon v) n ≤ σ}.ncard ≤
      ((σ * {n | n ∈ finiteEdges (u.charPowerSeries.newtonPolygon v) ∧
        unitSlope (u.charPowerSeries.newtonPolygon v) n ≤ σ}.ncard : ℝ) : WithTop ℝ) := by
  obtain ⟨l, l', hf⟩ := hu.exists_isFiniteFace_newtonPolygon_charPowerSeries v hb hv σ
  -- The polygon starts at or below the height `v 1 = 0` of the constant coefficient.
  have hadm := (PowerSeries.isAdmissible_addValuation_coeff_iff_exists_isRestricted
    u.charPowerSeries v hb hv).2 ⟨1, one_pos, hu.isEntire_charPowerSeries.isRestricted 1⟩
  simpa only [zero_add] using hf.apply_ncard_setOf_unitSlope_le_le
    (u.charPowerSeries.isConvexSeq_newtonPolygon v) (a := 0) <| by
      simpa using PowerSeries.newtonPolygon_le hadm 0

end PrCompact

/-- Block row decay with `s < 1` makes an operator on `C₀(J × ℕ, R)` row compact, since each
block `J × {k}` is finite. -/
private theorem isRowCompact_of_norm_matrixCoeff_le_pow_snd {J R : Type*} [TopologicalSpace J]
    [DiscreteTopology J] [DecidableEq J] [Finite J] [SeminormedRing R] {s : ℝ}
    {u : C₀(J × ℕ, R) →L[R] C₀(J × ℕ, R)} (hs₀ : 0 ≤ s) (hs₁ : s < 1)
    (hA : ∀ i j, ‖u.matrixCoeff i j‖ ≤ s ^ i.2) : u.IsRowCompact := by
  refine isRowCompact_of_norm_matrixCoeff_le ((tendsto_pow_atTop_nhds_zero_of_lt_one hs₀ hs₁).comp
    ?_) hA
  rw [← Nat.cofinite_eq_atTop]
  exact Tendsto.cofinite_of_finite_preimage_singleton fun k ↦
    (Set.finite_range fun j : J ↦ (j, k)).subset fun i hi ↦ ⟨i.1, Prod.ext rfl hi.symm⟩

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
