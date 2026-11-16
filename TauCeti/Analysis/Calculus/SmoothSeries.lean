/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Geometric series of smooth functions

If the derivatives of order `m ≤ k` of a sequence of functions `Gⱼ` are bounded by `B m * q ^ j`
with `0 ≤ q < 1`, then `∑ⱼ Gⱼ` is `C^k`, its derivatives through order `k` are the sums of the
derivatives, and its `m`-th derivative is bounded by `B m / (1 - q)`. These specialise Mathlib's
`contDiff_tsum` and `iteratedFDeriv_tsum` to geometric bounds.

## Main declarations

* `TauCeti.contDiff_tsum_of_norm_iteratedFDeriv_le_geometric`: the sum is `C^k`.
* `TauCeti.iteratedFDeriv_tsum_of_norm_iteratedFDeriv_le_geometric`: its derivatives through
  order `k` are the sums of the derivatives.
* `TauCeti.norm_iteratedFDeriv_tsum_le_of_geometric`: the bound `B m / (1 - q)` on them.
-/

public section

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] {k : ℕ} {G : ℕ → E → F} {B : ℕ → ℝ} {q : ℝ}

/-- A series of `C^k` functions whose derivatives of order `m ≤ k` are bounded by `B m * q ^ j`,
with `0 ≤ q < 1`, has a `C^k` sum. -/
theorem contDiff_tsum_of_norm_iteratedFDeriv_le_geometric (hG : ∀ j, ContDiff 𝕜 k (G j))
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbd : ∀ m ≤ k, ∀ j x, ‖iteratedFDeriv 𝕜 m (G j) x‖ ≤ B m * q ^ j) :
    ContDiff 𝕜 k (fun x ↦ ∑' j, G j x) :=
  contDiff_tsum hG (fun m _ ↦ (summable_geometric_of_lt_one hq0 hq1).mul_left (B m))
    fun m j x hm ↦ hbd m (by exact_mod_cast hm) j x

/-- For a series of `C^k` functions whose derivatives of order `m ≤ k` are bounded by
`B m * q ^ j`, with `0 ≤ q < 1`, the derivatives of the sum through order `k` are the sums of the
derivatives. -/
theorem iteratedFDeriv_tsum_of_norm_iteratedFDeriv_le_geometric (hG : ∀ j, ContDiff 𝕜 k (G j))
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbd : ∀ m ≤ k, ∀ j x, ‖iteratedFDeriv 𝕜 m (G j) x‖ ≤ B m * q ^ j) {i : ℕ} (hi : i ≤ k) :
    iteratedFDeriv 𝕜 i (fun x ↦ ∑' j, G j x) = fun x ↦ ∑' j, iteratedFDeriv 𝕜 i (G j) x :=
  iteratedFDeriv_tsum hG (fun m _ ↦ (summable_geometric_of_lt_one hq0 hq1).mul_left (B m))
    (fun m j x hm ↦ hbd m (by exact_mod_cast hm) j x) (by exact_mod_cast hi)

/-- For a series of `C^k` functions whose derivatives of order `m ≤ k` are bounded by
`B m * q ^ j`, with `0 ≤ q < 1`, the `i`-th derivative of the sum, `i ≤ k`, is bounded by
`B i / (1 - q)`. -/
theorem norm_iteratedFDeriv_tsum_le_of_geometric (hG : ∀ j, ContDiff 𝕜 k (G j))
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbd : ∀ m ≤ k, ∀ j x, ‖iteratedFDeriv 𝕜 m (G j) x‖ ≤ B m * q ^ j) {i : ℕ} (hi : i ≤ k)
    (x : E) :
    ‖iteratedFDeriv 𝕜 i (fun x ↦ ∑' j, G j x) x‖ ≤ B i * (1 - q)⁻¹ := by
  rw [iteratedFDeriv_tsum_of_norm_iteratedFDeriv_le_geometric hG hq0 hq1 hbd hi]
  exact tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hq0 hq1).mul_left (B i))
    fun j ↦ hbd i hi j x

end TauCeti
