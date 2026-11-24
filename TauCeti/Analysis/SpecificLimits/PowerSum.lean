/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The power-sum lemma

Let `ω_1, …, ω_k` be elements of a normed field of characteristic zero, and let `0 ≤ ρ`. If the
power sums `∑ i, ω_i ^ n` are `O(ρ ^ n)`, that is `‖∑ i, ω_i ^ n‖ ≤ C ρ ^ n` for all `n ≥ n₀`, then
every `‖ω_i‖ ≤ ρ`. This is how the Weil bound for a character sum follows from the root-power
identity for its `L`-polynomial: a bound for the sums over all extension fields bounds each
reciprocal root.

The proof groups equal values. For distinct `z_1, …, z_l` with coefficients `c_j`, the Vandermonde
matrix `(z_j ^ h)` for `0 ≤ h < l` is invertible, and its inverse writes each `c_j z_j ^ n` as a
fixed linear combination of the `l` consecutive sums `∑ j, c_j z_j ^ (n + h)`. So
`‖c_j z_j ^ n‖ ≤ D ρ ^ n` with `D` independent of `n`, and if `c_j ≠ 0` this forces `‖z_j‖ ≤ ρ`.

## Main results

* `TauCeti.norm_le_of_norm_sum_mul_pow_le`: for distinct bases `z_j` and `0 ≤ ρ`, if
  `‖∑ j, c_j z_j ^ n‖ ≤ C ρ ^ n` for all `n ≥ n₀`, then `‖z_j‖ ≤ ρ` whenever `c_j ≠ 0`.
* `TauCeti.norm_le_of_norm_sum_pow_le`: the power-sum lemma.

Characteristic zero is necessary in the power-sum lemma: in characteristic `p`, the family of `p`
copies of `1` has every power sum `0`.
-/

public section

open Filter Finset Matrix Topology

namespace TauCeti

variable {𝕜 : Type*} [NormedField 𝕜]

/-- If the bases `z j` for `j ∈ s` are distinct, `0 ≤ ρ`, and
`‖∑ j ∈ s, c j * z j ^ n‖ ≤ C * ρ ^ n` for all `n ≥ n₀`, then `‖z j‖ ≤ ρ` for every `j ∈ s` with
`c j ≠ 0`. -/
theorem norm_le_of_norm_sum_mul_pow_le {ι : Type*} {s : Finset ι} {z c : ι → 𝕜}
    (hz : Set.InjOn z s) {ρ C : ℝ} (hρ : 0 ≤ ρ) {n₀ : ℕ}
    (hsum : ∀ n ≥ n₀, ‖∑ j ∈ s, c j * z j ^ n‖ ≤ C * ρ ^ n) {j : ι} (hj : j ∈ s) (hc : c j ≠ 0) :
    ‖z j‖ ≤ ρ := by
  -- Index the bases by `Fin #s` and form their Vandermonde matrix `V k h = v k ^ h`.
  let e := s.equivFin
  let v : Fin #s → 𝕜 := fun k ↦ z (e.symm k)
  have hv : Function.Injective v := fun k k' hk ↦
    e.symm.injective (Subtype.ext (hz (e.symm k).property (e.symm k').property hk))
  let V := Matrix.vandermonde v
  have hV : IsUnit V.det := (Matrix.det_vandermonde_ne_zero_iff.2 hv).isUnit
  -- The row vector `a n = (c_k v_k ^ n)_k` times `V` is the vector of consecutive sums.
  let a : ℕ → Fin #s → 𝕜 := fun n k ↦ c (e.symm k) * v k ^ n
  have ha : ∀ n, a n ᵥ* V = fun h : Fin #s ↦ ∑ i ∈ s, c i * z i ^ (n + h) := fun n ↦ by
    ext h
    rw [← s.sum_coe_sort, ← e.symm.sum_comp]
    simp [Matrix.vecMul, dotProduct, V, a, v, pow_add, mul_assoc]
  -- Inverting `V` bounds each coefficient by a fixed multiple of `ρ ^ n`.
  let D := ∑ h : Fin #s, C * ρ ^ (h : ℕ) * ‖V⁻¹ h (e ⟨j, hj⟩)‖
  have hD : ∀ n ≥ n₀, ‖c j‖ * ‖z j‖ ^ n ≤ D * ρ ^ n := fun n hn ↦ by
    have hinv : a n = (a n ᵥ* V) ᵥ* V⁻¹ := by
      rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hV, Matrix.vecMul_one]
    have hj' : ‖c j‖ * ‖z j‖ ^ n = ‖a n (e ⟨j, hj⟩)‖ := by simp [a, v]
    rw [hj', hinv, ha]
    simp only [vecMul, dotProduct]
    refine (norm_sum_le _ _).trans
      ((Finset.sum_le_sum fun h _ ↦ ?_).trans_eq (Finset.sum_mul _ _ _).symm)
    rw [norm_mul]
    calc ‖∑ i ∈ s, c i * z i ^ (n + h)‖ * ‖V⁻¹ h (e ⟨j, hj⟩)‖
        ≤ C * ρ ^ (n + h) * ‖V⁻¹ h (e ⟨j, hj⟩)‖ :=
          mul_le_mul_of_nonneg_right (hsum _ (by omega)) (norm_nonneg _)
      _ = C * ρ ^ (h : ℕ) * ‖V⁻¹ h (e ⟨j, hj⟩)‖ * ρ ^ n := by ring
  -- If `ρ < ‖z j‖`, then `‖c j‖ ≤ D (ρ / ‖z j‖) ^ n → 0`, so `c j = 0`.
  by_contra! hlt
  have hz0 : 0 < ‖z j‖ := hρ.trans_lt hlt
  have hlim : Tendsto (fun n ↦ D * (ρ / ‖z j‖) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hρ hz0.le)
      ((div_lt_one hz0).2 hlt)).const_mul D
  have hle : ∀ᶠ n in atTop, ‖c j‖ ≤ D * (ρ / ‖z j‖) ^ n := by
    filter_upwards [eventually_ge_atTop n₀] with n hn
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos hz0 n)]
    exact hD n hn
  exact hc (norm_le_zero_iff.1 (ge_of_tendsto hlim hle))

/-- **The power-sum lemma.** In a normed field of characteristic zero, if `0 ≤ ρ` and
`‖∑ i, ω i ^ n‖ ≤ C * ρ ^ n` for all `n ≥ n₀`, then `‖ω i‖ ≤ ρ` for every `i`. -/
theorem norm_le_of_norm_sum_pow_le [CharZero 𝕜] {ι : Type*} [Fintype ι] {ω : ι → 𝕜}
    {ρ C : ℝ} (hρ : 0 ≤ ρ) {n₀ : ℕ} (hsum : ∀ n ≥ n₀, ‖∑ i, ω i ^ n‖ ≤ C * ρ ^ n) (i : ι) :
    ‖ω i‖ ≤ ρ := by
  classical
  -- Group equal values: the coefficient of the base `y` is the number of `i` with `ω i = y`.
  refine norm_le_of_norm_sum_mul_pow_le (s := univ.image ω) (z := id)
    (c := fun y ↦ (#{i | ω i = y} : 𝕜)) (Set.injOn_id _) hρ (n₀ := n₀) (C := C) (fun n hn ↦ ?_)
    (mem_image_of_mem ω (mem_univ i)) ?_
  · simpa [Finset.sum_comp (· ^ n) ω, nsmul_eq_mul] using hsum n hn
  · exact Nat.cast_ne_zero.2 (card_ne_zero.2 ⟨i, by simp⟩)

end TauCeti
