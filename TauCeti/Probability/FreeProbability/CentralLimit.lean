/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Analysis.Real.Sqrt
public import TauCeti.Combinatorics.NoncrossingPartition.Catalan
public import TauCeti.Probability.Distributions.Semicircle.Moments
public import TauCeti.Probability.FreeProbability.Cumulant.Bounds
public import TauCeti.Probability.FreeProbability.Cumulant.Free

/-!
# The free central limit theorem

Let `φ : A →ₗ[𝕜] 𝕜` be a normalised linear functional on an algebra over `𝕜 = ℝ` or `ℂ`, and let
`a 0, a 1, …` be freely independent centred elements of `A`, `φ (a j) = 0`, whose moments
`φ (a j ^ k)` are bounded uniformly in `j` for each `k`. The *free central limit theorem* states
that the odd moments of the normalised sums `S_N = (√N)⁻¹ • (a 0 + ⋯ + a (N - 1))` tend to `0`,
and, if the average variance `N⁻¹ ∑_{j < N} φ (a j ^ 2)` tends to `σ² ∈ 𝕜`, that the even moments
tend to the Catalan moments:

`φ (S_N ^ (2k)) → σ² ^ k * catalan k` and `φ (S_N ^ (2k + 1)) → 0`.

When `σ²` is a real number `v ≥ 0`, these limits are the moments of the centred semicircle law
`semicircleReal 0 v`. For identically distributed variables (equal moments
`φ (a j ^ k) = φ (a 0 ^ k)`) whose variance `φ (a 0 ^ 2)` is a real number `v ≥ 0`, the hypotheses
reduce to centring of `a 0`, and the limit is the moment sequence of `semicircleReal 0 v`.

The proof is the cumulant proof. Since free cumulants are additive on free elements, the
moment–cumulant formula gives
`φ (S_N ^ n) = ∑_{π ∈ NC(n)} (√N)⁻¹ ^ n ∏_{B ∈ π} ∑_{j < N} κ_B(a j)`. A partition with a
singleton part contributes nothing, because the first cumulants are the vanishing means. The
cumulants are bounded uniformly in `j`, because each is a fixed polynomial in moments; so a
partition all of whose parts have at least two positions and one of them at least three has at
most `(n - 1) / 2` parts, and its term is `O((√N)⁻¹)`. Only the noncrossing pairings survive,
each contributing `σ² ^ (n / 2)` in the limit, and there are `catalan k` of them for `n = 2k`
and none for odd `n`.

No positivity or traciality of `φ` is assumed, and the conclusion is convergence of moments; the
weak convergence of laws in a C*-probability space, which would follow by the method of moments,
is not stated here.

## Main results

* `TauCeti.IsFreelyIndependentElements.tendsto_apply_inv_sqrt_smul_sum_pow_two_mul` and
  `TauCeti.IsFreelyIndependentElements.tendsto_apply_inv_sqrt_smul_sum_pow_two_mul_add_one` —
  the free central limit theorem: the even moments of `S_N` tend to `σ² ^ k * catalan k` and the
  odd moments tend to `0`, the latter without any assumption on the variances.
* `TauCeti.IsFreelyIndependentElements.tendsto_apply_inv_sqrt_smul_sum_pow_semicircleReal` — for a
  limiting variance `v ≥ 0`, the moments of `S_N` tend to those of `semicircleReal 0 v`.
* `TauCeti.IsFreelyIndependentElements.tendsto_apply_inv_sqrt_smul_sum_pow_of_apply_pow_eq`
  — the same for identically distributed centred free elements of variance `v`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Theorem 8.10 for the
  free central limit theorem; the cumulant proof uses the moment–cumulant formula of Lecture 11
  and the additivity of free cumulants on free families of Lecture 12.
* D. Voiculescu, *Symmetries of some reduced free product C*-algebras*, Lecture Notes in Math.
  1132 (1985), 556–588.
-/

public section

open Finset Filter Topology IncidenceAlgebra NNReal

namespace TauCeti

section CentralLimit

variable {𝕜 A : Type*} [RCLike 𝕜] [Semiring A] [Algebra 𝕜 A] {φ : A →ₗ[𝕜] 𝕜} {a : ℕ → A}

/-- In the moment–cumulant expansion of `φ (((√N)⁻¹ • ∑_{j < N} a j) ^ n)`, the term of a
noncrossing partition `π` that is not a pairing tends to `0`. -/
private theorem tendsto_inv_sqrt_pow_mul_prod_sum_freeCumulant_of_not_isPairing
    (hcen : ∀ j, φ (a j) = 0) (hbdd : ∀ k, ∃ M, ∀ j, ‖φ (a j ^ k)‖ ≤ M) {n : ℕ}
    {π : NoncrossingPartition (univ : Finset (Fin n))} (hp : ¬π.1.IsPairing) :
    Tendsto (fun N : ℕ => (√(N : ℝ) : 𝕜)⁻¹ ^ n *
        ∏ B ∈ π.1.parts, ∑ j ∈ range N, freeCumulant φ (fun _ => a j) B) atTop (𝓝 0) := by
  by_cases h1 : ∃ B ∈ π.1.parts, #B = 1
  · -- A singleton part contributes the sum of the means, which vanish.
    obtain ⟨B, hB, hB1⟩ := h1
    obtain ⟨i, rfl⟩ := card_eq_one.1 hB1
    refine tendsto_const_nhds.congr fun N => ?_
    rw [prod_eq_zero hB (by simp [hcen]), mul_zero]
  -- Otherwise every part has at least two positions and some part at least three, so `π` has
  -- fewer than `n / 2` parts, while the cumulants are bounded uniformly in `j`.
  push Not at h1
  have hlt : 2 * #π.1.parts < n := by
    have hsum : ∑ B ∈ π.1.parts, #B = n := by simpa using π.1.sum_card_parts
    obtain ⟨B, hB, hB2⟩ : ∃ B ∈ π.1.parts, #B ≠ 2 := by
      simpa [Finpartition.isPairing_iff] using hp
    have h2 : ∀ B ∈ π.1.parts, 2 ≤ #B := fun B hB => by
      have := card_pos.2 (π.1.nonempty_of_mem_parts hB)
      have := h1 B hB
      omega
    calc 2 * #π.1.parts = ∑ B ∈ π.1.parts, 2 := by rw [sum_const, smul_eq_mul, mul_comm]
      _ < ∑ B ∈ π.1.parts, #B := sum_lt_sum h2 ⟨B, hB, lt_of_le_of_ne (h2 B hB) (Ne.symm hB2)⟩
      _ = n := hsum
  choose M hM using hbdd
  set C : Finset (Fin n) → ℝ := fun B =>
    ∑ τ : NoncrossingPartition B, ‖mu 𝕜 τ ⊤‖ * ∏ D ∈ τ.1.parts, M #D
  have hC (B : Finset (Fin n)) (j : ℕ) : ‖freeCumulant φ (fun _ => a j) B‖ ≤ C B :=
    norm_freeCumulant_const_le φ (a j) fun k _ => hM k j
  have hinv : Tendsto (fun N : ℕ => (√(N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun N : ℕ => (√(N : ℝ))⁻¹ ^ (n - 2 * #π.1.parts) * ∏ B ∈ π.1.parts, C B)
      atTop (𝓝 0) := by
    simpa [zero_pow (Nat.sub_ne_zero_of_lt hlt)] using
      (hinv.pow (n - 2 * #π.1.parts)).mul_const (∏ B ∈ π.1.parts, C B)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  calc ‖(√(N : ℝ) : 𝕜)⁻¹ ^ n * ∏ B ∈ π.1.parts, ∑ j ∈ range N, freeCumulant φ (fun _ => a j) B‖
      ≤ (√(N : ℝ))⁻¹ ^ n * ∏ B ∈ π.1.parts, ((N : ℝ) * C B) := by
        rw [norm_mul, norm_pow, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _)]
        refine mul_le_mul_of_nonneg_left ((Finset.norm_prod_le _ _).trans
          (prod_le_prod₀ (fun _ _ => norm_nonneg _) fun B _ => ?_)) (by positivity)
        refine (norm_sum_le _ _).trans ((sum_le_sum fun j _ => hC B j).trans_eq ?_)
        rw [sum_const, card_range, nsmul_eq_mul]
    _ = (√(N : ℝ))⁻¹ ^ (n - 2 * #π.1.parts) * ∏ B ∈ π.1.parts, C B := by
        rw [prod_mul_distrib, prod_const, ← mul_assoc, Real.inv_sqrt_pow_mul_pow hN' hlt.le]

/-- In the moment–cumulant expansion of `φ (((√N)⁻¹ • ∑_{j < N} a j) ^ n)`, the term of a
noncrossing partition `π` tends to `σ² ^ #π` if `π` is a pairing, and to `0` otherwise. -/
private theorem tendsto_inv_sqrt_pow_mul_prod_sum_freeCumulant (hcen : ∀ j, φ (a j) = 0)
    (hbdd : ∀ k, ∃ M, ∀ j, ‖φ (a j ^ k)‖ ≤ M) {σ2 : 𝕜}
    (hvar : Tendsto (fun N : ℕ => (N : 𝕜)⁻¹ * ∑ j ∈ range N, φ (a j ^ 2)) atTop (𝓝 σ2))
    {n : ℕ} (π : NoncrossingPartition (univ : Finset (Fin n))) :
    Tendsto (fun N : ℕ => (√(N : ℝ) : 𝕜)⁻¹ ^ n *
        ∏ B ∈ π.1.parts, ∑ j ∈ range N, freeCumulant φ (fun _ => a j) B) atTop
      (𝓝 (if π.1.IsPairing then σ2 ^ #π.1.parts else 0)) := by
  by_cases hp : π.1.IsPairing
  · -- Each part of a pairing contributes the sum of the variances, and `(√N)⁻¹ ^ 2 = N⁻¹`.
    have hn (x : 𝕜) : x ^ n = (x ^ 2) ^ #π.1.parts := by
      rw [← pow_mul, ← (by simpa using hp.card_eq_two_mul : n = 2 * #π.1.parts)]
    simp only [hp, ↓reduceIte]
    refine (hvar.pow #π.1.parts).congr fun N => ?_
    rw [prod_congr rfl fun B hB => sum_congr rfl fun j _ => by
        rw [freeCumulant_const_of_card_eq_two φ _ (Finpartition.isPairing_iff.1 hp B hB), hcen,
          sq (0 : 𝕜), mul_zero, sub_zero],
      prod_const, hn, ← mul_pow, inv_pow, ← RCLike.ofReal_pow,
      Real.sq_sqrt N.cast_nonneg, RCLike.ofReal_natCast]
  simpa only [hp, ↓reduceIte] using
    tendsto_inv_sqrt_pow_mul_prod_sum_freeCumulant_of_not_isPairing hcen hbdd hp

/-- The free central limit theorem with the number of noncrossing pairings of `n` points in the
limit. -/
private theorem IsFreelyIndependentElements.tendsto_apply_inv_sqrt_smul_sum_pow
    (h : IsFreelyIndependentElements φ a) (hφ : φ 1 = 1) (hcen : ∀ j, φ (a j) = 0)
    (hbdd : ∀ k, ∃ M, ∀ j, ‖φ (a j ^ k)‖ ≤ M) {σ2 : 𝕜}
    (hvar : Tendsto (fun N : ℕ => (N : 𝕜)⁻¹ * ∑ j ∈ range N, φ (a j ^ 2)) atTop (𝓝 σ2))
    (n : ℕ) :
    Tendsto (fun N : ℕ => φ (((√(N : ℝ) : 𝕜)⁻¹ • ∑ j ∈ range N, a j) ^ n)) atTop
      (𝓝 (σ2 ^ (n / 2) *
        Fintype.card {π : NoncrossingPartition (univ : Finset (Fin n)) // π.1.IsPairing})) := by
  have hL : σ2 ^ (n / 2) *
      Fintype.card {π : NoncrossingPartition (univ : Finset (Fin n)) // π.1.IsPairing} =
        ∑ π : NoncrossingPartition (univ : Finset (Fin n)),
          if π.1.IsPairing then σ2 ^ #π.1.parts else 0 := by
    rw [← sum_filter, Fintype.card_subtype, mul_comm, ← nsmul_eq_mul, ← sum_const]
    refine sum_congr rfl fun π hπ => ?_
    have := (mem_filter.1 hπ).2.card_eq_two_mul
    rw [card_univ, Fintype.card_fin] at this
    rw [show n / 2 = #π.1.parts by omega]
  rw [hL]
  refine (tendsto_finsetSum _ fun π _ =>
    tendsto_inv_sqrt_pow_mul_prod_sum_freeCumulant hcen hbdd hvar π).congr fun N => ?_
  rw [smul_pow, map_smul, smul_eq_mul, h.apply_sum_pow_eq_sum_prod_sum_freeCumulant hφ, mul_sum]

/-- *The free central limit theorem*, even moments: if the elements `a j` are freely independent
for a normalised `φ`, centred, with moments `φ (a j ^ k)` bounded uniformly in `j` for each `k`,
and with average variance `N⁻¹ ∑_{j < N} φ (a j ^ 2) → σ²`, then
`φ (((√N)⁻¹ • ∑_{j < N} a j) ^ (2k)) → σ² ^ k * catalan k`. -/
theorem IsFreelyIndependentElements.tendsto_apply_inv_sqrt_smul_sum_pow_two_mul
    (h : IsFreelyIndependentElements φ a) (hφ : φ 1 = 1) (hcen : ∀ j, φ (a j) = 0)
    (hbdd : ∀ k, ∃ M, ∀ j, ‖φ (a j ^ k)‖ ≤ M) {σ2 : 𝕜}
    (hvar : Tendsto (fun N : ℕ => (N : 𝕜)⁻¹ * ∑ j ∈ range N, φ (a j ^ 2)) atTop (𝓝 σ2))
    (k : ℕ) :
    Tendsto (fun N : ℕ => φ (((√(N : ℝ) : 𝕜)⁻¹ • ∑ j ∈ range N, a j) ^ (2 * k))) atTop
      (𝓝 (σ2 ^ k * catalan k)) := by
  simpa [NoncrossingPartition.card_isPairing_fin_eq_catalan] using
    h.tendsto_apply_inv_sqrt_smul_sum_pow hφ hcen hbdd hvar (2 * k)

/-- *The free central limit theorem*, odd moments: if the elements `a j` are freely independent
for a normalised `φ`, centred, with moments `φ (a j ^ k)` bounded uniformly in `j` for each `k`,
then `φ (((√N)⁻¹ • ∑_{j < N} a j) ^ (2k + 1)) → 0`. No convergence of the variances is needed. -/
theorem IsFreelyIndependentElements.tendsto_apply_inv_sqrt_smul_sum_pow_two_mul_add_one
    (h : IsFreelyIndependentElements φ a) (hφ : φ 1 = 1) (hcen : ∀ j, φ (a j) = 0)
    (hbdd : ∀ k, ∃ M, ∀ j, ‖φ (a j ^ k)‖ ≤ M) (k : ℕ) :
    Tendsto (fun N : ℕ => φ (((√(N : ℝ) : 𝕜)⁻¹ • ∑ j ∈ range N, a j) ^ (2 * k + 1))) atTop
      (𝓝 0) := by
  -- An odd number of positions has no pairing, so every term of the expansion tends to `0`.
  have hp (π : NoncrossingPartition (univ : Finset (Fin (2 * k + 1)))) : ¬π.1.IsPairing :=
    fun hp => by simpa using hp.even_card
  have := tendsto_finsetSum univ fun π _ =>
    tendsto_inv_sqrt_pow_mul_prod_sum_freeCumulant_of_not_isPairing hcen hbdd (hp π)
  rw [sum_const_zero] at this
  refine this.congr fun N => ?_
  rw [smul_pow, map_smul, smul_eq_mul, h.apply_sum_pow_eq_sum_prod_sum_freeCumulant hφ, mul_sum]

/-- *The free central limit theorem*: if the elements `a j` are freely independent for a
normalised `φ`, centred, with moments `φ (a j ^ k)` bounded uniformly in `j` for each `k`, and
with average variance `N⁻¹ ∑_{j < N} φ (a j ^ 2) → v` for a real `v ≥ 0`, then the moments of
`(√N)⁻¹ • ∑_{j < N} a j` tend to those of the centred semicircle law `semicircleReal 0 v`. -/
theorem IsFreelyIndependentElements.tendsto_apply_inv_sqrt_smul_sum_pow_semicircleReal
    (h : IsFreelyIndependentElements φ a) (hφ : φ 1 = 1) (hcen : ∀ j, φ (a j) = 0)
    (hbdd : ∀ k, ∃ M, ∀ j, ‖φ (a j ^ k)‖ ≤ M) {v : ℝ≥0}
    (hvar : Tendsto (fun N : ℕ => (N : 𝕜)⁻¹ * ∑ j ∈ range N, φ (a j ^ 2)) atTop
      (𝓝 ((v : ℝ) : 𝕜)))
    (n : ℕ) :
    Tendsto (fun N : ℕ => φ (((√(N : ℝ) : 𝕜)⁻¹ • ∑ j ∈ range N, a j) ^ n)) atTop
      (𝓝 ((∫ x, x ^ n ∂Probability.semicircleReal 0 v : ℝ) : 𝕜)) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · simpa using h.tendsto_apply_inv_sqrt_smul_sum_pow_two_mul hφ hcen hbdd hvar k
  · simpa using h.tendsto_apply_inv_sqrt_smul_sum_pow_two_mul_add_one hφ hcen hbdd k

/-- *The free central limit theorem* for identically distributed elements: if the elements `a j`
are freely independent for a normalised `φ` and have the moments of `a 0`, which is centred with
variance `φ (a 0 ^ 2) = v`, then the moments of `(√N)⁻¹ • ∑_{j < N} a j` tend to those of the
centred semicircle law `semicircleReal 0 v`. -/
theorem IsFreelyIndependentElements.tendsto_apply_inv_sqrt_smul_sum_pow_of_apply_pow_eq
    (h : IsFreelyIndependentElements φ a) (hφ : φ 1 = 1)
    (hid : ∀ j k, φ (a j ^ k) = φ (a 0 ^ k)) (hcen : φ (a 0) = 0) {v : ℝ≥0}
    (hv : φ (a 0 ^ 2) = ((v : ℝ) : 𝕜)) (n : ℕ) :
    Tendsto (fun N : ℕ => φ (((√(N : ℝ) : 𝕜)⁻¹ • ∑ j ∈ range N, a j) ^ n)) atTop
      (𝓝 ((∫ x, x ^ n ∂Probability.semicircleReal 0 v : ℝ) : 𝕜)) := by
  refine h.tendsto_apply_inv_sqrt_smul_sum_pow_semicircleReal hφ
    (fun j => by simpa [hcen] using hid j 1)
    (fun k => ⟨‖φ (a 0 ^ k)‖, fun j => (congrArg norm (hid j k)).le⟩) ?_ n
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with N hN
  rw [sum_congr rfl fun j _ => (hid j 2).trans hv, sum_const, card_range, nsmul_eq_mul,
    inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 hN)]

end CentralLimit

end TauCeti
