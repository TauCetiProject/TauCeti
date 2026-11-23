/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Topology.Instances.NNReal.Dyadic.Grid

import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.Topology.MetricSpace.Holder

/-!
# Deterministic dyadic chaining and Hölder extension on `[0, N]`

If a function `f : ℚ≥0 → E` into a complete extended metric space satisfies an adjacent dyadic
increment bound `edist (f (k / 2ˡ)) (f ((k + 1) / 2ˡ)) ≤ K * (2⁻ˡ) ^ γ` at all dyadic levels `l`
and grid indices `k < N * 2ˡ` for some positive exponent `γ : ℝ≥0`, then binary dyadic chaining
upgrades this to a `γ`-Hölder estimate on all dyadic rationals in `[0, N]`. Since dyadic rationals
are dense in `Iic (N : ℝ≥0)`, `HolderOnWith.extend_of_dense` extends `f` from those dyadic
rationals to a `γ`-Hölder map on `Iic (N : ℝ≥0)`.

This deterministic step is independent of probability theory and serves as the metric-space input
to the one-dimensional Kolmogorov–Chentsov theorem.

## Main results

* `TauCeti.exists_holderWith_Iic_of_edist_dyadicNNRat_succ_le`: extends a function on `ℚ≥0`
  satisfying adjacent dyadic increment bounds of order `γ > 0` on `[0, N]` to a `γ`-Hölder map on
  `Iic (N : ℝ≥0)` agreeing with `f` on all dyadic rationals in `[0, N]`.
-/

public section

open Filter Set
open scoped ENNReal NNReal Topology

namespace TauCeti

/-- Single parity-rounding step at dyadic level `j` (`b = a` or `b = a + 1`). -/
private lemma edist_dyadicNNRat_step {E : Type*} [PseudoEMetricSpace E] {f : ℚ≥0 → E}
    {N j : ℕ} {K γ : ℝ≥0}
    (hadj : ∀ l : ℕ, ∀ k < N * 2 ^ l,
      edist (f (dyadicNNRat l k)) (f (dyadicNNRat l (k + 1))) ≤
        (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ l) ^ (γ : ℝ))
    {a b : ℕ} (hb : b ≤ N * 2 ^ j) (hab : b = a ∨ b = a + 1) :
    edist (f (dyadicNNRat j a)) (f (dyadicNNRat j b)) ≤
      (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ j) ^ (γ : ℝ) := by
  rcases hab with rfl | rfl
  · simp
  · exact hadj j a (by omega)

/-- Binary inward-rounding chaining on dyadic rationals in an extended pseudometric space: if
adjacent increments at all levels `l` are bounded by `K * (2⁻ˡ) ^ γ`, then any two level-`(r + d)`
grid points within `2 * 2 ^ d` steps have values within `2 * K * ∑_{i ≤ d} (2^{-(r + i)}) ^ γ`. -/
private lemma edist_dyadicNNRat_le_sum {E : Type*} [PseudoEMetricSpace E] {f : ℚ≥0 → E}
    {N r : ℕ} {K γ : ℝ≥0}
    (hadj : ∀ l : ℕ, ∀ k < N * 2 ^ l,
      edist (f (dyadicNNRat l k)) (f (dyadicNNRat l (k + 1))) ≤
        (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ l) ^ (γ : ℝ)) :
    ∀ (d a b : ℕ), a ≤ b → b ≤ N * 2 ^ (r + d) → b - a ≤ 2 * 2 ^ d →
      edist (f (dyadicNNRat (r + d) a)) (f (dyadicNNRat (r + d) b)) ≤
        2 * (K : ℝ≥0∞) * ∑ i ∈ Finset.range (d + 1), ((2⁻¹ : ℝ≥0∞) ^ (r + i)) ^ (γ : ℝ) := by
  intro d
  induction d with
  | zero =>
    -- Base case: `b - a ≤ 2`, handled in at most two adjacent level-`r` steps.
    intro a b hab hb hba
    simp only [zero_add, add_zero, pow_zero, mul_one, Finset.range_one,
      Finset.sum_singleton] at hb hba ⊢
    obtain rfl | rfl | rfl : b = a ∨ b = a + 1 ∨ b = a + 2 := by omega
    · simp
    · refine (hadj r a (by omega)).trans ?_
      rw [mul_assoc]
      exact le_mul_of_one_le_left zero_le one_le_two
    · calc edist (f (dyadicNNRat r a)) (f (dyadicNNRat r (a + 2)))
          ≤ edist (f (dyadicNNRat r a)) (f (dyadicNNRat r (a + 1))) +
              edist (f (dyadicNNRat r (a + 1))) (f (dyadicNNRat r (a + 2))) := edist_triangle ..
        _ ≤ (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ r) ^ (γ : ℝ) +
              (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ r) ^ (γ : ℝ) :=
            add_le_add (hadj r a (by omega)) (hadj r (a + 1) (by omega))
        _ = 2 * (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ r) ^ (γ : ℝ) := by ring
  | succ d ih =>
    intro a b hab hb hba
    rw [Finset.sum_range_succ, mul_add]
    by_cases hsmall : b ≤ a + 1
    · refine (edist_dyadicNNRat_step hadj hb (by omega)).trans (le_trans ?_ le_add_self)
      rw [mul_assoc]
      exact le_mul_of_one_le_left zero_le one_le_two
    · -- Inductive step: round `a` up to `2 * a'` and `b` down to `2 * b'` inside `[a, b]`.
      let a' := (a + 1) / 2
      let b' := b / 2
      have : N * 2 ^ (r + (d + 1)) = 2 * (N * 2 ^ (r + d)) := by rw [← add_assoc, pow_succ]; ring
      have : 2 * 2 ^ (d + 1) = 4 * 2 ^ d := by rw [pow_succ]; ring
      have hleft : edist (f (dyadicNNRat (r + (d + 1)) a)) (f (dyadicNNRat (r + d) a')) ≤
          (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ (r + (d + 1))) ^ (γ : ℝ) := by
        rw [← add_assoc, ← dyadicNNRat_double (r + d) a', add_assoc]
        exact edist_dyadicNNRat_step hadj (by omega) (by omega)
      have hright : edist (f (dyadicNNRat (r + d) b')) (f (dyadicNNRat (r + (d + 1)) b)) ≤
          (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ (r + (d + 1))) ^ (γ : ℝ) := by
        rw [← add_assoc, ← dyadicNNRat_double (r + d) b', add_assoc]
        exact edist_dyadicNNRat_step hadj hb (by omega)
      calc edist (f (dyadicNNRat (r + (d + 1)) a)) (f (dyadicNNRat (r + (d + 1)) b))
          ≤ edist (f (dyadicNNRat (r + (d + 1)) a)) (f (dyadicNNRat (r + d) a')) +
              edist (f (dyadicNNRat (r + d) a')) (f (dyadicNNRat (r + d) b')) +
              edist (f (dyadicNNRat (r + d) b')) (f (dyadicNNRat (r + (d + 1)) b)) :=
            edist_triangle4 ..
        _ ≤ _ := add_le_add (add_le_add hleft (ih a' b' (by omega) (by omega) (by omega))) hright
        _ = _ := by ring

/-- Geometric series bound for the dyadic chaining tail in `ℝ≥0∞`. -/
private lemma two_mul_sum_edist_dyadic_le {r d : ℕ} {K γ : ℝ≥0} (hγ : 0 < γ) :
    2 * (K : ℝ≥0∞) * ∑ i ∈ Finset.range (d + 1), ((2⁻¹ : ℝ≥0∞) ^ (r + i)) ^ (γ : ℝ) ≤
      ((2 * K * (1 - (2⁻¹ : ℝ≥0) ^ (γ : ℝ))⁻¹ : ℝ≥0) : ℝ≥0∞) *
        ((2⁻¹ : ℝ≥0∞) ^ r) ^ (γ : ℝ) := by
  set ρ : ℝ≥0 := (2⁻¹ : ℝ≥0) ^ (γ : ℝ)
  have hρ1 : ρ < 1 := NNReal.rpow_lt_one (by norm_num) hγ
  have hρ_coe : (ρ : ℝ≥0∞) = (2⁻¹ : ℝ≥0∞) ^ (γ : ℝ) := by
    rw [ENNReal.coe_rpow_of_nonneg _ γ.coe_nonneg]
    simp
  have hrew (i : ℕ) :
      ((2⁻¹ : ℝ≥0∞) ^ (r + i)) ^ (γ : ℝ) = ((2⁻¹ : ℝ≥0∞) ^ r) ^ (γ : ℝ) * (ρ : ℝ≥0∞) ^ i := by
    rw [pow_add, ENNReal.mul_rpow_of_nonneg _ _ γ.coe_nonneg, ENNReal.pow_rpow_comm _ i, hρ_coe]
  simp_rw [hrew, ← Finset.mul_sum]
  have hgeom : ∑ i ∈ Finset.range (d + 1), (ρ : ℝ≥0∞) ^ i ≤ ((1 - ρ)⁻¹ : ℝ≥0) := by
    calc ∑ i ∈ Finset.range (d + 1), (ρ : ℝ≥0∞) ^ i
        ≤ ∑' i : ℕ, (ρ : ℝ≥0∞) ^ i := sum_le_tsum _
      _ = (1 - (ρ : ℝ≥0∞))⁻¹ := ENNReal.tsum_geometric _
      _ = ((1 - ρ)⁻¹ : ℝ≥0) := by
          rw [ENNReal.coe_inv (tsub_pos_of_lt hρ1).ne', ENNReal.coe_sub, ENNReal.coe_one]
  calc 2 * (K : ℝ≥0∞) * (((2⁻¹ : ℝ≥0∞) ^ r) ^ (γ : ℝ) * ∑ i ∈ Finset.range (d + 1), (ρ : ℝ≥0∞) ^ i)
      ≤ 2 * (K : ℝ≥0∞) * (((2⁻¹ : ℝ≥0∞) ^ r) ^ (γ : ℝ) * ((1 - ρ)⁻¹ : ℝ≥0)) := by gcongr
    _ = ((2 * K * (1 - ρ)⁻¹ : ℝ≥0) : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ r) ^ (γ : ℝ) := by
        push_cast; ring

/-- Symmetric form of binary dyadic chaining at common level `r + d`. -/
private lemma edist_dyadicNNRat_le_of_abs_sub_le {E : Type*} [PseudoEMetricSpace E]
    {f : ℚ≥0 → E} {N r d : ℕ} {K γ : ℝ≥0} (hγ : 0 < γ)
    (hadj : ∀ l : ℕ, ∀ k < N * 2 ^ l,
      edist (f (dyadicNNRat l k)) (f (dyadicNNRat l (k + 1))) ≤
        (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ l) ^ (γ : ℝ))
    {b₁ b₂ : ℕ} (hb₁ : b₁ ≤ N * 2 ^ (r + d)) (hb₂ : b₂ ≤ N * 2 ^ (r + d))
    (hbd : |(b₁ : ℝ) - b₂| ≤ 2 * (2 : ℝ) ^ d) :
    edist (f (dyadicNNRat (r + d) b₁)) (f (dyadicNNRat (r + d) b₂)) ≤
      ((2 * K * (1 - (2⁻¹ : ℝ≥0) ^ (γ : ℝ))⁻¹ : ℝ≥0) : ℝ≥0∞) *
        ((2⁻¹ : ℝ≥0∞) ^ r) ^ (γ : ℝ) := by
  wlog hle : b₁ ≤ b₂ generalizing b₁ b₂
  · rw [edist_comm]
    exact this hb₂ hb₁ (by rwa [abs_sub_comm]) (le_of_not_ge hle)
  have hba : b₂ - b₁ ≤ 2 * 2 ^ d := by
    refine Nat.cast_le (α := ℝ).mp ?_
    rw [Nat.cast_sub hle]
    push_cast
    linarith [le_abs_self ((b₂ : ℝ) - b₁), abs_sub_comm (b₁ : ℝ) b₂]
  exact (edist_dyadicNNRat_le_sum hadj d b₁ b₂ hle hb₂ hba).trans
    (two_mul_sum_edist_dyadic_le hγ)

/-- Short-range Hölder estimate on dyadic rationals in `[0, N]` at distance `< 1`. -/
private lemma edist_dyadicNNRat_le_of_dist_lt_one {E : Type*} [PseudoEMetricSpace E]
    {f : ℚ≥0 → E} {N : ℕ} {K γ : ℝ≥0} (hγ : 0 < γ)
    (hadj : ∀ l : ℕ, ∀ k < N * 2 ^ l,
      edist (f (dyadicNNRat l k)) (f (dyadicNNRat l (k + 1))) ≤
        (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ l) ^ (γ : ℝ))
    {n₁ k₁ n₂ k₂ : ℕ} (hk₁ : k₁ ≤ N * 2 ^ n₁) (hk₂ : k₂ ≤ N * 2 ^ n₂)
    (hdist : dist (dyadicNNRat n₁ k₁ : ℝ≥0) (dyadicNNRat n₂ k₂ : ℝ≥0) < 1) :
    edist (f (dyadicNNRat n₁ k₁)) (f (dyadicNNRat n₂ k₂)) ≤
      ((2 * K * (1 - (2⁻¹ : ℝ≥0) ^ (γ : ℝ))⁻¹ : ℝ≥0) : ℝ≥0∞) *
        edist (dyadicNNRat n₁ k₁ : ℝ≥0) (dyadicNNRat n₂ k₂ : ℝ≥0) ^ (γ : ℝ) := by
  set δ := dist (dyadicNNRat n₁ k₁ : ℝ≥0) (dyadicNNRat n₂ k₂ : ℝ≥0) with hδ
  rcases eq_or_lt_of_le (dist_nonneg : 0 ≤ δ) with hδ0 | hδ_pos
  · have hq : dyadicNNRat n₁ k₁ = dyadicNNRat n₂ k₂ :=
      NNRat.cast_injective (dist_eq_zero.mp hδ0.symm)
    simp [hq]
  · obtain ⟨m, hm_lo, hm_hi⟩ :=
      exists_nat_pow_near_of_lt_one hδ_pos hdist.le (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num)
    let r := m + 1
    -- Express both dyadics at the common level `r + (n₁ + n₂)`.
    let d := n₁ + n₂
    let a₁ := k₁ * 2 ^ (r + n₂)
    let a₂ := k₂ * 2 ^ (r + n₁)
    have heq₁ : dyadicNNRat (r + d) a₁ = dyadicNNRat n₁ k₁ := by
      have : r + d = n₁ + (r + n₂) := by omega
      rw [this]; exact dyadicNNRat_scale n₁ (r + n₂) k₁
    have heq₂ : dyadicNNRat (r + d) a₂ = dyadicNNRat n₂ k₂ := by
      have : r + d = n₂ + (r + n₁) := by omega
      rw [this]; exact dyadicNNRat_scale n₂ (r + n₁) k₂
    have ha₁ : a₁ ≤ N * 2 ^ (r + d) := by
      have : r + d = n₁ + (r + n₂) := by omega
      rw [this, pow_add, ← mul_assoc]; exact Nat.mul_le_mul_right _ hk₁
    have ha₂ : a₂ ≤ N * 2 ^ (r + d) := by
      have : r + d = n₂ + (r + n₁) := by omega
      rw [this, pow_add, ← mul_assoc]; exact Nat.mul_le_mul_right _ hk₂
    have hdiff : |(a₁ : ℝ) - a₂| ≤ 2 * (2 : ℝ) ^ d := by
      have hδ_eq : δ = |(a₁ : ℝ) - a₂| / 2 ^ (r + d) := by
        rw [hδ, ← heq₁, ← heq₂, NNReal.dist_eq, coe_dyadicNNRat, coe_dyadicNNRat]
        push_cast
        rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (r + d))]
      have hle : |(a₁ : ℝ) - a₂| ≤ (2 : ℝ)⁻¹ ^ m * 2 ^ (r + d) :=
        (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (r + d))).mp (hδ_eq ▸ hm_hi)
      have hcancel : (2 : ℝ)⁻¹ ^ m * 2 ^ (r + d) = 2 * (2 : ℝ) ^ d := by
        simp only [r, pow_add, pow_succ, inv_pow]
        field_simp
      linarith
    have hchain := edist_dyadicNNRat_le_of_abs_sub_le hγ hadj ha₁ ha₂ hdiff
    rw [← heq₁, ← heq₂]
    refine hchain.trans ?_
    have hr_lo_e : (2⁻¹ : ℝ≥0∞) ^ r ≤
        edist (dyadicNNRat (r + d) a₁ : ℝ≥0) (dyadicNNRat (r + d) a₂ : ℝ≥0) := by
      rw [heq₁, heq₂, edist_dist]
      calc (2⁻¹ : ℝ≥0∞) ^ r
          = ENNReal.ofReal ((2 : ℝ)⁻¹ ^ r) := by
              rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos zero_lt_two,
                ENNReal.ofReal_ofNat]
        _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hm_lo.le
    gcongr

/-- Uniform extended-distance bound from `f 0` to any dyadic grid point in `[0, N]`. -/
private lemma edist_dyadicNNRat_zero_le {E : Type*} [PseudoEMetricSpace E]
    {f : ℚ≥0 → E} {N : ℕ} {K γ : ℝ≥0} (hγ : 0 < γ)
    (hadj : ∀ l : ℕ, ∀ k < N * 2 ^ l,
      edist (f (dyadicNNRat l k)) (f (dyadicNNRat l (k + 1))) ≤
        (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ l) ^ (γ : ℝ))
    {n k : ℕ} (hk : k ≤ N * 2 ^ n) :
    edist (f 0) (f (dyadicNNRat n k)) ≤
      ((N * K + 2 * K * (1 - (2⁻¹ : ℝ≥0) ^ (γ : ℝ))⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  have hcoarse (l : ℕ) (hl : l ≤ N) : edist (f 0) (f (dyadicNNRat 0 l)) ≤ l * (K : ℝ≥0∞) := by
    induction l with
    | zero => simp
    | succ l ih =>
      have hstep : edist (f (dyadicNNRat 0 l)) (f (dyadicNNRat 0 (l + 1))) ≤ K := by
        simpa using hadj 0 l (by simpa using Nat.lt_of_succ_le hl)
      calc edist (f 0) (f (dyadicNNRat 0 (l + 1)))
          ≤ edist (f 0) (f (dyadicNNRat 0 l)) +
              edist (f (dyadicNNRat 0 l)) (f (dyadicNNRat 0 (l + 1))) := edist_triangle ..
        _ ≤ l * (K : ℝ≥0∞) + K := add_le_add (ih (Nat.le_of_succ_le hl)) hstep
        _ = ((l + 1 : ℕ) : ℝ≥0∞) * K := by push_cast; ring
  let j := ⌊((dyadicNNRat n k : ℝ≥0) : ℝ)⌋₊
  have hjN : j ≤ N := Nat.floor_le_of_le (by exact_mod_cast coe_dyadicNNRat_le_natCast_iff.2 hk)
  have hdist_lt : dist (dyadicNNRat 0 j : ℝ≥0) (dyadicNNRat n k : ℝ≥0) < 1 := by
    rw [NNReal.dist_eq, dyadicNNRat_zero_left, abs_sub_comm]
    have hle : (j : ℝ) ≤ ((dyadicNNRat n k : ℝ≥0) : ℝ) := Nat.floor_le (by positivity)
    have hlt : ((dyadicNNRat n k : ℝ≥0) : ℝ) < (j : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [NNRat.cast_natCast, NNReal.coe_natCast, abs_of_nonneg (sub_nonneg.2 hle)]
    linarith
  have hed_le : edist (dyadicNNRat 0 j : ℝ≥0) (dyadicNNRat n k : ℝ≥0) ^ (γ : ℝ) ≤ 1 := by
    refine ENNReal.rpow_le_one ?_ γ.coe_nonneg
    rw [edist_dist, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hdist_lt.le
  have hnear : edist (f (dyadicNNRat 0 j)) (f (dyadicNNRat n k)) ≤
      ((2 * K * (1 - (2⁻¹ : ℝ≥0) ^ (γ : ℝ))⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    have h := edist_dyadicNNRat_le_of_dist_lt_one hγ hadj (by simpa using hjN) hk hdist_lt
    exact h.trans (mul_le_of_le_one_right' hed_le)
  calc edist (f 0) (f (dyadicNNRat n k))
      ≤ edist (f 0) (f (dyadicNNRat 0 j)) +
          edist (f (dyadicNNRat 0 j)) (f (dyadicNNRat n k)) := edist_triangle ..
    _ ≤ j * (K : ℝ≥0∞) + ((2 * K * (1 - (2⁻¹ : ℝ≥0) ^ (γ : ℝ))⁻¹ : ℝ≥0) : ℝ≥0∞) :=
        add_le_add (hcoarse j hjN) hnear
    _ ≤ ((N * K + 2 * K * (1 - (2⁻¹ : ℝ≥0) ^ (γ : ℝ))⁻¹ : ℝ≥0) : ℝ≥0∞) := by
        push_cast; gcongr

/-- **Deterministic dyadic Hölder extension on `[0, N]`.** If `f : ℚ≥0 → E` into a complete
extended metric space satisfies adjacent level-`l` dyadic increment bounds
`edist (f (dyadicNNRat l k)) (f (dyadicNNRat l (k + 1))) ≤ K * (2⁻ˡ) ^ γ` for all `k < N * 2 ^ l`
with `0 < γ`, then `f` extends from dyadic rationals in `[0, N]` to a `γ`-Hölder map on
`Iic (N : ℝ≥0)`. -/
theorem exists_holderWith_Iic_of_edist_dyadicNNRat_succ_le {E : Type*} [EMetricSpace E]
    [CompleteSpace E] {f : ℚ≥0 → E} {N : ℕ} {K γ : ℝ≥0} (hγ : 0 < γ)
    (hadj : ∀ l : ℕ, ∀ k < N * 2 ^ l,
      edist (f (dyadicNNRat l k)) (f (dyadicNNRat l (k + 1))) ≤
        (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ l) ^ (γ : ℝ)) :
    ∃ (C : ℝ≥0) (g : Iic (N : ℝ≥0) → E), HolderWith C γ g ∧
      ∀ n k (hk : k ≤ N * 2 ^ n),
        g ⟨(dyadicNNRat n k : ℝ≥0), coe_dyadicNNRat_le_natCast_iff.2 hk⟩ = f (dyadicNNRat n k) := by
  classical
  let s : Set (Iic (N : ℝ≥0)) :=
    {x | ∃ q : ℚ≥0, (∃ n k : ℕ, k ≤ N * 2 ^ n ∧ q = dyadicNNRat n k) ∧ (x : ℝ≥0) = q}
  have hs_dense : Dense s := fun x ↦ mem_closure_iff_seq_limit.2
    ⟨fun n ↦ ⟨(approxDyadicNNRat n x.val : ℝ≥0),
        (coe_approxDyadicNNRat_le n x.val).trans x.property⟩,
      fun n ↦ ⟨approxDyadicNNRat n x.val,
        ⟨n, ⌊(x.val : ℝ) * 2 ^ n⌋₊,
          coe_dyadicNNRat_le_natCast_iff.1
            (approxDyadicNNRat_def n x.val ▸ (coe_approxDyadicNNRat_le n x.val).trans x.property),
          approxDyadicNNRat_def n x.val⟩, rfl⟩,
      tendsto_subtype_rng.2 (tendsto_approxDyadicNNRat x.val)⟩
  let F : Iic (N : ℝ≥0) → E := fun x ↦ if hx : x ∈ s then f hx.choose else f 0
  have hF_eq {x : Iic (N : ℝ≥0)} {n k : ℕ} (hk : k ≤ N * 2 ^ n)
      (hxq : (x : ℝ≥0) = dyadicNNRat n k) : F x = f (dyadicNNRat n k) := by
    have hx : x ∈ s := ⟨dyadicNNRat n k, ⟨n, k, hk, rfl⟩, hxq⟩
    simp only [F, hx, ↓reduceDIte]
    exact congrArg f (NNRat.cast_injective (hx.choose_spec.2.symm.trans hxq))
  set C₀ : ℝ≥0 := 2 * K * (1 - (2⁻¹ : ℝ≥0) ^ (γ : ℝ))⁻¹
  set C : ℝ≥0 := 2 * (N * K + C₀)
  have hC₀_le : C₀ ≤ C :=
    calc C₀ ≤ N * K + C₀ := le_add_self
      _ ≤ 2 * (N * K + C₀) := le_mul_of_one_le_left zero_le one_le_two
  have hholder_s : HolderOnWith C γ F s := by
    rintro x ⟨_, ⟨n₁, k₁, hk₁, rfl⟩, hxq⟩ y ⟨_, ⟨n₂, k₂, hk₂, rfl⟩, hyq⟩
    have hed : edist x y = edist (dyadicNNRat n₁ k₁ : ℝ≥0) (dyadicNNRat n₂ k₂ : ℝ≥0) := by
      rw [Subtype.edist_eq, hxq, hyq]
    rw [hF_eq hk₁ hxq, hF_eq hk₂ hyq, hed]
    rcases lt_or_ge (dist (dyadicNNRat n₁ k₁ : ℝ≥0) (dyadicNNRat n₂ k₂ : ℝ≥0)) 1 with hlt | hge
    · exact (edist_dyadicNNRat_le_of_dist_lt_one hγ hadj hk₁ hk₂ hlt).trans (by gcongr)
    · have h1_le : (1 : ℝ≥0∞) ≤
          edist (dyadicNNRat n₁ k₁ : ℝ≥0) (dyadicNNRat n₂ k₂ : ℝ≥0) ^ (γ : ℝ) := by
        refine ENNReal.one_le_rpow ?_ hγ
        rw [edist_dist, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hge
      calc edist (f (dyadicNNRat n₁ k₁)) (f (dyadicNNRat n₂ k₂))
          ≤ edist (f 0) (f (dyadicNNRat n₁ k₁)) + edist (f 0) (f (dyadicNNRat n₂ k₂)) :=
            edist_triangle_left ..
        _ ≤ ((N * K + C₀ : ℝ≥0) : ℝ≥0∞) + ((N * K + C₀ : ℝ≥0) : ℝ≥0∞) :=
            add_le_add (edist_dyadicNNRat_zero_le hγ hadj hk₁)
              (edist_dyadicNNRat_zero_le hγ hadj hk₂)
        _ = (C : ℝ≥0∞) := by simp only [C, two_mul, ENNReal.coe_add]
        _ ≤ (C : ℝ≥0∞) * edist (dyadicNNRat n₁ k₁ : ℝ≥0) (dyadicNNRat n₂ k₂ : ℝ≥0) ^ (γ : ℝ) :=
            le_mul_of_one_le_right zero_le h1_le
  obtain ⟨g, hg_holder, hg_eq⟩ := hholder_s.extend_of_dense hs_dense
  refine ⟨C, g, hg_holder, fun n k hk ↦ ?_⟩
  exact (hg_eq ⟨dyadicNNRat n k, ⟨n, k, hk, rfl⟩, rfl⟩).symm.trans (hF_eq hk rfl)

end TauCeti
