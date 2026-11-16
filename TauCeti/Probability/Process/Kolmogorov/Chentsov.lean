/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Data.NNRat.Encodable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Instances.Rat
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.Probability.Process.Kolmogorov.Edges
import TauCeti.Topology.Instances.NNReal.DyadicGrid
import TauCeti.Topology.MetricSpace.Holder

/-!
# The one-dimensional Kolmogorov–Chentsov continuous modification theorem

Given a stochastic process `X` indexed by nonnegative times (`ℚ≥0` or `ℝ≥0`) with values in a
complete extended metric Borel space `E` and satisfying a local Kolmogorov moment bound of
exponents `p > 0` and `q > 1` on each compact horizon `[0, N]`,
`∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤ M N * edist s t ^ q`, this file constructs a process
`Y : ℝ≥0 → Ω → E` such that:

* each coordinate `Y t` is Borel measurable;
* every sample path `t ↦ Y t ω` is continuous;
* `Y` agrees almost everywhere with `X` at each time;
* every sample path `t ↦ Y t ω` is simultaneously `γ`-Hölder continuous on `Iic T` for all
  `γ : ℝ≥0` with `(γ : ℝ) < (q - 1) / p` and all `T : ℝ≥0`.

No finiteness or completeness hypothesis on `P` and no separability hypothesis on `E` is required.
The construction builds on Mathlib's `ProbabilityTheory.IsKolmogorovProcess` and
`IsAEKolmogorovProcess` together with `TauCeti.Probability.Process.Kolmogorov.Edges`,
`TauCeti.Topology.Instances.NNReal.DyadicGrid`, and `HolderOnWith.extend_of_dense`.

## Main results

* `TauCeti.exists_continuous_extension_of_nnrat`: extends a process on `ℚ≥0` satisfying local
  Kolmogorov bounds to an all-paths continuous, coordinatewise measurable, locally Hölder process
  on `ℝ≥0`.
* `TauCeti.exists_continuous_modification_of_local_isAEKolmogorovProcess`: local
  Kolmogorov–Chentsov modification theorem on `ℝ≥0` for locally `IsAEKolmogorovProcess` processes.
* `ProbabilityTheory.IsKolmogorovProcess.exists_continuous_modification` and
  `ProbabilityTheory.IsAEKolmogorovProcess.exists_continuous_modification`: global specializations.

## References

* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Springer, 2021, Theorem 4.23.
* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991,
  Theorem 2.2.8.
* D. Revuz, M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Springer, 1999,
  Theorem I.2.1.
-/

public section

noncomputable section

open Filter MeasureTheory Metric ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

namespace TauCeti

section DyadicChaining

private lemma floor_mul_two_pow_le {N : ℕ} {t : ℝ≥0} (ht : t ≤ N) (n : ℕ) :
    ⌊(t : ℝ) * 2 ^ n⌋₊ ≤ N * 2 ^ n := by
  refine Nat.floor_le_of_le ?_
  have ht' : (t : ℝ) ≤ N := by exact_mod_cast ht
  calc (t : ℝ) * 2 ^ n ≤ (N : ℝ) * 2 ^ n := by gcongr
    _ = ((N * 2 ^ n : ℕ) : ℝ) := by push_cast; ring

/-- Any `δ ∈ (0, 1)` lies in `[2⁻ʳ, 2 · 2⁻ʳ)` for some positive dyadic scale `r : ℕ`. -/
private lemma exists_dyadic_scale {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ r : ℕ, 1 ≤ r ∧ (2 : ℝ)⁻¹ ^ r ≤ δ ∧ δ < 2 * (2 : ℝ)⁻¹ ^ r := by
  obtain ⟨z, hlo, hhi⟩ := exists_mem_Ico_zpow hδ0 one_lt_two
  have hz_neg : z < 0 := by
    by_contra! hge
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ z := by
      simpa using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hge
    linarith
  set r : ℕ := (-z).toNat
  have hz_eq : z = -(r : ℤ) := by omega
  refine ⟨r, by omega, ?_, ?_⟩
  · simpa [hz_eq, zpow_neg, zpow_natCast, inv_pow] using hlo
  · have hpow : (2 : ℝ) ^ (z + 1) = 2 * (2 : ℝ)⁻¹ ^ r := by
      rw [zpow_add₀ two_ne_zero, zpow_one, hz_eq, zpow_neg, zpow_natCast, inv_pow, mul_comm]
    linarith

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
  · obtain ⟨r, _, hr_lo, hr_hi⟩ := exists_dyadic_scale hδ_pos hdist
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
      have hlt : |(a₁ : ℝ) - a₂| < 2 * (2 : ℝ)⁻¹ ^ r * 2 ^ (r + d) :=
        (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ (r + d))).mp (by linarith [hδ_eq, hr_hi])
      have hcancel : 2 * (2 : ℝ)⁻¹ ^ r * 2 ^ (r + d) = 2 * (2 : ℝ) ^ d := by
        rw [pow_add, inv_pow]; field_simp
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
        _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hr_lo
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
  have hjN : j ≤ N := by
    have hle : (dyadicNNRat n k : ℝ≥0) ≤ N := coe_dyadicNNRat_le_natCast_iff.2 hk
    simpa only [j, pow_zero, mul_one] using floor_mul_two_pow_le hle 0
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

/-- Deterministic dyadic Hölder extension on `[0, N]`: if `f : ℚ≥0 → E` into a complete extended
metric space has adjacent level-`l` increments on `[0, N]` bounded by `K * (2⁻ˡ) ^ γ`, then `f`
extends from dyadic rationals in `[0, N]` to a `γ`-Hölder map on `Iic (N : ℝ≥0)`. -/
private lemma exists_holderWith_Iic_of_dyadic_adj {E : Type*} [EMetricSpace E] [CompleteSpace E]
    {f : ℚ≥0 → E} {N : ℕ} {K γ : ℝ≥0} (hγ : 0 < γ)
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
    ⟨fun n ↦ ⟨(approxDyadicNNRat n x.1 : ℝ≥0), (coe_approxDyadicNNRat_le n x.1).trans x.2⟩,
      fun n ↦ ⟨approxDyadicNNRat n x.1,
        ⟨n, ⌊(x.1 : ℝ) * 2 ^ n⌋₊, floor_mul_two_pow_le x.2 n, approxDyadicNNRat_def n x.1⟩, rfl⟩,
      tendsto_subtype_rng.2 (tendsto_approxDyadicNNRat x.1)⟩
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

/-- If `g : Iic (N : ℝ≥0) → E` is continuous and agrees with `f : ℚ≥0 → E` on dyadic rationals,
then `f (approxDyadicNNRat n t)` converges to `g t`. -/
private lemma tendsto_approxDyadicNNRat_apply_of_continuous {E : Type*} [TopologicalSpace E]
    {N : ℕ} {f : ℚ≥0 → E} {g : Iic (N : ℝ≥0) → E} (hg_cont : Continuous g)
    (hg_dyad : ∀ n k (hk : k ≤ N * 2 ^ n),
      g ⟨(dyadicNNRat n k : ℝ≥0), coe_dyadicNNRat_le_natCast_iff.2 hk⟩ = f (dyadicNNRat n k))
    (t : Iic (N : ℝ≥0)) :
    Tendsto (fun n ↦ f (approxDyadicNNRat n t.1)) atTop (𝓝 (g t)) := by
  have hconv : Tendsto (fun n ↦ (⟨(approxDyadicNNRat n t.1 : ℝ≥0),
      (coe_approxDyadicNNRat_le n t.1).trans t.2⟩ : Iic (N : ℝ≥0))) atTop (𝓝 t) :=
    tendsto_subtype_rng.2 (tendsto_approxDyadicNNRat t.1)
  refine (hg_cont.tendsto t).comp hconv |>.congr fun n ↦ ?_
  simp only [Function.comp_apply, approxDyadicNNRat_def]
  exact hg_dyad n ⌊(t.1 : ℝ) * 2 ^ n⌋₊ (floor_mul_two_pow_le t.2 n)

end DyadicChaining

section StochasticExtension

private lemma edist_nnrat_coe (r s : ℚ≥0) :
    edist r s = edist (r : ℝ≥0) (s : ℝ≥0) := by
  rw [edist_dist, edist_dist, NNRat.dist_eq, Rat.dist_eq, NNReal.dist_eq]
  have hcast (q : ℚ≥0) : ((q : ℝ≥0) : ℝ) = ((q : ℚ) : ℝ) := by
    have h1 := map_nnratCast NNReal.toRealHom q
    have h2 := map_nnratCast (Rat.castHom ℝ) q
    exact h1.trans h2.symm
  rw [hcast r, hcast s]

/-- The measurable event on which every adjacent dyadic increment in `[0, N]` at every level `n`
is bounded by `K * (2⁻ⁿ) ^ γ` for some `K : ℕ`. -/
private def goodDyadicEvent {Ω E : Type*} [PseudoEMetricSpace E] (X : ℚ≥0 → Ω → E)
    (N : ℕ) (γ : ℝ≥0) : Set Ω :=
  ⋃ K : ℕ, ⋂ n : ℕ, ⋂ k : Fin (N * 2 ^ n),
    {ω | edist (X (dyadicNNRat n k) ω) (X (dyadicNNRat n (k + 1)) ω) ≤
      (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ n) ^ (γ : ℝ)}

private lemma measurableSet_goodDyadicEvent {Ω E : Type*} {_ : MeasurableSpace Ω}
    [PseudoEMetricSpace E] {X : ℚ≥0 → Ω → E}
    (hedist : ∀ r s : ℚ≥0, Measurable fun ω ↦ edist (X r ω) (X s ω))
    (N : ℕ) (γ : ℝ≥0) :
    MeasurableSet (goodDyadicEvent X N γ) :=
  MeasurableSet.iUnion fun _ ↦ MeasurableSet.iInter fun _ ↦ MeasurableSet.iInter fun _ ↦
    measurableSet_le (hedist _ _) measurable_const

/-- Via `IsAEKolmogorovProcess.ae_exists_edist_le_mul_pow_rpow`, almost every sample path belongs
to `goodDyadicEvent X N γ` whenever `(γ : ℝ) < (q - 1) / p`. -/
private lemma ae_mem_goodDyadicEvent {Ω E : Type*} {_ : MeasurableSpace Ω}
    [PseudoEMetricSpace E] {P : Measure Ω} {X : ℚ≥0 → Ω → E} {p q : ℝ} {M : ℝ≥0} {N : ℕ}
    {γ : ℝ≥0} (hγ : (γ : ℝ) < (q - 1) / p)
    (hX : IsAEKolmogorovProcess (fun r : {r : ℚ≥0 // (r : ℝ≥0) ≤ N} ↦ X r.1) P p q M) :
    ∀ᵐ ω ∂P, ω ∈ goodDyadicEvent X N γ := by
  have hp := hX.p_pos
  have hcard (n : ℕ) :
      ((N * 2 ^ n : ℕ) : ℝ≥0) ≤ (N : ℝ≥0) * ((2⁻¹ : ℝ≥0) ^ (-(1 : ℝ))) ^ n := by
    have h2 : (2⁻¹ : ℝ≥0) ^ (-(1 : ℝ)) = 2 := by
      rw [NNReal.rpow_neg, NNReal.rpow_one, inv_inv]
    rw [h2]
    push_cast
    exact le_rfl
  have hedge (n : ℕ) (i : Fin (N * 2 ^ n)) :
      edist
        (⟨dyadicNNRat n i, coe_dyadicNNRat_le_natCast_iff.2 i.2.le⟩ :
          {r : ℚ≥0 // (r : ℝ≥0) ≤ N})
        (⟨dyadicNNRat n (i + 1), coe_dyadicNNRat_le_natCast_iff.2 i.2⟩ :
          {r : ℚ≥0 // (r : ℝ≥0) ≤ N}) ≤ ((2⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n := by
    rw [Subtype.edist_eq, edist_nnrat_coe, edist_dyadicNNRat_succ]
    simp
  have hγ' : 1 + p * (γ : ℝ) < q := by
    have : (γ : ℝ) * p < q - 1 := (lt_div_iff₀ hp).mp hγ
    linarith
  filter_upwards [hX.ae_exists_edist_le_mul_pow_rpow (C := N) (r := 2⁻¹) (d := 1) (γ := (γ : ℝ))
    (by norm_num) (by norm_num) hcard hedge hγ'] with ω ⟨K, hK⟩
  refine mem_iUnion.2 ⟨⌈(K : ℝ)⌉₊, mem_iInter.2 fun n ↦ mem_iInter.2 fun i ↦ ?_⟩
  have hK_le : (K : ℝ≥0∞) ≤ (⌈(K : ℝ)⌉₊ : ℝ≥0∞) := by
    exact_mod_cast (Nat.le_ceil (K : ℝ))
  have hKi := hK n i
  simp only [ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat] at hKi
  exact hKi.trans (by gcongr)

/-- Along any sequence `u : ℕ → T` approaching `t` at rate `2⁻ⁿ`, an `IsAEKolmogorovProcess`
converges almost surely to `X t`. -/
private lemma ae_tendsto_of_edist_le {T Ω E : Type*} [PseudoEMetricSpace T]
    {_ : MeasurableSpace Ω} [EMetricSpace E] {P : Measure Ω} {X : T → Ω → E}
    {p q : ℝ} {M : ℝ≥0} (hX : IsAEKolmogorovProcess X P p q M)
    {u : ℕ → T} {t : T} (hu : ∀ n, edist (u n) t ≤ (2⁻¹ : ℝ≥0∞) ^ n) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ X (u n) ω) atTop (𝓝 (X t ω)) := by
  have hp := hX.p_pos
  have hq := hX.q_pos
  set β : ℝ := q / (2 * p)
  have hβ : 0 < β := by positivity
  have hcard (n : ℕ) : ((1 : ℕ) : ℝ≥0) ≤ 1 * ((2⁻¹ : ℝ≥0) ^ (-(0 : ℝ))) ^ n := by simp
  have hedge (n : ℕ) (_ : Fin 1) : edist (u n) t ≤ ((2⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n := by
    simpa using hu n
  have hβ_lt : 0 + p * β < q := by
    have : p * β = q / 2 := by simp only [β]; field_simp
    linarith
  filter_upwards [hX.ae_exists_edist_le_mul_pow_rpow (C := 1) (r := 2⁻¹) (d := 0) (γ := β)
    (k := fun _ ↦ 1) (s := fun n _ ↦ u n) (t := fun _ _ ↦ t)
    (by norm_num) (by norm_num) hcard hedge hβ_lt] with ω ⟨K, hK⟩
  rw [tendsto_iff_edist_tendsto_0]
  have hρ_lt : (2⁻¹ : ℝ≥0∞) ^ β < 1 :=
    ENNReal.rpow_lt_one (by norm_num) hβ
  have hlim : Tendsto (fun n : ℕ ↦ (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ n) ^ β) atTop (𝓝 0) := by
    simpa only [ENNReal.pow_rpow_comm, mul_zero] using
      ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hρ_lt)
        (Or.inr ENNReal.coe_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ zero_le)
    fun n ↦ ?_
  simpa using hK n 0

/-- On `goodDyadicEvent X N γ`, the rational path `r ↦ X r ω` extends from dyadic rationals in
`[0, N]` to a `γ`-Hölder map on `Iic (N : ℝ≥0)`. -/
private lemma exists_holderWith_Iic_of_mem_goodDyadicEvent {Ω E : Type*}
    [EMetricSpace E] [CompleteSpace E] {X : ℚ≥0 → Ω → E} {ω : Ω} {N : ℕ} {γ : ℝ≥0}
    (hγ_pos : 0 < γ) (hω : ω ∈ goodDyadicEvent X N γ) :
    ∃ (C : ℝ≥0) (g : Iic (N : ℝ≥0) → E), HolderWith C γ g ∧
      ∀ n k (hk : k ≤ N * 2 ^ n),
        g ⟨(dyadicNNRat n k : ℝ≥0), coe_dyadicNNRat_le_natCast_iff.2 hk⟩ =
          X (dyadicNNRat n k) ω := by
  obtain ⟨K, hK⟩ := mem_iUnion.mp hω
  refine exists_holderWith_Iic_of_dyadic_adj (f := fun r ↦ X r ω) (K := (K : ℝ≥0)) hγ_pos
    fun l k hk ↦ ?_
  simpa using mem_iInter.mp (mem_iInter.mp hK l) ⟨k, hk⟩

/-- Canonical pathwise dyadic limit on `G`, equal to the constant path `X 0 ω` outside `G`. -/
private def dyadicExtension {Ω E : Type*} [TopologicalSpace E] (X : ℚ≥0 → Ω → E)
    (G : Set Ω) [DecidablePred (· ∈ G)] (t : ℝ≥0) (ω : Ω) : E :=
  letI : Nonempty E := ⟨X 0 ω⟩
  limUnder atTop (fun n ↦ if ω ∈ G then X (approxDyadicNNRat n t) ω else X 0 ω)

private lemma dyadicExtension_eq_of_mem {Ω E : Type*} [TopologicalSpace E] [T2Space E]
    {X : ℚ≥0 → Ω → E} {G : Set Ω} [DecidablePred (· ∈ G)] {ω : Ω} (hω : ω ∈ G)
    {N : ℕ} {g : Iic (N : ℝ≥0) → E} (hg_cont : Continuous g)
    (hg_dyad : ∀ n k (hk : k ≤ N * 2 ^ n),
      g ⟨(dyadicNNRat n k : ℝ≥0), coe_dyadicNNRat_le_natCast_iff.2 hk⟩ = X (dyadicNNRat n k) ω)
    {t : ℝ≥0} (ht : t ≤ N) :
    dyadicExtension X G t ω = g ⟨t, ht⟩ := by
  let : Nonempty E := ⟨X 0 ω⟩
  exact ((tendsto_approxDyadicNNRat_apply_of_continuous (f := fun r ↦ X r ω)
    hg_cont hg_dyad ⟨t, ht⟩) |>.congr fun _ ↦ by simp [hω]).limUnder_eq

private lemma dyadicExtension_eq_of_notMem {Ω E : Type*} [TopologicalSpace E] [T2Space E]
    {X : ℚ≥0 → Ω → E} {G : Set Ω} [DecidablePred (· ∈ G)] {ω : Ω} (hω : ω ∉ G) (t : ℝ≥0) :
    dyadicExtension X G t ω = X 0 ω := by
  let : Nonempty E := ⟨X 0 ω⟩
  exact (tendsto_const_nhds.congr fun _ ↦ by simp [hω]).limUnder_eq

/-- On `G`, the dyadic approximations `X (approxDyadicNNRat n t) ω` converge to
`dyadicExtension X G t ω`. -/
private lemma tendsto_approxDyadicNNRat_dyadicExtension_of_mem {Ω E : Type*}
    [EMetricSpace E] [CompleteSpace E] {X : ℚ≥0 → Ω → E} {γ₀ : ℝ≥0} (hγ₀_pos : 0 < γ₀)
    {G : Set Ω} [DecidablePred (· ∈ G)]
    (hG_sub : ∀ ω ∈ G, ∀ N : ℕ, ω ∈ goodDyadicEvent X N γ₀)
    {ω : Ω} (hω : ω ∈ G) (t : ℝ≥0) :
    Tendsto (fun n ↦ X (approxDyadicNNRat n t) ω) atTop (𝓝 (dyadicExtension X G t ω)) := by
  let N := ⌈(t : ℝ)⌉₊
  have htN : t ≤ N := by exact_mod_cast Nat.le_ceil (t : ℝ)
  obtain ⟨_, g, hg_h, hg_d⟩ :=
    exists_holderWith_Iic_of_mem_goodDyadicEvent hγ₀_pos (hG_sub ω hω N)
  have hg_cont : Continuous g := (hg_h.uniformContinuous hγ₀_pos).continuous
  rw [dyadicExtension_eq_of_mem hω hg_cont hg_d htN]
  exact tendsto_approxDyadicNNRat_apply_of_continuous (f := fun r ↦ X r ω) hg_cont hg_d ⟨t, htN⟩

private lemma measurable_dyadicExtension {Ω E : Type*} {_ : MeasurableSpace Ω}
    [EMetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {X : ℚ≥0 → Ω → E} {γ₀ : ℝ≥0} (hγ₀_pos : 0 < γ₀) (hmeasX : ∀ r : ℚ≥0, Measurable (X r))
    {G : Set Ω} [DecidablePred (· ∈ G)] (hG_meas : MeasurableSet G)
    (hG_sub : ∀ ω ∈ G, ∀ N : ℕ, ω ∈ goodDyadicEvent X N γ₀) (t : ℝ≥0) :
    Measurable (dyadicExtension X G t) := by
  refine measurable_of_tendsto_metrizable
    (f := fun n ω ↦ if ω ∈ G then X (approxDyadicNNRat n t) ω else X 0 ω)
    (fun _ ↦ Measurable.ite hG_meas (hmeasX _) (hmeasX 0)) (tendsto_pi_nhds.2 fun ω ↦ ?_)
  by_cases hω : ω ∈ G
  · exact (tendsto_approxDyadicNNRat_dyadicExtension_of_mem hγ₀_pos hG_sub hω t).congr
      fun _ ↦ by simp [hω]
  · simp [hω, dyadicExtension_eq_of_notMem hω]

private lemma continuous_dyadicExtension {Ω E : Type*}
    [EMetricSpace E] [CompleteSpace E] {X : ℚ≥0 → Ω → E} {γ₀ : ℝ≥0} (hγ₀_pos : 0 < γ₀)
    {G : Set Ω} [DecidablePred (· ∈ G)]
    (hG_sub : ∀ ω ∈ G, ∀ N : ℕ, ω ∈ goodDyadicEvent X N γ₀) (ω : Ω) :
    Continuous (dyadicExtension X G · ω) := by
  by_cases hω : ω ∈ G
  · rw [continuous_iff_continuousAt]
    intro t
    let N := ⌊(t : ℝ)⌋₊ + 1
    have ht_lt : t < (N : ℝ≥0) := by exact_mod_cast Nat.lt_floor_add_one (t : ℝ)
    obtain ⟨_, g, hg_h, hg_d⟩ :=
      exists_holderWith_Iic_of_mem_goodDyadicEvent hγ₀_pos (hG_sub ω hω N)
    have hg_cont : Continuous g := (hg_h.uniformContinuous hγ₀_pos).continuous
    have hcon : ContinuousOn (dyadicExtension X G · ω) (Iic (N : ℝ≥0)) :=
      continuousOn_iff_continuous_domRestrict.mpr
        (hg_cont.congr fun s ↦ (dyadicExtension_eq_of_mem hω hg_cont hg_d s.2).symm)
    exact hcon.continuousAt (Iic_mem_nhds ht_lt)
  · have hconst : (dyadicExtension X G · ω) = fun _ ↦ X 0 ω :=
      funext fun t ↦ dyadicExtension_eq_of_notMem hω t
    rw [hconst]
    exact continuous_const

/-- For any rational time `r : ℚ≥0`, `dyadicExtension X G r` agrees almost everywhere with `X r`. -/
private lemma ae_eq_dyadicExtension_of_nnrat {Ω E : Type*} {_ : MeasurableSpace Ω}
    [EMetricSpace E] [CompleteSpace E] {P : Measure Ω} {X : ℚ≥0 → Ω → E}
    {p q : ℝ} {M : ℕ → ℝ≥0} {γ₀ : ℝ≥0} (hγ₀_pos : 0 < γ₀)
    {G : Set Ω} [DecidablePred (· ∈ G)] (hG_ae : ∀ᵐ ω ∂P, ω ∈ G)
    (hG_sub : ∀ ω ∈ G, ∀ N : ℕ, ω ∈ goodDyadicEvent X N γ₀)
    (hX_loc : ∀ N : ℕ, IsAEKolmogorovProcess (fun r : {r : ℚ≥0 // (r : ℝ≥0) ≤ N} ↦ X r.1)
      P p q (M N)) (r : ℚ≥0) :
    dyadicExtension X G r =ᵐ[P] X r := by
  let N := ⌈((r : ℝ≥0) : ℝ)⌉₊
  have hrN : (r : ℝ≥0) ≤ N := by exact_mod_cast Nat.le_ceil ((r : ℝ≥0) : ℝ)
  have hu (n : ℕ) :
      edist
        (⟨approxDyadicNNRat n (r : ℝ≥0), (coe_approxDyadicNNRat_le n _).trans hrN⟩ :
          {s : ℚ≥0 // (s : ℝ≥0) ≤ N})
        (⟨r, hrN⟩ : {s : ℚ≥0 // (s : ℝ≥0) ≤ N}) ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
    rw [Subtype.edist_eq, edist_nnrat_coe]
    exact edist_approxDyadicNNRat_le n (r : ℝ≥0)
  filter_upwards [hG_ae, ae_tendsto_of_edist_le (hX_loc N) hu] with ω hω hX_tend
  exact tendsto_nhds_unique
    (tendsto_approxDyadicNNRat_dyadicExtension_of_mem hγ₀_pos hG_sub hω r) hX_tend

/-- Every sample path of `dyadicExtension X G` is simultaneously `γ`-Hölder on `Iic T` for all
`γ < (q - 1) / p` and all `T : ℝ≥0`, provided `G` intersects `goodDyadicEvent X N (γSeq k)` for a
cofinal sequence `γSeq k ↑ (q - 1) / p`. -/
private lemma exists_holderOnWith_dyadicExtension {Ω E : Type*}
    [EMetricSpace E] [CompleteSpace E] {X : ℚ≥0 → Ω → E} {γSeq : ℕ → ℝ≥0}
    (hγSeq_pos : ∀ k, 0 < γSeq k) {α : ℝ}
    (hcofinal : ∀ γ : ℝ≥0, (γ : ℝ) < α → ∃ k, γ ≤ γSeq k)
    {G : Set Ω} [DecidablePred (· ∈ G)]
    (hG_sub : ∀ ω ∈ G, ∀ N k : ℕ, ω ∈ goodDyadicEvent X N (γSeq k))
    (ω : Ω) (γ : ℝ≥0) (hγ : (γ : ℝ) < α) (T : ℝ≥0) :
    ∃ C : ℝ≥0, HolderOnWith C γ (dyadicExtension X G · ω) (Iic T) := by
  by_cases hω : ω ∈ G
  · obtain ⟨k, hk⟩ := hcofinal γ hγ
    let N := ⌈(T : ℝ)⌉₊
    have hTN : T ≤ N := by exact_mod_cast Nat.le_ceil (T : ℝ)
    obtain ⟨C₁, g, hg_holder, hg_dyad⟩ :=
      exists_holderWith_Iic_of_mem_goodDyadicEvent (hγSeq_pos k) (hG_sub ω hω N k)
    have hg_cont : Continuous g := (hg_holder.uniformContinuous (hγSeq_pos k)).continuous
    have hholder_k : HolderOnWith C₁ (γSeq k) (dyadicExtension X G · ω) (Iic T) := by
      intro s hs t ht
      have hsN : s ≤ N := hs.trans hTN
      have htN : t ≤ N := ht.trans hTN
      dsimp only
      rw [dyadicExtension_eq_of_mem hω hg_cont hg_dyad hsN,
        dyadicExtension_eq_of_mem hω hg_cont hg_dyad htN]
      exact hg_holder ⟨s, hsN⟩ ⟨t, htN⟩
    have hdiam : ∀ s ∈ Iic T, ∀ t ∈ Iic T, edist s t ≤ (T : ℝ≥0∞) := fun s hs t ht ↦ by
      rw [edist_dist, NNReal.dist_eq, ← ENNReal.ofReal_coe_nnreal]
      refine ENNReal.ofReal_le_ofReal (abs_sub_le_iff.2 ⟨?_, ?_⟩)
      · have hs' : (s : ℝ) ≤ T := hs
        linarith [t.coe_nonneg]
      · have ht' : (t : ℝ) ≤ T := ht
        linarith [s.coe_nonneg]
    exact ⟨_, hholder_k.of_le hdiam hk⟩
  · refine ⟨0, fun s _ t _ ↦ ?_⟩
    dsimp only
    rw [dyadicExtension_eq_of_notMem hω s, dyadicExtension_eq_of_notMem hω t, edist_self]
    exact zero_le

/-- Every `γ < α` (with `0 < α`) is bounded by `((k + 1) / (k + 2)) * α` for some `k : ℕ`. -/
private lemma exists_ratio_mul_ge {α : ℝ} (hα : 0 < α) {γ : ℝ≥0} (hγ : (γ : ℝ) < α) :
    ∃ k : ℕ, (γ : ℝ) ≤ ((k + 1 : ℝ) / (k + 2 : ℝ)) * α := by
  set δ : ℝ := α - γ
  have hδ : 0 < δ := sub_pos.2 hγ
  refine ⟨⌈α / δ⌉₊, ?_⟩
  have hceil : α / δ < (⌈α / δ⌉₊ : ℝ) + 2 := (Nat.le_ceil _).trans_lt (by linarith)
  have hmul : α < δ * ((⌈α / δ⌉₊ : ℝ) + 2) := by
    rw [mul_comm]
    exact (div_lt_iff₀ hδ).mp hceil
  have hdiv : α / ((⌈α / δ⌉₊ : ℝ) + 2) < δ := (div_lt_iff₀ (by positivity)).2 hmul
  have hid :
      (((⌈α / δ⌉₊ : ℝ) + 1) / ((⌈α / δ⌉₊ : ℝ) + 2)) * α = α - α / ((⌈α / δ⌉₊ : ℝ) + 2) := by
    field_simp; ring
  linarith

/-- **Kolmogorov–Chentsov extension from nonnegative rational times.** Let `X : ℚ≥0 → Ω → E` take
values in a complete extended metric Borel space `E`, with Borel-measurable pair evaluations and a
local Kolmogorov bound of exponents `p > 0` and `q > 1` on each bounded horizon `[0, N]`. Then `X`
extends to a process `Y : ℝ≥0 → Ω → E` such that:

1. `Y t` is Borel measurable for every `t : ℝ≥0`;
2. `t ↦ Y t ω` is continuous for *every* `ω : Ω`;
3. `Y r =ᵐ[P] X r` for every `r : ℚ≥0`;
4. every path `t ↦ Y t ω` is simultaneously `γ`-Hölder continuous on `Iic T` for all `γ : ℝ≥0`
   with `(γ : ℝ) < (q - 1) / p` and all `T : ℝ≥0`. -/
theorem exists_continuous_extension_of_nnrat {Ω E : Type*} {_ : MeasurableSpace Ω}
    [EMetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {X : ℚ≥0 → Ω → E} {p q : ℝ} {M : ℕ → ℝ≥0}
    (hp : 0 < p) (hq : 1 < q)
    (hpair : ∀ r s : ℚ≥0, Measurable[_, borel (E × E)] fun ω ↦ (X r ω, X s ω))
    (hkol : ∀ (N : ℕ) (r s : ℚ≥0), (r : ℝ≥0) ≤ N → (s : ℝ≥0) ≤ N →
      ∫⁻ ω, edist (X r ω) (X s ω) ^ p ∂P ≤ M N * edist (r : ℝ≥0) (s : ℝ≥0) ^ q) :
    ∃ Y : ℝ≥0 → Ω → E,
      (∀ t : ℝ≥0, Measurable (Y t)) ∧
      (∀ ω : Ω, Continuous (Y · ω)) ∧
      (∀ r : ℚ≥0, Y r =ᵐ[P] X r) ∧
      (∀ (ω : Ω) (γ : ℝ≥0), (γ : ℝ) < (q - 1) / p → ∀ T : ℝ≥0,
        ∃ C : ℝ≥0, HolderOnWith C γ (Y · ω) (Iic T)) := by
  classical
  have hedist (r s : ℚ≥0) : Measurable fun ω ↦ edist (X r ω) (X s ω) := by
    borelize (E × E)
    exact continuous_edist.measurable.comp (hpair r s)
  have hmeasX (r : ℚ≥0) : Measurable (X r) :=
    (measurable_fst.mono prod_le_borel_prod le_rfl).comp (hpair r r)
  have hX_loc (N : ℕ) :
      IsAEKolmogorovProcess (fun r : {r : ℚ≥0 // (r : ℝ≥0) ≤ N} ↦ X r.1) P p q (M N) :=
    IsKolmogorovProcess.IsAEKolmogorovProcess
      { measurablePair := fun r s ↦ hpair r.1 s.1
        kolmogorovCondition := fun r s ↦ by
          simpa [Subtype.edist_eq, edist_nnrat_coe] using hkol N r.1 s.1 r.2 s.2
        p_pos := hp
        q_pos := zero_lt_one.trans hq }
  -- Intersect `goodDyadicEvent X N (γSeq k)` along `γSeq k ↑ (q - 1) / p`.
  have hα_pos : 0 < (q - 1) / p := div_pos (sub_pos.2 hq) hp
  let γSeq : ℕ → ℝ≥0 := fun k ↦ Real.toNNReal (((k + 1 : ℝ) / (k + 2 : ℝ)) * ((q - 1) / p))
  have hγSeq_coe (k : ℕ) : (γSeq k : ℝ) = ((k + 1 : ℝ) / (k + 2 : ℝ)) * ((q - 1) / p) :=
    Real.coe_toNNReal _ (by positivity)
  have hγSeq_pos (k : ℕ) : 0 < γSeq k := by
    rw [← NNReal.coe_pos, hγSeq_coe]
    positivity
  have hγSeq_lt (k : ℕ) : (γSeq k : ℝ) < (q - 1) / p := by
    rw [hγSeq_coe]
    exact mul_lt_of_lt_one_left hα_pos ((div_lt_one (by positivity)).2 (by linarith))
  have hcofinal (γ : ℝ≥0) (hγ : (γ : ℝ) < (q - 1) / p) : ∃ k, γ ≤ γSeq k := by
    obtain ⟨k, hk⟩ := exists_ratio_mul_ge hα_pos hγ
    exact ⟨k, NNReal.coe_le_coe.1 (by rwa [hγSeq_coe])⟩
  let G : Set Ω := ⋂ N : ℕ, ⋂ k : ℕ, goodDyadicEvent X N (γSeq k)
  have hG_meas : MeasurableSet G :=
    MeasurableSet.iInter fun N ↦ MeasurableSet.iInter fun k ↦
      measurableSet_goodDyadicEvent hedist N (γSeq k)
  have hG_ae : ∀ᵐ ω ∂P, ω ∈ G := by
    simp only [G, mem_iInter, ae_all_iff]
    exact fun N k ↦ ae_mem_goodDyadicEvent (hγSeq_lt k) (hX_loc N)
  have hG_sub (ω : Ω) (hω : ω ∈ G) (N k : ℕ) : ω ∈ goodDyadicEvent X N (γSeq k) :=
    mem_iInter.mp (mem_iInter.mp hω N) k
  exact ⟨dyadicExtension X G,
    measurable_dyadicExtension (hγSeq_pos 0) hmeasX hG_meas (fun ω hω N ↦ hG_sub ω hω N 0),
    continuous_dyadicExtension (hγSeq_pos 0) (fun ω hω N ↦ hG_sub ω hω N 0),
    ae_eq_dyadicExtension_of_nnrat (hγSeq_pos 0) hG_ae (fun ω hω N ↦ hG_sub ω hω N 0) hX_loc,
    exists_holderOnWith_dyadicExtension hγSeq_pos hcofinal hG_sub⟩

/-- Glue local `IsAEKolmogorovProcess` versions across horizons `N : ℕ` into a single rational-time
process `X' : ℚ≥0 → Ω → E` with Borel-measurable pairs and the same local Kolmogorov bounds. -/
private lemma exists_nnrat_gluing_of_local_isAEKolmogorovProcess
    {Ω E : Type*} {_ : MeasurableSpace Ω} [Nonempty Ω] [EMetricSpace E]
    {P : Measure Ω} {X : ℝ≥0 → Ω → E} {p q : ℝ} {M : ℕ → ℝ≥0}
    (hX : ∀ N : ℕ, IsAEKolmogorovProcess (fun t : Iic (N : ℝ≥0) ↦ X t) P p q (M N)) :
    ∃ X' : ℚ≥0 → Ω → E,
      (∀ r : ℚ≥0, X' r =ᵐ[P] X r) ∧
      (∀ r s : ℚ≥0, Measurable[_, borel (E × E)] fun ω ↦ (X' r ω, X' s ω)) ∧
      (∀ (N : ℕ) (r s : ℚ≥0), (r : ℝ≥0) ≤ N → (s : ℝ≥0) ≤ N →
        ∫⁻ ω, edist (X' r ω) (X' s ω) ^ p ∂P ≤ M N * edist (r : ℝ≥0) (s : ℝ≥0) ^ q) := by
  classical
  let e₀ : E := X 0 (Classical.arbitrary Ω)
  let Z (N : ℕ) : Iic (N : ℝ≥0) → Ω → E := (hX N).mk _
  let N₀ (r : ℚ≥0) : ℕ := ⌈((r : ℝ≥0) : ℝ)⌉₊
  have hr₀ (r : ℚ≥0) : (r : ℝ≥0) ≤ N₀ r := by exact_mod_cast Nat.le_ceil ((r : ℝ≥0) : ℝ)
  -- Step 1: collect a measurable null set `S` covering all disagreements across horizons `N`.
  let bad (r : ℚ≥0) (N : ℕ) : Set Ω :=
    if h : (r : ℝ≥0) ≤ N then
      toMeasurable P {ω | Z (N₀ r) ⟨r, hr₀ r⟩ ω ≠ Z N ⟨r, h⟩ ω}
    else ∅
  let S : Set Ω := ⋃ r : ℚ≥0, ⋃ N : ℕ, bad r N
  have hS_meas : MeasurableSet S := MeasurableSet.iUnion fun r ↦ MeasurableSet.iUnion fun N ↦ by
    simp only [bad]
    split_ifs
    · exact measurableSet_toMeasurable P _
    · exact MeasurableSet.empty
  have hS_zero : P S = 0 := measure_iUnion_null fun r ↦ measure_iUnion_null fun N ↦ by
    simp only [bad]
    split_ifs with h
    · rw [measure_toMeasurable]
      exact ((hX (N₀ r)).ae_eq_mk ⟨r, hr₀ r⟩).symm.trans ((hX N).ae_eq_mk ⟨r, h⟩)
    · exact measure_empty
  -- Step 2: define `X'` by constant fallback `e₀` on `S`, so pairs match `Z (max (N₀ r) (N₀ s))`.
  let X' : ℚ≥0 → Ω → E := fun r ω ↦ if ω ∈ S then e₀ else Z (N₀ r) ⟨r, hr₀ r⟩ ω
  have hX'_ae (r : ℚ≥0) : X' r =ᵐ[P] X r := by
    filter_upwards [compl_mem_ae_iff.2 hS_zero, (hX (N₀ r)).ae_eq_mk ⟨r, hr₀ r⟩] with ω hω hZ
    have hnot : ω ∉ S := hω
    simp [X', hnot, Z, hZ]
  refine ⟨X', hX'_ae, fun r s ↦ ?_, fun N r s hr hs ↦ ?_⟩
  · let N := max (N₀ r) (N₀ s)
    have hrN : (r : ℝ≥0) ≤ N := (hr₀ r).trans (Nat.cast_le.2 (le_max_left _ _))
    have hsN : (s : ℝ≥0) ≤ N := (hr₀ s).trans (Nat.cast_le.2 (le_max_right _ _))
    have heq : (fun ω ↦ (X' r ω, X' s ω)) =
        S.piecewise (fun _ ↦ (e₀, e₀)) (fun ω ↦ (Z N ⟨r, hrN⟩ ω, Z N ⟨s, hsN⟩ ω)) := by
      ext ω <;> by_cases hω : ω ∈ S <;> simp only [Set.piecewise, X', hω, ↓reduceIte]
      · have hnot : ω ∉ bad r N := fun h ↦ hω (mem_iUnion.2 ⟨r, mem_iUnion.2 ⟨N, h⟩⟩)
        simp only [bad, hrN, ↓reduceDIte] at hnot
        exact not_not.mp fun hne ↦ hnot (subset_toMeasurable P _ hne)
      · have hnot : ω ∉ bad s N := fun h ↦ hω (mem_iUnion.2 ⟨s, mem_iUnion.2 ⟨N, h⟩⟩)
        simp only [bad, hsN, ↓reduceDIte] at hnot
        exact not_not.mp fun hne ↦ hnot (subset_toMeasurable P _ hne)
    rw [heq]
    let : MeasurableSpace (E × E) := borel (E × E)
    exact Measurable.piecewise hS_meas measurable_const
      ((hX N).IsKolmogorovProcess_mk.measurablePair ⟨r, hrN⟩ ⟨s, hsN⟩)
  · have hcongr : (fun ω ↦ edist (X' r ω) (X' s ω) ^ p) =ᵐ[P]
        fun ω ↦ edist (X r ω) (X s ω) ^ p := by
      filter_upwards [hX'_ae r, hX'_ae s] with ω hrω hsω
      rw [hrω, hsω]
    rw [lintegral_congr_ae hcongr]
    exact (hX N).kolmogorovCondition ⟨r, hr⟩ ⟨s, hs⟩

/-- **Local one-dimensional Kolmogorov–Chentsov theorem on `ℝ≥0`.** If `X : ℝ≥0 → Ω → E` into a
complete extended metric Borel space satisfies `IsAEKolmogorovProcess` on each compact horizon
`Iic (N : ℝ≥0)` with exponents `p > 0` and `q > 1`, then `X` admits an all-paths continuous,
coordinatewise measurable modification `Y` whose sample paths are all simultaneously `γ`-Hölder
continuous on `Iic T` for every `γ : ℝ≥0` with `(γ : ℝ) < (q - 1) / p` and every `T : ℝ≥0`. -/
theorem exists_continuous_modification_of_local_isAEKolmogorovProcess
    {Ω E : Type*} {_ : MeasurableSpace Ω}
    [EMetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {X : ℝ≥0 → Ω → E} {p q : ℝ} {M : ℕ → ℝ≥0} (hq : 1 < q)
    (hX : ∀ N : ℕ, IsAEKolmogorovProcess (fun t : Iic (N : ℝ≥0) ↦ X t) P p q (M N)) :
    ∃ Y : ℝ≥0 → Ω → E,
      (∀ t : ℝ≥0, Measurable (Y t)) ∧
      (∀ ω : Ω, Continuous (Y · ω)) ∧
      (∀ t : ℝ≥0, Y t =ᵐ[P] X t) ∧
      (∀ (ω : Ω) (γ : ℝ≥0), (γ : ℝ) < (q - 1) / p → ∀ T : ℝ≥0,
        ∃ C : ℝ≥0, HolderOnWith C γ (Y · ω) (Iic T)) := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · exact ⟨X, fun _ _ _ ↦ by convert MeasurableSet.empty; exact eq_empty_of_isEmpty _,
      isEmptyElim, fun _ ↦ EventuallyEq.rfl, isEmptyElim⟩
  obtain ⟨X', hX'_ae, hpair', hkol'⟩ := exists_nnrat_gluing_of_local_isAEKolmogorovProcess hX
  obtain ⟨Y, hY_meas, hY_cont, hY_nnrat, hY_holder⟩ :=
    exists_continuous_extension_of_nnrat (hX 0).p_pos hq hpair' hkol'
  refine ⟨Y, hY_meas, hY_cont, fun t ↦ ?_, hY_holder⟩
  let N := ⌈(t : ℝ)⌉₊
  have htN : t ≤ N := by exact_mod_cast Nat.le_ceil (t : ℝ)
  have hu (n : ℕ) :
      edist
        (⟨approxDyadicNNRat n t, (coe_approxDyadicNNRat_le n t).trans htN⟩ : Iic (N : ℝ≥0))
        (⟨t, htN⟩ : Iic (N : ℝ≥0)) ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
    rw [Subtype.edist_eq]
    exact edist_approxDyadicNNRat_le n t
  have hae_dyad : ∀ᵐ ω ∂P, ∀ n, Y (approxDyadicNNRat n t) ω = X (approxDyadicNNRat n t) ω :=
    ae_all_iff.mpr fun n ↦ (hY_nnrat (approxDyadicNNRat n t)).trans (hX'_ae _)
  filter_upwards [ae_tendsto_of_edist_le (hX N) hu, hae_dyad] with ω hX_tend hYX
  have hY_tend : Tendsto (fun n ↦ X (approxDyadicNNRat n t) ω) atTop (𝓝 (Y t ω)) :=
    ((hY_cont ω).tendsto t).comp (tendsto_approxDyadicNNRat t) |>.congr hYX
  exact tendsto_nhds_unique hY_tend hX_tend

end StochasticExtension

end TauCeti

namespace ProbabilityTheory

/-- **One-dimensional Kolmogorov–Chentsov theorem** for `IsAEKolmogorovProcess` on `ℝ≥0`. -/
theorem IsAEKolmogorovProcess.exists_continuous_modification
    {Ω E : Type*} {_ : MeasurableSpace Ω}
    [EMetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {X : ℝ≥0 → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M) (hq : 1 < q) :
    ∃ Y : ℝ≥0 → Ω → E,
      (∀ t : ℝ≥0, Measurable (Y t)) ∧
      (∀ ω : Ω, Continuous (Y · ω)) ∧
      (∀ t : ℝ≥0, Y t =ᵐ[P] X t) ∧
      (∀ (ω : Ω) (γ : ℝ≥0), (γ : ℝ) < (q - 1) / p → ∀ T : ℝ≥0,
        ∃ C : ℝ≥0, HolderOnWith C γ (Y · ω) (Iic T)) :=
  TauCeti.exists_continuous_modification_of_local_isAEKolmogorovProcess (M := fun _ ↦ M) hq
    fun _ ↦
      ⟨fun t ↦ hX.mk X t.1,
        { measurablePair := fun s t ↦ hX.IsKolmogorovProcess_mk.measurablePair s.1 t.1
          kolmogorovCondition := fun s t ↦ hX.IsKolmogorovProcess_mk.kolmogorovCondition s.1 t.1
          p_pos := hX.p_pos
          q_pos := hX.q_pos },
        fun t ↦ hX.ae_eq_mk t.1⟩

/-- **One-dimensional Kolmogorov–Chentsov theorem** for `IsKolmogorovProcess` on `ℝ≥0`. -/
theorem IsKolmogorovProcess.exists_continuous_modification
    {Ω E : Type*} {_ : MeasurableSpace Ω}
    [EMetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {X : ℝ≥0 → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hq : 1 < q) :
    ∃ Y : ℝ≥0 → Ω → E,
      (∀ t : ℝ≥0, Measurable (Y t)) ∧
      (∀ ω : Ω, Continuous (Y · ω)) ∧
      (∀ t : ℝ≥0, Y t =ᵐ[P] X t) ∧
      (∀ (ω : Ω) (γ : ℝ≥0), (γ : ℝ) < (q - 1) / p → ∀ T : ℝ≥0,
        ∃ C : ℝ≥0, HolderOnWith C γ (Y · ω) (Iic T)) :=
  hX.IsAEKolmogorovProcess.exists_continuous_modification hq

end ProbabilityTheory
