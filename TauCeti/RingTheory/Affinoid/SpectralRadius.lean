/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.PowerBounded
public import TauCeti.RingTheory.Affinoid.ValueGroup
public import Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm

import TauCeti.RingTheory.Huber.Normed

/-!
# The supremum seminorm as a spectral radius

Let `A` be an affinoid algebra over a complete nonarchimedean field `K`, equipped with a complete
ultrametric algebra norm `‖·‖`. This file proves the spectral-radius formula

`|f|sup = lim_{n → ∞} ‖f ^ n‖ ^ (1 / n) = inf_{n ≥ 1} ‖f ^ n‖ ^ (1 / n)`.

The infimum is Mathlib's `smoothingFun` of the norm, so the supremum seminorm is the smoothing of
every complete ultrametric algebra norm on `A`; when `‖1‖ ≤ 1` the bundled seminorms
`TauCeti.IsAffinoidAlgebra.supRingSeminorm` and `smoothingSeminorm` coincide. In particular the
limit does not depend on the chosen norm, and no reducedness of `A` is assumed.

The lower bound `|f|sup ≤ ‖f ^ n‖ ^ (1 / n)` combines power-multiplicativity of `|·|sup` with
`|·|sup ≤ ‖·‖`. For the upper bound, a single exponent `m ≥ 1` and a scalar `c` give
`|c f ^ m|sup = 1` (`TauCeti.IsAffinoidAlgebra.exists_supSeminorm_smul_pow_eq_one`). Then
`c f ^ m` is power-bounded (`TauCeti.IsAffinoidAlgebra.isPowerBounded_iff_supSeminorm_le_one`), so
`‖f ^ n‖ ≤ C |f|sup ^ n` for a constant `C`, and `C ^ (1 / n) → 1`. A nilpotent `f` has
`|f|sup = 0` and `f ^ n = 0` for large `n`.

## Main results

* `TauCeti.IsAffinoidAlgebra.supSeminorm_le_norm_pow_rpow`: `|f|sup ≤ ‖f ^ n‖ ^ (1 / n)` for
  `n ≠ 0`.
* `TauCeti.IsAffinoidAlgebra.exists_norm_pow_le_mul_supSeminorm_pow`: if `|f|sup > 0`, then
  `‖f ^ n‖ ≤ C |f|sup ^ n` for some constant `C` and every `n`.
* `TauCeti.IsAffinoidAlgebra.pow_norm_pow_one_div_tendsto_nhds_supSeminorm`: the sequence
  `‖f ^ n‖ ^ (1 / n)` tends to `|f|sup`.
* `TauCeti.IsAffinoidAlgebra.supSeminorm_eq_smoothingFun`: `|f|sup = inf_{n ≥ 1} ‖f ^ n‖ ^ (1 / n)`.
* `TauCeti.IsAffinoidAlgebra.supRingSeminorm_eq_smoothingSeminorm`: the same identity for the
  bundled ring seminorms.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§1.3.2 and 6.2.
-/

public section

namespace TauCeti.IsAffinoidAlgebra

open Filter Topology

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]

/-- **The supremum seminorm is bounded by the normalised norms of powers.** For every complete
ultrametric algebra norm on an affinoid algebra, `|f|sup ≤ ‖f ^ n‖ ^ (1 / n)` for `n ≠ 0`. -/
theorem supSeminorm_le_norm_pow_rpow (hA : IsAffinoidAlgebra K A) (f : A) {n : ℕ} (hn : n ≠ 0) :
    supSeminorm K f ≤ ‖f ^ n‖ ^ (1 / n : ℝ) := by
  rw [← Real.pow_rpow_inv_natCast (supSeminorm_nonneg f) hn, ← hA.supSeminorm_pow f hn, one_div]
  exact Real.rpow_le_rpow (supSeminorm_nonneg _) (hA.supSeminorm_le_norm _) (by positivity)

/-- **Norms of powers grow at most like the supremum seminorm.** For every complete ultrametric
algebra norm on an affinoid algebra and every `f` with `|f|sup > 0`, there is a constant `C` with
`‖f ^ n‖ ≤ C |f|sup ^ n` for all `n`. -/
theorem exists_norm_pow_le_mul_supSeminorm_pow (hA : IsAffinoidAlgebra K A) {f : A}
    (hf : 0 < supSeminorm K f) : ∃ C, ∀ n : ℕ, ‖f ^ n‖ ≤ C * supSeminorm K f ^ n := by
  obtain ⟨m, hm, h⟩ := hA.exists_supSeminorm_smul_pow_eq_one
  obtain ⟨c, hc⟩ := h f hf
  set r := supSeminorm K f
  have hcr : ‖(c : K)‖⁻¹ = r ^ m := by
    rw [hA.supSeminorm_smul, hA.supSeminorm_pow f (by omega)] at hc
    exact inv_eq_of_mul_eq_one_right hc
  -- The element `c • f ^ m` has supremum seminorm one, so its powers are norm-bounded.
  have hu : Huber.IsPowerBounded ((c : K) • f ^ m) :=
    hA.isPowerBounded_iff_supSeminorm_le_one.mpr hc.le
  obtain ⟨ϖ, hϖ⟩ := (Huber.IsTateRing.of_normedAlgebra K A).exists_isPseudoUniformizer
  obtain ⟨B, hB⟩ := hϖ.isBounded_iff_forall_norm_le.mp (Huber.isPowerBounded_iff.mp hu)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB _ ⟨0, rfl⟩)
  -- Hence the bound holds along multiples of `m`.
  have hmul (k : ℕ) : ‖f ^ (m * k)‖ ≤ B * r ^ (m * k) := by
    have hfk : f ^ (m * k) = (c : K)⁻¹ ^ k • ((c : K) • f ^ m) ^ k := by
      rw [smul_pow, smul_smul, ← mul_pow, inv_mul_cancel₀ c.ne_zero, one_pow, one_smul, pow_mul]
    rw [hfk, norm_smul, norm_pow, norm_inv, hcr, ← pow_mul, mul_comm B]
    exact mul_le_mul_of_nonneg_left (hB _ ⟨k, rfl⟩) (by positivity)
  -- In general write `n = m * q + j` with `j < m`.
  refine ⟨B * ∑ j ∈ Finset.range m, ‖f ^ j‖ * r⁻¹ ^ j, fun n ↦ ?_⟩
  have hj : n % m ∈ Finset.range m := Finset.mem_range.mpr (Nat.mod_lt n (by omega))
  calc ‖f ^ n‖ = ‖f ^ (m * (n / m)) * f ^ (n % m)‖ := by rw [← pow_add, Nat.div_add_mod]
    _ ≤ ‖f ^ (m * (n / m))‖ * ‖f ^ (n % m)‖ := norm_mul_le _ _
    _ ≤ B * r ^ (m * (n / m)) * ‖f ^ (n % m)‖ := by gcongr; exact hmul _
    _ = B * (‖f ^ (n % m)‖ * r⁻¹ ^ (n % m)) * r ^ n := by
      have hrn : r ^ n = r ^ (m * (n / m)) * r ^ (n % m) := by rw [← pow_add, Nat.div_add_mod]
      rw [hrn, inv_pow]
      field_simp
    _ ≤ B * (∑ j ∈ Finset.range m, ‖f ^ j‖ * r⁻¹ ^ j) * r ^ n := by
      gcongr
      exact Finset.single_le_sum (f := fun j ↦ ‖f ^ j‖ * r⁻¹ ^ j)
        (fun j _ ↦ by positivity) hj

/-- **The spectral-radius formula.** For every complete ultrametric algebra norm on an affinoid
algebra, `‖f ^ n‖ ^ (1 / n)` tends to the supremum seminorm `|f|sup`. -/
theorem pow_norm_pow_one_div_tendsto_nhds_supSeminorm (hA : IsAffinoidAlgebra K A) (f : A) :
    Tendsto (fun n : ℕ ↦ ‖f ^ n‖ ^ (1 / n : ℝ)) atTop (𝓝 (supSeminorm K f)) := by
  rcases (supSeminorm_nonneg (K := K) f).eq_or_lt with h | h
  · -- A nilpotent `f` has vanishing powers from some point on.
    obtain ⟨k, hk⟩ := hA.supSeminorm_eq_zero_iff.mp h.symm
    rw [← h]
    refine tendsto_atTop_of_eventually_const (i₀ := k + 1) fun n hn ↦ ?_
    rw [pow_eq_zero_of_le (by omega) hk, norm_zero,
      Real.zero_rpow (one_div_ne_zero (Nat.cast_ne_zero.mpr (by omega)))]
  · have : Nontrivial A := by
      by_contra hA'
      rw [not_nontrivial_iff_subsingleton] at hA'
      exact h.ne' (supSeminorm_eq_zero_of_subsingleton f)
    obtain ⟨C, hC⟩ := hA.exists_norm_pow_le_mul_supSeminorm_pow h
    have hC0 : 0 < C := (norm_pos_iff.mpr one_ne_zero).trans_le (by simpa using hC 0)
    -- Squeeze between `|f|sup` and `C ^ (1 / n) * |f|sup`.
    have hup : Tendsto (fun n : ℕ ↦ C ^ (1 / n : ℝ) * supSeminorm K f) atTop
        (𝓝 (supSeminorm K f)) := by
      simpa using ((Real.continuousAt_const_rpow hC0.ne' (b := 0)).tendsto.comp
        tendsto_one_div_atTop_nhds_zero_nat).mul_const (supSeminorm K f)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_ne_atTop 0] with n hn
      exact hA.supSeminorm_le_norm_pow_rpow f hn
    · filter_upwards [eventually_ne_atTop 0] with n hn
      calc ‖f ^ n‖ ^ (1 / n : ℝ) ≤ (C * supSeminorm K f ^ n) ^ (1 / n : ℝ) :=
            Real.rpow_le_rpow (norm_nonneg _) (hC n) (by positivity)
        _ = C ^ (1 / n : ℝ) * supSeminorm K f := by
          rw [Real.mul_rpow hC0.le (by positivity), one_div,
            Real.pow_rpow_inv_natCast h.le hn]

/-- **The supremum seminorm is the smoothing of the norm.** For every complete ultrametric algebra
norm on an affinoid algebra, `|f|sup = inf_{n ≥ 1} ‖f ^ n‖ ^ (1 / n)`, which is Mathlib's
`smoothingFun` of the norm. -/
theorem supSeminorm_eq_smoothingFun (hA : IsAffinoidAlgebra K A) (f : A) :
    supSeminorm K f = smoothingFun (normRingSeminorm A) f := by
  -- `normRingSeminorm A` is the norm itself, so the terms of the infimum are `‖f ^ n‖ ^ (1 / n)`.
  refine le_antisymm (le_ciInf fun n ↦ hA.supSeminorm_le_norm_pow_rpow f n.ne_zero) ?_
  refine ge_of_tendsto (hA.pow_norm_pow_one_div_tendsto_nhds_supSeminorm f) ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact smoothingFun_le (normRingSeminorm A) f ⟨n, Nat.pos_of_ne_zero hn⟩

/-- **The supremum seminorm is the smoothing seminorm of the norm.** For every complete ultrametric
algebra norm on an affinoid algebra with `‖1‖ ≤ 1`, the bundled supremum seminorm is Mathlib's
`smoothingSeminorm` of the norm. -/
theorem supRingSeminorm_eq_smoothingSeminorm (hA : IsAffinoidAlgebra K A)
    (h1 : ‖(1 : A)‖ ≤ 1) :
    hA.supRingSeminorm =
      smoothingSeminorm (normRingSeminorm A) h1 IsUltrametricDist.isNonarchimedean_norm :=
  -- `smoothingSeminorm` is bundled `smoothingFun`.
  RingSeminorm.ext fun f ↦ by
    rw [coe_supRingSeminorm]
    exact hA.supSeminorm_eq_smoothingFun f

end TauCeti.IsAffinoidAlgebra
