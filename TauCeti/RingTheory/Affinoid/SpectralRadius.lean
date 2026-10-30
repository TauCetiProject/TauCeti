/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm
public import TauCeti.RingTheory.Affinoid.PowerBounded

import TauCeti.RingTheory.Affinoid.ValueGroup
import TauCeti.RingTheory.Huber.Normed

/-!
# The supremum seminorm as a spectral radius

Let `A` be an affinoid algebra over a complete nonarchimedean field `K`, equipped with any
complete ultrametric algebra norm `‖·‖`. This file proves the spectral-radius formula

`|f|sup = inf_{n ≥ 1} ‖f ^ n‖ ^ (1 / n) = lim_{n → ∞} ‖f ^ n‖ ^ (1 / n)`.

In other words, the supremum seminorm is the smoothing of every complete ultrametric algebra
norm, in the sense of Mathlib's `smoothingFun`. Since the supremum seminorm is defined through
classical points, this shows once more that the smoothing does not depend on the chosen norm.

The inequality `|f|sup ≤ ‖f ^ n‖ ^ (1 / n)` follows from power-multiplicativity of the supremum
seminorm. For the converse, a fixed power `f ^ m` has a unit multiple `c • f ^ m` of supremum
seminorm one when `|f|sup > 0`, by the value-group theorem; this multiple is power-bounded, so its
powers are norm-bounded. It follows that `‖f ^ n‖ ≤ D * |f|sup ^ n` for a constant `D`, whence the
limit. Nilpotent elements, which are exactly those of supremum seminorm zero, are treated
separately.

## Main results

* `TauCeti.IsAffinoidAlgebra.exists_norm_pow_le_mul_supSeminorm_pow`: if `|f|sup > 0`, then
  `‖f ^ n‖ ≤ D * |f|sup ^ n` for all `n` and some constant `D`.
* `TauCeti.IsAffinoidAlgebra.tendsto_norm_pow_rpow_supSeminorm`:
  `‖f ^ n‖ ^ (1 / n) → |f|sup`.
* `TauCeti.IsAffinoidAlgebra.supSeminorm_eq_iInf_norm_pow_rpow`:
  `|f|sup = ⨅ n ≥ 1, ‖f ^ n‖ ^ (1 / n)`.
* `TauCeti.IsAffinoidAlgebra.supSeminorm_eq_smoothingFun`: the same identity, stated with
  Mathlib's smoothing of the norm.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§1.3.2 and 6.2.
-/

public section

namespace TauCeti.IsAffinoidAlgebra

open Filter Topology

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]

/-- For every complete ultrametric algebra norm on an affinoid algebra,
`|f|sup ≤ ‖f ^ n‖ ^ (1 / n)` for every `n ≥ 1`. -/
theorem supSeminorm_le_norm_pow_rpow (hA : IsAffinoidAlgebra K A) (f : A) {n : ℕ}
    (hn : n ≠ 0) : supSeminorm K f ≤ ‖f ^ n‖ ^ (1 / n : ℝ) := by
  rw [← Real.pow_rpow_inv_natCast (supSeminorm_nonneg f) hn, one_div,
    ← hA.supSeminorm_pow f hn]
  exact Real.rpow_le_rpow (supSeminorm_nonneg _) (hA.supSeminorm_le_norm _) (by positivity)

/-- **Powers grow at the rate of the supremum seminorm.** For every complete ultrametric algebra
norm on an affinoid algebra and every `f` with `|f|sup > 0`, there is a constant `D` with
`‖f ^ n‖ ≤ D * |f|sup ^ n` for all `n`. The hypothesis excludes exactly the nilpotent elements;
for a nonzero nilpotent the bound fails at `n = 1`. -/
theorem exists_norm_pow_le_mul_supSeminorm_pow (hA : IsAffinoidAlgebra K A) {f : A}
    (hf : 0 < supSeminorm K f) :
    ∃ D : ℝ, ∀ n : ℕ, ‖f ^ n‖ ≤ D * supSeminorm K f ^ n := by
  set s := supSeminorm K f
  obtain ⟨m, hm, h⟩ := hA.exists_supSeminorm_smul_pow_eq_one
  obtain ⟨c, hc⟩ := h f hf
  -- `g = c • f ^ m` has supremum seminorm one, so it is power-bounded and its powers are
  -- norm-bounded by some `C`.
  obtain ⟨ϖ, hϖ⟩ := (Huber.IsTateRing.of_normedAlgebra K A).exists_isPseudoUniformizer
  obtain ⟨C, hC⟩ := hϖ.isBounded_iff_forall_norm_le.mp <| Huber.isPowerBounded_iff.mp <|
    hA.isPowerBounded_iff_supSeminorm_le_one.mpr hc.le
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ ⟨0, rfl⟩)
  have hcs : ‖(c : K)‖⁻¹ = s ^ m := by
    rw [hA.supSeminorm_smul, hA.supSeminorm_pow f (by omega)] at hc
    exact inv_eq_of_mul_eq_one_right hc
  -- Write `n = m * (n / m) + n % m`; the remainder contributes one of finitely many factors.
  refine ⟨C * ∑ r ∈ Finset.range m, ‖f ^ r‖ / s ^ r, fun n ↦ ?_⟩
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < m ∧ n = m * k + r :=
    ⟨n / m, n % m, Nat.mod_lt n (by omega), (Nat.div_add_mod n m).symm⟩
  have hfn : f ^ (m * k + r) = ((c : K)⁻¹ ^ k) • (((c : K) • f ^ m) ^ k * f ^ r) := by
    rw [smul_pow, smul_mul_assoc, smul_smul, ← mul_pow, inv_mul_cancel₀ c.ne_zero, one_pow,
      one_smul, ← pow_mul, ← pow_add]
  have hterm : ‖f ^ r‖ / s ^ r ≤ ∑ i ∈ Finset.range m, ‖f ^ i‖ / s ^ i :=
    Finset.single_le_sum (f := fun i ↦ ‖f ^ i‖ / s ^ i) (fun i _ ↦ by positivity)
      (Finset.mem_range.mpr hr)
  calc ‖f ^ (m * k + r)‖ ≤ ‖(c : K)‖⁻¹ ^ k * (C * ‖f ^ r‖) := by
        rw [hfn, norm_smul, norm_pow, norm_inv]
        gcongr
        calc ‖((c : K) • f ^ m) ^ k * f ^ r‖ ≤ ‖((c : K) • f ^ m) ^ k‖ * ‖f ^ r‖ :=
              norm_mul_le _ _
          _ ≤ C * ‖f ^ r‖ := by gcongr; exact hC _ ⟨k, rfl⟩
    _ = C * (‖f ^ r‖ / s ^ r) * s ^ (m * k + r) := by
        rw [hcs, ← pow_mul, pow_add]
        field_simp
    _ ≤ C * (∑ i ∈ Finset.range m, ‖f ^ i‖ / s ^ i) * s ^ (m * k + r) := by
        gcongr

/-- **The spectral-radius formula, as a limit.** For every complete ultrametric algebra norm on
an affinoid algebra, `‖f ^ n‖ ^ (1 / n)` tends to `|f|sup`. -/
theorem tendsto_norm_pow_rpow_supSeminorm (hA : IsAffinoidAlgebra K A) (f : A) :
    Tendsto (fun n : ℕ ↦ ‖f ^ n‖ ^ (1 / n : ℝ)) atTop (𝓝 (supSeminorm K f)) := by
  rcases (supSeminorm_nonneg (K := K) f).eq_or_lt with h0 | hpos
  · -- A nilpotent element: the sequence is eventually zero.
    obtain ⟨N, hN⟩ := (hA.supSeminorm_eq_zero_iff.mp h0.symm)
    rw [← h0]
    refine tendsto_const_nhds.congr' <| eventually_atTop.mpr ⟨N + 1, fun n hn ↦ ?_⟩
    beta_reduce
    rw [pow_eq_zero_of_le (show N ≤ n by omega) hN, norm_zero,
      Real.zero_rpow (one_div_ne_zero (Nat.cast_ne_zero.mpr (by omega)))]
  · -- Squeeze between `|f|sup` and `D ^ (1 / n) * |f|sup`.
    obtain ⟨D, hD⟩ := hA.exists_norm_pow_le_mul_supSeminorm_pow hpos
    have hD1 : 0 < max D 1 := lt_max_of_lt_right one_pos
    have hlim : Tendsto (fun n : ℕ ↦ max D 1 ^ (1 / n : ℝ) * supSeminorm K f) atTop
        (𝓝 (supSeminorm K f)) := by
      simpa using (tendsto_const_nhds.rpow tendsto_one_div_atTop_nhds_zero_nat
        (Or.inl hD1.ne')).mul_const (supSeminorm K f)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (eventually_atTop.mpr ⟨1, fun n hn ↦ hA.supSeminorm_le_norm_pow_rpow f (by omega)⟩)
      (eventually_atTop.mpr ⟨1, fun n hn ↦ ?_⟩)
    have hn : n ≠ 0 := by omega
    calc ‖f ^ n‖ ^ (1 / n : ℝ) ≤ (max D 1 * supSeminorm K f ^ n) ^ (1 / n : ℝ) := by
          gcongr
          exact (hD n).trans (by gcongr; exact le_max_left D 1)
      _ = max D 1 ^ (1 / n : ℝ) * supSeminorm K f := by
          rw [Real.mul_rpow hD1.le (by positivity), one_div,
            Real.pow_rpow_inv_natCast hpos.le hn]

/-- **The spectral-radius formula.** For every complete ultrametric algebra norm on an affinoid
algebra, `|f|sup = inf_{n ≥ 1} ‖f ^ n‖ ^ (1 / n)`. -/
theorem supSeminorm_eq_iInf_norm_pow_rpow (hA : IsAffinoidAlgebra K A) (f : A) :
    supSeminorm K f = ⨅ n : ℕ+, ‖f ^ (n : ℕ)‖ ^ (1 / (n : ℝ)) := by
  have hbdd : BddBelow (Set.range fun n : ℕ+ ↦ ‖f ^ (n : ℕ)‖ ^ (1 / (n : ℝ))) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; positivity⟩
  refine le_antisymm (le_ciInf fun n ↦ hA.supSeminorm_le_norm_pow_rpow f n.ne_zero) ?_
  refine ge_of_tendsto (hA.tendsto_norm_pow_rpow_supSeminorm f) ?_
  exact eventually_atTop.mpr ⟨1, fun n hn ↦ ciInf_le hbdd ⟨n, hn⟩⟩

/-- **The supremum seminorm is the smoothing of every complete algebra norm.** For every complete
ultrametric algebra norm on an affinoid algebra, `|f|sup` is Mathlib's `smoothingFun` of the norm,
viewed as a ring seminorm. -/
theorem supSeminorm_eq_smoothingFun (hA : IsAffinoidAlgebra K A) (f : A) :
    supSeminorm K f = smoothingFun (normRingSeminorm A) f :=
  -- `smoothingFun` is the infimum above, and `normRingSeminorm A` evaluates to the norm.
  hA.supSeminorm_eq_iInf_norm_pow_rpow f

end TauCeti.IsAffinoidAlgebra
