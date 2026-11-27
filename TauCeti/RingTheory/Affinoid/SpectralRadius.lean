/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.PowerBounded
public import TauCeti.RingTheory.Affinoid.ValueGroup
public import Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm

import TauCeti.RingTheory.Affinoid.FunctionAlgebra
import TauCeti.RingTheory.Huber.Normed

/-!
# The supremum seminorm as a spectral radius

Let `A` be an affinoid algebra over a complete nonarchimedean field `K`, equipped with a complete
algebra norm `‖·‖`. This file records the spectral-radius formula

`|f|sup = lim_{n → ∞} ‖f ^ n‖ ^ (1 / n) = inf_{n ≥ 1} ‖f ^ n‖ ^ (1 / n)`.

Since `|f|sup = gelfandRadius f` (`TauCeti.IsAffinoidAlgebra.supSeminorm_eq_gelfandRadius`) and
`gelfandRadius f` coincides with Mathlib's `smoothingFun (normRingSeminorm A) f`, both the limit
formula and the smoothing formula hold for every complete `K`-algebra norm on `A` without requiring
ultrametricity or reducedness. When `‖·‖` is ultrametric and `‖1‖ ≤ 1`, the bundled seminorms
`TauCeti.IsAffinoidAlgebra.supRingSeminorm` and `smoothingSeminorm` coincide, and when `|f|sup > 0`
the powers satisfy the quantitative bound `‖f ^ n‖ ≤ C |f|sup ^ n`.

## Main results

* `TauCeti.supSeminorm_le_norm_pow_rpow`: `|f|sup ≤ ‖f ^ n‖ ^ (1 / n)` for `n ≠ 0`.
* `TauCeti.IsAffinoidAlgebra.pow_norm_pow_one_div_tendsto_nhds_supSeminorm`: the sequence
  `‖f ^ n‖ ^ (1 / n)` tends to `|f|sup` (for any complete `K`-algebra norm).
* `TauCeti.IsAffinoidAlgebra.supSeminorm_eq_smoothingFun`: `|f|sup = inf_{n ≥ 1} ‖f ^ n‖ ^ (1 / n)`
  (for any complete `K`-algebra norm).
* `TauCeti.IsAffinoidAlgebra.exists_norm_pow_le_mul_supSeminorm_pow`: for a complete ultrametric
  algebra norm, if `|f|sup > 0`, then `‖f ^ n‖ ≤ C |f|sup ^ n` for some constant `C` and every `n`.
* `TauCeti.IsAffinoidAlgebra.supRingSeminorm_eq_smoothingSeminorm`: the smoothing identity for the
  bundled ring seminorms in the ultrametric case with `‖1‖ ≤ 1`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§1.3.2 and 6.2.
-/

public section

namespace TauCeti

open Filter Topology

/-- **The supremum seminorm is bounded by the normalised norms of powers.** For every algebra
norm with summable geometric series over a complete ultrametric field `K`,
`|f|sup ≤ ‖f ^ n‖ ^ (1 / n)` for `n ≠ 0`. -/
theorem supSeminorm_le_norm_pow_rpow {K A : Type*} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [NormedCommRing A] [NormedAlgebra K A] [HasSummableGeomSeries A]
    (f : A) {n : ℕ} (hn : n ≠ 0) :
    supSeminorm K f ≤ ‖f ^ n‖ ^ (1 / n : ℝ) :=
  ((AlgHom.id K A).supSeminorm_apply_le_gelfandRadius f).trans <| by
    simpa only [one_div] using gelfandRadius_le_norm_pow f hn

namespace IsAffinoidAlgebra

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **The spectral-radius formula.** For every complete algebra norm on an affinoid algebra (not
assumed ultrametric or reduced), `‖f ^ n‖ ^ (1 / n)` tends to the supremum seminorm `|f|sup`. -/
theorem pow_norm_pow_one_div_tendsto_nhds_supSeminorm {A : Type*} [NormedCommRing A]
    [NormedAlgebra K A] [CompleteSpace A] (hA : IsAffinoidAlgebra K A) (f : A) :
    Tendsto (fun n : ℕ ↦ ‖f ^ n‖ ^ (1 / n : ℝ)) atTop (𝓝 (supSeminorm K f)) := by
  rw [hA.supSeminorm_eq_gelfandRadius f]
  simpa only [one_div] using tendsto_gelfandRadius f

/-- **The supremum seminorm is the smoothing of the norm.** For every complete algebra norm on an
affinoid algebra (not assumed ultrametric or reduced), `|f|sup = inf_{n ≥ 1} ‖f ^ n‖ ^ (1 / n)`,
which is Mathlib's `smoothingFun` of the norm. -/
theorem supSeminorm_eq_smoothingFun {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    [CompleteSpace A] (hA : IsAffinoidAlgebra K A) (f : A) :
    supSeminorm K f = smoothingFun (normRingSeminorm A) f := by
  rw [hA.supSeminorm_eq_gelfandRadius f, smoothingFun_normRingSeminorm_eq_gelfandRadius]

/-- A complete multiplicative algebra norm on an affinoid algebra is its supremum norm.
No normalisation of a Tate presentation is needed. -/
@[simp]
theorem supSeminorm_eq_norm_of_normMulClass {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    [CompleteSpace A] [NormOneClass A] [NormMulClass A]
    (hA : IsAffinoidAlgebra K A) (f : A) : supSeminorm K f = ‖f‖ := by
  rw [hA.supSeminorm_eq_smoothingFun]
  exact smoothingFun_apply_of_map_mul_eq_mul (normRingSeminorm A)
    (le_of_eq norm_one) (fun g ↦ norm_mul f g)

variable {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]

/-- **Norms of powers grow at most like the supremum seminorm.** For every complete ultrametric
algebra norm on an affinoid algebra and every `f` with `|f|sup > 0`, there is a constant `C` with
`‖f ^ n‖ ≤ C |f|sup ^ n` for all `n`. -/
theorem exists_norm_pow_le_mul_supSeminorm_pow (hA : IsAffinoidAlgebra K A) {f : A}
    (hf : 0 < supSeminorm K f) : ∃ C, ∀ n : ℕ, ‖f ^ n‖ ≤ C * supSeminorm K f ^ n := by
  obtain ⟨m, hm, h⟩ := hA.exists_supSeminorm_smul_pow_eq_one
  obtain ⟨c, hc⟩ := h f hf
  set r := supSeminorm K f
  have hcr : ‖(c : K)‖⁻¹ = r ^ m := by
    rw [supSeminorm_smul, supSeminorm_pow f (by omega)] at hc
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

end IsAffinoidAlgebra

end TauCeti
