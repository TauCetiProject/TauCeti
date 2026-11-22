/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.MeasureTheory.Group.GeometryOfNumbers.Basic

/-!
# Minkowski's shortest-vector bound in a Euclidean space

This file deduces Minkowski's shortest-vector bound for a full `ℤ`-lattice in a nontrivial
finite-dimensional real inner product space `E` from Minkowski's convex body theorem
(`ZLattice.exists_ne_zero_mem_of_covolume_mul_two_pow_le`) applied to a closed ball of the claimed
radius.

## Main results

* `ZLattice.exists_ne_zero_mem_norm_le`: every full lattice `L` in a nontrivial finite-dimensional
  real inner product space `E` of dimension `n` contains a nonzero vector `x` with
  `‖x‖ ≤ 2 / √π · Γ(n / 2 + 1) ^ (1 / n) · (covolume L) ^ (1 / n)`.
-/

public section

open MeasureTheory Metric Module

namespace ZLattice

/-- **Minkowski's shortest-vector bound in a Euclidean space.** Every full `ℤ`-lattice `L` in a
nontrivial finite-dimensional real inner product space `E` of dimension `n` contains a nonzero
vector `x` with `‖x‖ ≤ 2 / √π · Γ(n / 2 + 1) ^ (1 / n) · (covolume L) ^ (1 / n)`. -/
theorem exists_ne_zero_mem_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ x ∈ L, x ≠ 0 ∧
      ‖x‖ ≤ 2 / √Real.pi *
        Real.Gamma ((finrank ℝ E : ℝ) / 2 + 1) ^ ((finrank ℝ E : ℝ)⁻¹) *
        ZLattice.covolume L ^ ((finrank ℝ E : ℝ)⁻¹) := by
  set n := finrank ℝ E
  have hn : 0 < n := finrank_pos
  set Γ := Real.Gamma ((n : ℝ) / 2 + 1)
  have hΓ : 0 < Γ := Real.Gamma_pos_of_pos (by positivity)
  have hcov : 0 < ZLattice.covolume L volume := ZLattice.covolume_pos L volume
  set R : ℝ := 2 / √Real.pi * Γ ^ ((n : ℝ)⁻¹) * ZLattice.covolume L volume ^ ((n : ℝ)⁻¹)
  have hR : 0 < R := by positivity
  have hs_symm : ∀ x ∈ closedBall (0 : E) R, -x ∈ closedBall (0 : E) R := fun x hx ↦ by
    simpa using hx
  have hs_vol :
      ENNReal.ofReal (ZLattice.covolume L volume) * 2 ^ finrank ℝ E ≤
        volume (closedBall (0 : E) R) := by
    rw [InnerProductSpace.volume_closedBall]
    have hpow : R ^ n * (√Real.pi ^ n / Γ) = ZLattice.covolume L volume * 2 ^ n := by
      have hpi : √Real.pi ^ n ≠ 0 := pow_ne_zero n (Real.sqrt_pos.mpr Real.pi_pos).ne'
      dsimp only [R]
      rw [mul_pow, mul_pow, div_pow, Real.rpow_inv_natCast_pow hΓ.le hn.ne',
        Real.rpow_inv_natCast_pow hcov.le hn.ne']
      field_simp [hpi, hΓ.ne']
    rw [← ENNReal.ofReal_pow hR.le, ← ENNReal.ofReal_mul (pow_nonneg hR.le _), hpow,
      ENNReal.ofReal_mul hcov.le]
    simp [n]
  obtain ⟨x, hxL, hx0, hxs⟩ :=
    ZLattice.exists_ne_zero_mem_of_covolume_mul_two_pow_le L volume hs_symm
      (convex_closedBall 0 R) (isCompact_closedBall 0 R) hs_vol
  exact ⟨x, hxL, hx0, mem_closedBall_zero_iff.mp hxs⟩

end ZLattice
