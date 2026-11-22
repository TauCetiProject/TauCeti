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
import TauCeti.NumberTheory.GeometryOfNumbers.MinkowskiSecond

/-!
# Minkowski's shortest-vector bound in a Euclidean space

This file deduces Minkowski's shortest-vector bound for a full `ℤ`-lattice in a nontrivial
finite-dimensional real inner product space `E` from Minkowski's first theorem on the successive
minima (`ZLattice.successiveMin_pow_mul_measureReal_le_two_pow_mul_covolume`) applied to the
closed unit ball `ConvexBody.closedUnitBall E`.

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
  set K := ConvexBody.closedUnitBall E
  have hK : (K : Set E) = closedBall 0 1 := ConvexBody.coe_closedUnitBall
  have hK_symm : ∀ x ∈ K, -x ∈ K := fun x hx ↦ by
    rw [← SetLike.mem_coe, hK, mem_closedBall_zero_iff, norm_neg, ← mem_closedBall_zero_iff, ← hK]
    exact hx
  have hmin := successiveMin_pow_mul_measureReal_le_two_pow_mul_covolume L volume hK_symm hn
  have hvol : volume.real (K : Set E) = √Real.pi ^ n / Γ := by
    rw [measureReal_def, hK, InnerProductSpace.volume_closedBall]
    simp [n, Γ, ENNReal.toReal_ofReal (by positivity : 0 ≤ √Real.pi ^ n / Γ)]
  set lam₀ := successiveMin L K ⟨0, hn⟩
  set R : ℝ := 2 / √Real.pi * Γ ^ ((n : ℝ)⁻¹) * ZLattice.covolume L volume ^ ((n : ℝ)⁻¹)
  have hR : 0 < R := by positivity
  have hlam₀_pow : lam₀ ^ n ≤ R ^ n := by
    have hpi : √Real.pi ^ n ≠ 0 := pow_ne_zero n (Real.sqrt_pos.mpr Real.pi_pos).ne'
    rw [hvol] at hmin
    have hle : lam₀ ^ n ≤ (2 ^ n * ZLattice.covolume L volume) / (√Real.pi ^ n / Γ) :=
      (le_div_iff₀ (by positivity)).2 hmin
    refine hle.trans_eq ?_
    dsimp only [R]
    rw [mul_pow, mul_pow, div_pow, Real.rpow_inv_natCast_pow hΓ.le hn.ne',
      Real.rpow_inv_natCast_pow hcov.le hn.ne']
    field_simp [hpi, hΓ.ne']
  have hlam₀_le : lam₀ ≤ R :=
    le_of_pow_le_pow_left₀ hn.ne' hR.le hlam₀_pow
  obtain ⟨x, hxL, hx0, hxK⟩ :=
    (successiveMin_zero_le_iff L (ConvexBody.zero_mem_interior_of_coe_eq_closedBall hK) hn
      hR.le).1 hlam₀_le
  exact ⟨x, hxL, hx0, (ConvexBody.mem_smul_iff_norm_le_of_coe_eq_closedBall hK hR.le).1 hxK⟩

end ZLattice
