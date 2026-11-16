/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers

import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Minkowski's convex body theorem for lattices

Mathlib states Minkowski's convex body theorem for an arbitrary discrete subgroup with a
fundamental domain. This file packages it for full `ℤ`-lattices in terms of `ZLattice.covolume`,
deduces the Euclidean shortest-vector bound in a finite-dimensional real inner product space, and
records the standard coordinate instance for the integer lattice `ℤ^η` in `η → ℝ` with Lebesgue
measure.

## Main results

* `MeasureTheory.exists_ne_zero_int_vec_mem_of_two_pow_le_volume`: a compact convex symmetric
  set `s ⊆ η → ℝ` of volume at least `2 ^ |η|` contains a nonzero integer vector.
* `ZLattice.exists_ne_zero_mem_of_covolume_mul_two_pow_le`: a compact convex symmetric set `s` in a
  nontrivial finite-dimensional real normed space `E` with `covolume L μ * 2 ^ finrank ℝ E ≤ μ s`
  contains a nonzero vector of the full lattice `L`.
* `ZLattice.exists_ne_zero_mem_norm_le`: every full lattice `L` in a nontrivial finite-dimensional
  real inner product space `E` of dimension `n` contains a nonzero vector `x` with
  `‖x‖ ≤ 2 / √π · Γ(n / 2 + 1) ^ (1 / n) · (covolume L) ^ (1 / n)`.
-/

public section

open Module

namespace MeasureTheory

/-- **Minkowski's convex body theorem for the integer lattice.** A compact convex set
`s ⊆ η → ℝ`, symmetric about the origin, of volume at least `2 ^ |η|` contains a nonzero integer
vector. -/
theorem exists_ne_zero_int_vec_mem_of_two_pow_le_volume {η : Type*} [Fintype η] [Nonempty η]
    {s : Set (η → ℝ)} (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s) (h_cpt : IsCompact s)
    (h : 2 ^ Fintype.card η ≤ volume s) :
    ∃ z : η → ℤ, z ≠ 0 ∧ (fun k ↦ (z k : ℝ)) ∈ s := by
  set b := Pi.basisFun ℝ η
  have : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  obtain ⟨⟨v, hv⟩, hv0, hvs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (ZSpan.isAddFundamentalDomain' b volume) h_symm h_conv h_cpt (by
      rw [ZSpan.fundamentalDomain_pi_basisFun, Real.volume_pi_Ico, finrank_fintype_fun_eq_card]
      simpa using h)
  choose z hz using fun k ↦ by simpa [b] using (b.mem_span_iff_repr_mem ℤ v).1 hv k
  have hvz : v = fun k ↦ (z k : ℝ) := funext fun k ↦ (hz k).symm
  subst hvz
  exact ⟨z, fun h0 ↦ hv0 (Subtype.ext (funext fun k ↦ by simp [h0])), hvs⟩

end MeasureTheory

namespace ZLattice

open MeasureTheory Metric

/-- **Minkowski's convex body theorem for a full lattice.** Let `L` be a full `ℤ`-lattice in a
nontrivial finite-dimensional real normed space `E` with Haar measure `μ`. Every compact convex
symmetric set `s ⊆ E` with `covolume L μ * 2 ^ finrank ℝ E ≤ μ s` contains a nonzero vector of
`L`. -/
theorem exists_ne_zero_mem_of_covolume_mul_two_pow_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : Measure E := by volume_tac) [μ.IsAddHaarMeasure]
    {s : Set E} (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s) (h_cpt : IsCompact s)
    (h : ENNReal.ofReal (ZLattice.covolume L μ) * 2 ^ finrank ℝ E ≤ μ s) :
    ∃ x ∈ L, x ≠ 0 ∧ x ∈ s := by
  let b := Free.chooseBasis ℤ L
  have hfund := ZLattice.isAddFundamentalDomain b μ
  have : Countable L.toAddSubgroup := (inferInstance : Countable L)
  have : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
  have hvol : μ (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) * 2 ^ finrank ℝ E ≤ μ s := by
    rwa [ZLattice.covolume_eq_measure_fundamentalDomain L μ hfund,
      ofReal_measureReal (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne] at h
  obtain ⟨⟨x, hxL⟩, hx0, hxs⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure (L := L.toAddSubgroup)
      hfund h_symm h_conv h_cpt hvol
  exact ⟨x, hxL, fun h0 ↦ hx0 (Subtype.ext h0), hxs⟩

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
  have hRN : ZLattice.covolume L volume * (2 : ℝ) ^ n = R ^ n * (√Real.pi ^ n / Γ) := by
    have hpi : √Real.pi ^ n ≠ 0 := pow_ne_zero n (Real.sqrt_pos.mpr Real.pi_pos).ne'
    dsimp only [R]
    rw [mul_pow, mul_pow, div_pow, Real.rpow_inv_natCast_pow hΓ.le hn.ne',
      Real.rpow_inv_natCast_pow hcov.le hn.ne']
    field_simp [hpi, hΓ.ne']
  have hvol :
      ENNReal.ofReal (ZLattice.covolume L volume) * 2 ^ n ≤ volume (closedBall (0 : E) R) := by
    have h2 : (2 : ENNReal) ^ n = ENNReal.ofReal ((2 : ℝ) ^ n) := by
      rw [ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
    rw [InnerProductSpace.volume_closedBall, ← ENNReal.ofReal_pow hR.le,
      ← ENNReal.ofReal_mul (by positivity), h2, ← ENNReal.ofReal_mul hcov.le, hRN]
  obtain ⟨x, hxL, hx0, hxB⟩ :=
    exists_ne_zero_mem_of_covolume_mul_two_pow_le L volume (s := closedBall 0 R)
      (fun y hy ↦ by simpa [mem_closedBall_zero_iff] using hy)
      (convex_closedBall (0 : E) R) (isCompact_closedBall (0 : E) R) hvol
  exact ⟨x, hxL, hx0, mem_closedBall_zero_iff.mp hxB⟩

end ZLattice
