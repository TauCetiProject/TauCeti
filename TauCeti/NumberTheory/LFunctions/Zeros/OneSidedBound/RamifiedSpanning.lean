/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FixedSubmodule
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Spanning
import TauCeti.NumberTheory.ModularForms.ThetaLift.RamifiedCodimension

/-!
# Spanning under cyclic ramification conditions

At a separated theta-lift level, the simultaneous cyclic norm kernels lose only a small share
of the source dimension. Applying greedy selection to that subspace gives a collection of
translates with controlled cost that still spans most of the target. The cyclic operators on the
source need not commute for this form of the argument.

The constants and the use of the ramified subspace are from `New.Data.enough_forms` in
`grh/src/New/Reduction/ShortAndEnough.lean` of [lsernau/grh-lean][short-proof].

[short-proof]:
  https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/New/Reduction/ShortAndEnough.lean
-/

public section

open Module Finset

namespace TauCeti.IsSpread

/-- Select few translates of the simultaneous cyclic norm kernels at level `N`. If each fixed
space has dimension at most `dim V / (N - 1)` and the level budget is `#ι · b⁸ < N`, the selected
images span at least `1 - 4 / b²` of the target. The selection cost counts each translate with
weight equal to the dimension of the common kernel, not the dimension of the full source. -/
theorem exists_card_mul_finrank_le_and_le_finrank_biSup_map_cyclicNormKernels
    {K V W Θ ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype ι] {B : Θ → V →ₗ[K] W} {b N : ℕ}
    (hB : IsSpread B (3 / (16 * (b : ℝ) ^ 2))) (hb : b ≠ 0) (hV : 0 < finrank K V)
    (z : ι → Module.End K V) (hN : Fintype.card ι * b ^ 8 < N)
    (hz : ∀ w, z w ^ (N - 1) = 1)
    (hfix : ∀ w, (N - 1) * finrank K (z w).fixedSubmodule ≤ finrank K V) :
    let U := ⨅ w, LinearMap.ker (∑ i ∈ range (N - 1), z w ^ i)
    ∃ t : Finset Θ, #t * finrank K U ≤ 5 * Real.log (1 + 2 * (b : ℝ) ^ 2) * finrank K W ∧
      (1 - 4 / (b : ℝ) ^ 2) * finrank K W ≤ finrank K ↥(⨆ s ∈ t, U.map (B s)) := by
  intro U
  have hN₁ : 1 ≤ N := (Nat.zero_le _).trans_lt hN
  have hdim : (1 - (Fintype.card ι : ℝ) / (N - 1)) * finrank K V ≤ (finrank K U : ℝ) :=
    OneSidedBound.le_finrank_ramifiedSourceForms z hN₁ le_rfl hz hfix
  have hbudget : (Fintype.card ι : ℝ) * (b : ℝ) ^ 8 ≤ (N : ℝ) - 1 := by
    have h : Fintype.card ι * b ^ 8 ≤ N - 1 := by omega
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hN₁, Nat.cast_one] using
      (Nat.cast_le (α := ℝ)).mpr h
  have hfrac : (Fintype.card ι : ℝ) / (N - 1) ≤ ((b : ℝ) ^ 8)⁻¹ := by
    obtain rfl | hN₂ := hN₁.eq_or_lt
    · simp
    · have hden : (0 : ℝ) < N - 1 := sub_pos.mpr (by exact_mod_cast hN₂)
      rwa [← one_div, div_le_div_iff₀ hden (pow_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hb)) _),
        one_mul]
  refine hB.exists_card_mul_finrank_le_and_le_finrank_biSup_map (Nat.cast_ne_zero.mpr hb) hV U ?_
  linarith only [hdim, mul_le_mul_of_nonneg_right hfrac (Nat.cast_nonneg (finrank K V))]

end TauCeti.IsSpread
