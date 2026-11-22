/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import TauCeti.NumberTheory.Height.Arakelov.Subspace.Covolume

import TauCeti.MeasureTheory.Group.GeometryOfNumbers.Euclidean

/-!
# Sharp Minkowski-ball Siegel lemma for a number-field subspace

Applying Minkowski's shortest-vector bound in Euclidean space
(`ZLattice.exists_ne_zero_mem_norm_le`) to the lattice `W.integerLattice` scaled by
`W.mulMixedSubmodule (multSqrt K)` yields the sharp `(D * m)`-dimensional Minkowski-ball form of
Siegel's lemma for a nonzero `m`-dimensional `K`-subspace `W` of `ι → K`, without using successive
minima or kernel-basis extraction:

`H₂(z) ≤ 2 / √(D * π) * Γ(D * m / 2 + 1) ^ (1 / (D * m)) * |discr K| ^ (1 / (2 * D)) *`
  `H₂(W) ^ (1 / m)`.

## Main results

* `Submodule.exists_ne_zero_mem_integerPoints_height2_le_mul_Gamma_rpow`: the sharp Minkowski-ball
  Euclidean Siegel lemma for a number-field subspace.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  §2.9, Corollary 2.9.7.
* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace Theorem*,
  Ann. of Math. **177** (2013), 513–590, §13, Lemma 13.1.
-/

public section

noncomputable section

open MeasureTheory Module NumberField NumberField.mixedEmbedding TauCeti
open TauCeti.NumberField.mixedEmbedding

namespace Submodule

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι] [LinearOrder ι]

omit [LinearOrder ι] in
open Classical in
/-- For any integral point `z ∈ W.integerPoints`, `height2 z` is bounded by the Euclidean norm of
`W.mulMixedSubmodule (multSqrt K) (W.integerPointsEquivIntegerLattice z)` divided by
`√[K : ℚ]`. -/
private theorem height2_le_norm_mulMixedSubmodule_multSqrt_div [Fintype ι]
    (W : Submodule K (ι → K)) (z : W.integerPoints) :
    height2 (fun i ↦ ((z : ι → 𝓞 K) i : K)) ≤
      ‖W.mulMixedSubmodule (multSqrt K)
          (W.integerPointsEquivIntegerLattice z : W.euclideanSpan)‖ /
        √(finrank ℚ K : ℝ) := by
  refine (height2_le_sqrt_sum_mult_mul_sum_norm_sq_div (z : ι → 𝓞 K)).trans_eq ?_
  rw [← W.norm_sq_mulMixedSubmodule_multSqrt z, Real.sqrt_div (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]

open Classical in
/-- **Fixed-field Siegel's lemma for a subspace (sharp Minkowski-ball constant).**
Every nonzero `K`-subspace `W` of `ι → K` of dimension `m` contains a nonzero integral point
`z ∈ W.integerPoints` (`W ∩ 𝓞_K^ι`) with
`height2 z ≤ 2 / √(D * π) * Γ(D * m / 2 + 1) ^ (1 / (D * m)) * |discr K| ^ (1 / (2 * D)) *
  W.subspaceHeight ^ (1 / m)`, where `D = [K : ℚ]`. -/
theorem exists_ne_zero_mem_integerPoints_height2_le_mul_Gamma_rpow {W : Submodule K (ι → K)}
    (hW : W ≠ ⊥) :
    ∃ z ∈ W.integerPoints, z ≠ 0 ∧
      height2 (fun i ↦ (z i : K)) ≤
        2 / √((finrank ℚ K : ℝ) * Real.pi) *
          Real.Gamma ((finrank ℚ K * finrank K W : ℝ) / 2 + 1) ^
            ((finrank ℚ K * finrank K W : ℝ)⁻¹) *
          |(discr K : ℝ)| ^ (1 / (2 * (finrank ℚ K : ℝ))) *
          W.subspaceHeight ^ (finrank K W : ℝ)⁻¹ := by
  cases nonempty_fintype ι
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  set D : ℕ := finrank ℚ K
  set m : ℕ := finrank K W
  set N : ℕ := D * m
  have hD : (0 : ℝ) < D := Nat.cast_pos.mpr finrank_pos
  have hfin : finrank ℝ W.euclideanSpan = N := W.finrank_euclideanSpan
  have : Nontrivial W.euclideanSpan := by
    rw [← finrank_pos_iff (R := ℝ), hfin]
    exact Nat.mul_pos finrank_pos finrank_pos
  let L' := ZLattice.comap ℝ W.integerLattice
    (W.mulMixedSubmoduleEquiv (isUnit_multSqrt K)).symm.toLinearMap
  -- Apply Minkowski's shortest-vector bound to the scaled lattice `L'`.
  obtain ⟨x, hxL', hx0, hx_norm⟩ := ZLattice.exists_ne_zero_mem_norm_le L'
  set z : W.integerPoints :=
    (W.integerPointsEquivComapMulMixed (isUnit_multSqrt K)).symm ⟨x, hxL'⟩
  have hz_ne : (z : ι → 𝓞 K) ≠ 0 := fun hz0 ↦ hx0 <| congrArg Subtype.val <|
    (W.integerPointsEquivComapMulMixed (isUnit_multSqrt K)).symm.map_eq_zero_iff.mp
      (Subtype.ext hz0)
  have hTx :
      W.mulMixedSubmodule (multSqrt K) (W.integerPointsEquivIntegerLattice z : W.euclideanSpan) =
        x := by
    rw [← W.coe_integerPointsEquivComapMulMixed_apply (isUnit_multSqrt K) z]
    exact congrArg Subtype.val
      ((W.integerPointsEquivComapMulMixed (isUnit_multSqrt K)).apply_symm_apply ⟨x, hxL'⟩)
  rw [hfin, W.covolume_comap_mulMixedSubmodule_multSqrt_rpow hW] at hx_norm
  refine ⟨z, z.property, hz_ne, ?_⟩
  calc height2 (fun i ↦ ((z : ι → 𝓞 K) i : K))
      ≤ ‖x‖ / √(D : ℝ) := hTx ▸ height2_le_norm_mulMixedSubmodule_multSqrt_div W z
    _ ≤ (2 / √Real.pi * Real.Gamma ((N : ℝ) / 2 + 1) ^ ((N : ℝ)⁻¹) *
          (|(discr K : ℝ)| ^ (1 / (2 * (D : ℝ))) * W.subspaceHeight ^ ((m : ℝ)⁻¹))) /
          √(D : ℝ) := div_le_div_of_nonneg_right hx_norm (Real.sqrt_nonneg _)
    _ = 2 / √((D : ℝ) * Real.pi) *
          Real.Gamma ((D * m : ℝ) / 2 + 1) ^ ((D * m : ℝ)⁻¹) *
          |(discr K : ℝ)| ^ (1 / (2 * (D : ℝ))) *
          W.subspaceHeight ^ ((m : ℝ)⁻¹) := by
        rw [Nat.cast_mul, Real.sqrt_mul hD.le]
        ring

end Submodule

end
