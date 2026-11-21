/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import TauCeti.Algebra.Module.ZLattice.RationalSubspace
public import TauCeti.NumberTheory.Height.Arakelov.Subspace.Bounds
public import TauCeti.NumberTheory.NumberField.SubspaceIntegerPoints

import TauCeti.Algebra.Module.ZLattice.Covolume
import TauCeti.MeasureTheory.Group.GeometryOfNumbers
import TauCeti.NumberTheory.Height.Arakelov.Comparison
import TauCeti.NumberTheory.Height.Arakelov.SiegelsLemma
import TauCeti.NumberTheory.Height.Arakelov.Subspace.Covolume
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.MulVolume

/-!
# Minkowski-ball and Euclidean Siegel bounds for subspaces and rational systems

Let `K` be a number field of degree `D = [K : ℚ]` and discriminant `discr K`. For any nonzero
`K`-subspace `W` of `ι → K` of dimension `m`, there exists a nonzero integral point
`z ∈ W.integerPoints` (`W ∩ 𝓞_K^ι`) whose absolute Euclidean height satisfies the sharp `(D * m)`-
dimensional Minkowski-ball bound

```text
height2 z ≤ 2 / √(D * π) * Γ(D * m / 2 + 1) ^ (1 / (D * m)) *
              |discr K| ^ (1 / (2 * D)) * W.subspaceHeight ^ (1 / m).
```

The proof applies Minkowski's shortest-vector bound (`ZLattice.exists_ne_zero_mem_norm_le`) inside
`W.euclideanSpan` to the image of `W.integerLattice` under the coordinatewise real-linear
automorphism `W.mulMixedSubmodule (multSqrt K)` scaling real places by `1` and complex places by
`√2`. By `Submodule.det_mulMixedSubmodule` and `algebraNorm_multSqrt`, this scaling has real
determinant `2 ^ (r₂ * m)`, cancelling the `2 ^ (-r₂ * m)` factor in Schmidt's covolume identity
(`Submodule.covolume_integerLattice`) while converting the ambient Euclidean norm squared into
the multiplicity-weighted sum `∑ w, w.mult * ∑ i, ‖w.embedding (z i)‖ ^ 2`
(`Submodule.norm_sq_mulMixedSubmodule_multSqrt`). Weighted AM–GM and integrality at finite places
(`TauCeti.height2_le_sqrt_sum_mult_mul_sum_norm_sq_div`) then bound `height2 z`.

We also record the `K`-vector form for subspaces (`Submodule.exists_ne_zero_mem_height2_le`) and
the rational `ℤ`-point / `ℤ`-matrix Euclidean height specializations
(`Submodule.exists_ne_zero_mem_intPoints_height2_le` and
`Matrix.exists_ne_zero_int_mulVec_eq_zero_height2_le`).

## Main results

* `Submodule.exists_ne_zero_mem_integerPoints_height2_le_mul_Gamma_rpow`: the sharp Minkowski-ball
  form of Siegel's lemma for a nonzero subspace of `ι → K`.
* `Submodule.exists_ne_zero_mem_height2_le`: the `K`-vector form for a nonzero subspace.
* `Submodule.exists_ne_zero_mem_intPoints_height2_le`: the specialization to rational subspaces
  with solutions in `ℤ`.
* `Matrix.exists_ne_zero_int_mulVec_eq_zero_height2_le`: the specialization to rational matrices
  with integer solutions.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace Theorem*,
  Ann. of Math. **177** (2013), 513–590, §13, Lemma 13.1.
* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32.
* W. M. Schmidt, *On heights of algebraic subspaces and diophantine approximations*, Ann. of Math.
  **85** (1967), 430–472, §3.
-/

noncomputable section

open MeasureTheory Module NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding Set TauCeti TauCeti.NumberField.mixedEmbedding
open scoped BigOperators Matrix

public section

namespace Submodule

section NumberField

variable {K ι : Type*} [Field K] [NumberField K] [Finite ι] [LinearOrder ι]

open Classical in
/-- The `(D * m)`-th root of the covolume of `W.integerLattice` scaled by
`W.mulMixedSubmodule (multSqrt K)` is `|discr K| ^ (1 / (2 * D)) * W.subspaceHeight ^ (1 / m)`:
the `2 ^ (r₂ * m)` determinant cancels the `2 ^ (-r₂ * m)` factor in Schmidt's covolume formula. -/
private theorem covolume_comap_mulMixedSubmodule_multSqrt_rpow [Fintype ι]
    {W : Submodule K (ι → K)} (hW : W ≠ ⊥)
    (eT : W.euclideanSpan ≃L[ℝ] W.euclideanSpan)
    (heT : (eT.toLinearEquiv : W.euclideanSpan →ₗ[ℝ] W.euclideanSpan) =
      W.mulMixedSubmodule (multSqrt K)) :
    ZLattice.covolume (ZLattice.comap ℝ W.integerLattice eT.symm.toLinearMap) ^
        (((finrank ℚ K * finrank K W : ℕ) : ℝ)⁻¹) =
      |(discr K : ℝ)| ^ (1 / (2 * (finrank ℚ K : ℝ))) *
        W.subspaceHeight ^ (finrank K W : ℝ)⁻¹ := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  set D : ℕ := finrank ℚ K
  set m : ℕ := finrank K W
  have hD : (0 : ℝ) < D := Nat.cast_pos.mpr finrank_pos
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr finrank_pos
  have hdet_symm : |eT.symm.toLinearMap.det|⁻¹ = (2 : ℝ) ^ (nrComplexPlaces K * m) := by
    rw [ContinuousLinearEquiv.toLinearEquiv_symm, LinearEquiv.det_coe_symm, heT, abs_inv, inv_inv,
      W.det_mulMixedSubmodule, algebraNorm_multSqrt, ← pow_mul, abs_of_pos (by positivity)]
  have hcov :
      ZLattice.covolume (ZLattice.comap ℝ W.integerLattice eT.symm.toLinearMap) =
        (√|(discr K : ℝ)|) ^ m * W.subspaceHeight ^ D := by
    rw [ZLattice.covolume_comap_continuousLinearEquiv W.integerLattice eT.symm volume,
      W.covolume_integerLattice, hdet_symm, mul_pow, ← pow_mul, inv_pow]
    dsimp only [D, m]
    field_simp
  rw [hcov, Real.mul_rpow (by positivity) (pow_nonneg (Submodule.subspaceHeight_pos W).le _),
    Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _),
    ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_natCast,
    ← Real.rpow_mul (Submodule.subspaceHeight_pos W).le, Nat.cast_mul]
  congr 1 <;> congr 1 <;> field_simp [hD.ne', hm.ne']

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
  set T := W.mulMixedSubmodule (multSqrt K)
  have hT_det : LinearMap.det T ≠ 0 := by
    rw [W.det_mulMixedSubmodule, algebraNorm_multSqrt]
    positivity
  let eT : W.euclideanSpan ≃L[ℝ] W.euclideanSpan :=
    (T.equivOfDetNeZero hT_det).toContinuousLinearEquiv
  have heT : (eT.toLinearEquiv : W.euclideanSpan →ₗ[ℝ] W.euclideanSpan) = T := by
    dsimp only [eT]
    rw [LinearEquiv.toLinearEquiv_toContinuousLinearEquiv, LinearEquiv.coe_ofIsUnitDet]
  let L' : Submodule ℤ W.euclideanSpan := ZLattice.comap ℝ W.integerLattice eT.symm.toLinearMap
  -- Apply Minkowski's shortest-vector bound to the scaled lattice `T (W.integerLattice)`.
  obtain ⟨x, hxL', hx0, hx_norm⟩ := ZLattice.exists_ne_zero_mem_norm_le L'
  have hwL : eT.symm x ∈ W.integerLattice := hxL'
  set z : W.integerPoints := W.integerPointsEquivIntegerLattice.symm ⟨eT.symm x, hwL⟩
  have hz_ne : (z : ι → 𝓞 K) ≠ 0 := by
    intro hz0
    apply hx0
    have h0 : (⟨eT.symm x, hwL⟩ : W.integerLattice) = 0 :=
      (W.integerPointsEquivIntegerLattice.symm.map_eq_zero_iff).mp (Subtype.ext hz0)
    exact eT.symm.injective ((congrArg Subtype.val h0).trans (map_zero eT.symm).symm)
  have hsum_eq :
      ∑ v : InfinitePlace K, (v.mult : ℝ) * ∑ i : ι, ‖v.embedding ((z : ι → 𝓞 K) i : K)‖ ^ 2 =
        ‖x‖ ^ 2 := by
    have hzw : (W.integerPointsEquivIntegerLattice z : W.euclideanSpan) = eT.symm x :=
      congrArg Subtype.val (W.integerPointsEquivIntegerLattice.apply_symm_apply ⟨eT.symm x, hwL⟩)
    have hTx : T (eT.symm x) = x := by
      rw [← heT]
      exact eT.apply_symm_apply x
    rw [← hTx, ← hzw]
    exact (W.norm_sq_mulMixedSubmodule_multSqrt z).symm
  have hcov_rpow := covolume_comap_mulMixedSubmodule_multSqrt_rpow hW eT heT
  refine ⟨z, z.property, hz_ne, ?_⟩
  rw [hfin, hcov_rpow] at hx_norm
  calc height2 (fun i ↦ ((z : ι → 𝓞 K) i : K))
      ≤ √((∑ v : InfinitePlace K,
            (v.mult : ℝ) * ∑ i : ι, ‖v.embedding ((z : ι → 𝓞 K) i : K)‖ ^ 2) / D) :=
        height2_le_sqrt_sum_mult_mul_sum_norm_sq_div (z : ι → 𝓞 K)
    _ = ‖x‖ / √(D : ℝ) := by
        rw [hsum_eq, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    _ ≤ (2 / √Real.pi * Real.Gamma ((N : ℝ) / 2 + 1) ^ ((N : ℝ)⁻¹) *
          (|(discr K : ℝ)| ^ (1 / (2 * (D : ℝ))) * W.subspaceHeight ^ ((m : ℝ)⁻¹))) /
          √(D : ℝ) := div_le_div_of_nonneg_right hx_norm (Real.sqrt_nonneg _)
    _ = 2 / √((D : ℝ) * Real.pi) *
          Real.Gamma ((D * m : ℝ) / 2 + 1) ^ ((D * m : ℝ)⁻¹) *
          |(discr K : ℝ)| ^ (1 / (2 * (D : ℝ))) *
          W.subspaceHeight ^ ((m : ℝ)⁻¹) := by
        rw [Nat.cast_mul, Real.sqrt_mul hD.le]
        ring

/-- **Fixed-field Siegel's lemma for a subspace (`K`-vector form).**
Every nonzero `K`-subspace `W` of `ι → K` of dimension `m` contains a nonzero vector `x ∈ W` with
`height2 x ≤ √m * |discr K| ^ (1 / (2 * [K : ℚ])) * W.subspaceHeight ^ (1 / m)`. -/
theorem exists_ne_zero_mem_height2_le {W : Submodule K (ι → K)} (hW : W ≠ ⊥) :
    ∃ x ∈ W, x ≠ 0 ∧
      height2 x ≤
        √(finrank K W : ℝ) * |(discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹ *
          W.subspaceHeight ^ (finrank K W : ℝ)⁻¹ := by
  obtain ⟨z, hzW, hz0, hle⟩ := exists_ne_zero_mem_integerPoints_height2_le_sqrt hW
  exact ⟨fun i ↦ (z i : K), mem_integerPoints.mp hzW,
    mt RingOfIntegers.coe_tuple_eq_zero_iff.mp hz0, hle⟩

end NumberField

section Rat

variable {ι : Type*} [Finite ι] [LinearOrder ι]

/-- **Siegel's lemma for a rational subspace, in the Euclidean height.**
Every nonzero subspace `V` of `ℚ^ι` of dimension `m` contains a nonzero integral point
`z ∈ V.intPoints` with `height2 z ≤ √m * V.subspaceHeight ^ (1 / m)`. -/
theorem exists_ne_zero_mem_intPoints_height2_le {V : Submodule ℚ (ι → ℚ)} (hV : V ≠ ⊥) :
    ∃ z ∈ V.intPoints, z ≠ 0 ∧
      height2 (fun i ↦ (z i : ℚ)) ≤
        √(finrank ℚ V : ℝ) * V.subspaceHeight ^ (finrank ℚ V : ℝ)⁻¹ := by
  obtain ⟨z, hzV, hz0, hle⟩ := exists_ne_zero_mem_integerPoints_height2_le_sqrt hV
  let w : V.intPoints := V.integerPointsEquivIntPoints ⟨z, hzV⟩
  have hw0 : (w : ι → ℤ) ≠ 0 := by
    intro h
    apply hz0
    have : (⟨z, hzV⟩ : V.integerPoints) = 0 :=
      (V.integerPointsEquivIntPoints.map_eq_zero_iff).mp (Subtype.ext h)
    exact congrArg Subtype.val this
  have hcoe : (fun i ↦ ((w : ι → ℤ) i : ℚ)) = (fun i ↦ (z i : ℚ)) := by
    ext i
    simp [w, Rat.ringOfIntegersEquiv_apply_coe, RingOfIntegers.coe_eq_algebraMap]
  refine ⟨w, w.property, hw0, ?_⟩
  rw [hcoe]
  simpa [discr_rat, finrank_self] using hle

end Rat

end Submodule

namespace Matrix

section Rat

variable {m ι : Type*} [Fintype m] [Fintype ι]

/-- **Siegel's lemma for a rational linear system, in the Euclidean height.**
For any matrix `A : Matrix m ι ℚ` of `#m < #ι` nonzero rows (without row independence), `A *ᵥ z = 0`
has a nonzero integer solution `z : ι → ℤ` with
`height2 z ≤ √(#ι) * (∏ i, height2 (A.row i)) ^ (1 / (#ι - #m))`. -/
theorem exists_ne_zero_int_mulVec_eq_zero_height2_le {A : Matrix m ι ℚ} (hA : ∀ i, A.row i ≠ 0)
    (hlt : Fintype.card m < Fintype.card ι) :
    ∃ z : ι → ℤ, z ≠ 0 ∧ A *ᵥ (fun i ↦ (z i : ℚ)) = 0 ∧
      height2 (fun i ↦ (z i : ℚ)) ≤
        √(Fintype.card ι : ℝ) *
          (∏ i, height2 (A.row i)) ^ ((Fintype.card ι : ℝ) - Fintype.card m)⁻¹ := by
  obtain ⟨z, hz0, hmul, hle⟩ := exists_ne_zero_mulVec_eq_zero_height2_le_of_card_lt hA hlt
  let w : ι → ℤ := fun i ↦ Rat.ringOfIntegersEquiv (z i)
  have hcoe : (fun i ↦ (w i : ℚ)) = (fun i ↦ (z i : ℚ)) := by
    ext i
    simp [w, Rat.ringOfIntegersEquiv_apply_coe, RingOfIntegers.coe_eq_algebraMap]
  have hw0 : w ≠ 0 := by
    intro h
    apply hz0
    ext1 i
    exact Rat.ringOfIntegersEquiv.injective (by simpa [w] using congrFun h i)
  refine ⟨w, hw0, hcoe.symm ▸ hmul, ?_⟩
  rw [hcoe]
  simpa [discr_rat, finrank_self] using hle

end Rat

end Matrix

end

end
