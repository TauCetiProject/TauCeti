/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.L2OpNorm
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Bessel.LevelDilation
import TauCeti.Analysis.Matrix.EntrywiseOpNorm

/-!
# Level dilations contract the unipotent Bessel group

Let `𝕜` be `ℝ` or `ℂ` (any `RCLike` field) and `d = TauCeti.levelDilation ϱ μ t` the diagonal
matrix `diag(t ^ (ϱ - level i))` on the basis of the split form, for a unit `t` with `1 ≤ ‖t‖`.
For a matrix `u` that is block upper unitriangular for the levels, as are the elements of the
unipotent Bessel group `TauCeti.besselU`, the entries of `d⁻¹ * (u - 1) * d` are those of
`u - 1` multiplied by `t ^ (level i - level j)` with `level i < level j`, so each has norm at most
`‖u‖ / ‖t‖`. Bounding the `ℓ²` operator norm by the size `r` of the basis times the largest
entry gives

`‖d⁻¹ * u * d‖ ≤ 1 + r * ‖u‖ / ‖t‖`.

For real `T ≥ 1` and `t = T`, which is self-adjoint, `d` lies in the unitary group of the split
form, and this gives the dilations of the unipotent Bessel group.

## Main results

* `TauCeti.norm_inv_levelDilation_mul_mul_le`: the bound above, for block unitriangular `u`.
* `TauCeti.exists_levelDilation`: for real `T ≥ 1` there is `d` in the unitary group of the split
  form of any middle block `M` with `(d⁻¹ * u * d) i j = T ^ (level i - level j) * u i j` for every
  matrix `u`, and `‖d⁻¹ * u * d‖ ≤ 1 + r * ‖u‖ / T` for `u` in the unipotent Bessel group.

## References

* the folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207, declaration `New.RealPlace.exists_dilation`.
* H. Xue, *Bessel models for real unitary groups: the tempered case*, Duke Math. J. 172 (2023).
-/

public section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {ϱ : ℕ} {μ : Type*} [Fintype μ] [DecidableEq μ]

/-- The entries of a level-unitriangular matrix minus `1`, multiplied by
`t ^ (level i - level j)`, have norm at most `‖u‖ / ‖t‖` when `1 ≤ ‖t‖`. -/
private theorem norm_zpow_mul_sub_one_apply_le {t : 𝕜ˣ} (ht : 1 ≤ ‖(t : 𝕜)‖)
    {u : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) 𝕜} (hu : u.BlockUnitriangular splitLevel)
    (i j : SplitIndex ϱ μ) :
    ‖((t ^ ((splitLevel i : ℤ) - splitLevel j) : 𝕜ˣ) : 𝕜) * (u - 1) i j‖ ≤ ‖u‖ / ‖(t : 𝕜)‖ := by
  rcases lt_or_ge (splitLevel i) (splitLevel j) with hlt | hge
  · have hij : i ≠ j := fun h ↦ hlt.ne (congrArg splitLevel h)
    have hpow : ‖(t : 𝕜)‖ ^ ((splitLevel i : ℤ) - splitLevel j) ≤ ‖(t : 𝕜)‖⁻¹ := by
      rw [← _root_.zpow_neg_one]
      exact zpow_le_zpow_right₀ ht (by omega)
    rw [Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow, Matrix.sub_apply, one_apply_ne hij,
      sub_zero, div_eq_inv_mul]
    exact mul_le_mul hpow (norm_apply_le_l2_opNorm u i j) (norm_nonneg _) (by positivity)
  · -- below and on the diagonal blocks, `u` agrees with the identity
    have h0 : (u - 1) i j = 0 := by
      rw [Matrix.sub_apply, sub_eq_zero]
      rcases hge.lt_or_eq with hgt | heq
      · rw [hu.blockTriangular hgt, one_apply_ne fun h ↦ hgt.ne (congrArg splitLevel h).symm]
      · exact hu.apply_of_eq heq.symm
    rw [h0, mul_zero, norm_zero]
    positivity

/-- **Level dilations contract the level-unitriangular matrices.** For a unit `t` with
`1 ≤ ‖t‖` and a matrix `u` that is block upper unitriangular for the levels (for instance an
element of the unipotent Bessel group `TauCeti.besselU`), conjugation by the level dilation `d`
gives `‖d⁻¹ * u * d‖ ≤ 1 + r * ‖u‖ / ‖t‖`, where `r` is the size of the basis. -/
theorem norm_inv_levelDilation_mul_mul_le {t : 𝕜ˣ} (ht : 1 ≤ ‖(t : 𝕜)‖)
    {u : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) 𝕜} (hu : u.BlockUnitriangular splitLevel) :
    ‖(((levelDilation ϱ μ t)⁻¹ : GL (SplitIndex ϱ μ) 𝕜) :
        Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) 𝕜) * u *
        ((levelDilation ϱ μ t : GL (SplitIndex ϱ μ) 𝕜) :
          Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) 𝕜)‖ ≤
      1 + Fintype.card (SplitIndex ϱ μ) * ‖u‖ / ‖(t : 𝕜)‖ := by
  set D : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) 𝕜 := ↑(levelDilation ϱ μ t)
  set D' : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) 𝕜 := ↑(levelDilation ϱ μ t)⁻¹
  have hsplit : D' * u * D = 1 + D' * (u - 1) * D := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul, add_sub_cancel]
  have hX : ‖D' * (u - 1) * D‖ ≤ Fintype.card (SplitIndex ϱ μ) * (‖u‖ / ‖(t : 𝕜)‖) := by
    rw [l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ ?_
    refine norm_toEuclideanLin_le_of_entry_le_square (fun i j ↦ ?_) x
    rw [inv_levelDilation_mul_mul_apply]
    exact norm_zpow_mul_sub_one_apply_le ht hu i j
  rw [hsplit, mul_div_assoc]
  exact (norm_add_le _ _).trans (add_le_add l2_opNorm_one_le hX)

/-- **Dilations of the unipotent Bessel group.** For real `T ≥ 1` and any middle block `M`, there
is an element `d` of the unitary group of the split form of `M` (the level dilation
`diag(T ^ (ϱ - level i))`) such that `(d⁻¹ * u * d) i j = T ^ (level i - level j) * u i j` for every
matrix `u`, and `‖d⁻¹ * u * d‖ ≤ 1 + r * ‖u‖ / T` for every `u` in the unipotent Bessel group,
where `r` is the size of the basis. -/
theorem exists_levelDilation {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Matrix (κ ⊕ Unit) (κ ⊕ Unit) 𝕜) {T : ℝ} (hT : 1 ≤ T) :
    ∃ d : unitaryGroupOf (splitGram ϱ M),
      (∀ (u : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) 𝕜) (i j : BesselIndex ϱ κ),
        ((((d : GL (BesselIndex ϱ κ) 𝕜)⁻¹ : GL (BesselIndex ϱ κ) 𝕜) :
            Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) 𝕜) * u * (d : GL (BesselIndex ϱ κ) 𝕜)) i j =
          (T : 𝕜) ^ ((splitLevel i : ℤ) - splitLevel j) * u i j) ∧
      ∀ u ∈ besselU ϱ M,
        ‖(((d⁻¹ * u * d : unitaryGroupOf (splitGram ϱ M)) : GL (BesselIndex ϱ κ) 𝕜) :
            Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) 𝕜)‖ ≤
          1 + Fintype.card (BesselIndex ϱ κ) * ‖((u : GL (BesselIndex ϱ κ) 𝕜) :
            Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) 𝕜)‖ / T := by
  have hT0 : (T : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr (one_pos.trans_le hT).ne'
  let t : 𝕜ˣ := Units.mk0 (T : 𝕜) hT0
  have htT : ‖(t : 𝕜)‖ = T := by
    rw [Units.val_mk0, RCLike.norm_ofReal, abs_of_pos (one_pos.trans_le hT)]
  have ht : star (t : 𝕜) = t := by
    rw [Units.val_mk0]
    exact RCLike.conj_ofReal T
  refine ⟨⟨levelDilation ϱ (κ ⊕ Unit) t, levelDilation_mem_unitaryGroupOf ht M⟩,
    fun u i j ↦ ?_, fun u hu ↦ ?_⟩
  · rw [inv_levelDilation_mul_mul_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  · have h := norm_inv_levelDilation_mul_mul_le (htT ▸ hT) ((mem_besselU ϱ M).mp hu)
    rw [htT] at h
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul] using h

end TauCeti
