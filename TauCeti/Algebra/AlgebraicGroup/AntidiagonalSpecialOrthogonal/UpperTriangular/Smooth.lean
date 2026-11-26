/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.UpperTriangular.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.SmoothConnected
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import TauCeti.LinearAlgebra.Matrix.IdealEntries
import TauCeti.LinearAlgebra.Matrix.IsometryMatrices.Basic
import TauCeti.RingTheory.Ideal.Operations

/-!
# Smoothness of the upper triangular subgroup of `SO_l^J`

Let `J_l` be the antidiagonal matrix and `B ⊆ SO_l^J` the subgroup of upper triangular matrices
`g` of determinant one with `g J_l gᵀ = J_l`
(`TauCeti.AntidiagonalSpecialOrthogonal.UpperTriangular`). When `2` is invertible, its coordinate
algebra is smooth.

The infinitesimal lifting criterion reduces this to lifting matrices across a square-zero
quotient `S → S / I`. Lift the entries of an upper triangular point `G` over `S / I` on and
above the diagonal to an upper triangular `g₀`. The error `ε = g₀ J_l g₀ᵀ - J_l` is symmetric
with entries in `I`, and it vanishes at `(i, k)` with `i + k ≥ l`, as `g₀ J_l g₀ᵀ` and `J_l` do for
upper triangular `g₀`.
Since `J_l` is symmetric with `J_l⁻¹ = J_l`, the square-zero correction of `g₀ᵀ`
(`Matrix.mul_one_add_mem_isometryMatrices_of_sq_eq_bot`), transposed, is `g = (1 + δ) g₀` with
`δ = -½ ε J_l`, whose entry at `(i, j)` is `-½ ε_{i, l - 1 - j}`. So `δ` is upper triangular, and
`g` is upper triangular with `g J_l gᵀ = J_l`. Its determinant squares to one and is congruent to
one modulo `I`, so it is one since `2` is invertible (`Ideal.eq_one_of_sq_eq_one_of_sub_one_mem`).

## Main declarations

* `TauCeti.AntidiagonalSpecialOrthogonal.UpperTriangular.map_quotient_mk_surjective_of_sq_eq_bot`:
  upper triangular points of `SO_l^J` lift across square-zero quotients when `2` is invertible.
* `TauCeti.AntidiagonalSpecialOrthogonal.UpperTriangular.instSmoothCoordinateHopfAlgebra`,
  `smoothCommHopfAlgProperty_coordinateHopfAlgebra`: the coordinate algebra of the upper
  triangular subgroup of `SO_l^J` is smooth when `2` is invertible.

## References

* The Stacks Project, Tags 00TH and 00TN, for formal smoothness and smooth algebras.

The infinitesimal lifting follows `TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Smooth`, and
the correction is `Matrix.mul_one_add_mem_isometryMatrices_of_sq_eq_bot`, kept upper triangular.
-/

public section

open Matrix WithConv

namespace TauCeti.AntidiagonalSpecialOrthogonal.UpperTriangular

universe u

noncomputable section

/-! ### Lifting matrices -/

section Lift

variable {l : ℕ} {S : Type*} [CommRing S]

/-- For upper triangular `g`, the entry of `g J_l gᵀ` at `(i, k)` vanishes when `i + k ≥ l`. -/
private theorem mul_formMatrix_mul_transpose_apply_eq_zero {g : Matrix (Fin l) (Fin l) S}
    (hg : g.IsUpperTriangular) {i k : Fin l} (hik : l ≤ (i : ℕ) + k) :
    (g * formMatrix S l * gᵀ) i k = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [mul_formMatrix_apply, transpose_apply]
  by_cases hij : i ≤ Fin.rev j
  · have hkj : j < k := by
      rw [Fin.le_def, Fin.val_rev] at hij
      rw [Fin.lt_def]
      omega
    rw [hg hkj, mul_zero]
  · rw [show g i j.rev = 0 from hg (not_le.mp hij), zero_mul]

/-- **The upper triangular correction.** If `g₀` is upper triangular and `J_l - g₀ J_l g₀ᵀ` has
entries in a square-zero ideal `I`, then the transpose of the square-zero correction of `g₀ᵀ`
(`Matrix.mul_one_add_mem_isometryMatrices_of_sq_eq_bot`) is upper triangular, preserves `J_l` and
is congruent to `g₀` modulo `I`. -/
private theorem exists_correction [Invertible (2 : S)] {I : Ideal S} (hI : I ^ 2 = ⊥)
    {g₀ : Matrix (Fin l) (Fin l) S} (hg₀ : g₀.IsUpperTriangular)
    (hE : ∀ i j, (formMatrix S l - g₀ * formMatrix S l * g₀ᵀ) i j ∈ I) :
    ∃ g : Matrix (Fin l) (Fin l) S, g.IsUpperTriangular ∧
      g * formMatrix S l * gᵀ = formMatrix S l ∧
      g.map (Ideal.Quotient.mk I) = g₀.map (Ideal.Quotient.mk I) := by
  obtain ⟨hX, hZ⟩ := mul_one_add_mem_isometryMatrices_of_sq_eq_bot hI (transpose_formMatrix S l)
    isUnit_det_formMatrix (by rwa [transpose_transpose])
  rw [transpose_transpose, inv_eq_left_inv formMatrix_mul_self] at hX hZ
  set Z : Matrix (Fin l) (Fin l) S :=
    (⅟2 : S) • (formMatrix S l * (formMatrix S l - g₀ * formMatrix S l * g₀ᵀ)) with hZ_def
  -- The correction stays upper triangular, as the error vanishes at `(i, k)` with `i + k ≥ l`.
  have hZ_upper : Zᵀ.IsUpperTriangular := fun i j hji ↦ by
    have hle : l ≤ ((Fin.rev j : Fin l) : ℕ) + i := by
      rw [Fin.val_rev]
      simp only [id, Fin.lt_def] at hji
      omega
    rw [transpose_apply, hZ_def, Matrix.smul_apply, formMatrix_mul_apply, Matrix.sub_apply,
      mul_formMatrix_mul_transpose_apply_eq_zero hg₀ hle, formMatrix_apply_eq_zero hle,
      sub_zero, smul_zero]
  refine ⟨(g₀ᵀ * (1 + Z))ᵀ, ?_, ?_, ?_⟩
  · rw [transpose_mul, transpose_transpose, transpose_add, transpose_one]
    exact (blockTriangular_one.add hZ_upper).mul hg₀
  · rw [transpose_transpose]
    exact mem_isometryMatrices.mp hX
  · rw [← Ideal.mk_ker (I := I)] at hZ
    rw [transpose_map, Matrix.map_mul, Matrix.map_add _ (map_add _),
      Matrix.map_one _ (map_zero _) (map_one _), forall_mem_ker_iff_map_eq_zero.mp hZ, add_zero,
      mul_one, transpose_map, transpose_transpose]

/-- **Upper triangular points of `SO_l^J` lift across square-zero quotients** when `2` is
invertible. -/
theorem map_quotient_mk_surjective_of_sq_eq_bot [Invertible (2 : S)] (I : Ideal S)
    (hI : I ^ 2 = (⊥ : Ideal S)) :
    Function.Surjective (pointsSubgroupMap (l := l) (Ideal.Quotient.mk I)) := by
  classical
  intro g
  obtain ⟨hSO, hUT⟩ := (UpperTriangular.mem_pointsSubgroup_iff _).mp g.property
  obtain ⟨hdet, hJ⟩ := (AntidiagonalSpecialOrthogonal.mem_pointsSubgroup_iff _).mp hSO
  set G : Matrix (Fin l) (Fin l) (S ⧸ I) :=
    ((g : GL (Fin l) (S ⧸ I)) : Matrix (Fin l) (Fin l) (S ⧸ I))
  -- Lift the entries on and above the diagonal.
  choose a ha using fun i j ↦ Ideal.Quotient.mk_surjective (G i j)
  set g₀ : Matrix (Fin l) (Fin l) S := of fun i j ↦ if i ≤ j then a i j else 0 with hg₀_def
  have hg₀ : g₀.IsUpperTriangular := fun i j hji ↦ by
    simp only [hg₀_def, of_apply, ite_eq_right_iff]
    exact fun h ↦ absurd h (not_le.mpr hji)
  have hg₀_map : g₀.map (Ideal.Quotient.mk I) = G := by
    ext i j
    simp only [hg₀_def, map_apply, of_apply]
    split_ifs with hij
    · exact ha i j
    · rw [map_zero]
      exact (hUT (not_le.mp hij)).symm
  have hE : ∀ i j, (formMatrix S l - g₀ * formMatrix S l * g₀ᵀ) i j ∈ I := by
    rw [← Ideal.mk_ker (I := I), forall_mem_ker_iff_map_eq_zero, Matrix.map_sub _ (map_sub _),
      Matrix.map_mul, Matrix.map_mul, transpose_map, hg₀_map,
      map_formMatrix S l _ (map_zero _) (map_one _), hJ, sub_self]
  -- Correct it.
  obtain ⟨g₁, hg₁_upper, hg₁J, hg₁_map⟩ := exists_correction hI hg₀ hE
  rw [hg₀_map] at hg₁_map
  -- Its determinant squares to one and is one modulo `I`, hence one.
  have hdet_sq : g₁.det ^ 2 = 1 := by
    have h := congrArg Matrix.det hg₁J
    rw [det_mul, det_mul, det_transpose] at h
    apply isUnit_det_formMatrix.mul_left_cancel
    linear_combination h
  have hdet₁ : g₁.det = 1 := by
    refine Ideal.eq_one_of_sq_eq_one_of_sub_one_mem hI (isUnit_of_invertible 2) ?_ hdet_sq
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, RingHom.map_det, RingHom.mapMatrix_apply,
      hg₁_map, hdet, map_one, sub_self]
  refine ⟨⟨Matrix.GeneralLinearGroup.mk'' g₁ (by rw [hdet₁]; exact isUnit_one),
    (UpperTriangular.mem_pointsSubgroup_iff _).mpr
      ⟨(AntidiagonalSpecialOrthogonal.mem_pointsSubgroup_iff _).mpr ⟨hdet₁, hg₁J⟩,
        hg₁_upper⟩⟩, ?_⟩
  apply Subtype.ext
  rw [UpperTriangular.coe_pointsSubgroupMap]
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply]
  exact congrArg (fun M : Matrix (Fin l) (Fin l) (S ⧸ I) ↦ M i j) hg₁_map

end Lift

/-! ### Smoothness -/

variable (R : Type u) [CommRing R] (l : ℕ)

/-- The coordinate algebra of the upper triangular subgroup of `SO_l^J` is formally smooth when
`2` is invertible. -/
private instance instFormallySmoothCoordinateHopfAlgebra [Invertible (2 : R)] :
    Algebra.FormallySmooth R (coordinateHopfAlgebra R l) := by
  apply Algebra.FormallySmooth.of_comp_surjective
  intro B _ _ I hI f
  let : Invertible (2 : B) :=
    (Invertible.map (algebraMap R B) 2).copy 2 (map_ofNat (algebraMap R B) 2).symm
  obtain ⟨t, ht⟩ := map_quotient_mk_surjective_of_sq_eq_bot I hI
    (pointsMulEquiv R l (A := B ⧸ I) (toConv f))
  let g : WithConv (coordinateHopfAlgebra R l →ₐ[R] B) := (pointsMulEquiv R l (A := B)).symm t
  refine ⟨g.ofConv, ?_⟩
  apply toConv_injective
  apply (pointsMulEquiv R l (A := B ⧸ I)).injective
  rw [← AlgHom.mapValue_apply, pointsMulEquiv_mapValue]
  have hg : pointsMulEquiv R l (A := B) g = t := (pointsMulEquiv R l (A := B)).apply_symm_apply t
  rw [hg]
  have hq : ((Ideal.Quotient.mkₐ R I : B →ₐ[R] B ⧸ I) : B →+* B ⧸ I) = Ideal.Quotient.mk I := by
    rw [← AlgHom.toRingHom_eq_coe]
    exact Ideal.Quotient.mkₐ_toRingHom (R₁ := R) I
  rw [hq]
  exact ht

/-- **The upper triangular subgroup of `SO_l^J` is smooth** when `2` is invertible: its
coordinate algebra is smooth. -/
instance instSmoothCoordinateHopfAlgebra [Invertible (2 : R)] :
    Algebra.Smooth R (coordinateHopfAlgebra R l) := by
  let _ : Algebra.FinitePresentation R (coordinateHopfAlgebra R l) :=
    Algebra.FinitePresentation.quotient (definingHopfIdeal_toIdeal_fg R l)
  exact ⟨inferInstance, inferInstance⟩

/-- The coordinate Hopf algebra of the upper triangular subgroup of `SO_l^J` satisfies the
smoothness object property when `2` is invertible. -/
theorem smoothCommHopfAlgProperty_coordinateHopfAlgebra [Invertible (2 : R)] :
    smoothCommHopfAlgProperty R (coordinateHopfAlgebra R l) := by
  rw [smoothCommHopfAlgProperty_iff]
  infer_instance

end

end TauCeti.AntidiagonalSpecialOrthogonal.UpperTriangular
