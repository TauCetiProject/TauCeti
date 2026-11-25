/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.UpperTriangular
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.SmoothConnected
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import TauCeti.LinearAlgebra.Matrix.IdealEntries

/-!
# Smoothness of the upper triangular subgroup of `SO_l^J`

Let `J_l` be the antidiagonal matrix and `B ⊆ SO_l^J` the subgroup of upper triangular matrices
`g` of determinant one with `g J_l gᵀ = J_l`
(`TauCeti.AntidiagonalSpecialOrthogonal.UpperTriangular`). When `2` is invertible, its coordinate
algebra is smooth.

The infinitesimal lifting criterion reduces this to lifting matrices across a square-zero
quotient `S → S / I`. Lift the entries of an upper triangular `ḡ` on and above the diagonal to an
upper triangular `g₀`. The error `ε = g₀ J_l g₀ᵀ - J_l` is symmetric with entries in `I`, and it
vanishes at `(i, k)` with `i + k ≥ l`, as `g₀ J_l g₀ᵀ` and `J_l` do for upper triangular `g₀`.
So `δ = -½ ε J_l`, whose entry at `(i, j)` is `-½ ε_{i, l - 1 - j}`, is upper triangular, and
`g = (1 + δ) g₀` is upper triangular with `g J_l gᵀ = J_l + ε + δ J_l + J_l δᵀ = J_l`, the terms
quadratic in `I` vanishing. Its determinant squares to one and is congruent to one modulo `I`, so
it is one since `2` is invertible.

## Main declarations

* `TauCeti.AntidiagonalSpecialOrthogonal.UpperTriangular.map_quotient_mk_surjective_of_sq_eq_bot`:
  upper triangular points of `SO_l^J` lift across square-zero quotients when `2` is invertible.
* `TauCeti.AntidiagonalSpecialOrthogonal.UpperTriangular.instSmoothCoordinateHopfAlgebra`,
  `smoothCommHopfAlgProperty_coordinateHopfAlgebra`: the coordinate algebra of the upper
  triangular subgroup of `SO_l^J` is smooth when `2` is invertible.

## References

* The Stacks Project, Tags 00TH and 00TN, for formal smoothness and smooth algebras.

The infinitesimal lifting follows `TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Smooth` and
`Matrix.exists_map_eq_of_mem_isometryMatrices_map`, with the correction kept upper triangular.
-/

public section

open Matrix WithConv

namespace TauCeti.AntidiagonalSpecialOrthogonal.UpperTriangular

universe u

noncomputable section

/-! ### Lifting matrices -/

section Lift

variable {l : ℕ} {S : Type*} [CommRing S]

/-- Right multiplication by `J_l` reverses the columns. -/
private theorem mul_formMatrix_apply (M : Matrix (Fin l) (Fin l) S) (i j : Fin l) :
    (M * formMatrix S l) i j = M i (Fin.rev j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · simp [formMatrix_apply]
  · intro x _ hx
    rw [formMatrix_apply, ite_eq_right (fun h ↦ hx (by rw [h, Fin.rev_rev])), mul_zero]
  · simp

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

/-- The entry of `J_l` at `(i, k)` vanishes when `i + k ≥ l`. -/
private theorem formMatrix_apply_eq_zero {i k : Fin l} (hik : l ≤ (i : ℕ) + k) :
    formMatrix S l i k = 0 := by
  rw [formMatrix_apply, ite_eq_right]
  rintro rfl
  rw [Fin.val_rev] at hik
  omega

/-- **The linear correction.** If `g₀` is upper triangular and `g₀ J_l g₀ᵀ - J_l` has entries in
a square-zero ideal `I`, then `(1 + δ) g₀` with `δ = -½ (g₀ J_l g₀ᵀ - J_l) J_l` is upper
triangular and preserves `J_l`, and `δ` has entries in `I`. -/
private theorem exists_correction [Invertible (2 : S)] {I : Ideal S} (hI : I * I = ⊥)
    {g₀ : Matrix (Fin l) (Fin l) S} (hg₀ : g₀.IsUpperTriangular)
    (hε : ∀ i j, (g₀ * formMatrix S l * g₀ᵀ - formMatrix S l) i j ∈ I) :
    ∃ δ : Matrix (Fin l) (Fin l) S, (∀ i j, δ i j ∈ I) ∧ ((1 + δ) * g₀).IsUpperTriangular ∧
      (1 + δ) * g₀ * formMatrix S l * ((1 + δ) * g₀)ᵀ = formMatrix S l := by
  set J := formMatrix S l with hJ_def
  set ε := g₀ * J * g₀ᵀ - J with hε_def
  have hεt : εᵀ = ε := by
    rw [hε_def, transpose_sub, transpose_mul, transpose_mul, transpose_transpose, hJ_def,
      transpose_formMatrix, mul_assoc]
  have hε_zero {i k : Fin l} (hik : l ≤ (i : ℕ) + k) : ε i k = 0 := by
    rw [hε_def, Matrix.sub_apply, mul_formMatrix_mul_transpose_apply_eq_zero hg₀ hik, hJ_def,
      formMatrix_apply_eq_zero hik, sub_zero]
  set δ := -(⅟2 : S) • (ε * J) with hδ_def
  have hδ : ∀ i j, δ i j ∈ I := fun i j ↦ by
    rw [hδ_def, Matrix.smul_apply, smul_eq_mul]
    exact I.mul_mem_left _ (mul_apply_mem_right hε J i j)
  have hδ_upper : δ.IsUpperTriangular := fun i j hji ↦ by
    rw [hδ_def, Matrix.smul_apply, mul_formMatrix_apply, hε_zero, smul_zero]
    rw [Fin.val_rev]
    simp only [id, Fin.lt_def] at hji
    omega
  have hJJ : J * J = 1 := formMatrix_mul_self
  have hδJ : δ * J = -(⅟2 : S) • ε := by
    rw [hδ_def, smul_mul_assoc, mul_assoc, hJJ, mul_one]
  have hJδ : J * δᵀ = -(⅟2 : S) • ε :=
    calc J * δᵀ = (δ * J)ᵀ := by rw [transpose_mul, hJ_def, transpose_formMatrix]
      _ = -(⅟2 : S) • ε := by rw [hδJ, transpose_smul, hεt]
  have h₁ : δ * ε = 0 := mul_eq_zero_of_mul_eq_bot hI hδ hε
  have h₂ : ε * δᵀ = 0 := mul_eq_zero_of_mul_eq_bot hI hε fun i j ↦ hδ j i
  have h₃ : δ * (J * δᵀ) = 0 := by
    rw [hJδ]
    exact mul_eq_zero_of_mul_eq_bot hI hδ fun i j ↦ by
      rw [Matrix.smul_apply, smul_eq_mul]; exact I.mul_mem_left _ (hε i j)
  have hhalf : (⅟2 : S) • ε + (⅟2 : S) • ε = ε := by
    rw [← add_smul, ← two_mul, mul_invOf_self, one_smul]
  refine ⟨δ, hδ, (Matrix.blockTriangular_one.add hδ_upper).mul hg₀, ?_⟩
  calc (1 + δ) * g₀ * J * ((1 + δ) * g₀)ᵀ = (1 + δ) * (g₀ * J * g₀ᵀ) * (1 + δᵀ) := by
        simp only [transpose_mul, transpose_add, transpose_one, mul_assoc]
    _ = J + ε + δ * J + J * δᵀ + δ * ε + ε * δᵀ + δ * (J * δᵀ) + δ * ε * δᵀ := by
        rw [show g₀ * J * g₀ᵀ = J + ε by rw [hε_def, add_sub_cancel]]
        noncomm_ring
    _ = J + (ε - ((⅟2 : S) • ε + (⅟2 : S) • ε)) := by
        rw [h₃, h₁, h₂, zero_mul, hδJ, hJδ, neg_smul]
        abel
    _ = J := by rw [hhalf, sub_self, add_zero]

/-- An element congruent to `1` modulo a square-zero ideal whose square is `1` is `1`, when `2`
is invertible. -/
private theorem eq_one_of_sq_eq_one [Invertible (2 : S)] {I : Ideal S} (hI : I * I = ⊥) {x : S}
    (hx : x - 1 ∈ I) (hx2 : x ^ 2 = 1) : x = 1 := by
  have hsq : (x - 1) ^ 2 = 0 := by
    rw [← Ideal.mem_bot, ← hI, pow_two]
    exact Ideal.mul_mem_mul hx hx
  have htwo : (2 : S) * (x - 1) = 0 :=
    calc (2 : S) * (x - 1) = x ^ 2 - 1 - (x - 1) ^ 2 := by ring
      _ = 0 := by rw [hx2, hsq]; ring
  apply sub_eq_zero.mp
  apply (isUnit_of_invertible (2 : S)).mul_left_cancel
  simpa only [mul_zero] using htwo

/-- **Upper triangular points of `SO_l^J` lift across square-zero quotients** when `2` is
invertible. -/
theorem map_quotient_mk_surjective_of_sq_eq_bot [Invertible (2 : S)] (I : Ideal S)
    (hI : I ^ 2 = (⊥ : Ideal S)) :
    Function.Surjective (pointsSubgroupMap (l := l) (Ideal.Quotient.mk I)) := by
  classical
  intro g
  rw [sq] at hI
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
  have hε : ∀ i j, (g₀ * formMatrix S l * g₀ᵀ - formMatrix S l) i j ∈ I := by
    rw [← Ideal.mk_ker (I := I), forall_mem_ker_iff_map_eq_zero, Matrix.map_sub _ (map_sub _),
      Matrix.map_mul, Matrix.map_mul, transpose_map, hg₀_map,
      map_formMatrix S l _ (map_zero _) (map_one _), hJ, sub_self]
  -- Correct it.
  obtain ⟨δ, hδ, hg₁_upper, hg₁J⟩ := exists_correction hI hg₀ hε
  have hg₁_map : ((1 + δ) * g₀).map (Ideal.Quotient.mk I) = G := by
    rw [← Ideal.mk_ker (I := I)] at hδ
    rw [Matrix.map_mul, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _),
      forall_mem_ker_iff_map_eq_zero.mp hδ, add_zero, one_mul, hg₀_map]
  have hdet_sq : ((1 + δ) * g₀).det ^ 2 = 1 := by
    have h := congrArg Matrix.det hg₁J
    rw [det_mul, det_mul, det_transpose] at h
    have hJJ : (formMatrix S l).det * (formMatrix S l).det = 1 := by
      rw [← det_mul, formMatrix_mul_self, det_one]
    apply (isUnit_iff_exists_inv.mpr ⟨_, hJJ⟩).mul_left_cancel
    linear_combination h
  have hdet₁ : ((1 + δ) * g₀).det = 1 := by
    refine eq_one_of_sq_eq_one hI ?_ hdet_sq
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, RingHom.map_det, RingHom.mapMatrix_apply,
      hg₁_map, hdet, map_one, sub_self]
  refine ⟨⟨Matrix.GeneralLinearGroup.mk'' ((1 + δ) * g₀) (by rw [hdet₁]; exact isUnit_one),
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
  have hfg : (definingHopfIdeal R l).toIdeal.FG := by
    rw [definingHopfIdeal_def, HopfIdeal.sup_toIdeal,
      AntidiagonalSpecialOrthogonal.definingHopfIdeal_toIdeal,
      GeneralLinear.UpperTriangular.definingHopfIdeal_toIdeal]
    refine (Submodule.FG.sup (Submodule.FG.sup ?_ (Submodule.fg_span_singleton _)) ?_)
    · refine Submodule.fg_span ((Set.finite_range fun ij : Fin l × Fin l ↦
        ConstantForm.relationMatrix R l (formMatrix R l) ij.1 ij.2).subset fun x hx ↦ ?_)
      obtain ⟨i, j, hij⟩ :=
        (ConstantForm.mem_relationSet_iff (R := R) (n := l) (C := formMatrix R l)).mp hx
      exact ⟨(i, j), hij⟩
    · refine Submodule.fg_span ((Set.finite_range fun p : Fin l × Fin l ↦
        GeneralLinear.coordinateHopfAlgebraAlgEquiv R l
          (GeneralLinear.coordinateRingMap R l (MvPolynomial.X p))).subset fun x hx ↦ ?_)
      obtain ⟨i, j, -, rfl⟩ :=
        (GeneralLinear.UpperTriangular.mem_definingRelationSet_iff R l x).mp hx
      exact ⟨(i, j), rfl⟩
  let _ : Algebra.FinitePresentation R (coordinateHopfAlgebra R l) :=
    Algebra.FinitePresentation.quotient hfg
  exact ⟨inferInstance, inferInstance⟩

/-- The coordinate Hopf algebra of the upper triangular subgroup of `SO_l^J` satisfies the
smoothness object property when `2` is invertible. -/
theorem smoothCommHopfAlgProperty_coordinateHopfAlgebra [Invertible (2 : R)] :
    smoothCommHopfAlgProperty R (coordinateHopfAlgebra R l) := by
  rw [smoothCommHopfAlgProperty_iff]
  infer_instance

end

end TauCeti.AntidiagonalSpecialOrthogonal.UpperTriangular
