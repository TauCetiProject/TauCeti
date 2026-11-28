/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Finite
import TauCeti.LinearAlgebra.Basis.SumExtend

/-!
# Cancellation of common directions in a pairing determinant ratio

Two families of linear forms can share a block of forms up to a change of basis of determinant
of norm one. Their ratio of absolute pairing determinants then reduces to the ratio computed
on the common annihilator, using only the forms outside that block. No basis of the ambient
space adapted to the annihilator is required as input. The shared forms may be produced by
row operations of determinant of norm one that leave the retained forms fixed.

This is the determinant reduction used in `New.RealPlace.IsNegativeBasis.volumeRatio_eq` in
`New/Spanning/RemainingTerms/OneRealPlace.lean` of lsernau/grh-lean at `72fead1`.
-/

public section

open Matrix Module

namespace TauCeti

/-- In a ratio of absolute pairing determinants, discard a block of forms common to both
families up to a change of basis `D` with `‖det D‖ = 1`. The reduced determinants evaluate the
remaining forms on an independent family `u` annihilated by the common block. For a Hermitian
pairing this applies to the forms `w ↦ h(v, w)`; conjugating and transposing the pairing matrix
does not affect the norm of its determinant. -/
theorem norm_det_pairing_ratio_on_common_annihilator {K V ι κ : Type*} [NormedField K]
    [AddCommGroup V] [Module K V] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (b : Basis (ι ⊕ κ) K V) (f g : ι ⊕ κ → V →ₗ[K] K)
    (D : Matrix κ κ K) (hD : ‖D.det‖ = 1)
    (hfg : ∀ j : κ, f (.inr j) = ∑ k : κ, D j k • g (.inr k))
    {u : ι → V} (hu : LinearIndependent K u) (hker : ∀ j : κ, ∀ i : ι, g (.inr j) (u i) = 0)
    (hg : (LinearMap.toMatrix b (Pi.basisFun K (ι ⊕ κ)) (LinearMap.pi g)).det ≠ 0) :
    ‖(LinearMap.toMatrix b (Pi.basisFun K (ι ⊕ κ)) (LinearMap.pi f)).det‖ /
        ‖(LinearMap.toMatrix b (Pi.basisFun K (ι ⊕ κ)) (LinearMap.pi g)).det‖ =
      ‖(of fun i j : ι ↦ f (.inl i) (u j)).det‖ / ‖(of fun i j : ι ↦ g (.inl i) (u j)).det‖ := by
  classical
  -- Extend the given family, then cancel the common change-of-basis determinant.
  have : Module.Finite K V := Module.Finite.of_basis b
  let e := Basis.sumExtend hu
  have : Finite (ι ⊕ Basis.sumExtendIndex hu) := Module.Finite.finite_basis e
  have : Finite (Basis.sumExtendIndex hu) :=
    Finite.of_injective (Sum.inr : Basis.sumExtendIndex hu → ι ⊕ Basis.sumExtendIndex hu)
      Sum.inr_injective
  let _ := Fintype.ofFinite (Basis.sumExtendIndex hu)
  have he : Fintype.card (Basis.sumExtendIndex hu) = Fintype.card κ := by
    have hc := (finrank_eq_card_basis e).symm.trans (finrank_eq_card_basis b)
    simpa only [Fintype.card_sum, Nat.add_left_cancel_iff] using hc
  let eqv := Fintype.equivOfCardEq he
  let c := e.reindex (Equiv.sumCongr (Equiv.refl ι) eqv)
  have hcu (i : ι) : c (.inl i) = u i := by simp [c, e, Basis.sumExtend_apply_inl]
  let M (a : ι ⊕ κ → V →ₗ[K] K) :=
    LinearMap.toMatrix c (Pi.basisFun K (ι ⊕ κ)) (LinearMap.pi a)
  let T := LinearMap.toMatrix b c (LinearMap.id : V →ₗ[K] V)
  have hchange (a : ι ⊕ κ → V →ₗ[K] K) :
      LinearMap.toMatrix b (Pi.basisFun K (ι ⊕ κ)) (LinearMap.pi a) = M a * T := by
    simpa [M, T] using (LinearMap.toMatrix_comp b c (Pi.basisFun K (ι ⊕ κ))
      (LinearMap.pi a) (LinearMap.id : V →ₗ[K] V))
  rw [hchange, det_mul] at hg
  have hT : ‖T.det‖ ≠ 0 := norm_ne_zero_iff.mpr (right_ne_zero_of_mul hg)
  rw [hchange, hchange, det_mul, det_mul, norm_mul, norm_mul, mul_div_mul_right _ _ hT]
  -- In the extended basis the annihilation makes both evaluation matrices block triangular.
  let C := (M g).toBlocks₂₂
  have hM (a : ι ⊕ κ → V →ₗ[K] K) (i j : ι ⊕ κ) : M a i j = a i (c j) := by
    simp [M, LinearMap.toMatrix_apply]
  have hblock (a : ι ⊕ κ → V →ₗ[K] K) (ha : ∀ j : κ, ∀ i : ι, a (.inr j) (u i) = 0) :
      (M a).det = (of fun i j : ι ↦ a (.inl i) (u j)).det * (M a).toBlocks₂₂.det := by
    have hzero : (M a).toBlocks₂₁ = 0 := by
      ext j i
      simp [Matrix.toBlocks₂₁, hM, hcu, ha]
    have hleft : (M a).toBlocks₁₁ = of fun i j : ι ↦ a (.inl i) (u j) := by
      ext i j
      simp [Matrix.toBlocks₁₁, hM, hcu]
    conv_lhs => rw [← (M a).fromBlocks_toBlocks, hzero, det_fromBlocks_zero₂₁, hleft]
  have hfker (j : κ) (i : ι) : f (.inr j) (u i) = 0 := by simp [hfg, hker]
  have hC : (M f).toBlocks₂₂ = D * C := by
    ext j k
    simp [C, Matrix.toBlocks₂₂, hM, hfg, Matrix.mul_apply]
  have hC0 : C.det ≠ 0 := by
    have h := left_ne_zero_of_mul hg
    rw [hblock g hker] at h
    exact right_ne_zero_of_mul h
  rw [hblock f hfker, hblock g hker, hC, det_mul, norm_mul, norm_mul, norm_mul, hD, one_mul]
  exact mul_div_mul_right _ _ (norm_ne_zero_iff.mpr hC0)

/-- Reduce a pairing determinant ratio when the common forms are obtained by norm-preserving
row operations. The changes of forms `P` and `Q` must have determinants of norm one and fix
all retained rows. The independent family `u` need only annihilate the resulting common forms.
In a flag comparison one can use triangular changes with diagonal entries of norm one. -/
theorem norm_det_pairing_ratio_of_row_operations {K V ι κ : Type*} [NormedField K]
    [AddCommGroup V] [Module K V] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (b : Basis (ι ⊕ κ) K V) (f g : ι ⊕ κ → V →ₗ[K] K)
    (P Q : Matrix (ι ⊕ κ) (ι ⊕ κ) K) (hP : ‖P.det‖ = 1) (hQ : ‖Q.det‖ = 1)
    (hPleft : ∀ i : ι, P (.inl i) = (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) K) (.inl i))
    (hQleft : ∀ i : ι, Q (.inl i) = (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) K) (.inl i))
    (hfg : ∀ j : κ, ∑ k, P (.inr j) k • f k = ∑ k, Q (.inr j) k • g k)
    {u : ι → V} (hu : LinearIndependent K u)
    (hker : ∀ j : κ, ∀ i : ι, ∑ k, Q (.inr j) k * g k (u i) = 0)
    (hg : (LinearMap.toMatrix b (Pi.basisFun K (ι ⊕ κ)) (LinearMap.pi g)).det ≠ 0) :
    ‖(LinearMap.toMatrix b (Pi.basisFun K (ι ⊕ κ)) (LinearMap.pi f)).det‖ /
        ‖(LinearMap.toMatrix b (Pi.basisFun K (ι ⊕ κ)) (LinearMap.pi g)).det‖ =
      ‖(of fun i j : ι ↦ f (.inl i) (u j)).det‖ / ‖(of fun i j : ι ↦ g (.inl i) (u j)).det‖ := by
  let modify (A : Matrix (ι ⊕ κ) (ι ⊕ κ) K) (a : ι ⊕ κ → V →ₗ[K] K) (j : ι ⊕ κ) :=
    ∑ k, A j k • a k
  have hmatrix (A : Matrix (ι ⊕ κ) (ι ⊕ κ) K) (a : ι ⊕ κ → V →ₗ[K] K) :
      LinearMap.toMatrix b (Pi.basisFun K (ι ⊕ κ)) (LinearMap.pi (modify A a)) =
        A * LinearMap.toMatrix b (Pi.basisFun K (ι ⊕ κ)) (LinearMap.pi a) := by
    ext i j
    simp [modify, LinearMap.toMatrix_apply, Matrix.mul_apply]
  have hleft (A : Matrix (ι ⊕ κ) (ι ⊕ κ) K) (a : ι ⊕ κ → V →ₗ[K] K)
      (hA : ∀ i : ι, A (.inl i) = (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) K) (.inl i)) (i : ι) :
      modify A a (.inl i) = a (.inl i) := by
    simp [modify, hA, Matrix.one_apply, ite_smul]
  have hQg :
      (LinearMap.toMatrix b (Pi.basisFun K (ι ⊕ κ)) (LinearMap.pi (modify Q g))).det ≠ 0 := by
    rw [hmatrix, det_mul]
    exact mul_ne_zero (norm_ne_zero_iff.mp (by simp [hQ])) hg
  have h := norm_det_pairing_ratio_on_common_annihilator b (modify P f) (modify Q g) 1
    (by simp) (fun j ↦ by
      simpa only [Matrix.one_apply, ite_smul, zero_smul, one_smul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true] using hfg j)
    hu (fun j i ↦ by simpa [modify] using hker j i) hQg
  simpa only [hmatrix, det_mul, norm_mul, hP, hQ, one_mul, hleft P f hPleft, hleft Q g hQleft]
    using h

end TauCeti
