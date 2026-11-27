/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Alternating
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Change of basis for the Capelli determinant

The full quantum minor of a family of matrix units is invariant under a scalar change
of basis. Polarizing the rows and columns of the shifted matrices separates the two
basis changes: each contributes the ordinary determinant of its scalar matrix.

The invariance is the quantum determinant clause of `Formalism.FourierDecayAlt.Q.Econj`
in L. Alpöge's formalization of the Riemann hypothesis for Dirichlet L-functions.
-/

public section

open Equiv Equiv.Perm

namespace Matrix

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A] {n : ℕ}

private def minorPair (E : Matrix (Fin n) (Fin n) A) (u : K) (k : Fin n) :
    (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] A :=
  ∑ i, ∑ j, (LinearMap.proj i).smulRight ((LinearMap.proj j).smulRight
    ((if i = j then algebraMap K A (u - (k.val : K)) else 0) + E i j))

private theorem minorPair_apply (E : Matrix (Fin n) (Fin n) A) (u : K)
    (k : Fin n) (v w : Fin n → K) :
    minorPair E u k v w = ∑ i, ∑ j, (v i * w j) •
      ((if i = j then algebraMap K A (u - (k.val : K)) else 0) + E i j) := by
  simp [minorPair, LinearMap.sum_apply, mul_smul]

private def minorRows (E : Matrix (Fin n) (Fin n) A) (u : K) (w : Fin n → Fin n → K) :
    (Fin n → K) [⋀^Fin n]→ₗ[K] A :=
  MultilinearMap.alternatization ((MultilinearMap.mkPiAlgebraFin K n A).compLinearMap
    fun k ↦ (minorPair E u k).flip (w k))

private def minorCols (E : Matrix (Fin n) (Fin n) A) (u : K) (v : Fin n → Fin n → K) :
    (Fin n → Fin n → K) →ₘₗ[K] A :=
  ∑ e : Perm (Fin n), sign e • (MultilinearMap.mkPiAlgebraFin K n A).compLinearMap
    (fun k ↦ minorPair E u k (v (e k)))

private theorem minorRows_apply (E : Matrix (Fin n) (Fin n) A) (u : K)
    (v w : Fin n → Fin n → K) :
    minorRows E u w v = (of fun i k ↦ minorPair E u k (v i) (w k)).columnDet := by
  simp [minorRows, MultilinearMap.alternatization_apply, columnDet_apply, Units.smul_def]

private theorem minorCols_apply (E : Matrix (Fin n) (Fin n) A) (u : K)
    (v w : Fin n → Fin n → K) :
    minorCols E u v w = (of fun i k ↦ minorPair E u k (v i) (w k)).columnDet := by
  simp [minorCols, columnDet_apply, Units.smul_def]

private theorem minorCols_apply_basis (E : Matrix (Fin n) (Fin n) A) (u : K)
    (a b : Fin n → Fin n) :
    minorCols E u (fun i ↦ Pi.basisFun K _ (a i)) (fun j ↦ Pi.basisFun K _ (b j)) =
      E.quantumMinor u a b := by
  rw [minorCols_apply, quantumMinor_eq_columnDet]
  congr 1
  ext i j
  simp only [of_apply, minorPair_apply, Pi.basisFun_apply, Pi.single_apply, mul_ite,
    mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, one_smul]

private theorem minorRows_eq_det_smul (E : Matrix (Fin n) (Fin n) A) (u : K)
    (v w : Fin n → Fin n → K) :
    minorRows E u w v = (of v).det • minorRows E u w (Pi.basisFun K _) := by
  simpa only [AlternatingMap.smulRight_apply, Pi.basisFun_det_apply] using
    DFunLike.congr_fun ((minorRows E u w).eq_basis_det_smulRight (Pi.basisFun K _)) v

private theorem minorCols_apply_standard (E : Matrix (Fin n) (Fin n) A)
    (hE : E.HasMatrixUnitLieRelations) (u : K) (w : Fin n → Fin n → K) :
    minorCols E u (Pi.basisFun K _) w = (of w).det • E.quantumMinor u id id := by
  have h : minorCols E u (Pi.basisFun K _) =
      ((Pi.basisFun K (Fin n)).det.smulRight (E.quantumMinor u id id)).toMultilinearMap := by
    apply Module.Basis.ext_multilinear (fun _ ↦ Pi.basisFun K _)
    intro b
    simp only [AlternatingMap.coe_multilinearMap, AlternatingMap.smulRight_apply]
    have hbasis := minorCols_apply_basis E u id b
    simp only [id_eq] at hbasis
    rw [hbasis]
    -- Compare on tuples of basis vectors; the determinant vanishes on repeated vectors.
    by_cases hb : Function.Injective b
    · let e : Perm (Fin n) := Equiv.ofBijective b (Finite.injective_iff_bijective.mp hb)
      have he : (fun j ↦ Pi.basisFun K _ (b j)) = Pi.basisFun K _ ∘ e := rfl
      have hid : b = id ∘ e := rfl
      rw [he, AlternatingMap.map_perm, hid, E.quantumMinor_comp_perm_right hE]
      have hdet : detRowAlternating (Pi.basisFun K (Fin n)) = 1 := by
        simpa only [Pi.basisFun_det] using (Pi.basisFun K (Fin n)).det_self
      simp [hdet, Units.smul_def, Int.cast_smul_eq_zsmul]
    · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hb
      rw [AlternatingMap.map_eq_zero_of_eq _ (fun k ↦ Pi.basisFun K _ (b k))
        (i := i) (j := j) (congrArg (fun t ↦ Pi.basisFun K (Fin n) t) hij) hne, zero_smul]
      exact E.quantumMinor_eq_zero_of_not_injective_right hE u id b hb
  rw [h, AlternatingMap.coe_multilinearMap, AlternatingMap.smulRight_apply, Pi.basisFun_det_apply]

/-- The Capelli determinant is invariant when the matrix-unit generators are replaced by
`E'ᵢⱼ = ∑ c, ∑ d, (P c i * Q j d) • E c d`, where `Q * P = 1`. The ordinary determinants of
`P` and `Q` are the factors from the two changes of basis and cancel each other. -/
theorem quantumMinor_conj_of_mul_eq_one (E : Matrix (Fin n) (Fin n) A)
    (hE : E.HasMatrixUnitLieRelations) (u : K) (P Q : Matrix (Fin n) (Fin n) K)
    (hQP : Q * P = 1) :
    (of fun i j ↦ ∑ c, ∑ d, (P c i * Q j d) • E c d).quantumMinor u id id =
      E.quantumMinor u id id := by
  have hpair (i j : Fin n) :
      minorPair E u j (Pᵀ i) (Q j) =
        (if i = j then algebraMap K A (u - (j.val : K)) else 0) +
          ∑ c, ∑ d, (P c i * Q j d) • E c d := by
    rw [minorPair_apply]
    simp only [transpose_apply, smul_add, Finset.sum_add_distrib, smul_ite, smul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.sum_smul]
    have hsum : (∑ c, P c i * Q j c) = if i = j then 1 else 0 := calc
      _ = (Q * P) j i := by rw [Matrix.mul_apply]; simp only [mul_comm (P _ _)]
      _ = _ := by rw [hQP, Matrix.one_apply]; exact if_congr eq_comm rfl rfl
    rw [hsum, ite_smul, one_smul, zero_smul]
  calc
    _ = minorRows E u (fun j d ↦ Q j d) (fun i c ↦ P c i) := by
      rw [quantumMinor_eq_columnDet, minorRows_apply]
      congr 1
      ext i j
      exact (hpair i j).symm
    _ = P.det • minorCols E u (Pi.basisFun K _) (fun j d ↦ Q j d) := by
      have hP : (of fun i c ↦ P c i) = Pᵀ := by
        ext i c
        rw [of_apply, transpose_apply]
      rw [minorRows_eq_det_smul, hP, det_transpose, minorRows_apply, minorCols_apply]
    _ = E.quantumMinor u id id := by
      have hdet : (of fun j d ↦ Q j d) = Q := by
        ext j d
        rw [of_apply]
      rw [minorCols_apply_standard E hE, hdet, smul_smul, mul_comm P.det Q.det, ← det_mul,
        hQP, det_one, one_smul]

end Matrix
