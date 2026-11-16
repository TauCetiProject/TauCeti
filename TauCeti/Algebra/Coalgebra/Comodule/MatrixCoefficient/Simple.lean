/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Trace
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Module
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Intertwiner
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Subcoalgebra
public import TauCeti.Algebra.Coalgebra.Subcomodule.Convolution
import TauCeti.LinearAlgebra.Trace.Nondegenerate
import TauCeti.RingTheory.Semisimple.Schur

/-!
# The coefficient space of a simple comodule

Over an algebraically closed field, the matrix coefficient map of a finite-dimensional
simple comodule `M` identifies `M* ⊗ M` with its coefficient subcoalgebra. In particular,
the entries of the coefficient matrix of a finite basis form a basis of the coefficient
submodule (so that subcoalgebra has dimension `(dim M)²`), and every comodule endomorphism
of `M` is scalar.

The convolution dual exhausts all endomorphisms of `M` by Burnside's theorem, and the
trace pairing detects the kernel of the coefficient map. No linear reductivity assumption
on the coalgebra is needed. For an affine group this identifies the individual blocks
in the algebraic Peter--Weyl decomposition, including in positive characteristic.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2.
* J. S. Milne, *Algebraic Groups* (2017), §12, matrix coefficients.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

variable {k C M : Type*} [Field k] [IsAlgClosed k]
  [AddCommGroup C] [Module k C] [Coalgebra k C]
  [AddCommGroup M] [Module k M] [Comodule k C M]
  [Module.Finite k M] [IsSimpleOrder (Subcomodule k C M)]

/-- The matrix coefficient tensor map of a finite-dimensional simple comodule over an
algebraically closed field is injective. -/
theorem matrixCoefficientTensor_injective :
    Function.Injective (matrixCoefficientTensor (R := k) (C := C) (M := M)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  apply (dualTensorHom_bijective (R := k) (M := M) (N := M)).1
  rw [map_zero]
  apply LinearMap.forall_trace_mul_eq_zero_iff.mp
  intro T
  obtain ⟨f, rfl⟩ := convolutionAction_surjective (C := C) T
  rw [LinearMap.trace_mul_comm, ← WithConv.apply_matrixCoefficientTensor_eq_trace, hz, map_zero]

/-- The coefficient tensor identifies a simple comodule's tensor product `M* ⊗ M` with the
underlying module of its coefficient subcoalgebra. -/
noncomputable def matrixCoefficientTensorEquiv :
    Module.Dual k M ⊗[k] M ≃ₗ[k]
      (matrixCoefficientSubcoalgebra (R := k) (C := C) (M := M)).toSubmodule :=
  LinearEquiv.ofInjective (matrixCoefficientTensor (R := k) (C := C))
      matrixCoefficientTensor_injective ≪≫ₗ
    LinearEquiv.ofEq _ _ (by
      rw [range_matrixCoefficientTensor, matrixCoefficientSubcoalgebra_toSubmodule])

/-- The coefficient-space identification is the coefficient tensor map on underlying vectors. -/
@[simp]
theorem coe_matrixCoefficientTensorEquiv_apply (z : Module.Dual k M ⊗[k] M) :
    (matrixCoefficientTensorEquiv (C := C) z : C) =
      matrixCoefficientTensor (C := C) z := by
  simp [matrixCoefficientTensorEquiv]

/-- The inverse coefficient-space identification recovers the tensor of a coefficient. -/
@[simp]
theorem matrixCoefficientTensor_matrixCoefficientTensorEquiv_symm
    (c : (matrixCoefficientSubcoalgebra (R := k) (C := C) (M := M)).toSubmodule) :
    matrixCoefficientTensor (C := C) ((matrixCoefficientTensorEquiv (C := C)).symm c) =
      (c : C) := by
  rw [← coe_matrixCoefficientTensorEquiv_apply, LinearEquiv.apply_symm_apply]

/-- The coefficient subcoalgebra of a finite-dimensional simple comodule has square dimension
over an algebraically closed field. -/
theorem finrank_matrixCoefficientSubcoalgebra :
    Module.finrank k (matrixCoefficientSubcoalgebra (R := k) (C := C) (M := M)).toSubmodule =
      Module.finrank k M ^ 2 := by
  rw [← (matrixCoefficientTensorEquiv (k := k) (C := C) (M := M)).finrank_eq,
    Module.finrank_tensorProduct, Subspace.dual_finrank_eq, pow_two]

section Basis

variable {ι : Type*} [Finite ι] [DecidableEq ι]

/-- The entries of the coefficient matrix of a finite simple comodule over an algebraically
closed field form a basis of its coefficient submodule. -/
noncomputable def matrixCoefficientBasis (b : Module.Basis ι k M) :
    Module.Basis (ι × ι) k (matrixCoefficientSubmodule (R := k) (C := C) (M := M)) :=
  (b.dualBasis.tensorProduct b).map
    ((matrixCoefficientTensorEquiv (k := k) (C := C) (M := M)).trans
      (LinearEquiv.ofEq _ _ matrixCoefficientSubcoalgebra_toSubmodule))

/-- The `(i, j)` basis vector of `matrixCoefficientBasis b` is the `(i, j)` entry of the
coefficient matrix. -/
@[simp]
theorem coe_matrixCoefficientBasis (b : Module.Basis ι k M) (p : ι × ι) :
    (matrixCoefficientBasis (C := C) b p : C) = coefficientMatrix (C := C) b p.1 p.2 := by
  rcases p with ⟨i, j⟩
  simp [matrixCoefficientBasis, coefficientMatrix_apply]

end Basis

/-- The entries of the coefficient matrix of a finite simple comodule over an algebraically
closed field are linearly independent. -/
theorem linearIndependent_coefficientMatrix {ι : Type*} [Finite ι] (b : Module.Basis ι k M) :
    LinearIndependent k (fun p : ι × ι ↦ coefficientMatrix (C := C) b p.1 p.2) := by
  classical
  have h : (fun p : ι × ι ↦ coefficientMatrix (C := C) b p.1 p.2) =
      (matrixCoefficientSubmodule (R := k) (C := C) (M := M)).subtype ∘
        matrixCoefficientBasis (C := C) b := by
    ext p
    simp
  rw [h]
  exact (matrixCoefficientBasis (C := C) b).linearIndependent.map' _
    (Submodule.ker_subtype _)

section Schur

attribute [local instance] convolutionModule

/-- **Schur's lemma for simple comodules over an algebraically closed field.** Every comodule
endomorphism of a finite-dimensional simple comodule is multiplication by a scalar. -/
theorem Hom.exists_eq_smul_id (f : Hom k C M M) :
    ∃ c : k, ∀ m : M, f m = c • m := by
  have : IsSimpleModule (WithConv (C →ₗ[k] k)) M := isSimpleModule_convolution_iff.mpr inferInstance
  exact ⟨endAlgEquivSelfOfIsSimpleModule (k := k) f.toConvolutionLinearMap,
    fun m ↦ by simp⟩

end Schur

section Algebra

variable {A : Type*} [Ring A] [Algebra k A] [Coalgebra k A]
  [Comodule k A M] [IsSimpleOrder (Subcomodule k A M)]

/-- A scalar matrix commuting with the coefficient matrix of a finite simple comodule over an
algebraically closed field is a scalar multiple of the identity matrix. -/
theorem exists_eq_smul_one_of_coefficientMatrix_comm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k M) {T : Matrix ι ι k}
    (hT : coefficientMatrix (C := A) b * T.map (algebraMap k A) =
      T.map (algebraMap k A) * coefficientMatrix (C := A) b) :
    ∃ c : k, T = c • 1 := by
  let f : M →ₗ[k] M := (LinearMap.toMatrix b b).symm T
  have hf : TensorProduct.map f LinearMap.id ∘ₗ coact (R := k) (C := A) =
      coact (R := k) (C := A) ∘ₗ f :=
    (b.map_coact_iff_coefficientMatrix b f).mpr (by simpa [f] using hT)
  obtain ⟨c, hc⟩ := Hom.exists_eq_smul_id (C := A) ⟨f, hf⟩
  refine ⟨c, ?_⟩
  have hfeq : f = c • LinearMap.id := LinearMap.ext hc
  simpa [f] using congrArg (LinearMap.toMatrix b b) hfeq

/-- Two scalar matrices fix the coefficient matrix `u` of a finite simple comodule under
two-sided multiplication `X u Y = u` exactly when they are inverse nonzero scalar matrices. -/
theorem mul_coefficientMatrix_mul_eq_self_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k M) (X Y : Matrix ι ι k) :
    X.map (algebraMap k A) * coefficientMatrix (C := A) b * Y.map (algebraMap k A) =
        coefficientMatrix (C := A) b ↔
      ∃ c : k, c ≠ 0 ∧ X = c • 1 ∧ Y = c⁻¹ • 1 := by
  set u := coefficientMatrix (C := A) b
  constructor
  · intro h
    have : Nontrivial M := Subcomodule.nontrivial_of_isSimpleOrder (R := k) (C := A)
    have : Nonempty ι := b.index_nonempty
    have hcoeff (i j p q : ι) : X i p * Y q j = if (p, q) = (i, j) then 1 else 0 := by
      have hij : ∑ p' : ι × ι, (X i p'.1 * Y p'.2 j) • u p'.1 p'.2 =
          ∑ p' : ι × ι, (if p' = (i, j) then (1 : k) else 0) • u p'.1 p'.2 := by
        have he := congrFun (congrFun h i) j
        simp only [Matrix.mul_apply, Matrix.map_apply, Algebra.algebraMap_eq_smul_one,
          smul_mul_assoc, mul_smul_comm, one_mul, mul_one, Finset.smul_sum, smul_smul] at he
        rw [Fintype.sum_prod_type]
        calc ∑ a, ∑ b', (X i a * Y b' j) • u a b'
            = ∑ b', ∑ a, (X i a * Y b' j) • u a b' := Finset.sum_comm
          _ = u i j := by
            simpa only [mul_comm (Y _ _)] using he
          _ = ∑ p' : ι × ι, (if p' = (i, j) then (1 : k) else 0) • u p'.1 p'.2 := by
            simp
      have hlin := Fintype.linearIndependent_iff.mp (linearIndependent_coefficientMatrix (C := A) b)
        (fun p' ↦ X i p'.1 * Y p'.2 j - if p' = (i, j) then 1 else 0) (by
          simpa [sub_smul, Finset.sum_sub_distrib, sub_eq_zero] using hij) (p, q)
      exact sub_eq_zero.mp hlin
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    have h1 : X i₀ i₀ * Y i₀ i₀ = 1 := by simpa using hcoeff i₀ i₀ i₀ i₀
    have hc : X i₀ i₀ ≠ 0 := left_ne_zero_of_mul_eq_one h1
    have hY0 : Y i₀ i₀ = (X i₀ i₀)⁻¹ := eq_inv_of_mul_eq_one_right h1
    refine ⟨X i₀ i₀, hc, ?_, ?_⟩
    · ext i p
      have hXp := hcoeff i i₀ p i₀
      simp only [Prod.mk.injEq, and_true, hY0] at hXp
      by_cases hip : p = i
      · subst hip
        simp only [↓reduceIte, Matrix.smul_apply, Matrix.one_apply_eq,
          smul_eq_mul, mul_one] at hXp ⊢
        exact mul_inv_eq_one₀ hc |>.mp hXp
      · simp only [hip, ↓reduceIte, mul_eq_zero, inv_eq_zero, hc, or_false] at hXp
        simp [Ne.symm hip, hXp]
    · ext q j
      have hYq := hcoeff i₀ j i₀ q
      simp only [Prod.mk.injEq, true_and] at hYq
      by_cases hqj : q = j
      · subst hqj
        simp only [↓reduceIte, Matrix.smul_apply, Matrix.one_apply_eq,
          smul_eq_mul, mul_one] at hYq ⊢
        exact eq_inv_of_mul_eq_one_right hYq
      · simp only [hqj, ↓reduceIte, mul_eq_zero, hc, false_or] at hYq
        simp [hqj, hYq]
  · rintro ⟨c, hc, rfl, rfl⟩
    have hX : (c • (1 : Matrix ι ι k)).map (algebraMap k A) = c • (1 : Matrix ι ι A) := by
      ext i j
      by_cases hij : i = j <;> simp [hij, Algebra.algebraMap_eq_smul_one]
    have hY : (c⁻¹ • (1 : Matrix ι ι k)).map (algebraMap k A) = c⁻¹ • (1 : Matrix ι ι A) := by
      ext i j
      by_cases hij : i = j <;> simp [hij, Algebra.algebraMap_eq_smul_one]
    rw [hX, hY, smul_mul_assoc, Matrix.one_mul, mul_smul_comm, Matrix.mul_one, smul_smul,
      inv_mul_cancel₀ hc, one_smul]

end Algebra

end TauCeti.Comodule
