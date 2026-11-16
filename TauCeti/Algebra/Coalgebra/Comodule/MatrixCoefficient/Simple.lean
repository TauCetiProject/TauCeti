/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Module
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Intertwiner
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Trace
import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
import TauCeti.LinearAlgebra.Trace.Nondegenerate
import TauCeti.RingTheory.Semisimple.Schur
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Matrix
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Subcoalgebra
public import TauCeti.Algebra.Coalgebra.Subcomodule.Convolution

/-!
# The coefficient space of a simple comodule

Over an algebraically closed field, the matrix coefficient map of a finite-dimensional
simple comodule `M` identifies `M* ⊗ M` with its coefficient subcoalgebra. In particular,
that subcoalgebra has dimension `(dim M)²`, and the entries of the coefficient matrix of any
simple comodule in any basis are linearly independent
(`TauCeti.Comodule.linearIndependent_coefficientMatrix`).

The convolution dual exhausts all endomorphisms of `M` by Burnside's theorem, and the
trace pairing detects the kernel of the coefficient map. No linear reductivity assumption
on the coalgebra is needed. For an affine group this identifies the individual blocks
in the algebraic Peter--Weyl decomposition, including in positive characteristic.

When the coalgebra also carries a `k`-algebra structure, Schur's lemma in matrix coordinates
says that every scalar matrix commuting with the coefficient matrix of a simple comodule is a
scalar multiple of the identity (`TauCeti.Comodule.exists_eq_smul_one_of_coefficientMatrix_mul_eq`).

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2.
* J. S. Milne, *Algebraic Groups* (2017), §12, matrix coefficients.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

section Finite

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

end Finite

/-- **Linear independence of the matrix coefficients of a simple comodule.** Over an algebraically
closed field, the entries of the coefficient matrix of any simple comodule in any basis are
linearly independent. -/
theorem linearIndependent_coefficientMatrix {k C M ι : Type*} [Field k] [IsAlgClosed k]
    [AddCommGroup C] [Module k C] [Coalgebra k C]
    [AddCommGroup M] [Module k M] [Comodule k C M] [IsSimpleOrder (Subcomodule k C M)]
    (b : Module.Basis ι k M) :
    LinearIndependent k (Function.uncurry (coefficientMatrix (C := C) b)) := by
  classical
  have : Module.Finite k M := by
    have hfin : Module.Finite k (⊤ : Subcomodule k C M).toSubmodule :=
      Subcomodule.finite_of_isAtom isAtom_top
    rw [Subcomodule.top_toSubmodule] at hfin
    exact Module.Finite.equiv (Submodule.topEquiv (R := k) (M := M))
  rw [linearIndependent_iff]
  intro l hl
  have hker : Finsupp.linearCombination k
      (fun p : ι × ι ↦ b.coord p.1 ⊗ₜ[k] b p.2) l = 0 := by
    apply matrixCoefficientTensor_injective (k := k) (C := C) (M := M)
    rw [map_zero, Finsupp.linearCombination_apply, map_finsuppSum]
    rw [Finsupp.linearCombination_apply] at hl
    rw [← hl]
    refine Finsupp.sum_congr fun ⟨i, j⟩ _ ↦ ?_
    rw [map_smul, matrixCoefficientTensor_tmul]
    exact congrArg (l (i, j) • ·) (coefficientMatrix_apply b i j).symm
  ext ⟨i, j⟩
  let ev : Module.Dual k M ⊗[k] M →ₗ[k] k :=
    (TensorProduct.lid k k).toLinearMap.comp
      (TensorProduct.map (Module.Dual.eval k M (b i)) (b.coord j))
  have hev := congrArg ev hker
  rw [map_zero, Finsupp.linearCombination_apply, map_finsuppSum] at hev
  have hsum : l.sum (fun p r ↦ ev (r • (b.coord p.1 ⊗ₜ[k] b p.2))) = l (i, j) := by
    rw [Finsupp.sum_eq_single (i, j)]
    · simp [ev, Module.Basis.coord_apply]
    · intro ⟨p₁, p₂⟩ _ hp
      simp only [ev, map_smul, LinearMap.comp_apply, LinearEquiv.coe_coe,
        TensorProduct.map_tmul, Module.Dual.eval_apply, TensorProduct.lid_tmul, smul_eq_mul,
        Module.Basis.coord_apply, Module.Basis.repr_self]
      by_cases h1 : p₁ = i
      · have h2 : j ≠ p₂ := fun h2 ↦ hp (Prod.ext h1 h2.symm)
        simp [Finsupp.single_eq_of_ne h2]
      · simp [Finsupp.single_eq_of_ne h1]
    · simp
  rw [hsum] at hev
  exact hev

/-- **Schur's lemma in matrix coordinates.** Over an algebraically closed field, any scalar matrix
commuting with the coefficient matrix of a simple comodule in a finite basis is a scalar multiple
of the identity matrix. -/
theorem exists_eq_smul_one_of_coefficientMatrix_mul_eq {k A M ι : Type*}
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [Coalgebra k A]
    [AddCommGroup M] [Module k M] [Comodule k A M] [IsSimpleOrder (Subcomodule k A M)]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k M) {X : Matrix ι ι k}
    (hX : coefficientMatrix (C := A) b * X.map (algebraMap k A) =
      X.map (algebraMap k A) * coefficientMatrix (C := A) b) :
    ∃ c : k, X = c • 1 := by
  let _ : FiniteDimensional k M := Module.Finite.of_basis b
  let _ := convolutionModule (R := k) (C := A) (M := M)
  have : IsSimpleModule (WithConv (A →ₗ[k] k)) M :=
    isSimpleModule_convolution_iff.mpr inferInstance
  let T : Hom k A M M :=
    { toLinearMap := Matrix.toLin b b X
      map_coact := (b.map_coact_iff_coefficientMatrix b _).mpr
        (by rw [LinearMap.toMatrix_toLin]; exact hX) }
  set c : k := endAlgEquivSelfOfIsSimpleModule (k := k) T.toConvolutionLinearMap
  refine ⟨c, ?_⟩
  have hT : T.toLinearMap = c • LinearMap.id :=
    LinearMap.ext fun m ↦ by
      rw [Hom.coe_toLinearMap, ← Hom.toConvolutionLinearMap_apply,
        ← endAlgEquivSelfOfIsSimpleModule_smul (k := k), LinearMap.smul_apply,
        LinearMap.id_apply]
  have hTX : LinearMap.toMatrix b b T.toLinearMap = X := LinearMap.toMatrix_toLin b b X
  rw [← hTX, hT, map_smul, LinearMap.toMatrix_id]

end TauCeti.Comodule
