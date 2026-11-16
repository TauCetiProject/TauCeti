/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Adjoin
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Matrix

/-!
# Finite matrix-coefficient submodules

This file proves that the matrix-coefficient submodule of a finite projective right comodule
over a commutative semiring is finite, and that for a finite basis it is spanned by the entries
of the coefficient matrix.

This is a finite-dimensionality step toward the fundamental theorem of comodules.

## Main results

* `TauCeti.Comodule.matrixCoefficientSubmodule_finite`: a finite projective comodule has a
  finite matrix-coefficient submodule.
* `TauCeti.Comodule.span_range_coefficientMatrix_eq`: the entries of the coefficient matrix of a
  finite basis span the matrix-coefficient submodule.

## References

The coefficient-space construction is standard; see Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

namespace TauCeti

namespace Comodule

universe u v w

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- The matrix-coefficient submodule of a finite projective comodule is finite. -/
instance matrixCoefficientSubmodule_finite [Module.Finite R M] [Module.Projective R M] :
    Module.Finite R
      (matrixCoefficientSubmodule (R := R) (C := C) (M := M)) := by
  rw [← range_matrixCoefficientTensor]
  infer_instance

/-- The entries of the coefficient matrix of a finite basis span the matrix-coefficient
submodule. -/
theorem span_range_coefficientMatrix_eq {ι : Type*} [Finite ι] (b : Module.Basis ι R M) :
    Submodule.span R (Set.range (fun p : ι × ι ↦ coefficientMatrix (C := C) b p.1 p.2)) =
      matrixCoefficientSubmodule (R := R) (C := C) (M := M) := by
  have := Fintype.ofFinite ι
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    dsimp only
    rw [SetLike.mem_coe, coefficientMatrix_apply]
    exact matrixCoefficient_mem_submodule (R := R) (C := C) (b.coord i) (b j)
  · refine matrixCoefficientSubmodule_le fun φ m ↦ ?_
    have hφ : φ = ∑ i, φ (b i) • b.coord i := by
      refine b.ext fun j ↦ ?_
      simp
    rw [hφ, ← b.sum_repr m]
    simp only [map_sum, map_smul, ← matrixCoefficientBilinear_apply_apply, LinearMap.sum_apply,
      LinearMap.smul_apply]
    refine Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ ?_
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ ?_
    rw [matrixCoefficientBilinear_apply_apply, ← coefficientMatrix_apply]
    exact Submodule.subset_span ⟨(i, j), rfl⟩

end Comodule

end TauCeti
