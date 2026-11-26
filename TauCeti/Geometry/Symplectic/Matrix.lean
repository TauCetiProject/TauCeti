/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.RepresentationTheory.ClassicalGroups.Symplectic
import TauCeti.Algebra.Lie.Symplectic.Basic

/-!
# The symplectic form of the symplectic matrices

Mathlib's real symplectic matrices `Matrix.symplecticGroup (Fin n) ℝ`, the matrices `A` with
`A * J * Aᵀ = J`, and its symplectic Lie algebra `LieAlgebra.Symplectic.sp (Fin n) ℝ`, the
matrices skew-adjoint for `J`, are defined through the canonical skew-symmetric matrix
`J = Matrix.J (Fin n) ℝ`. The alternating form `u ⬝ᵥ J w` behind them is
`TauCeti.stdSymplecticBilinForm ℝ n`. This file bundles it as a symplectic form
`TauCeti.matrixSymplecticForm n` on `ℝ²ⁿ = Fin n ⊕ Fin n → ℝ`,

`ω(u, w) = u ⬝ᵥ J w = ∑ i, (u (inr i) * w (inl i) - u (inl i) * w (inr i))`

(`TauCeti.matrixSymplecticForm_apply_eq_sum`), so that the symplectic matrices and their Lie
algebra are the linear symmetries of a symplectic vector space in the sense of
`TauCeti.SymplecticForm`:

* a matrix preserves `ω` exactly when it is symplectic
  (`TauCeti.matrixSymplecticForm_mulVec_mulVec_iff`), since `ω(A u, A w) = u ⬝ᵥ (Aᵀ J A) w`
  and `Aᵀ J A = J` is the symplectic condition for `Aᵀ`;
* a matrix acts by an endomorphism in the symplectic Lie algebra `sp(ω)` of `ω`
  (`skewAdjointLieSubalgebra`) exactly when it lies in `sp (Fin n) ℝ`
  (`TauCeti.toLin'_mem_skewAdjointLieSubalgebra_matrixSymplecticForm_iff`).

This is the linear model on which the real symplectic group acts, and the input for its moment
map in `TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.SymplecticGroup`.

## Main definitions

* `TauCeti.matrixSymplecticForm n`: the symplectic form `u ⬝ᵥ J w` on `Fin n ⊕ Fin n → ℝ`.

## Main results

* `TauCeti.matrixSymplecticForm_mulVec_mulVec_iff`: the linear symplectomorphisms of
  `matrixSymplecticForm n` are the symplectic matrices.
* `TauCeti.toLin'_mem_skewAdjointLieSubalgebra_matrixSymplecticForm_iff`: the infinitesimal
  symplectomorphisms of `matrixSymplecticForm n` are the matrices of `sp (Fin n) ℝ`.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

variable (n : ℕ)

/-- The **standard symplectic form of the symplectic matrices**: the form
`ω(u, w) = u ⬝ᵥ J w` on `Fin n ⊕ Fin n → ℝ` with Gram matrix Mathlib's canonical
skew-symmetric matrix `J = Matrix.J (Fin n) ℝ`, that is `TauCeti.stdSymplecticBilinForm ℝ n`.
In coordinates it is `∑ i, dpᵢ ∧ dqᵢ` for `qᵢ = inl i` and `pᵢ = inr i`
(`TauCeti.matrixSymplecticForm_apply_eq_sum`). -/
def matrixSymplecticForm : SymplecticForm (Fin n ⊕ Fin n → ℝ) where
  toBilinForm := stdSymplecticBilinForm ℝ n
  isAlt := isAlt_stdSymplecticBilinForm ℝ n
  nondegenerate := stdSymplecticBilinForm_nondegenerate ℝ n

variable {n}

/-- The standard symplectic form is `ω(u, w) = u ⬝ᵥ J w`. -/
theorem matrixSymplecticForm_apply (u w : Fin n ⊕ Fin n → ℝ) :
    matrixSymplecticForm n u w = u ⬝ᵥ J (Fin n) ℝ *ᵥ w :=
  stdSymplecticBilinForm_apply ℝ n u w

/-- The bilinear form of the standard symplectic form is `Matrix.toBilin' J`. -/
theorem matrixSymplecticForm_toBilinForm :
    (matrixSymplecticForm n).toBilinForm = toBilin' (J (Fin n) ℝ) :=
  LinearMap.ext₂ fun u w ↦ (matrixSymplecticForm_apply u w).trans (toBilin'_apply' _ u w).symm

/-- The standard symplectic form in coordinates: `ω = ∑ i, dpᵢ ∧ dqᵢ` for `qᵢ = inl i` and
`pᵢ = inr i`. -/
theorem matrixSymplecticForm_apply_eq_sum (u w : Fin n ⊕ Fin n → ℝ) :
    matrixSymplecticForm n u w =
      ∑ i, (u (Sum.inr i) * w (Sum.inl i) - u (Sum.inl i) * w (Sum.inr i)) := by
  simp [matrixSymplecticForm_apply, J, fromBlocks_mulVec, neg_mulVec, dotProduct,
    Fintype.sum_sum_type, Finset.sum_add_distrib, sub_eq_neg_add]

/-- Precomposing the form with the matrices `A` and `B` gives the form of the matrix `Aᵀ J B`. -/
private theorem matrixSymplecticForm_comp_toLin'
    (A B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    (matrixSymplecticForm n).toBilinForm.comp (toLin' A) (toLin' B) =
      toBilin' (Aᵀ * J (Fin n) ℝ * B) := by
  rw [matrixSymplecticForm_toBilinForm, toBilin'_comp]

/-- **The linear symplectomorphisms of `u ⬝ᵥ J w` are the symplectic matrices.** A matrix `A`
preserves the standard symplectic form, `ω(A u, A w) = ω(u, w)` for all `u` and `w`, exactly when
it lies in `Matrix.symplecticGroup (Fin n) ℝ`. -/
theorem matrixSymplecticForm_mulVec_mulVec_iff (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    (∀ u w, matrixSymplecticForm n (A *ᵥ u) (A *ᵥ w) = matrixSymplecticForm n u w) ↔
      A ∈ symplecticGroup (Fin n) ℝ := by
  rw [SymplecticGroup.mem_iff', ← toBilin'.injective.eq_iff, ← matrixSymplecticForm_comp_toLin',
    ← matrixSymplecticForm_toBilinForm, LinearMap.ext_iff₂]
  simp only [LinearMap.BilinForm.comp_apply, toLin'_apply]

/-- Symplectic matrices preserve the standard symplectic form: `ω(A u, A w) = ω(u, w)`. -/
@[simp]
theorem matrixSymplecticForm_mulVec_mulVec {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hA : A ∈ symplecticGroup (Fin n) ℝ) (u w : Fin n ⊕ Fin n → ℝ) :
    matrixSymplecticForm n (A *ᵥ u) (A *ᵥ w) = matrixSymplecticForm n u w :=
  (matrixSymplecticForm_mulVec_mulVec_iff A).2 hA u w

attribute [local instance 100] LieRing.ofAssociativeRing in
/-- **The infinitesimal symplectomorphisms of `u ⬝ᵥ J w` are the matrices of `sp (Fin n) ℝ`.** A
matrix `A` acts by an endomorphism in the symplectic Lie algebra of the standard symplectic form,
the endomorphisms `X` with `ω(X u, w) = -ω(u, X w)`, exactly when `A` lies in Mathlib's symplectic
Lie algebra `LieAlgebra.Symplectic.sp (Fin n) ℝ`. -/
theorem toLin'_mem_skewAdjointLieSubalgebra_matrixSymplecticForm_iff
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    toLin' A ∈ skewAdjointLieSubalgebra (matrixSymplecticForm n).toBilinForm ↔
      A ∈ LieAlgebra.Symplectic.sp (Fin n) ℝ := by
  -- The underlying submodule of `skewAdjointLieSubalgebra B` is `B.skewAdjointSubmodule`, and
  -- skew-adjointness of `A` compares the forms of the matrices `Aᵀ J` and `-(J A)`.
  have h₁ : (matrixSymplecticForm n).toBilinForm.comp (toLin' A) LinearMap.id =
      toBilin' (Aᵀ * J (Fin n) ℝ) := by
    simpa using matrixSymplecticForm_comp_toLin' A 1
  have h₂ : (matrixSymplecticForm n).toBilinForm.comp LinearMap.id (-toLin' A) =
      toBilin' (-(J (Fin n) ℝ * A)) := by
    simpa using matrixSymplecticForm_comp_toLin' 1 (-A)
  rw [LieAlgebra.Symplectic.mem_sp, ← LieSubalgebra.mem_toSubmodule,
    show (skewAdjointLieSubalgebra (matrixSymplecticForm n).toBilinForm).toSubmodule =
      (matrixSymplecticForm n).toBilinForm.skewAdjointSubmodule from rfl,
    LinearMap.mem_skewAdjointSubmodule, ← toBilin'.injective.eq_iff, ← h₁, ← h₂,
    LinearMap.ext_iff₂]
  -- `LinearMap.IsSkewAdjoint B f` is by definition `∀ u w, B (f u) w = B u (-f w)`.
  rfl

end TauCeti
