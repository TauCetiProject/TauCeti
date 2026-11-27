/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Standard
public import TauCeti.RepresentationTheory.Tensor.Induction.Basic

import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import TauCeti.Algebra.Group.Action.End
import TauCeti.LinearAlgebra.Matrix.StdBasis

/-!
# The triality action of `GL₂ ≀ S₃` on `M₂ ⊗ R²`

Let `R` be a commutative semiring. The module `M₂(R) ⊗[R] R²` is a triple tensor product of
copies of `R²`: the rank-one matrix `x yᵀ` tensored with `v` corresponds to the pure tensor
`x ⊗ v ⊗ y`. Under this identification a triple `(g₀, g₁, g₂)` of invertible matrices acts by
`m ⊗ v ↦ g₀ m g₂ᵀ ⊗ g₁ v`, and the symmetric group `S₃` permutes the three tensor factors. The
transposition `(0 2)` exchanges the row and column factors of the matrix, so it sends `m ⊗ v` to
`mᵀ ⊗ v`.

This file constructs that action as a representation of the permutation wreath product
`GL₂(R) ≀ S₃ = (Fin 3 → GL₂(R)) ⋊ S₃`, by transporting the tensor cube of the standard
representation of `GL₂(R)` along the identification. The semidirect product relation
`σ (g₀, g₁, g₂) σ⁻¹ = (g_{σ⁻¹ 0}, g_{σ⁻¹ 1}, g_{σ⁻¹ 2})` expresses that permuting the tensor
factors permutes the three copies of `GL₂(R)`. This is the action on the symplectic space
`M₂(F) ⊗ F²` underlying Dor's triality kernel.

## Main definitions

* `TauCeti.GL2Triality.tripleTensorEquiv`: the identification `M₂(R) ⊗[R] R² ≃ₗ[R] ⨂[R]³ R²`
  sending `x₀ x₂ᵀ ⊗ x₁` to `x₀ ⊗ x₁ ⊗ x₂`.
* `TauCeti.GL2Triality.representation`: the triality representation of `GL₂(R) ≀ S₃` on
  `M₂(R) ⊗[R] R²`.

## Main results

* `TauCeti.GL2Triality.tripleTensorEquiv_representation`: the identification intertwines the
  triality representation with the tensor cube of the standard representation.
* `TauCeti.GL2Triality.representation_inl_tmul`: a triple of matrices acts by
  `m ⊗ v ↦ g₀ m g₂ᵀ ⊗ g₁ v`.
* `TauCeti.GL2Triality.representation_inr_swap_tmul`: the transposition `(0 2)` acts by
  `m ⊗ v ↦ mᵀ ⊗ v`.
* `TauCeti.GL2Triality.representation_inr_mul_inl_mul_inr_inv`: conjugation by a permutation
  permutes the three copies of `GL₂(R)`.

## References

* Gal Dor, *Exotic Monoidal Structures and Abstractly Automorphic Representations for GL(2)*,
  Forum of Mathematics, Pi 11 (2023), e20, Constructions 2.7 and 2.9.
-/

public section

namespace TauCeti.GL2Triality

open Matrix TensorProduct

variable (R : Type*) [CommSemiring R]

/-- The bijection between index pairs `((a, b), c)` of the matrix units `E_{ab} ⊗ e_c` and the
triple indices `![a, c, b]`: the row is the first factor, the vector the second and the column the
third. -/
private def tripleIndexEquiv : (Fin 2 × Fin 2) × Fin 2 ≃ (Fin 3 → Fin 2) where
  toFun p := ![p.1.1, p.2, p.1.2]
  invFun i := ((i 0, i 2), i 1)
  left_inv _ := rfl
  right_inv i := by
    ext k
    fin_cases k <;> rfl

private theorem tripleIndexEquiv_symm_apply (i : Fin 3 → Fin 2) :
    tripleIndexEquiv.symm i = ((i 0, i 2), i 1) :=
  rfl

/-- The basis of `M₂(R) ⊗[R] R²` indexed by triples of indices: its vector at `i` is
`E_{i 0, i 2} ⊗ e_{i 1}`. -/
private noncomputable def tripleBasis :
    Module.Basis (Fin 3 → Fin 2) R (Matrix (Fin 2) (Fin 2) R ⊗[R] (Fin 2 → R)) :=
  ((Matrix.stdBasis R (Fin 2) (Fin 2)).tensorProduct (Pi.basisFun R (Fin 2))).reindex
    tripleIndexEquiv

/-- The coordinates of `a cᵀ ⊗ b` in the triple basis are the products of the coordinates of
the three vectors. -/
private theorem tripleBasis_repr_vecMulVec_tmul (a b c : Fin 2 → R) (i : Fin 3 → Fin 2) :
    (tripleBasis R).repr (vecMulVec a c ⊗ₜ b) i = ∏ k, ![a, b, c] k (i k) := by
  simp only [tripleBasis, Module.Basis.repr_reindex_apply, tripleIndexEquiv_symm_apply,
    Module.Basis.tensorProduct_repr_tmul_apply, stdBasis_repr_apply, Pi.basisFun_repr,
    vecMulVec_apply, smul_eq_mul, Fin.prod_univ_three, cons_val]
  ring

/-- The identification of `M₂(R) ⊗[R] R²` with the triple tensor power of `R²`, sending
`x₀ x₂ᵀ ⊗ x₁` to `x₀ ⊗ x₁ ⊗ x₂`: the rows of a matrix form the first tensor factor, the vector the
second and the columns the third. -/
noncomputable def tripleTensorEquiv :
    (Matrix (Fin 2) (Fin 2) R ⊗[R] (Fin 2 → R)) ≃ₗ[R] ⨂[R] _ : Fin 3, (Fin 2 → R) :=
  (tripleBasis R).repr ≪≫ₗ
    (Basis.piTensorProduct fun _ : Fin 3 ↦ Pi.basisFun R (Fin 2)).repr.symm

variable {R}

/-- The identification sends `a cᵀ ⊗ b` to the pure tensor `a ⊗ b ⊗ c`. -/
@[simp]
theorem tripleTensorEquiv_vecMulVec_tmul (a b c : Fin 2 → R) :
    tripleTensorEquiv R (vecMulVec a c ⊗ₜ b) = ⨂ₜ[R] k, ![a, b, c] k := by
  refine (Basis.piTensorProduct fun _ : Fin 3 ↦ Pi.basisFun R (Fin 2)).repr.injective
    (Finsupp.ext fun i ↦ ?_)
  simp [tripleTensorEquiv, tripleBasis_repr_vecMulVec_tmul]

/-- The identification sends the pure tensor `x₀ ⊗ x₁ ⊗ x₂` back to `x₀ x₂ᵀ ⊗ x₁`. -/
@[simp]
theorem tripleTensorEquiv_symm_tprod (x : Fin 3 → Fin 2 → R) :
    (tripleTensorEquiv R).symm (⨂ₜ[R] k, x k) = vecMulVec (x 0) (x 2) ⊗ₜ x 1 := by
  rw [LinearEquiv.symm_apply_eq, tripleTensorEquiv_vecMulVec_tmul]
  congr 1
  ext k
  fin_cases k <;> rfl

/-- Linear maps out of `M₂(R) ⊗[R] R²` agreeing on the tensors `a cᵀ ⊗ b` are equal. -/
theorem linearMap_ext_vecMulVec_tmul {N : Type*} [AddCommMonoid N] [Module R N]
    {f g : Matrix (Fin 2) (Fin 2) R ⊗[R] (Fin 2 → R) →ₗ[R] N}
    (h : ∀ a b c : Fin 2 → R, f (vecMulVec a c ⊗ₜ b) = g (vecMulVec a c ⊗ₜ b)) : f = g := by
  refine (LinearMap.cancel_right (tripleTensorEquiv R).symm.surjective).mp
    (PiTensorProduct.ext (MultilinearMap.ext fun x ↦ ?_))
  simpa using h (x 0) (x 1) (x 2)

section Action

variable (R)

/-- The triality representation of the permutation wreath product `GL₂(R) ≀ S₃` on
`M₂(R) ⊗[R] R²`: a triple `(g₀, g₁, g₂)` acts by `m ⊗ v ↦ g₀ m g₂ᵀ ⊗ g₁ v`, and `S₃` permutes the
three tensor factors. It is the tensor cube of the standard representation of `GL₂(R)`,
transported along `tripleTensorEquiv`. -/
noncomputable def representation :
    Representation R (WreathProduct (GL (Fin 2) R) (Fin 3))
      (Matrix (Fin 2) (Fin 2) R ⊗[R] (Fin 2 → R)) :=
  (((tripleTensorEquiv R).symm.conjAlgEquiv R : Module.End R _ ≃ₐ[R] Module.End R _) :
    Module.End R _ →* Module.End R _).comp ((stdRep R 2).wreathTensor (Fin 3))

variable {R}

/-- The identification with the triple tensor power intertwines the triality representation with
the tensor cube of the standard representation. -/
@[simp]
theorem tripleTensorEquiv_representation (w : WreathProduct (GL (Fin 2) R) (Fin 3))
    (y : Matrix (Fin 2) (Fin 2) R ⊗[R] (Fin 2 → R)) :
    tripleTensorEquiv R (representation R w y) =
      (stdRep R 2).wreathTensor (Fin 3) w (tripleTensorEquiv R y) := by
  simp [representation, LinearEquiv.conjAlgEquiv_apply]

/-- The triality representation on the tensors `a cᵀ ⊗ b`: the factor in position `k` of
`![a, b, c]` moves to position `σ k`, for the permutation `σ` of `w`, and the matrix of `w` in each
position is then applied. -/
theorem representation_vecMulVec_tmul (w : WreathProduct (GL (Fin 2) R) (Fin 3))
    (a b c : Fin 2 → R) :
    representation R w (vecMulVec a c ⊗ₜ b) =
      vecMulVec ((w.left 0 : Matrix (Fin 2) (Fin 2) R) *ᵥ ![a, b, c] (w.right⁻¹ 0))
          ((w.left 2 : Matrix (Fin 2) (Fin 2) R) *ᵥ ![a, b, c] (w.right⁻¹ 2)) ⊗ₜ
        ((w.left 1 : Matrix (Fin 2) (Fin 2) R) *ᵥ ![a, b, c] (w.right⁻¹ 1)) := by
  apply (tripleTensorEquiv R).injective
  rw [tripleTensorEquiv_representation, tripleTensorEquiv_vecMulVec_tmul,
    tripleTensorEquiv_vecMulVec_tmul]
  simp only [Representation.wreathTensor_apply_tprod, stdRep_apply_apply, ← Equiv.Perm.inv_def]
  refine congrArg _ (funext fun k ↦ ?_)
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, cons_val]

/-- A triple of invertible matrices acts on `M₂(R) ⊗[R] R²` by `m ⊗ v ↦ g₀ m g₂ᵀ ⊗ g₁ v`. -/
@[simp]
theorem representation_inl_tmul (g : Fin 3 → GL (Fin 2) R) (m : Matrix (Fin 2) (Fin 2) R)
    (v : Fin 2 → R) :
    representation R (SemidirectProduct.inl g) (m ⊗ₜ v) =
      ((g 0 : Matrix (Fin 2) (Fin 2) R) * m * (g 2 : Matrix (Fin 2) (Fin 2) R)ᵀ) ⊗ₜ
        ((g 1 : Matrix (Fin 2) (Fin 2) R) *ᵥ v) := by
  have h : representation R (SemidirectProduct.inl g) = TensorProduct.map
      (LinearMap.mulLeft R (g 0 : Matrix (Fin 2) (Fin 2) R) ∘ₗ
        LinearMap.mulRight R (g 2 : Matrix (Fin 2) (Fin 2) R)ᵀ)
      (Matrix.toLin' (g 1 : Matrix (Fin 2) (Fin 2) R)) :=
    linearMap_ext_vecMulVec_tmul fun a b c ↦ by
      simp [representation_vecMulVec_tmul, mul_vecMulVec, vecMulVec_mul,
        vecMul_transpose]
  simp [h, Matrix.mul_assoc]

/-- The transposition exchanging the row and column factors acts on `M₂(R) ⊗[R] R²` by
`m ⊗ v ↦ mᵀ ⊗ v`. -/
@[simp]
theorem representation_inr_swap_tmul (m : Matrix (Fin 2) (Fin 2) R) (v : Fin 2 → R) :
    representation R (SemidirectProduct.inr (Equiv.swap 0 2)) (m ⊗ₜ v) = mᵀ ⊗ₜ v := by
  have h : representation R (SemidirectProduct.inr (Equiv.swap 0 2)) =
      TensorProduct.map (Matrix.transposeLinearEquiv (Fin 2) (Fin 2) R R).toLinearMap
        LinearMap.id :=
    linearMap_ext_vecMulVec_tmul fun a b c ↦ by
      simp [representation_vecMulVec_tmul, transpose_vecMulVec, Equiv.swap_apply_of_ne_of_ne]
  simp [h]

/-- Conjugating the action of a triple of invertible matrices by a permutation `σ` of the tensor
factors permutes the three copies of `GL₂(R)`: the matrix in position `k` moves to position
`σ k`. -/
theorem representation_inr_mul_inl_mul_inr_inv (σ : Equiv.Perm (Fin 3))
    (g : Fin 3 → GL (Fin 2) R) :
    representation R (SemidirectProduct.inr σ) * representation R (SemidirectProduct.inl g) *
        representation R (SemidirectProduct.inr σ⁻¹) =
      representation R (SemidirectProduct.inl (g ∘ σ.symm)) := by
  rw [← map_mul, ← map_mul, ← SemidirectProduct.inl_aut]
  refine congrArg (fun h ↦ representation R (SemidirectProduct.inl h)) (funext fun k ↦ ?_)
  rw [Function.comp_apply, mulAutArrow_apply_apply_eq_apply_inv_smul, Equiv.Perm.smul_def,
    Equiv.Perm.inv_def]

end Action

end TauCeti.GL2Triality
