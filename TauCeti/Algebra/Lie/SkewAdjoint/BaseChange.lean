/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.SkewAdjoint
public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.Algebra.Matrix.BaseChange

/-!
# Extension of scalars for skew-adjoint matrix Lie algebras

For a square matrix `J` over a commutative ring `R` and a flat `R`-algebra `S`, extending scalars
identifies `S ⊗[R] skewAdjointMatricesLieSubalgebra J` with the Lie algebra of matrices over `S`
that are skew-adjoint for the image `J.map (algebraMap R S)` of `J`, entrywise. The orthogonal and
symplectic Lie algebras `LieAlgebra.Orthogonal.so` and `LieAlgebra.Symplectic.sp` are of this
form, so their scalar extensions are again orthogonal and symplectic Lie algebras. This lets
properties of these Lie algebras that are proved over an algebraic closure be descended to the
base field.

Skew-adjointness for `J` is the vanishing of the linear map `A ↦ Aᵀ * J + J * A`, and over a flat
algebra extension of scalars commutes with kernels.

## Main declarations

* `TauCeti.skewAdjointMatricesLieSubalgebraBaseChangeEquiv`: the Lie algebra isomorphism
  `S ⊗[R] skewAdjointMatricesLieSubalgebra J ≃ₗ⁅S⁆
  skewAdjointMatricesLieSubalgebra (J.map (algebraMap R S))`.
* `TauCeti.skewAdjointMatricesLieSubalgebraBaseChangeEquiv_tmul`: it sends `s ⊗ₜ A` to
  `s • A.map (algebraMap R S)`.
-/

public section

namespace TauCeti

open scoped TensorProduct
open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The linear map `A ↦ Aᵀ * J + J * A`, whose kernel consists of the matrices skew-adjoint for
`J`. -/
private def skewAdjointDefect {T : Type*} [CommRing T] (J : Matrix n n T) :
    Matrix n n T →ₗ[T] Matrix n n T where
  toFun A := Aᵀ * J + J * A
  map_add' A B := by simp only [transpose_add, add_mul, mul_add]; abel
  map_smul' c A := by simp [transpose_smul, smul_add]

private theorem mem_skewAdjointMatricesSubmodule_iff_skewAdjointDefect {T : Type*} [CommRing T]
    (J A : Matrix n n T) :
    A ∈ skewAdjointMatricesSubmodule J ↔ skewAdjointDefect J A = 0 := by
  simp [skewAdjointDefect, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, add_eq_zero_iff_eq_neg]

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] (J : Matrix n n R)

private theorem matrixBaseChangeAlgEquiv_skewAdjointDefect (x : S ⊗[R] Matrix n n R) :
    Algebra.matrixBaseChangeAlgEquiv R S n
        (TensorProduct.AlgebraTensorModule.lTensor S S (skewAdjointDefect J) x) =
      skewAdjointDefect (J.map (algebraMap R S)) (Algebra.matrixBaseChangeAlgEquiv R S n x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s A =>
    simp [skewAdjointDefect, Matrix.map_add, Matrix.map_mul, Matrix.transpose_map, smul_add]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Extension of scalars of a skew-adjoint matrix, as a Lie algebra map into matrices over `S`. -/
private def skewAdjointBaseChangeToMatrix :
    S ⊗[R] skewAdjointMatricesLieSubalgebra J →ₗ⁅S⁆ Matrix n n S :=
  { (Algebra.matrixBaseChangeAlgEquiv R S n).toLinearMap.comp
      (TensorProduct.AlgebraTensorModule.lTensor S S
        ((skewAdjointMatricesLieSubalgebra J).incl : skewAdjointMatricesLieSubalgebra J →ₗ[R]
          Matrix n n R)) with
    map_lie' := by
      intro x y
      simp only [LinearMap.toFun_eq_coe]
      induction x using TensorProduct.inductionOn with
      | add x x' hx hx' => simp only [add_lie, map_add, hx, hx']
      | tmul s a =>
        induction y using TensorProduct.inductionOn with
        | add y y' hy hy' => simp only [lie_add, map_add, hy, hy']
        | tmul t b =>
          simp only [LieAlgebra.ExtendScalars.bracket_tmul]
          simp [Ring.lie_def, Matrix.map_sub, Matrix.map_mul, smul_sub, smul_smul, mul_comm s t] }

private theorem skewAdjointBaseChangeToMatrix_apply
    (x : S ⊗[R] skewAdjointMatricesLieSubalgebra J) :
    skewAdjointBaseChangeToMatrix S J x = Algebra.matrixBaseChangeAlgEquiv R S n
      (((skewAdjointMatricesLieSubalgebra J).incl :
        skewAdjointMatricesLieSubalgebra J →ₗ[R] Matrix n n R).lTensor S x) :=
  rfl

private theorem skewAdjointBaseChangeToMatrix_tmul (s : S)
    (A : skewAdjointMatricesLieSubalgebra J) :
    skewAdjointBaseChangeToMatrix S J (s ⊗ₜ A) = s • (A : Matrix n n R).map (algebraMap R S) := by
  simp [skewAdjointBaseChangeToMatrix_apply]

private theorem skewAdjointBaseChangeToMatrix_mem (x : S ⊗[R] skewAdjointMatricesLieSubalgebra J) :
    skewAdjointBaseChangeToMatrix S J x ∈
      skewAdjointMatricesLieSubalgebra (J.map (algebraMap R S)) := by
  rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule_iff_skewAdjointDefect]
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | tmul s A =>
    have hA := (mem_skewAdjointMatricesSubmodule_iff_skewAdjointDefect J A).mp A.2
    rw [skewAdjointBaseChangeToMatrix_tmul, ← Algebra.matrixBaseChangeAlgEquiv_tmul,
      ← matrixBaseChangeAlgEquiv_skewAdjointDefect]
    simp [hA]

/-- Extension of scalars of a skew-adjoint matrix, with values in the skew-adjoint matrices over
`S`. -/
private def skewAdjointBaseChangeToSubalgebra :
    S ⊗[R] skewAdjointMatricesLieSubalgebra J →ₗ⁅S⁆
      skewAdjointMatricesLieSubalgebra (J.map (algebraMap R S)) where
  toFun x := ⟨skewAdjointBaseChangeToMatrix S J x, skewAdjointBaseChangeToMatrix_mem S J x⟩
  map_add' x y := Subtype.ext (map_add _ x y)
  map_smul' c x := Subtype.ext (map_smul _ c x)
  map_lie' := Subtype.ext (LieHom.map_lie _ _ _)

private theorem coe_skewAdjointBaseChangeToSubalgebra_apply
    (x : S ⊗[R] skewAdjointMatricesLieSubalgebra J) :
    (skewAdjointBaseChangeToSubalgebra S J x : Matrix n n S) =
      skewAdjointBaseChangeToMatrix S J x :=
  rfl

variable [Module.Flat R S]

private theorem skewAdjointBaseChangeToSubalgebra_bijective :
    Function.Bijective (skewAdjointBaseChangeToSubalgebra S J) := by
  let L := skewAdjointMatricesLieSubalgebra J
  let ι : L →ₗ[R] Matrix n n R := (L.incl : L →ₗ[R] Matrix n n R)
  let e := Algebra.matrixBaseChangeAlgEquiv R S n
  have hexact : Function.Exact ι (skewAdjointDefect J) := fun y ↦ by
    rw [← mem_skewAdjointMatricesSubmodule_iff_skewAdjointDefect]
    exact ⟨fun hy ↦ ⟨⟨y, hy⟩, rfl⟩, fun ⟨z, hz⟩ ↦ hz ▸ z.2⟩
  have hexactS := Module.Flat.lTensor_exact S hexact
  refine ⟨fun x y hxy ↦ ?_, fun z ↦ ?_⟩
  · have h := congrArg Subtype.val hxy
    simp only [coe_skewAdjointBaseChangeToSubalgebra_apply,
      skewAdjointBaseChangeToMatrix_apply] at h
    exact Module.Flat.lTensor_preserves_injective_linearMap ι Subtype.val_injective (e.injective h)
  · obtain ⟨z, hz⟩ := z
    have hzero : (skewAdjointDefect J).lTensor S (e.symm z) = 0 := by
      apply e.injective
      have := matrixBaseChangeAlgEquiv_skewAdjointDefect S J (e.symm z)
      rw [AlgEquiv.apply_symm_apply] at this
      rw [map_zero]
      refine this.trans ?_
      exact (mem_skewAdjointMatricesSubmodule_iff_skewAdjointDefect _ z).mp hz
    obtain ⟨w, hw⟩ := (hexactS (e.symm z)).mp hzero
    refine ⟨w, Subtype.ext ?_⟩
    rw [coe_skewAdjointBaseChangeToSubalgebra_apply, skewAdjointBaseChangeToMatrix_apply]
    exact (congrArg e hw).trans (e.apply_symm_apply z)

/-- **Extension of scalars for skew-adjoint matrix Lie algebras.** Over a flat `R`-algebra `S`,
`S ⊗[R] skewAdjointMatricesLieSubalgebra J` is the Lie algebra of matrices over `S` that are
skew-adjoint for `J.map (algebraMap R S)`, entrywise. -/
noncomputable def skewAdjointMatricesLieSubalgebraBaseChangeEquiv :
    S ⊗[R] skewAdjointMatricesLieSubalgebra J ≃ₗ⁅S⁆
      skewAdjointMatricesLieSubalgebra (J.map (algebraMap R S)) :=
  LieEquiv.ofBijective (skewAdjointBaseChangeToSubalgebra S J)
    (skewAdjointBaseChangeToSubalgebra_bijective S J)

/-- The extension-of-scalars isomorphism sends `s ⊗ₜ A` to `s • A.map (algebraMap R S)`. -/
@[simp]
theorem skewAdjointMatricesLieSubalgebraBaseChangeEquiv_tmul (s : S)
    (A : skewAdjointMatricesLieSubalgebra J) :
    (skewAdjointMatricesLieSubalgebraBaseChangeEquiv S J (s ⊗ₜ A) : Matrix n n S) =
      s • (A : Matrix n n R).map (algebraMap R S) :=
  skewAdjointBaseChangeToMatrix_tmul S J s A

end TauCeti
