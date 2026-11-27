/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Balanced tensor products over commutative rings

If `A` is a commutative `R`-algebra and the right `A`-action on `M` agrees with its left
`A`-action, `BalancedTensorProduct.tensorProductEquiv` identifies the balanced tensor product
with Mathlib's `M ⊗[A] N` by an `R`-linear equivalence natural in both factors. In particular,
taking `A = R` compares the two constructions of the tensor product over the same ring.

The comparison uses Mathlib's `TensorProduct.AlgebraTensorModule.ker_mapOfCompatibleSMul`.
The description of the ring tensor product by the balancing relations is in Mac Lane,
*Categories for the Working Mathematician*, §IX.6.
-/

public section

namespace TauCeti.BalancedTensorProduct

open scoped Pointwise TensorProduct

variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [Module Aᵐᵒᵖ M] [IsCentralScalar A M]
  [IsScalarTower R A M] [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]

private theorem relations_eq_ker :
    balancedTensorRelations R A M N =
      ((TensorProduct.mapOfCompatibleSMul A R A M N).restrictScalars R).ker := by
  rw [LinearMap.ker_restrictScalars, TensorProduct.AlgebraTensorModule.ker_mapOfCompatibleSMul,
    balancedTensorRelations_def]
  simp only [op_smul_eq_smul]
  let S : Set (M ⊗[R] N) := {z | ∃ (a : A) (m : M) (n : N),
    (a • m) ⊗ₜ[R] n - m ⊗ₜ[R] (a • n) = z}
  -- Multiplying a generator by a scalar of A multiplies its first factor by that scalar.
  have hS : (Set.univ : Set A) • S = S := by
    refine Set.Subset.antisymm ?_ (fun z hz ↦ ⟨1, Set.mem_univ _, z, hz, one_smul A z⟩)
    rintro _ ⟨b, -, z, hz, rfl⟩
    obtain ⟨a, m, n, rfl⟩ := hz
    refine ⟨a, b • m, n, ?_⟩
    simp only [smul_sub, TensorProduct.smul_tmul']
    rw [smul_comm b a m]
  have hgen : {z : M ⊗[R] N | ∃ (a : A) (m : M) (n : N),
      z = (a • m) ⊗ₜ[R] n - m ⊗ₜ[R] (a • n)} = S := by
    ext z
    constructor <;> rintro ⟨a, m, n, h⟩ <;> exact ⟨a, m, n, h.symm⟩
  rw [hgen, ← Submodule.span_smul_of_span_eq_top (R := R) (S := A) Submodule.span_univ S, hS]

variable (R A M N) in
/-- Over a commutative algebra, the balanced tensor product of compatible modules is the
ordinary tensor product over that algebra, viewed over the ground ring. -/
noncomputable def tensorProductEquiv : BalancedTensorProduct R A M N ≃ₗ[R] M ⊗[A] N :=
  (balancedTensorRelations R A M N).quotEquivOfEq _ relations_eq_ker ≪≫ₗ
    ((TensorProduct.mapOfCompatibleSMul A R A M N).restrictScalars R).quotKerEquivOfSurjective
      (TensorProduct.mapOfCompatibleSMul_surjective A R A M N)

/-- The comparison sends a balanced pure tensor to the corresponding ordinary pure tensor. -/
@[simp]
theorem tensorProductEquiv_tmul (m : M) (n : N) :
    tensorProductEquiv R A M N (tmul R A m n) = m ⊗ₜ[A] n := by
  rw [← mkQ_tmul, mkQ_def, tensorProductEquiv]
  let f := (TensorProduct.mapOfCompatibleSMul A R A M N).restrictScalars R
  let e := f.quotKerEquivOfSurjective (TensorProduct.mapOfCompatibleSMul_surjective A R A M N)
  exact (congrArg e (Submodule.quotEquivOfEq_mk _ _ relations_eq_ker _)).trans
    ((LinearMap.quotKerEquivOfSurjective_apply_mk f _ _).trans
      (TensorProduct.mapOfCompatibleSMul_tmul A R A M N m n))

/-- The inverse comparison sends an ordinary pure tensor to the corresponding balanced one. -/
@[simp]
theorem tensorProductEquiv_symm_tmul (m : M) (n : N) :
    (tensorProductEquiv R A M N).symm (m ⊗ₜ[A] n) = tmul R A m n := by
  rw [LinearEquiv.symm_apply_eq, tensorProductEquiv_tmul]

variable {M' N' : Type*}
  [AddCommGroup M'] [Module R M'] [Module A M'] [Module Aᵐᵒᵖ M'] [IsCentralScalar A M']
  [IsScalarTower R A M'] [AddCommGroup N'] [Module R N'] [Module A N'] [IsScalarTower R A N']

/-- The commutative comparison intertwines the maps induced by linear maps in both factors. -/
@[simp]
theorem tensorProductEquiv_map (f : M →ₗ[A] M') (g : N →ₗ[A] N')
    (z : BalancedTensorProduct R A M N) :
    tensorProductEquiv R A M' N'
        (map (f.restrictScalars R) (g.restrictScalars R)
          (fun a m ↦ by simp) (fun a n ↦ by simp) z) =
      TensorProduct.map f g (tensorProductEquiv R A M N z) := by
  induction z using induction_on with
  | ht m n => simp
  | ha x y hx hy => simp [map_add, hx, hy]

end TauCeti.BalancedTensorProduct
