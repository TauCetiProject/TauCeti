/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.Defs
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Unit
import TauCeti.Algebra.Ring.NegOnePow

/-!
# The differential on a balanced tensor product of DG modules

For a right DG module `M` and a left DG module `N` over the same DG algebra `A`, the
ordinary balanced tensor product carries the differential
`d (m ⊗ n) = dM m ⊗ n + (-1)^|m| m ⊗ dN n`.
The two module Leibniz rules make this formula balanced even when the algebra differential
is nonzero. Its square vanishes by cancellation of the mixed terms.

This file constructs that endomorphism over an arbitrary commutative ground ring and proves
compatibility with tensoring DG module morphisms and with the regular-module unit
identifications. It supplies the differential on the underlying balanced module; a grading
on the quotient and outer bimodule actions are separate constructions.

## References

* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public section

open MulOpposite DirectSum

namespace TauCeti.BalancedTensorProduct

variable {R A M N : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A}
  {hA : IsDGAlgebra 𝒜 dA} {ℳ : ℤ → Submodule R M} {ℳN : ℤ → Submodule R N}
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℳN]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  [SetLike.GradedSMul 𝒜 ℳN]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N}

private noncomputable def differentialBilinear :
    M →ₗ[R] N →ₗ[R] BalancedTensorProduct R A M N :=
  (mk R A).comp dM +
    ((mk R A).comp ((InternalGrading.ofDecomposition ℳ).koszulTwist 1)).compl₂ dN

omit [Algebra R A] [IsScalarTower R Aᵐᵒᵖ M] [IsScalarTower R A N] in
private theorem differentialBilinear_apply (m : M) (n : N) :
    differentialBilinear (R := R) (A := A) (ℳ := ℳ) (dM := dM) (dN := dN) m n =
      tmul R A (dM m) n +
        tmul R A ((InternalGrading.ofDecomposition ℳ).koszulTwist 1 m) (dN n) := by
  simp [differentialBilinear]

omit [Algebra R A] [IsScalarTower R Aᵐᵒᵖ M] [IsScalarTower R A N] in
private theorem differentialBilinear_of_mem {q : ℤ} {m : M} (hm : m ∈ ℳ q) (n : N) :
    differentialBilinear (R := R) (A := A) (ℳ := ℳ) (dM := dM) (dN := dN) m n =
      tmul R A (dM m) n + (((q.negOnePow : ℤ) : R)) • tmul R A m (dN n) := by
  rw [differentialBilinear_apply,
    (InternalGrading.ofDecomposition ℳ).koszulTwist_apply_of_mem
      (by simpa only [InternalGrading.ofDecomposition_piece] using hm) 1, one_mul, smul_tmul]

private theorem differentialBilinear_balanced_of_mem
    (hM : IsDGRightModule hA ℳ dM) (hN : IsDGLeftModule hA ℳN dN)
    {p q : ℤ} {a : A} {m : M} (ha : a ∈ 𝒜 p) (hm : m ∈ ℳ q) (n : N) :
    differentialBilinear (R := R) (A := A) (ℳ := ℳ) (dM := dM) (dN := dN) (op a • m) n =
      differentialBilinear (R := R) (A := A) (ℳ := ℳ) (dM := dM) (dN := dN) m (a • n) := by
  have hop : op a ∈ (InternalGrading.ofDecomposition 𝒜).opposite.piece p :=
    ((InternalGrading.ofDecomposition 𝒜).op_mem_opposite_piece_iff p a).2
      (by simpa only [InternalGrading.ofDecomposition_piece] using ha)
  rw [differentialBilinear_of_mem (SetLike.GradedSMul.smul_mem hop hm),
    differentialBilinear_of_mem hm, hM.leibniz hm a, hN.leibniz ha n]
  simp only [negOnePow_smul_eq_negOnePowCast_smul (R := R), negOnePowCast_eq_intCast,
    add_tmul, smul_tmul, tmul_add, tmul_smul, balance, smul_add, smul_smul,
    vadd_eq_add, Int.negOnePow_add, Units.val_mul, Int.cast_mul]
  module

private theorem differentialBilinear_balanced
    (hM : IsDGRightModule hA ℳ dM) (hN : IsDGLeftModule hA ℳN dN) (a : A) (m : M) (n : N) :
    differentialBilinear (R := R) (A := A) (ℳ := ℳ) (dM := dM) (dN := dN) (op a • m) n =
      differentialBilinear (R := R) (A := A) (ℳ := ℳ) (dM := dM) (dN := dN) m (a • n) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 a, ← DirectSum.sum_support_decompose ℳ m]
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 a, ← DirectSum.sum_support_decompose ℳ m]
  simp only [Finset.op_sum, Finset.sum_smul, Finset.smul_sum, map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  exact differentialBilinear_balanced_of_mem hM hN (SetLike.coe_mem _) (SetLike.coe_mem _) n

/-- The signed tensor differential on the ordinary balanced tensor product of a right and a
left DG module. No flatness assumption is needed for this underived construction. -/
noncomputable def differential (hM : IsDGRightModule hA ℳ dM) (hN : IsDGLeftModule hA ℳN dN) :
    Module.End R (BalancedTensorProduct R A M N) :=
  lift (differentialBilinear (R := R) (A := A) (ℳ := ℳ) (dM := dM) (dN := dN))
    (differentialBilinear_balanced hM hN)

/-- On arbitrary pure tensors, the sign is represented by the grading's Koszul twist. -/
@[simp]
theorem differential_tmul (hM : IsDGRightModule hA ℳ dM) (hN : IsDGLeftModule hA ℳN dN)
    (m : M) (n : N) :
    differential hM hN (tmul R A m n) = tmul R A (dM m) n +
      tmul R A ((InternalGrading.ofDecomposition ℳ).koszulTwist 1 m) (dN n) := by
  rw [differential, lift_tmul, differentialBilinear_apply]

/-- The tensor differential has the usual sign on a homogeneous left factor. -/
theorem differential_tmul_of_mem (hM : IsDGRightModule hA ℳ dM)
    (hN : IsDGLeftModule hA ℳN dN) {q : ℤ} {m : M} (hm : m ∈ ℳ q) (n : N) :
    differential hM hN (tmul R A m n) =
      tmul R A (dM m) n + (((q.negOnePow : ℤ) : R)) • tmul R A m (dN n) := by
  rw [differential, lift_tmul, differentialBilinear_of_mem hm]

/-- The differential on the balanced tensor product squares to zero. -/
@[simp]
theorem differential_comp_self (hM : IsDGRightModule hA ℳ dM)
    (hN : IsDGLeftModule hA ℳN dN) :
    differential hM hN ∘ₗ differential hM hN = 0 := by
  apply hom_ext
  intro m n
  have key :
      ((differential hM hN ∘ₗ differential hM hN) ∘ₗ (mk R A).flip n :
        M →ₗ[R] BalancedTensorProduct R A M N) = 0 := by
    apply (InternalGrading.ofDecomposition ℳ).linearMap_ext
    intro q x hx
    rw [InternalGrading.ofDecomposition_piece] at hx
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, mk_apply]
    rw [differential_tmul_of_mem hM hN hx, map_add, map_smul,
      differential_tmul_of_mem hM hN (hM.isHomogeneous.map_mem hx),
      differential_tmul_of_mem hM hN hx, hM.sq_zero, hN.sq_zero, Int.negOnePow_succ]
    simp
  simpa only [LinearMap.comp_apply, LinearMap.flip_apply, mk_apply, LinearMap.zero_apply]
    using LinearMap.congr_fun key m

/-- Applying the tensor differential twice gives zero. -/
@[simp]
theorem differential_sq_zero (hM : IsDGRightModule hA ℳ dM) (hN : IsDGLeftModule hA ℳN dN)
    (z : BalancedTensorProduct R A M N) : differential hM hN (differential hM hN z) = 0 :=
  LinearMap.congr_fun (differential_comp_self hM hN) z

section Naturality

variable {M' N' : Type*}
  [AddCommGroup M'] [Module R M'] [Module Aᵐᵒᵖ M'] [IsScalarTower R Aᵐᵒᵖ M']
  [AddCommGroup N'] [Module R N'] [Module A N'] [IsScalarTower R A N']
  {ℳ' : ℤ → Submodule R M'} {ℳN' : ℤ → Submodule R N'}
  [DirectSum.Decomposition ℳ'] [DirectSum.Decomposition ℳN']
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ']
  [SetLike.GradedSMul 𝒜 ℳN'] {dM' : M' →ₗ[R] M'} {dN' : N' →ₗ[R] N'}

/-- Tensoring equivariant chain maps, with the first map of degree zero, commutes with the balanced
tensor differential. Only the first map's degree is needed for this differential identity. -/
theorem differential_naturality (hM : IsDGRightModule hA ℳ dM) (hN : IsDGLeftModule hA ℳN dN)
    (hM' : IsDGRightModule hA ℳ' dM') (hN' : IsDGLeftModule hA ℳN' dN')
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (hf : ∀ (a : A) m, f (op a • m) = op a • f m)
    (hg : ∀ (a : A) n, g (a • n) = a • g n)
    (hf₀ : LinearMap.IsHomogeneous f ℳ ℳ' 0)
    (hfd : dM' ∘ₗ f = f ∘ₗ dM) (hgd : dN' ∘ₗ g = g ∘ₗ dN) :
    differential hM' hN' ∘ₗ map f g hf hg = map f g hf hg ∘ₗ differential hM hN := by
  apply hom_ext
  intro m n
  have key :
      ((differential hM' hN' ∘ₗ map f g hf hg) ∘ₗ (mk R A).flip n :
        M →ₗ[R] BalancedTensorProduct R A M' N') =
      (map f g hf hg ∘ₗ differential hM hN) ∘ₗ (mk R A).flip n := by
    apply (InternalGrading.ofDecomposition ℳ).linearMap_ext
    intro q x hx
    rw [InternalGrading.ofDecomposition_piece] at hx
    have hfx : f x ∈ ℳ' q := by simpa only [add_zero] using hf₀.map_mem hx
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, mk_apply, map_tmul]
    rw [differential_tmul_of_mem hM' hN' hfx,
      differential_tmul_of_mem hM hN hx, map_add, map_smul, map_tmul, map_tmul]
    simp only [← LinearMap.comp_apply, hfd, hgd]
  simpa only [LinearMap.comp_apply, LinearMap.flip_apply, mk_apply] using LinearMap.congr_fun key m

end Naturality

/-- The left regular-module unit identification commutes with the tensor differential. -/
@[simp]
theorem lid_comp_differential (hA : IsDGAlgebra 𝒜 dA) (hN : IsDGLeftModule hA ℳN dN) :
    (lid R A N).toLinearMap ∘ₗ differential hA.isDGRightModule hN =
      dN ∘ₗ (lid R A N).toLinearMap := by
  apply hom_ext
  intro a n
  have key :
      (((lid R A N).toLinearMap ∘ₗ differential hA.isDGRightModule hN) ∘ₗ
        (mk R A).flip n : A →ₗ[R] N) =
      (dN ∘ₗ (lid R A N).toLinearMap) ∘ₗ (mk R A).flip n := by
    apply (InternalGrading.ofDecomposition 𝒜).linearMap_ext
    intro p x hx
    rw [InternalGrading.ofDecomposition_piece] at hx
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, mk_apply, LinearEquiv.coe_coe]
    rw [differential_tmul_of_mem hA.isDGRightModule hN hx, map_add, map_smul,
      lid_tmul, lid_tmul, lid_tmul, hN.leibniz hx n,
      negOnePow_smul_eq_negOnePowCast_smul (R := R), negOnePowCast_eq_intCast]
  simpa only [LinearMap.comp_apply, LinearMap.flip_apply, mk_apply] using LinearMap.congr_fun key a

/-- The right regular-module unit identification commutes with the tensor differential. -/
@[simp]
theorem rid_comp_differential (hA : IsDGAlgebra 𝒜 dA) (hM : IsDGRightModule hA ℳ dM) :
    (rid R A M).toLinearMap ∘ₗ differential hM hA.isDGLeftModule =
      dM ∘ₗ (rid R A M).toLinearMap := by
  apply hom_ext
  intro m a
  have key :
      (((rid R A M).toLinearMap ∘ₗ differential hM hA.isDGLeftModule) ∘ₗ
        (mk R A).flip a : M →ₗ[R] M) =
      (dM ∘ₗ (rid R A M).toLinearMap) ∘ₗ (mk R A).flip a := by
    apply (InternalGrading.ofDecomposition ℳ).linearMap_ext
    intro q x hx
    rw [InternalGrading.ofDecomposition_piece] at hx
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, mk_apply, LinearEquiv.coe_coe]
    rw [differential_tmul_of_mem hM hA.isDGLeftModule hx, map_add, map_smul,
      rid_tmul, rid_tmul, rid_tmul, hM.leibniz hx a,
      negOnePow_smul_eq_negOnePowCast_smul (R := R), negOnePowCast_eq_intCast]
  simpa only [LinearMap.comp_apply, LinearMap.flip_apply, mk_apply] using LinearMap.congr_fun key m

end TauCeti.BalancedTensorProduct
