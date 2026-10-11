/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.Defs
public import TauCeti.Algebra.Homology.DG.Module.TensorProduct.Complex
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Actions
import TauCeti.Algebra.Ring.NegOnePow

/-!
# Tensor products of DG bimodules

For an `(A, B)` DG bimodule `M` and a `(B, C)` DG bimodule `N`, the ordinary balanced tensor
product `M ⊗_B N` is an `(A, C)` DG bimodule. Its outer actions are
`a (m ⊗ n) = (a m) ⊗ n` and `(m ⊗ n) c = m ⊗ (n c)`.
The total grading and differential are the existing balanced tensor constructions, with
`d(m ⊗ n) = dM(m) ⊗ n + (-1)^|m| m ⊗ dN(n)`.

This file proves the two outer Leibniz rules and assembles the DG bimodule predicate. The
construction is underived and does not require flatness. The outer module structures are
installed locally from `BalancedTensorProduct.leftModule` and `rightModule` so that consumers
can select these actions explicitly without introducing competing global instances.

## References

* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public section

open MulOpposite DirectSum

namespace TauCeti.BalancedTensorProduct

variable {R A B C M N : Type*} [CommRing R] [Ring A] [Ring B] [Ring C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  [AddCommGroup M] [Module R M] [Module A M] [Module Bᵐᵒᵖ M]
  [IsScalarTower R A M] [IsScalarTower R Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module B N] [Module Cᵐᵒᵖ N]
  [IsScalarTower R B N] [IsScalarTower R Cᵐᵒᵖ N] [SMulCommClass B Cᵐᵒᵖ N]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB} {hC : IsDGAlgebra 𝒞 dC}
  {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N}
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul 𝒜 ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]
  [SetLike.GradedSMul ℬ 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒞).opposite.piece 𝒩]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N}

-- Prefer the existing ground-ring module when an outer ring specializes to `R`.
/-- The outer left action on the balanced tensor product, induced by the action on `M`. -/
local instance (priority := 50) : Module A (BalancedTensorProduct R B M N) :=
  leftModule (k := R) (A := B) (M := M) (N := N) A
/-- The outer right action on the balanced tensor product, induced by the action on `N`. -/
local instance (priority := 50) : Module Cᵐᵒᵖ (BalancedTensorProduct R B M N) :=
  rightModule (k := R) (A := B) (M := M) (N := N) Cᵐᵒᵖ
local instance : IsScalarTower R A (BalancedTensorProduct R B M N) :=
  leftIsScalarTower (k := R) (A := B) (M := M) (N := N) A
local instance : IsScalarTower R Cᵐᵒᵖ (BalancedTensorProduct R B M N) :=
  rightIsScalarTower (k := R) (A := B) (M := M) (N := N) Cᵐᵒᵖ
local instance : SMulCommClass A Cᵐᵒᵖ (BalancedTensorProduct R B M N) :=
  outerSMulCommClass (k := R) (A := B) (M := M) (N := N) A Cᵐᵒᵖ

-- The characteristic piece equation transports the graded actions through `ofDecomposition`.
local instance : SetLike.GradedSMul 𝒜 (InternalGrading.ofDecomposition ℳ).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

local instance : SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece
    (InternalGrading.ofDecomposition ℳ).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

local instance : SetLike.GradedSMul ℬ (InternalGrading.ofDecomposition 𝒩).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

local instance : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒞).opposite.piece
    (InternalGrading.ofDecomposition 𝒩).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

local instance : SetLike.GradedSMul 𝒜
    (grading (𝒜 := ℬ) (InternalGrading.ofDecomposition ℳ)
      (InternalGrading.ofDecomposition 𝒩)).piece :=
  gradedSMul_left (InternalGrading.ofDecomposition ℳ)
    (InternalGrading.ofDecomposition 𝒩) A 𝒜

local instance : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒞).opposite.piece
    (grading (𝒜 := ℬ) (InternalGrading.ofDecomposition ℳ)
      (InternalGrading.ofDecomposition 𝒩)).piece :=
  gradedSMul_right (InternalGrading.ofDecomposition ℳ)
    (InternalGrading.ofDecomposition 𝒩) Cᵐᵒᵖ (InternalGrading.ofDecomposition 𝒞).opposite.piece

private theorem differential_smul_tmul_left (hM : IsDGBimodule hA hB ℳ dM)
    (hN : IsDGLeftModule hB 𝒩 dN) {p q : ℤ} {a : A} {m : M}
    (ha : a ∈ 𝒜 p) (hm : m ∈ ℳ q) (n : N) :
    differential hM.isDGRightModule hN (a • tmul R B m n) =
      dA a • tmul R B m n + p.negOnePow •
        (a • differential hM.isDGRightModule hN (tmul R B m n)) := by
  rw [smul_tmul_left, differential_tmul_of_mem hM.isDGRightModule hN
      (SetLike.GradedSMul.smul_mem ha hm), hM.leibniz ha m,
    differential_tmul_of_mem hM.isDGRightModule hN hm]
  simp only [add_tmul, smul_add, smul_tmul_left,
    negOnePow_smul_eq_negOnePowCast_smul (R := R), negOnePowCast_eq_intCast,
    smul_tmul, vadd_eq_add, Int.negOnePow_add, Units.val_mul, Int.cast_mul,
    smul_smul, smul_comm a]
  module

/-- The balanced tensor differential obeys the left outer Leibniz rule. Only the outer
algebra element needs to be homogeneous. -/
theorem differential_smul_left (hM : IsDGBimodule hA hB ℳ dM)
    (hN : IsDGLeftModule hB 𝒩 dN) {p : ℤ} {a : A} (ha : a ∈ 𝒜 p)
    (z : BalancedTensorProduct R B M N) :
    differential hM.isDGRightModule hN (a • z) =
      dA a • z + p.negOnePow • (a • differential hM.isDGRightModule hN z) := by
  induction z using induction_on with
  | ht m n =>
    induction m using Decomposition.inductionOn ℳ with
    | zero => simp
    | add x y hx hy => simp only [add_tmul, smul_add, map_add, hx, hy]; abel
    | @homogeneous q m => exact differential_smul_tmul_left hM hN ha m.2 n
  | ha x y hx hy => simp only [smul_add, map_add, hx, hy]; abel

private theorem differential_smul_tmul_right (hM : IsDGRightModule hB ℳ dM)
    (hN : IsDGBimodule hB hC 𝒩 dN) {p q : ℤ} {m : M} {n : N}
    (hm : m ∈ ℳ p) (hn : n ∈ 𝒩 q) (c : C) :
    differential hM hN.toIsDGLeftModule (op c • tmul R B m n) =
      op c • differential hM hN.toIsDGLeftModule (tmul R B m n) +
        (p + q).negOnePow • (op (dC c) • tmul R B m n) := by
  rw [smul_tmul_right, differential_tmul_of_mem hM hN.toIsDGLeftModule hm,
    hN.leibniz_right hn c,
    differential_tmul_of_mem hM hN.toIsDGLeftModule hm]
  simp only [negOnePow_smul_eq_negOnePowCast_smul (R := R), negOnePowCast_eq_intCast]
  simp only [tmul_add, smul_add, smul_tmul_right, tmul_smul,
    Int.negOnePow_add, Units.val_mul, Int.cast_mul, smul_smul, smul_comm (op c)]
  module

/-- The balanced tensor differential obeys the right outer Leibniz rule. Only the tensor
needs to be homogeneous; the outer right scalar can be arbitrary. -/
theorem differential_smul_right (hM : IsDGRightModule hB ℳ dM)
    (hN : IsDGBimodule hB hC 𝒩 dN) {p : ℤ} {z : BalancedTensorProduct R B M N}
    (hz : z ∈ (grading (𝒜 := ℬ) (InternalGrading.ofDecomposition ℳ)
      (InternalGrading.ofDecomposition 𝒩)).piece p) (c : C) :
    differential hM hN.toIsDGLeftModule (op c • z) =
      op c • differential hM hN.toIsDGLeftModule z +
        p.negOnePow • (op (dC c) • z) := by
  let F : Module.End R (BalancedTensorProduct R B M N) :=
    differential hM hN.toIsDGLeftModule ∘ₗ
      DistribSMul.toLinearMap R _ (op c) -
      DistribSMul.toLinearMap R _ (op c) ∘ₗ differential hM hN.toIsDGLeftModule -
      (((p.negOnePow : ℤ) : R)) • DistribSMul.toLinearMap R _ (op (dC c))
  have hF : (grading (𝒜 := ℬ) (InternalGrading.ofDecomposition ℳ)
      (InternalGrading.ofDecomposition 𝒩)).piece p ≤ LinearMap.ker F := by
    rw [grading_piece_eq_iSup]
    refine iSup_le fun q ↦ Submodule.map₂_le.mpr fun m hm n hn ↦ ?_
    rw [InternalGrading.ofDecomposition_piece] at hm hn
    rw [LinearMap.mem_ker, mk_apply]
    simp only [F, LinearMap.sub_apply, LinearMap.comp_apply, DistribSMul.toLinearMap_apply,
      LinearMap.smul_apply]
    have hdeg : q + (p - q) = p := by omega
    rw [differential_smul_tmul_right hM hN hm hn, hdeg,
      negOnePow_smul_eq_negOnePowCast_smul (R := R), negOnePowCast_eq_intCast]
    abel
  have h := hF hz
  simp only [LinearMap.mem_ker, F, LinearMap.sub_apply, LinearMap.comp_apply,
    DistribSMul.toLinearMap_apply, LinearMap.smul_apply] at h
  rw [negOnePow_smul_eq_negOnePowCast_smul (R := R), negOnePowCast_eq_intCast]
  exact sub_eq_iff_eq_add'.mp (sub_eq_zero.mp h)

/-- The ordinary balanced tensor product of an `(A, B)` DG bimodule and a `(B, C)` DG
bimodule is an `(A, C)` DG bimodule, with the outer actions on its two factors. -/
theorem isDGBimodule_tensorProduct (hM : IsDGBimodule hA hB ℳ dM)
    (hN : IsDGBimodule hB hC 𝒩 dN) :
    IsDGBimodule hA hC
      (grading (𝒜 := ℬ) (InternalGrading.ofDecomposition ℳ)
        (InternalGrading.ofDecomposition 𝒩)).piece
      (differential hM.isDGRightModule hN.toIsDGLeftModule) where
  isHomogeneous := isHomogeneous_differential hM.isDGRightModule hN.toIsDGLeftModule
  sq_zero := differential_sq_zero hM.isDGRightModule hN.toIsDGLeftModule
  leibniz := fun ha z ↦ differential_smul_left hM hN.toIsDGLeftModule ha z
  leibniz_right := fun hz c ↦ differential_smul_right hM.isDGRightModule hN hz c

end TauCeti.BalancedTensorProduct
