/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Internal
public import TauCeti.Algebra.Module.GradedModule.Opposite
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Koszul twists as algebra automorphisms

On an internally integer-graded algebra, multiplication of degree-`p` elements by
`(-1)^(n * p)` is an involutive algebra automorphism. Restricting a module action along this
map supplies the signed left action on cohomological shifts of DG bimodules. The construction
bundles `TauCeti.InternalGrading.koszulTwist` using its existing multiplication and unit laws.

On a graded right module, the Koszul twist of parameter `n` intertwines the action through this
automorphism with the original action
(`TauCeti.InternalGrading.koszulTwist_op_koszulTwistAlgEquiv_smul`).
-/

public section

namespace TauCeti.InternalGrading

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]

/-- The algebra automorphism scaling degree `p` by `(-1)^(n * p)`. -/
noncomputable def koszulTwistAlgEquiv (n : ℤ) : A ≃ₐ[R] A :=
  AlgEquiv.ofAlgHom
    (AlgHom.ofLinearMap ((ofDecomposition 𝒜).koszulTwist n)
      (koszulTwist_ofDecomposition_one n) (koszulTwist_ofDecomposition_mul n))
    (AlgHom.ofLinearMap ((ofDecomposition 𝒜).koszulTwist n)
      (koszulTwist_ofDecomposition_one n) (koszulTwist_ofDecomposition_mul n))
    (by ext a; exact (ofDecomposition 𝒜).koszulTwist_koszulTwist n a)
    (by ext a; exact (ofDecomposition 𝒜).koszulTwist_koszulTwist n a)

/-- The algebra automorphism has the existing Koszul twist as its underlying linear map. -/
@[simp]
theorem koszulTwistAlgEquiv_apply (n : ℤ) (a : A) :
    koszulTwistAlgEquiv 𝒜 n a = (ofDecomposition 𝒜).koszulTwist n a := (rfl)

/-- On a homogeneous element the automorphism is multiplication by the Koszul sign. -/
theorem koszulTwistAlgEquiv_apply_of_mem (n : ℤ) {p : ℤ} {a : A} (ha : a ∈ 𝒜 p) :
    koszulTwistAlgEquiv 𝒜 n a = (n * p).negOnePow • a := by
  rw [koszulTwistAlgEquiv_apply, koszulTwist_ofDecomposition_apply_of_mem 𝒜 ha]
  simp only [Units.smul_def, Int.cast_smul_eq_zsmul]

/-- The inverse Koszul automorphism is the same automorphism. -/
@[simp]
theorem koszulTwistAlgEquiv_symm (n : ℤ) :
    (koszulTwistAlgEquiv 𝒜 n).symm = koszulTwistAlgEquiv 𝒜 n := by
  ext a
  rfl

/-- A zero twist is the identity algebra automorphism. -/
@[simp]
theorem koszulTwistAlgEquiv_zero : koszulTwistAlgEquiv 𝒜 0 = AlgEquiv.refl := by
  ext a
  simp [koszulTwistAlgEquiv_apply, koszulTwist_zero]

/-- Koszul algebra automorphisms compose by adding their parameters. -/
@[simp]
theorem koszulTwistAlgEquiv_trans (m n : ℤ) :
    (koszulTwistAlgEquiv 𝒜 m).trans (koszulTwistAlgEquiv 𝒜 n) =
      koszulTwistAlgEquiv 𝒜 (n + m) := by
  ext a
  simpa only [AlgEquiv.trans_apply, koszulTwistAlgEquiv_apply, LinearMap.comp_apply] using
    LinearMap.congr_fun ((ofDecomposition 𝒜).koszulTwist_comp n m) a

section RightModule

open MulOpposite

variable {M : Type*} [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (ofDecomposition 𝒜).opposite.piece ℳ]

/-- On a graded right module, the Koszul twist of parameter `n` intertwines the action through the
Koszul automorphism with the original action: an `a ∈ Aᵉ` passing an `x ∈ Mᵖ` costs the sign
`(-1)^(n e)` recorded by the twist of `a`. -/
theorem koszulTwist_op_koszulTwistAlgEquiv_smul (n : ℤ) (a : A) (x : M) :
    (ofDecomposition ℳ).koszulTwist n (op (koszulTwistAlgEquiv 𝒜 n a) • x) =
      op a • (ofDecomposition ℳ).koszulTwist n x := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a a' ha ha' => simp only [map_add, op_add, add_smul, ha, ha']
  | @homogeneous e a =>
    induction x using DirectSum.Decomposition.inductionOn ℳ with
    | zero => simp
    | add x x' hx hx' => simp only [smul_add, map_add, hx, hx']
    | @homogeneous p x =>
      obtain ⟨a, ha⟩ := a
      obtain ⟨x, hx⟩ := x
      -- Passing `a` costs `(-1)^(n e)`, and the twist of `a • x` costs `(-1)^(n (p + e))`.
      have hsign : (n * e).negOnePow * (n * (p + e)).negOnePow = (n * p).negOnePow := by
        rw [← Int.negOnePow_add, Int.negOnePow_eq_iff]
        exact ⟨n * e, by ring⟩
      rw [koszulTwistAlgEquiv_apply_of_mem 𝒜 n ha, op_smul, smul_assoc, map_zsmul_unit,
        koszulTwist_ofDecomposition_apply_of_mem ℳ (op_smul_mem_of_mem_graded ha hx),
        koszulTwist_ofDecomposition_apply_of_mem ℳ hx]
      simp only [Int.cast_smul_eq_zsmul, ← Units.smul_def, smul_comm (op a), smul_smul, hsign]

end RightModule

end TauCeti.InternalGrading
