/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Star.Unitary

/-!
# Topological closures of self-adjoint parts

For any star-closed subobject `s` closed under addition and scalar multiplication by a division
semiring with `2 ≠ 0` inside a Hausdorff topological module with continuous addition, continuous
fixed-scalar multiplication, and continuous star, taking self-adjoint parts commutes with
topological closure (`StarMemClass.closure_inter_selfAdjoint`).
-/

public section

namespace StarMemClass

/-- Taking self-adjoint parts commutes with taking the closure of a star-closed subobject closed
under addition and scalar multiplication by a division semiring with `2 ≠ 0`, in a Hausdorff
topological module with continuous addition, continuous fixed-scalar multiplication, and continuous
star. -/
theorem closure_inter_selfAdjoint (𝕜 : Type*) {A S : Type*} [DivisionSemiring 𝕜]
    [NeZero (2 : 𝕜)] [TopologicalSpace A] [T2Space A] [AddCommGroup A] [StarAddMonoid A]
    [Module 𝕜 A] [ContinuousAdd A] [ContinuousConstSMul 𝕜 A] [ContinuousStar A]
    [SetLike S A] [AddMemClass S A] [SMulMemClass S 𝕜 A] [StarMemClass S A] (s : S) :
    closure ((s : Set A) ∩ selfAdjoint A) = closure (s : Set A) ∩ selfAdjoint A := by
  refine subset_antisymm
    (closure_inter_subset.trans
      (Set.inter_subset_inter_right _
        (isClosed_eq continuous_star continuous_id).closure_eq.subset))
    fun x ⟨hx, hxsa⟩ ↦ ?_
  have hre := map_mem_closure (f := fun a : A ↦ (2⁻¹ : 𝕜) • (a + star a)) (by fun_prop) hx
    (t := (s : Set A) ∩ selfAdjoint A) fun a ha ↦ by
      refine ⟨SMulMemClass.smul_mem _ (add_mem ha (star_mem ha)), ?_⟩
      simp only [SetLike.mem_coe, selfAdjoint.mem_iff]
      rw [← Nat.cast_two (R := 𝕜), star_inv_natCast_smul, (IsSelfAdjoint.add_star_self a).star_eq]
  have hx2 : (2⁻¹ : 𝕜) • (x + star x) = x := by
    rw [hxsa.star_eq, ← two_smul 𝕜 x, smul_smul, inv_mul_cancel₀ (NeZero.ne (2 : 𝕜)), one_smul]
  rwa [hx2] at hre

end StarMemClass
