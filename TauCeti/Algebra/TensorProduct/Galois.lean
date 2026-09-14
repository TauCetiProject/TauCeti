/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.GaloisDescent.Range

/-!
# Galois invariants of a scalar extension

For a finite Galois extension `L/k`, the elements of `L ⊗[k] A` fixed by the scalar-factor
action are precisely the tensors `1 ⊗ a`. This identifies the original vector space inside its
scalar extension, in arbitrary characteristic. Applied to algebras, it allows descent of
equivariant coordinate-algebra isomorphisms.

## References

* J. S. Milne, *Algebraic Groups* (2017), Appendix A.64.
-/

public section

open scoped TensorProduct

namespace TauCeti.ScalarAut

variable {k L A : Type*} [Field k] [Field L] [Algebra k L]
variable [AddCommGroup A] [Module k A] [FiniteDimensional k L] [IsGalois k L]

/-- The fixed elements of a scalar extension along a finite Galois extension are exactly
the image of the original vector space. -/
theorem forall_map_eq_self_iff_exists_one_tmul_eq (x : L ⊗[k] A) :
    (∀ σ : L ≃ₐ[k] L, TensorProduct.map σ.toLinearMap LinearMap.id x = x) ↔
      ∃ a : A, 1 ⊗ₜ[k] a = x := by
  let ρ : Representation k (L ≃ₐ[k] L) (L ⊗[k] A) :=
    { toFun := fun σ ↦ TensorProduct.map σ.toLinearMap LinearMap.id
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp }
  let f : A →ₗ[k] L ⊗[k] A := TensorProduct.mk k L A 1
  have hrange : LinearMap.range f = ρ.invariants :=
    GaloisDescent.range_eq_invariants_of_liftBaseChange_surjective
      (k := k) (L := L) (ρ := ρ) (f := f)
      (fun σ a y ↦ by
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [smul_add, map_add, hx, hy]
        | tmul b c => simp [ρ, TensorProduct.smul_tmul', map_mul])
      (fun σ a ↦ by simp [ρ, f])
      (fun y ↦ ⟨y, by
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul a b =>
            simp only [LinearMap.liftBaseChange_tmul, f, TensorProduct.mk_apply]
            exact (TensorProduct.smul_tmul' a (1 : L) b).trans (by simp)⟩)
  have hx : (∀ σ : L ≃ₐ[k] L, TensorProduct.map σ.toLinearMap LinearMap.id x = x) ↔
      x ∈ ρ.invariants := by
    simp [Representation.mem_invariants, ρ]
  rw [hx, ← hrange]
  rfl

end TauCeti.ScalarAut
