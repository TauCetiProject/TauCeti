/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.TensorProduct.BaseChange
public import TauCeti.RepresentationTheory.GaloisDescent.Range

/-!
# Galois invariants of a scalar extension

For a finite Galois extension `L/k`, the elements of `L ⊗[k] A` fixed by the scalar-factor
action are precisely the tensors `1 ⊗ a`. This identifies the original algebra inside its
scalar extension, as needed to descend equivariant coordinate-algebra isomorphisms.

The proof uses `GaloisDescent.range_eq_invariants_of_liftBaseChange_surjective`, whose
trace-one argument works in arbitrary characteristic.

## References

* J. S. Milne, *Algebraic Groups* (2017), Appendix A.64.
-/

public section

open scoped TensorProduct

namespace TauCeti.ScalarAut

variable {k L A : Type*} [Field k] [Field L] [Algebra k L]
variable [Ring A] [Algebra k A] [FiniteDimensional k L] [IsGalois k L]

/-- The fixed elements of a scalar extension along a finite Galois extension are exactly
the image of the original algebra. -/
theorem forall_smul_eq_iff (x : L ⊗[k] A) :
    (∀ σ : L ≃ₐ[k] L, σ • x = x) ↔ ∃ a : A, 1 ⊗ₜ[k] a = x := by
  let ρ : Representation k (L ≃ₐ[k] L) (L ⊗[k] A) :=
    { toFun := fun σ ↦ (Algebra.TensorProduct.congr σ (AlgEquiv.refl : A ≃ₐ[k] A)).toLinearMap
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp }
  let f : A →ₗ[k] L ⊗[k] A := Algebra.TensorProduct.includeRight.toLinearMap
  have hrange : LinearMap.range f = ρ.invariants :=
    GaloisDescent.range_eq_invariants_of_liftBaseChange_surjective
      (k := k) (L := L) (ρ := ρ) (f := f)
      (fun σ a y ↦ by
        simpa [ρ, smul_def] using smul_smulₛₗ σ a y)
      (fun σ a ↦ by simp [ρ, f])
      (fun y ↦ ⟨y, by
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul a b =>
            simp only [LinearMap.liftBaseChange_tmul, f, AlgHom.toLinearMap_apply,
              Algebra.TensorProduct.includeRight_apply]
            exact (TensorProduct.smul_tmul' a (1 : L) b).trans (by simp)⟩)
  have hx : (∀ σ : L ≃ₐ[k] L, σ • x = x) ↔ x ∈ ρ.invariants := by
    simp [Representation.mem_invariants, ρ, smul_def]
  rw [hx, ← hrange]
  rfl

end TauCeti.ScalarAut
