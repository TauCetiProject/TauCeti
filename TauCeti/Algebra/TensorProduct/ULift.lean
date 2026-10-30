/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Scalar extension to a lifted base ring

Extending an `R`-algebra `A` along `R → ULift R` gives the actual lifted algebra `ULift A`.
The equivalence sends `r ⊗ a` to `r.down • a`, lifted to the larger universe. This identifies
scalar extension with transport of the ring and algebra structures, including when `A` is
noncommutative. The lifted scalar action is Mathlib's `ULift.algebra'`.

The construction uses Mathlib's base-change universal property `AlgHom.liftEquiv` and the
bijectivity of the tensor inclusion along a bijective scalar map.
-/

public noncomputable section

universe u v w

open scoped TensorProduct

open Algebra.TensorProduct

namespace TauCeti.Algebra.TensorProduct

variable (R : Type u) [CommSemiring R] (A : Type v) [Semiring A] [Algebra R A]

-- Keep the tensor product's canonical left-scalar action ahead of this fallback.
attribute [local instance 100] ULift.algebra'

/-- Scalar extension to `ULift R` is the lifted algebra, by `r ⊗ a ↦ up (r.down • a)`. -/
def uliftBaseChangeAlgEquiv :
    ULift.{w} R ⊗[R] A ≃ₐ[ULift.{w} R] ULift.{w} A := by
  let f := AlgHom.liftEquiv R (ULift.{w} R) A (ULift.{w} A)
    (ULift.algEquiv.symm : A ≃ₐ[R] ULift.{w} A).toAlgHom
  have h : Function.Bijective (algebraMap R (ULift.{w} R)) := by
    exact ⟨fun x y hxy => by simpa using congrArg ULift.down hxy,
      fun x => ⟨x.down, rfl⟩⟩
  refine AlgEquiv.ofBijective f ?_
  rw [← Function.Bijective.of_comp_iff _ (includeRight_bijective (B := A) h)]
  have hf : f ∘ (includeRight : A →ₐ[R] ULift.{w} R ⊗[R] A) =
      (ULift.algEquiv.symm : A ≃ₐ[R] ULift.{w} A) := by
    funext a
    exact (AlgHom.liftEquiv_tmul _ 1 a).trans (one_smul _ _)
  rw [hf]
  exact (ULift.algEquiv.symm : A ≃ₐ[R] ULift.{w} A).bijective

/-- The scalar-extension equivalence evaluates a pure tensor by the original scalar action. -/
@[simp]
theorem uliftBaseChangeAlgEquiv_tmul (r : ULift.{w} R) (a : A) :
    uliftBaseChangeAlgEquiv R A (r ⊗ₜ[R] a) = ULift.up (r.down • a) := by
  rw [uliftBaseChangeAlgEquiv, AlgEquiv.ofBijective_apply, AlgHom.liftEquiv_tmul]
  rfl

/-- The inverse sends a lifted element to its tensor inclusion. -/
@[simp]
theorem uliftBaseChangeAlgEquiv_symm_up (a : A) :
    (uliftBaseChangeAlgEquiv R A).symm (ULift.up a) = 1 ⊗ₜ[R] a := by
  apply (uliftBaseChangeAlgEquiv R A).injective
  simp

end TauCeti.Algebra.TensorProduct
