/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Base change along a pair of scalar towers

Given compatible scalar towers `R → A₀ → A`, `R → K → A` and `R → B → L`, `R → K → L`, the
universal property of the tensor product defines a canonical `R`-algebra homomorphism
`A₀ ⊗[R] B →ₐ[R] A ⊗[K] L` (`TauCeti.baseChangeOfTower`) sending `a₀ ⊗ b` to
`algebraMap A₀ A a₀ ⊗ algebraMap B L b`. When `A` and `L` are commutative and
`Algebra.IsPushout R K B L`, `Module.Flat R B`, and `FaithfulSMul A₀ A` hold, `baseChangeOfTower`
is injective (`TauCeti.baseChangeOfTower_injective`) via `A ⊗[R] B ≃ₐ[A] A ⊗[K] L`.

This abstracts the integral-to-field semilocal map `𝒪̂_v ⊗[𝒪_v] 𝒪'_v → K̂_v ⊗[K] L` from
`TauCeti/NumberTheory/NumberField/LocalGlobal/Semilocal/Integers.lean` for reuse by Dedekind-domain
adic completions and intrinsic function-field place completions.

## Main definitions and results

* `TauCeti.baseChangeOfTower`, `TauCeti.baseChangeOfTower_tmul`: the canonical `R`-algebra map
  `A₀ ⊗[R] B →ₐ[R] A ⊗[K] L` and its action on pure tensors.
* `TauCeti.baseChangeOfTower_injective`: injectivity under `Algebra.IsPushout R K B L`,
  `Module.Flat R B`, and `FaithfulSMul A₀ A`.
-/

public section

open scoped TensorProduct

namespace TauCeti

section Semiring

variable (R K A₀ A B L : Type*) [CommSemiring R] [CommSemiring K] [Algebra R K]
  [CommSemiring A₀] [Algebra R A₀] [Semiring A] [Algebra R A] [Algebra K A] [Algebra A₀ A]
  [IsScalarTower R K A] [IsScalarTower R A₀ A]
  [CommSemiring B] [Algebra R B] [Semiring L] [Algebra R L] [Algebra K L] [Algebra B L]
  [IsScalarTower R K L] [IsScalarTower R B L]

/-- The canonical `R`-algebra homomorphism `A₀ ⊗[R] B →ₐ[R] A ⊗[K] L` sending `a₀ ⊗ b` to
`algebraMap A₀ A a₀ ⊗ algebraMap B L b` along compatible scalar towers over `R → K`. -/
noncomputable def baseChangeOfTower : A₀ ⊗[R] B →ₐ[R] A ⊗[K] L :=
  Algebra.TensorProduct.lift
    (Algebra.TensorProduct.includeLeft.comp (IsScalarTower.toAlgHom R A₀ A))
    ((Algebra.TensorProduct.includeRight.restrictScalars R).comp (IsScalarTower.toAlgHom R B L))
    fun _ _ ↦ (Commute.one_right _).tmul (Commute.one_left _)

/-- On a pure tensor, `baseChangeOfTower` applies `algebraMap` on each factor. -/
@[simp]
theorem baseChangeOfTower_tmul (a₀ : A₀) (b : B) :
    baseChangeOfTower R K A₀ A B L (a₀ ⊗ₜ[R] b) = algebraMap A₀ A a₀ ⊗ₜ[K] algebraMap B L b :=
  (Algebra.TensorProduct.lift_tmul _ _ _ a₀ b).trans (by simp)

end Semiring

section Pushout

variable (R K A₀ A B L : Type*) [CommSemiring R] [CommSemiring K] [Algebra R K]
  [CommSemiring A₀] [Algebra R A₀] [CommSemiring A] [Algebra R A] [Algebra K A] [Algebra A₀ A]
  [IsScalarTower R K A] [IsScalarTower R A₀ A]
  [CommSemiring B] [Algebra R B] [CommSemiring L] [Algebra R L] [Algebra K L] [Algebra B L]
  [IsScalarTower R K L] [IsScalarTower R B L] [Algebra.IsPushout R K B L]

/-- When `L` is the pushout of `B` along `R → K`, `B` is flat over `R`, and `A₀` embeds faithfully
into `A`, the canonical map `A₀ ⊗[R] B →ₐ[R] A ⊗[K] L` is injective. -/
theorem baseChangeOfTower_injective [Module.Flat R B] [FaithfulSMul A₀ A] :
    Function.Injective (baseChangeOfTower R K A₀ A B L) := by
  let e : A ⊗[R] B ≃ₐ[A] A ⊗[K] L :=
    (Algebra.TensorProduct.cancelBaseChange R K A A B).symm.trans
      (Algebra.TensorProduct.congr (.refl : A ≃ₐ[A] A) (Algebra.IsPushout.equiv R K B L))
  have hcomp : baseChangeOfTower R K A₀ A B L =
      (e.toAlgHom.restrictScalars R).comp
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A₀ A) (AlgHom.id R B)) :=
    Algebra.TensorProduct.ext' fun _ _ ↦ by simp [e, Algebra.IsPushout.equiv_tmul]
  rw [hcomp, AlgHom.coe_comp]
  refine e.injective.comp ?_
  rw [← AlgHom.coe_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
    AlgHom.toLinearMap_id, TensorProduct.AlgebraTensorModule.map_eq, ← LinearMap.rTensor_def]
  exact Module.Flat.rTensor_preserves_injective_linearMap _ (FaithfulSMul.algebraMap_injective A₀ A)

end Pushout

end TauCeti
