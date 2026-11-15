/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Composition through the base change adjunction

For an `R`-algebra `A`, an `R`-algebra `S` and an `S`-algebra map `q : S →ₐ[S] T`,
`AlgHom.liftEquiv` identifies `R`-algebra maps `A → S` and `A → T` with `S`-algebra maps out of
`S ⊗[R] A`, compatibly with composition by `q`. So composing with `q` is bijective on `R`-algebra
maps out of `A` if and only if it is bijective on `S`-algebra maps out of `S ⊗[R] A`
(`AlgHom.restrictScalars_comp_bijective_iff`). This reduces lifting problems for algebras over an
arbitrary base `R` to lifting problems over `S` itself.
-/

public section

open scoped TensorProduct

namespace AlgHom

variable (R : Type*) {S T : Type*} (A : Type*) [CommSemiring R] [CommSemiring S] [Semiring T]
  [Semiring A] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] [Algebra R A]

/-- Composing with an `S`-algebra map `q : S →ₐ[S] T` is bijective on `R`-algebra maps out of `A`
if and only if it is bijective on `S`-algebra maps out of the base change `S ⊗[R] A`. -/
theorem restrictScalars_comp_bijective_iff (q : S →ₐ[S] T) :
    Function.Bijective ((q.restrictScalars R).comp : (A →ₐ[R] S) → A →ₐ[R] T) ↔
      Function.Bijective (q.comp : (S ⊗[R] A →ₐ[S] S) → S ⊗[R] A →ₐ[S] T) := by
  have hcomp : ((q.restrictScalars R).comp : (A →ₐ[R] S) → A →ₐ[R] T) =
      (liftEquiv R S A T).symm ∘ q.comp ∘ liftEquiv R S A S := by
    ext f a
    simp
  rw [hcomp, (liftEquiv R S A T).symm.bijective.of_comp_iff',
    Function.Bijective.of_comp_iff _ (liftEquiv R S A S).bijective]

end AlgHom
