/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Tower

/-!
# Restriction of scalars of algebra homomorphisms is functorial

Restricting the scalars of an `S`-algebra homomorphism along `R → S` (`AlgHom.restrictScalars`)
commutes with composition. Mathlib records injectivity of `AlgHom.restrictScalars` and its
interaction with the underlying ring and linear maps, but not this composition law, which is what a
rewrite needs when a composite homomorphism is restricted and then fed to a construction that is
functorial in `R`-algebra homomorphisms.

## Main results

* `AlgHom.restrictScalars_comp`: `(f.comp g).restrictScalars R = (f.restrictScalars R).comp
  (g.restrictScalars R)`.
-/

public section

variable {R S A B C : Type*} [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
  [Semiring C] [Algebra R S] [Algebra S A] [Algebra S B] [Algebra S C] [Algebra R A] [Algebra R B]
  [Algebra R C] [IsScalarTower R S A] [IsScalarTower R S B] [IsScalarTower R S C]

/-- Restricting scalars of a composite algebra homomorphism gives the composite of the restricted
algebra homomorphisms. -/
@[simp]
theorem AlgHom.restrictScalars_comp (f : B →ₐ[S] C) (g : A →ₐ[S] B) :
    (f.comp g).restrictScalars R = (f.restrictScalars R).comp (g.restrictScalars R) :=
  rfl
