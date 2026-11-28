/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finiteness of the self-adjoint part

The self-adjoint elements of a finite star module over a Noetherian ring with trivial star form a
finite module. Over a field this says they are finite-dimensional, for instance the Hermitian
matrices over `ℝ`.

## Main declarations

* `selfAdjoint.instModuleFinite`: `selfAdjoint A` is a finite module when `A` is.
-/

public section

/-- The self-adjoint elements of a finite star module over a Noetherian ring form a finite module:
they are the submodule `selfAdjoint.submodule R A` of the Noetherian module `A`. -/
instance selfAdjoint.instModuleFinite {R A : Type*} [Ring R] [IsNoetherianRing R] [StarMul R]
    [TrivialStar R] [AddCommGroup A] [StarAddMonoid A] [Module R A] [StarModule R A]
    [Module.Finite R A] : Module.Finite R (selfAdjoint A) :=
  inferInstanceAs (Module.Finite R (selfAdjoint.submodule R A))
