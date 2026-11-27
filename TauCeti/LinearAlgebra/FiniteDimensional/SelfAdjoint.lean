/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite dimension of the self-adjoint part

The self-adjoint elements of a finite-dimensional star module over a division ring with trivial
star form a finite-dimensional module, for instance the Hermitian matrices over `ℝ`.

## Main declarations

* `selfAdjoint.instFiniteDimensional`: `selfAdjoint A` is finite-dimensional when `A` is.
-/

public section

/-- The self-adjoint elements of a finite-dimensional star module form a finite-dimensional
module: they are the submodule `selfAdjoint.submodule R A`. -/
instance selfAdjoint.instFiniteDimensional {R A : Type*} [DivisionRing R] [StarMul R]
    [TrivialStar R] [AddCommGroup A] [StarAddMonoid A] [Module R A] [StarModule R A]
    [FiniteDimensional R A] : FiniteDimensional R (selfAdjoint A) :=
  inferInstanceAs (FiniteDimensional R (selfAdjoint.submodule R A))
