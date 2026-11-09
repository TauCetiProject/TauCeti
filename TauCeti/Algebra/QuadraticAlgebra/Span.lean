/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Spanning families of a quadratic algebra

A family of elements of a quadratic algebra over a nontrivial commutative semiring that spans it
cannot have all imaginary coordinates vanishing.
-/

public section

namespace QuadraticAlgebra

/-- A family of elements of a quadratic algebra over a nontrivial commutative semiring whose span
is everything has an element with nonvanishing imaginary coordinate. -/
theorem exists_im_ne_zero_of_span_range_eq_top {R ι : Type*} [CommSemiring R] [Nontrivial R]
    {c d : R} (a : ι → QuadraticAlgebra R c d)
    (hspan : Submodule.span R (Set.range a) = ⊤) : ∃ i, (a i).im ≠ 0 := by
  by_contra! hzero
  have h0 : imₗ c d = (0 : QuadraticAlgebra R c d →ₗ[R] R) :=
    LinearMap.ext_on_range hspan hzero
  simpa using congrArg (fun f : QuadraticAlgebra R c d →ₗ[R] R ↦ f omega) h0

end QuadraticAlgebra
