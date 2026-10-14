/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv

/-!
# The degree-zero Leibniz rule for manifold forms

The exterior derivative of a product of scalar functions is the usual product rule, expressed in
Tau Ceti's fixed-coefficient form carrier. This is the degree-zero specialization of the paired
wedge Leibniz rule in DifferentialGeometry Layer 1.4; higher-degree factors require the alternating
wedge calculation.

The proof uses the existing `mextDeriv_ofFunction` bridge and Mathlib's `mvfderiv_mul` theorem.
-/

public section

noncomputable section

open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The exterior derivative obeys the Leibniz rule on products of differentiable scalar functions.

This is the degree-zero case of the fixed-pairing wedge rule: the two functions are represented by
`RoughForm.ofFunction`, and the result is an equality of their 1-form derivatives at `x`. -/
theorem mextDeriv_ofFunction_mul {f g : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x) :
    mextDeriv (RoughForm.ofFunction I (f * g)) x =
      f x • mextDeriv (RoughForm.ofFunction I g) x +
        g x • mextDeriv (RoughForm.ofFunction I f) x := by
  rw [mextDeriv_ofFunction, mextDeriv_ofFunction, mextDeriv_ofFunction]
  rw [mvfderiv_mul hf hg]
  rfl

end TauCeti
