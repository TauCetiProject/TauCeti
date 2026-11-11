/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Geometry.Manifold.Instances.OnePoint.VectorField

/-!
# Examples: holomorphic vector fields on the Riemann sphere

The holomorphic vector fields on `OnePoint ℂ` form the kernel of the Cauchy–Riemann operator
`∂bar` on `TS²`. Their real dimension `6` agrees with the value `n χ + 2 c₁ = 1 · 2 + 2 · 2` of the
Riemann–Roch index formula, with `n = 1`, `χ(S²) = 2` and `c₁(TS²)[S²] = 2`, and rules out the
variant `n χ + c₁ = 1 · 2 + 2`, which would predict `4`. These examples only use the kernel
dimension; the vanishing of the cokernel and the value of `c₁` are not formalized here.
-/

open OnePoint

-- The holomorphic vector fields are the fields `(a + b z + c z²) ∂_z`.
example (X : OnePoint ℂ → ℂ) :
    X ∈ holomorphicVectorFields ↔ ∃ p ∈ Polynomial.degreeLT ℂ 3, polynomialVectorField p = X := by
  rw [mem_holomorphicVectorFields, mdifferentiable_tangent_iff]

-- They form a real vector space of dimension `n χ + 2 c₁ = 1 · 2 + 2 · 2`.
example : Module.finrank ℝ holomorphicVectorFields = 1 * 2 + 2 * 2 :=
  finrank_real_holomorphicVectorFields

-- The variant `n χ + c₁ = 1 · 2 + 2` of the formula gives the wrong dimension.
example : Module.finrank ℝ holomorphicVectorFields ≠ 1 * 2 + 2 := by
  rw [finrank_real_holomorphicVectorFields]
  decide
