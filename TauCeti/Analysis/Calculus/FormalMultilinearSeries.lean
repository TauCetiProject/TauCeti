/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FormalMultilinearSeries

/-!
# Basic properties of formal multilinear series

The `n`-th term of a formal multilinear series, evaluated on the diagonal, is homogeneous of
degree `n`: its value at `c • x` is `c ^ n` times its value at `x`
(`FormalMultilinearSeries.apply_smul`). For a Cartesian product of formal multilinear series
`p.prod q`, the `n`-th term is the product of the `n`-th terms
(`FormalMultilinearSeries.prod_apply`).
-/

public section

section

variable {𝕜 E F G : Type*} [Semiring 𝕜]
  [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousConstSMul 𝕜 E] [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
  [ContinuousAdd F] [ContinuousConstSMul 𝕜 F] [AddCommMonoid G] [Module 𝕜 G]
  [TopologicalSpace G] [ContinuousAdd G] [ContinuousConstSMul 𝕜 G]

/-- The `n`-th term of a product formal multilinear series is the product of the `n`-th terms. -/
@[simp]
theorem FormalMultilinearSeries.prod_apply (p : FormalMultilinearSeries 𝕜 E F)
    (q : FormalMultilinearSeries 𝕜 E G) (n : ℕ) : p.prod q n = (p n).prod (q n) :=
  (rfl)

end

variable {𝕜 E F : Type*} [CommSemiring 𝕜]
  [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousConstSMul 𝕜 E] [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
  [ContinuousAdd F] [ContinuousConstSMul 𝕜 F]

/-- The `n`-th term of a formal multilinear series, evaluated on the diagonal, is homogeneous of
degree `n`. -/
theorem FormalMultilinearSeries.apply_smul (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) (c : 𝕜)
    (x : E) : (p n fun _ ↦ c • x) = c ^ n • p n fun _ ↦ x := by
  simpa using (p n).map_smul_univ (fun _ ↦ c) fun _ ↦ x
