/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Smooth inclusion of self-adjoint elements

The inclusion of the self-adjoint elements into a normed star module over a field with trivial
star is smooth at every order. This lets smooth ambient maps restrict to the self-adjoint
space, for example when constructing exponential coordinates on Hermitian matrices.
-/

public section

open scoped ContDiff

/-- The inclusion of the self-adjoint elements into a normed star module is smooth at every
order over a scalar field with trivial star. -/
theorem selfAdjoint.contDiff_subtype_val (𝕜 : Type*) {A : Type*}
    [NontriviallyNormedField 𝕜] [StarRing 𝕜] [TrivialStar 𝕜]
    [NormedAddCommGroup A] [StarAddMonoid A] [NormedSpace 𝕜 A] [StarModule 𝕜 A]
    {k : ℕ∞ω} : ContDiff 𝕜 k (Subtype.val : selfAdjoint A → A) :=
  -- The subgroup and submodule have the same carrier and induced normed structure.
  (selfAdjoint.submodule 𝕜 A).subtypeL.contDiff
