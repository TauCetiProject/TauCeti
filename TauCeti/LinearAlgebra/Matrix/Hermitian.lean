/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Real diagonal matrices over `RCLike` fields

A diagonal matrix with real entries is Hermitian after scalar inclusion into any `RCLike`
field. This supplies Hermiticity witnesses for real diagonal perturbations.
-/

public section

namespace Matrix

/-- A real diagonal matrix is Hermitian over any `RCLike` field. -/
@[simp]
theorem isHermitian_diagonal_ofReal {n 𝕜 : Type*} [DecidableEq n] [RCLike 𝕜]
    (d : n → ℝ) : (diagonal fun i ↦ (d i : 𝕜)).IsHermitian := by
  simp [isHermitian_diagonal_iff, isSelfAdjoint_iff]

end Matrix
