/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import TauCeti.LinearAlgebra.Matrix.Realify
import TauCeti.Topology.Algebra.Matrix.Realify

/-!
# The exponential of a realified matrix

Realification `Matrix.realify`, `X + i Y ↦ [[X, -Y], [Y, X]]`, is a continuous `ℝ`-algebra
homomorphism from `𝕜`-matrices to real matrices, for `𝕜 = ℝ` or `ℂ`. So it commutes with the
exponential: `exp X.realify = (exp X).realify` (`Matrix.exp_realify`). This identifies the
one-parameter subgroups of the realified general linear group with the realified one-parameter
subgroups of `GL n 𝕜`.
-/

public section

open NormedSpace

namespace Matrix

open scoped Matrix.Norms.Operator

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- **Realification commutes with the exponential.** -/
theorem exp_realify (X : Matrix n n 𝕜) : exp X.realify = (exp X).realify := by
  -- `NormedSpace.map_exp` is stated for normed `ℚ`-algebras; the operator norms give normed
  -- `ℝ`-algebras, whose scalars this restricts.
  let +nondep : NormedAlgebra ℚ (Matrix n n 𝕜) := .restrictScalars ℚ ℝ _
  have hc : Continuous (realifyAlgHom n 𝕜) := by
    rw [show ⇑(realifyAlgHom n 𝕜) = realify from funext realifyAlgHom_apply]
    exact isClosedEmbedding_realify.continuous
  have h := (NormedSpace.map_exp (realifyAlgHom n 𝕜) hc X).symm
  rwa [realifyAlgHom_apply, realifyAlgHom_apply] at h

end Matrix
