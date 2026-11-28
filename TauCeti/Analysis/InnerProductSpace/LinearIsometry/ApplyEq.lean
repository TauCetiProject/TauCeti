/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Linear isometries sending a vector to a vector of the same norm

Two finite-dimensional real inner product spaces of the same dimension are linearly isometric,
through `OrthonormalBasis.equiv` applied to their standard orthonormal bases. Composing with the
reflection in the hyperplane orthogonal to a difference of two vectors of the same norm
(`Submodule.reflection_sub`), such an isometry can be chosen to send any prescribed vector to any
prescribed vector of the same norm (`TauCeti.exists_linearIsometryEquiv_apply_eq`). For instance,
a two-dimensional real inner product space is identified with `ℂ` by a linear isometry sending a
given vector to the negative real axis.
-/

public section

namespace TauCeti

open Module

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Between finite-dimensional real inner product spaces of the same dimension, there is a linear
isometry equivalence sending a given vector `v` to any given vector `w` of the same norm. -/
theorem exists_linearIsometryEquiv_apply_eq (h : finrank ℝ E = finrank ℝ F) {v : E} {w : F}
    (hvw : ‖v‖ = ‖w‖) : ∃ L : E ≃ₗᵢ[ℝ] F, L v = w := by
  let l : E ≃ₗᵢ[ℝ] F := (stdOrthonormalBasis ℝ E).equiv (stdOrthonormalBasis ℝ F) (finCongr h)
  exact ⟨l.trans (ℝ ∙ (l v - w))ᗮ.reflection,
    Submodule.reflection_sub (by rw [l.norm_map, hvw])⟩

end TauCeti
