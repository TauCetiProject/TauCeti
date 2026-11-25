/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

/-!
# Orthogonal automorphisms of a norm form

When a real quadratic form `Q` is the negative of the square of a norm, `Q v = -‖v‖²` (the sign
convention of the Clifford algebras of Euclidean spaces), every element of the orthogonal group of
`Q` preserves the norm (`TauCeti.QuadraticMap.norm_map_of_mem_orthogonalGroup`).
-/

public section

namespace TauCeti.QuadraticMap

variable {V : Type*} [SeminormedAddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}

/-- An isometry of a quadratic form `Q` with `Q v = -‖v‖²` preserves the norm. -/
theorem norm_map_of_mem_orthogonalGroup (hQ : ∀ v, Q v = -‖v‖ ^ 2) {f : V ≃ₗ[ℝ] V}
    (hf : f ∈ orthogonalGroup Q) (v : V) : ‖f v‖ = ‖v‖ := by
  have h := map_app_of_mem_orthogonalGroup hf v
  rw [hQ, hQ, neg_inj] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

end TauCeti.QuadraticMap
