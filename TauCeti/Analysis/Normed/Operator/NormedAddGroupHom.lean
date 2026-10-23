/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Hom
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Comparing linear and additive operator norms

A continuous semilinear map and a bounded additive homomorphism with the same values have the
same operator norm. This comparison lets completion results for bounded additive homomorphisms
apply to continuous linear operators without unfolding either operator-norm definition.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ]

/-- A continuous semilinear map and a bounded additive homomorphism with the same values have
the same operator norm. -/
theorem norm_eq_normedAddGroupHom (f : E →SL[σ] F) (g : NormedAddGroupHom E F)
    (h : ∀ x, f x = g x) : ‖f‖ = ‖g‖ := by
  apply le_antisymm
  · exact f.opNorm_le_bound (norm_nonneg g) fun x => by rw [h]; exact g.le_opNorm x
  · exact g.opNorm_le_bound (norm_nonneg f) fun x => by rw [← h]; exact f.le_opNorm x

end ContinuousLinearMap
