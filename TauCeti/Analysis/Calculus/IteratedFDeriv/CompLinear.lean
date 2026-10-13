/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Iterated derivatives of a composition with a linear map

Precomposing a function with a continuous linear map `g` multiplies the norm of its `i`-th
iterated derivative by at most `‖g‖ ^ i`. This is the norm form of Mathlib's
`ContinuousLinearMap.iteratedFDeriv_comp_right`; for a linear isometry equivalence the norm is
preserved (`LinearIsometryEquiv.norm_iteratedFDeriv_comp_right`).
-/

public section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : WithTop ℕ∞}

/-- Precomposition with a continuous linear map `g` multiplies the norm of the `i`-th iterated
derivative by at most `‖g‖ ^ i`. -/
theorem norm_iteratedFDeriv_comp_right_le (g : G →L[𝕜] E) {f : E → F} (hf : ContDiff 𝕜 n f)
    (x : G) {i : ℕ} (hi : i ≤ n) :
    ‖iteratedFDeriv 𝕜 i (f ∘ g) x‖ ≤ ‖iteratedFDeriv 𝕜 i f (g x)‖ * ‖g‖ ^ i := by
  rw [g.iteratedFDeriv_comp_right hf x hi]
  exact ((iteratedFDeriv 𝕜 i f (g x)).norm_compContinuousLinearMap_le _).trans_eq
    (by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin])

end ContinuousLinearMap
