/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Radial maps of a real inner product space

A *radial map* of a real inner product space `E` is a map `x ↦ g(‖x‖²) • x` for a real function
`g`. Where `g` is differentiable at `s = ‖z‖²`, its derivative at `z` is
`v ↦ g(s) v + 2 g'(s) ⟪z, v⟫ z` (`TauCeti.hasFDerivAt_smul_self_of_hasDerivAt_sq_norm`).

Mathlib's diffeomorphism `OpenPartialHomeomorph.univBall c r` of `E` onto the ball of radius `r`
is such a radial map, followed by the translation to `c`. Mathlib proves its inverse smooth on the
ball; `OpenPartialHomeomorph.contDiffOn_univBall_symm_target` states this on the target of
`univBall c r` for every `r`, so that it applies directly to charts built from `univBall c r`.

## Main results

* `TauCeti.hasFDerivAt_smul_self_of_hasDerivAt_sq_norm`: the derivative of a radial map.
* `OpenPartialHomeomorph.contDiffOn_univBall_symm_target`: the inverse of `univBall c r` is
  smooth on its target.
-/

public section

open RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace TauCeti

/-- **The derivative of a radial map.** If `g` is differentiable at `‖z‖²`, the map
`x ↦ g(‖x‖²) • x` has derivative `v ↦ g(‖z‖²) v + 2 g'(‖z‖²) ⟪z, v⟫ z` at `z`. -/
theorem hasFDerivAt_smul_self_of_hasDerivAt_sq_norm {g : ℝ → ℝ} {g' : ℝ} {z : E}
    (hg : HasDerivAt g g' (‖z‖ ^ 2)) :
    HasFDerivAt (fun x : E ↦ g (‖x‖ ^ 2) • x)
      (g (‖z‖ ^ 2) • ContinuousLinearMap.id ℝ E + (2 * g') • (innerSL ℝ z).smulRight z) z := by
  have hn : HasFDerivAt (fun x : E ↦ g (‖x‖ ^ 2)) (g' • (2 • innerSL ℝ z)) z :=
    hg.comp_hasFDerivAt z (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  refine (hn.smul (hasFDerivAt_id z)).congr_fderiv ?_
  ext v
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, id_eq, smul_smul]
  ring_nf

end TauCeti

namespace OpenPartialHomeomorph

/-- The inverse of `univBall c r` is smooth on its target, the ball of radius `r` about `c` if
`r > 0` and all of `E` otherwise. -/
theorem contDiffOn_univBall_symm_target {n : ℕ∞} (c : E) (r : ℝ) :
    ContDiffOn ℝ n (univBall c r).symm (univBall c r).target := by
  by_cases hr : 0 < r
  · rw [univBall_target _ hr]
    exact contDiffOn_univBall_symm
  · -- For `r ≤ 0`, `univBall c r` is the translation by `c`.
    simp only [univBall, hr, ↓reduceDIte]
    exact (contDiff_id.sub contDiff_const).contDiffOn

end OpenPartialHomeomorph
