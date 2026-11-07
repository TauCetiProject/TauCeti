/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Operator-norm bounds for continuous multilinear maps on products

A continuous multilinear map `D` on `E × F` in `j + l` variables, evaluated on `j` directions
`(u i, 0)` in `E` followed by `l` directions `(0, w i)` in `F`, is bounded by
`‖D‖ * ((∏ i, ‖u i‖) * ∏ i, ‖w i‖)`. This is the form in which mixed derivatives in two groups
of variables are estimated by a full Fréchet derivative.

## Main declarations

* `ContinuousMultilinearMap.norm_apply_append_prod_le`: the operator-norm bound on
  `Fin.append (fun i ↦ (u i, 0)) (fun i ↦ (0, w i))`.
-/

public section

namespace ContinuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F G : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G]
  [NormedSpace 𝕜 G]

/-- The operator-norm bound for a multilinear map on `E × F` evaluated on `j` directions in `E`
followed by `l` directions in `F`. -/
theorem norm_apply_append_prod_le {j l : ℕ} (D : (E × F) [×(j + l)]→L[𝕜] G) (u : Fin j → E)
    (w : Fin l → F) :
    ‖D (Fin.append (fun i => (u i, 0)) (fun i => (0, w i)))‖ ≤
      ‖D‖ * ((∏ i, ‖u i‖) * ∏ i, ‖w i‖) := by
  refine (D.le_opNorm _).trans_eq ?_
  simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right, Prod.norm_mk, norm_zero,
    norm_nonneg, max_eq_left, max_eq_right]

end ContinuousMultilinearMap
