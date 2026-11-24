/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Round balls in a product of normed spaces

The norm of a product `E × F` of seminormed groups is the maximum of the coordinate norms, whose
balls are boxes. Coordinates `z = (q, p)` of `ℂⁿ = ℝⁿ × ℝⁿ`, as in symplectic normal forms, call
instead for the round balls `‖q‖² + ‖p‖² < r²`. This file records that these sets are convex, so
in particular preconnected. That they form a basis of neighbourhoods of the origin is
`TauCeti.exists_setOf_norm_fst_sq_add_norm_snd_sq_lt_subset` in
`TauCeti.Analysis.Normed.Group.Prod`, as it needs no module structure.

## Main results

* `TauCeti.convex_setOf_norm_fst_sq_add_norm_snd_sq_lt`: the set `‖z.1‖² + ‖z.2‖² < c` is
  convex.
-/

public section

namespace TauCeti

open Set

/-- The round ball `‖z.1‖² + ‖z.2‖² < c` of a product of real normed spaces is convex. -/
theorem convex_setOf_norm_fst_sq_add_norm_snd_sq_lt {E F : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [SeminormedAddCommGroup F] [NormedSpace ℝ F] (c : ℝ) :
    Convex ℝ {z : E × F | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < c} := by
  have hE : ConvexOn ℝ univ fun x : E ↦ ‖x‖ ^ 2 :=
    (convexOn_norm convex_univ).pow (fun _ _ ↦ norm_nonneg _) 2
  have hF : ConvexOn ℝ univ fun x : F ↦ ‖x‖ ^ 2 :=
    (convexOn_norm convex_univ).pow (fun _ _ ↦ norm_nonneg _) 2
  simpa using ((hE.comp_linearMap (LinearMap.fst ℝ E F)).add
    (hF.comp_linearMap (LinearMap.snd ℝ E F))).convex_lt c

end TauCeti
