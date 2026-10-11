/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
public import TauCeti.Geometry.Convex.ConvexSpace.Defs

/-!
# The parametrization of the standard `1`-simplex by the unit interval

Values of Mathlib's homeomorphism `Convexity.StdSimplex.homeomorphI` between the standard
`1`-simplex and the unit interval: it is the last weight (`homeomorphI_apply_eq_mk`), and it sends
the two faces of the standard `1`-simplex, its vertices, to `1` and `0`
(`homeomorphI_map_succAbove_zero`, `homeomorphI_map_succAbove_one`).
-/

public section

namespace Convexity.StdSimplex

/-- The parameter of a point of the standard `1`-simplex is its last weight. -/
lemma homeomorphI_apply_eq_mk (w : StdSimplex ℝ (Fin 2)) :
    homeomorphI w = ⟨w.weights 1, w.weights_nonneg 1, w.weights_apply_le_one 1⟩ :=
  Subtype.ext (homeomorphI_apply_coe w)

/-- The `0`-th face of the standard `1`-simplex is its last vertex, of parameter `1`. -/
-- Not a simp lemma: `Fin.succAbove_zero` rewrites the face map first.
lemma homeomorphI_map_succAbove_zero (w : StdSimplex ℝ (Fin 1)) :
    homeomorphI (map (Fin.succAbove (0 : Fin 2)) w) = 1 := by
  refine Subtype.ext ((homeomorphI_apply_coe _).trans ?_)
  have h : (0 : Fin 2).succAbove 0 = 1 := by simp
  rw [← h, weights_map_apply_of_injective Fin.succAbove_right_injective]
  simp

/-- The `1`-st face of the standard `1`-simplex is its first vertex, of parameter `0`. -/
@[simp]
lemma homeomorphI_map_succAbove_one (w : StdSimplex ℝ (Fin 1)) :
    homeomorphI (map (Fin.succAbove (1 : Fin 2)) w) = 0 :=
  Subtype.ext ((homeomorphI_apply_coe _).trans (weights_map_succAbove_self 1 w))

end Convexity.StdSimplex
