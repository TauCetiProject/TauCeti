/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex

/-!
# The parametrization of the standard `1`-simplex by the unit interval

Values of Mathlib's homeomorphism `Convexity.StdSimplex.homeomorphI` between the standard
`1`-simplex and the unit interval: it is the last weight (`homeomorphI_apply_eq_mk`), and it sends
the two faces of the standard `1`-simplex, its vertices, to `1` and `0`
(`homeomorphI_map_succAbove_zero`, `homeomorphI_map_succAbove_one`).

Through this parametrization, a pair of points `f 0` and `f 1` of `M` gives the path
`Convexity.StdSimplex.edgePath f` in the standard simplex on `M` from the vertex `f 0` to the
vertex `f 1`, the image of the standard `1`-simplex under `StdSimplex.map f`; for a face map `f`
of the standard `2`-simplex, this is the path along one of its edges.
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
  simp [Subsingleton.elim w (single 0)]

/-- The `1`-st face of the standard `1`-simplex is its first vertex, of parameter `0`. -/
@[simp]
lemma homeomorphI_map_succAbove_one (w : StdSimplex ℝ (Fin 1)) :
    homeomorphI (map (Fin.succAbove (1 : Fin 2)) w) = 0 := by
  simp [Subsingleton.elim w (single 0)]

/-- The path in the standard simplex on `M` from the vertex `f 0` to the vertex `f 1`: the
standard `1`-simplex, parametrized by the unit interval through `homeomorphI`, followed by
`StdSimplex.map f`. For a face map `f = i.succAbove` of the standard `2`-simplex, it runs along
the `i`-th edge. -/
noncomputable def edgePath {M : Type*} (f : Fin 2 → M) :
    Path (single (R := ℝ) (f 0)) (single (f 1)) where
  toFun t := map f (homeomorphI.symm t)
  continuous_toFun := (continuous_map ℝ f).comp homeomorphI.symm.continuous
  source' := by rw [homeomorphI_symm_zero, map_single]
  target' := by rw [homeomorphI_symm_one, map_single]

@[simp]
lemma edgePath_apply {M : Type*} (f : Fin 2 → M) (t : unitInterval) :
    edgePath f t = map f (homeomorphI.symm t) :=
  (rfl)

end Convexity.StdSimplex
