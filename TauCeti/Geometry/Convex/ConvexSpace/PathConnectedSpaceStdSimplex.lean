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
`1`-simplex and the unit interval: it is the last weight (`homeomorphI_apply_eq_mk`), its inverse
has weights `1 - t` and `t` (`homeomorphI_symm_weights_zero`, `homeomorphI_symm_weights_one`), and
it sends the two faces of the standard `1`-simplex, its vertices, to `1` and `0`
(`homeomorphI_map_succAbove_zero`, `homeomorphI_map_succAbove_one`).

Through this parametrization, a pair of points `f 0` and `f 1` of `M` gives the path
`Convexity.StdSimplex.edgePath f` in the standard simplex on `M` from the vertex `f 0` to the
vertex `f 1`, the image of the standard `1`-simplex under `StdSimplex.map f`; for a face map `f`
of the standard `2`-simplex, this is the path along one of its edges.

More generally, the weight of a vertex of any real standard simplex is a continuous map to the
unit interval (`weightI`), and so is the sum of the weights of the last two vertices of the
standard `2`-simplex (`weightsOneAddTwoI`).
-/

public section

namespace Convexity.StdSimplex

/-- The parameter of a point of the standard `1`-simplex is its last weight. -/
lemma homeomorphI_apply_eq_mk (w : StdSimplex ℝ (Fin 2)) :
    homeomorphI w = ⟨w.weights 1, w.weights_nonneg 1, w.weights_apply_le_one 1⟩ :=
  Subtype.ext (homeomorphI_apply_coe w)

/-- The last weight of the point of the standard `1`-simplex of parameter `t` is `t`. -/
@[simp]
lemma homeomorphI_symm_weights_one (t : unitInterval) : (homeomorphI.symm t).weights 1 = t := by
  rw [← homeomorphI_apply_coe, Homeomorph.apply_symm_apply]

/-- The first weight of the point of the standard `1`-simplex of parameter `t` is `1 - t`. -/
@[simp]
lemma homeomorphI_symm_weights_zero (t : unitInterval) :
    (homeomorphI.symm t).weights 0 = 1 - t := by
  rw [← homeomorphI_symm_weights_one t, ← total_fin_two (homeomorphI.symm t)]
  ring

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

/-- The weight of the vertex `i` of a real standard simplex, as a point of the unit interval. -/
noncomputable def weightI {ι : Type*} (i : ι) : C(StdSimplex ℝ ι, unitInterval) :=
  ⟨fun w ↦ ⟨w.weights i, w.weights_nonneg i, w.weights_apply_le_one i⟩,
    (continuous_weights_apply ℝ i).subtype_mk _⟩

/-- The value of `weightI i` at a point is its `i`-th weight. -/
@[simp]
lemma coe_weightI_apply {ι : Type*} (i : ι) (w : StdSimplex ℝ ι) :
    (weightI i w : ℝ) = w.weights i :=
  (rfl)

/-- The point `weightI i w` of the unit interval is the `i`-th weight of `w`. -/
lemma weightI_apply_eq_mk {ι : Type*} (i : ι) (w : StdSimplex ℝ ι) :
    weightI i w = ⟨w.weights i, w.weights_nonneg i, w.weights_apply_le_one i⟩ :=
  (rfl)

/-- The sum of the weights of the last two vertices of a point of the standard `2`-simplex, as a
point of the unit interval. -/
noncomputable def weightsOneAddTwoI : C(StdSimplex ℝ (Fin 3), unitInterval) :=
  ⟨fun w ↦ ⟨w.weights 1 + w.weights 2,
    add_nonneg (w.weights_nonneg 1) (w.weights_nonneg 2), w.weights_one_add_weights_two_le_one⟩,
    ((continuous_weights_apply ℝ 1).add (continuous_weights_apply ℝ 2)).subtype_mk _⟩

/-- The value of `weightsOneAddTwoI` at a point is the sum of its last two weights. -/
@[simp]
lemma coe_weightsOneAddTwoI_apply (w : StdSimplex ℝ (Fin 3)) :
    (weightsOneAddTwoI w : ℝ) = w.weights 1 + w.weights 2 :=
  (rfl)

/-- The point `weightsOneAddTwoI w` of the unit interval is the sum of the last two weights of
`w`. -/
lemma weightsOneAddTwoI_apply_eq_mk (w : StdSimplex ℝ (Fin 3)) :
    weightsOneAddTwoI w = ⟨w.weights 1 + w.weights 2,
      add_nonneg (w.weights_nonneg 1) (w.weights_nonneg 2), w.weights_one_add_weights_two_le_one⟩ :=
  (rfl)

end Convexity.StdSimplex
