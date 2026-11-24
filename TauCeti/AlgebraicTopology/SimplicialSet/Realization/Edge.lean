/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.AlgebraicTopology.SimplicialSet.Realization.PiZero
public import TauCeti.Geometry.Convex.ConvexSpace.ContractibleSpaceStdSimplex

/-!
# Edge paths in geometric realizations

An edge `e : X.Edge x₀ x₁` of a simplicial set `X` (a `1`-simplex with faces `x₀` and `x₁`)
traces a path `e.toTopPath` in the geometric realization `|X|` from the point `SSet.toTopPoint x₀`
of its source to the point of its target: at time `t` it is the point of `e` with barycentric
coordinates `(1 - t, t)`.

These paths satisfy the relations of the homotopy category of `X` up to homotopy rel endpoints:

* the degenerate edge at a vertex traces the constant path (`SSet.Edge.toTopPath_id`);
* a `2`-simplex with faces `e₀₁`, `e₁₂` and `e₀₂` makes `e₀₁` followed by `e₁₂` homotopic to `e₀₂`
  (`SSet.Edge.CompStruct.toTopPath_trans_homotopic`), the homotopy taking place in the realized
  `2`-simplex, which is simply connected;
* the realization of a map of simplicial sets carries the path of an edge to the path of its image
  (`SSet.Edge.map_toTopPath`).

For the nerve of a category these are the edge paths of its classifying space.

## References

* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Math. 341 (1973), §1, p. 89.
* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Section I.2.
-/

public section

open CategoryTheory Simplicial Convexity unitInterval

universe u

namespace SSet

variable {X Y : SSet.{u}}

namespace Edge

variable {x₀ x₁ x₂ : X _⦋0⦌}

/-- The point of an edge at a vertex of `Δ¹` is the point of the corresponding face. -/
private lemma toTopObjMk_edge_single (e : X.Edge x₀ x₁) (i : Fin 2) :
    toTopObjMk e.edge (.single i) = toTopPoint (X.δ (1 - i) e.edge) := by
  rw [toTopPoint_eq_toTopObjMk _ (.single 0), toTopObjMk_δ, StdSimplex.map_single]
  congr 2
  fin_cases i <;> rfl

/-- The path in the geometric realization `|X|` traced by an edge `e` of `X`: the path
`TauCeti.TopCat.path₁` of the singular `1`-simplex of `|X|` given by `e`, so that at time `t` it is
the point of `e` with barycentric coordinates `(1 - t, t)`. -/
noncomputable def toTopPath (e : X.Edge x₀ x₁) : _root_.Path (toTopPoint x₀) (toTopPoint x₁) :=
  (TauCeti.TopCat.path₁ ((sSetTopAdj.unit.app X).app _ e.edge)).cast
    (by rw [TauCeti.TopCat.source₁, ← toTopObjMk_def, toTopObjMk_edge_single, sub_zero, e.src_eq])
    (by rw [TauCeti.TopCat.target₁, ← toTopObjMk_def, toTopObjMk_edge_single, sub_self, e.tgt_eq])

@[simp]
lemma toTopPath_apply (e : X.Edge x₀ x₁) (t : I) :
    e.toTopPath t = toTopObjMk e.edge (StdSimplex.homeomorphI.symm t) := by
  rw [toTopPath, _root_.Path.cast_coe, TauCeti.TopCat.path₁_apply, toTopObjMk_def]

/-- Edges with the same underlying `1`-simplex trace pointwise equal paths, even when their
endpoints are given as different (though necessarily equal) vertices. -/
lemma toTopPath_apply_eq_of_edge_eq {y₀ y₁ : X _⦋0⦌} {e : X.Edge x₀ x₁} {e' : X.Edge y₀ y₁}
    (h : e.edge = e'.edge) (t : I) : e.toTopPath t = e'.toTopPath t := by
  rw [toTopPath_apply, toTopPath_apply, h]

/-- The degenerate edge at a vertex traces the constant path at its point. -/
@[simp]
lemma toTopPath_id (x : X _⦋0⦌) : (Edge.id x).toTopPath = _root_.Path.refl (toTopPoint x) := by
  ext t
  rw [toTopPath_apply, id_edge, SimplicialObject.σ, toTopObjMk_map,
    ← toTopPoint_eq_toTopObjMk, _root_.Path.refl_apply]

/-- The realization of a map `f` of simplicial sets carries the path of an edge `e` to the path of
the edge `e.map f`, after identifying the images of the endpoints with the points of the image
vertices (`SSet.toTop_map_toTopPoint`). -/
lemma map_toTopPath (e : X.Edge x₀ x₁) (f : X ⟶ Y) :
    e.toTopPath.map (toTop.map f).hom.continuous =
      (e.map f).toTopPath.cast (toTop_map_toTopPoint f x₀) (toTop_map_toTopPoint f x₁) := by
  ext t
  simp [map_edge]

namespace CompStruct

variable {e₀₁ : X.Edge x₀ x₁} {e₁₂ : X.Edge x₁ x₂} {e₀₂ : X.Edge x₀ x₂}

/-- The path of an edge of a `2`-simplex `s` is the path along the corresponding edge of the
topological `2`-simplex, followed by the map to `|X|` given by `s`. -/
private lemma toTopPath_eq_of_δ_eq {e : X.Edge x₀ x₁} {s : X _⦋2⦌} {i : Fin 3}
    (h : X.δ i s = e.edge) (t : I) :
    e.toTopPath t = toTopObjMk s (StdSimplex.edgePath i.succAbove t) := by
  rw [toTopPath_apply, ← h, toTopObjMk_δ, StdSimplex.edgePath_apply, SimplexCategory.coe_δ]

/-- A `2`-simplex with faces `e₀₁`, `e₁₂` and `e₀₂` makes the path of `e₀₁` followed by the path
of `e₁₂` homotopic rel endpoints to the path of `e₀₂`. -/
theorem toTopPath_trans_homotopic (h : CompStruct e₀₁ e₁₂ e₀₂) :
    (e₀₁.toTopPath.trans e₁₂.toTopPath).Homotopic e₀₂.toTopPath := by
  -- The three paths are images of the paths along the edges of the topological `2`-simplex,
  -- which is simply connected, under the continuous map `g` given by the `2`-simplex `h.simplex`.
  let g : C(StdSimplex ℝ (Fin 3), |X|) := ⟨toTopObjMk h.simplex, continuous_toTopObjMk _⟩
  -- The paths along the edges, with their endpoints `Fin.succAbove i j` on numerals evaluated
  -- by computation, so that they compose.
  let p₀ : _root_.Path (StdSimplex.single (R := ℝ) (1 : Fin 3)) (.single 2) :=
    (StdSimplex.edgePath (Fin.succAbove 0)).cast rfl rfl
  let p₁ : _root_.Path (StdSimplex.single (R := ℝ) (0 : Fin 3)) (.single 2) :=
    (StdSimplex.edgePath (Fin.succAbove 1)).cast rfl rfl
  let p₂ : _root_.Path (StdSimplex.single (R := ℝ) (0 : Fin 3)) (.single 1) :=
    (StdSimplex.edgePath (Fin.succAbove 2)).cast rfl rfl
  refine ⟨ContinuousMap.HomotopyRel.cast
    ((SimplyConnectedSpace.paths_homotopic (p₂.trans p₀) p₁).map g).some ?_ ?_⟩
  · ext t
    simp only [_root_.Path.coe_toContinuousMap, _root_.Path.map_coe, Function.comp_apply,
      _root_.Path.trans_apply, p₀, p₂]
    split_ifs
    · exact (toTopPath_eq_of_δ_eq h.d₂ _).symm
    · exact (toTopPath_eq_of_δ_eq h.d₀ _).symm
  · ext t
    exact (toTopPath_eq_of_δ_eq h.d₁ t).symm

end CompStruct

end Edge

end SSet
