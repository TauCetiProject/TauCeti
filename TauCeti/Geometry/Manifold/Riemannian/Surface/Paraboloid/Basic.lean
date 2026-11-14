/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The Cartesian paraboloid graph

The graph `F(x₀,x₁)=(x₀,x₁,x₀²+x₁²)` is smooth and regular everywhere, including its
vertex. Its differential has induced inner product `⟪u,v⟫+4⟪x,u⟫⟪x,v⟫`.

## References

* M. P. do Carmo, *Differential Geometry of Curves and Surfaces*, Chapter 3.
-/

public noncomputable section

open scoped ContDiff InnerProductSpace

namespace TauCeti.Manifold

local notation "V₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The global Cartesian graph of the paraboloid `z=x²+y²`. -/
def paraboloidGraph (x : V₂) : E₃ :=
  x 0 • EuclideanSpace.basisFun (Fin 3) ℝ 0 +
    x 1 • EuclideanSpace.basisFun (Fin 3) ℝ 1 +
    ‖x‖ ^ 2 • EuclideanSpace.basisFun (Fin 3) ℝ 2

/-- The ambient coordinates of the Cartesian graph, with Euclidean squared radius as height. -/
theorem paraboloidGraph_def (x : V₂) : paraboloidGraph x =
    x 0 • EuclideanSpace.basisFun (Fin 3) ℝ 0 +
      x 1 • EuclideanSpace.basisFun (Fin 3) ℝ 1 +
      ‖x‖ ^ 2 • EuclideanSpace.basisFun (Fin 3) ℝ 2 := by
  rfl

namespace Paraboloid

/-- Ambient Cartesian projection onto the first two coordinates. -/
def cartesianProjection : E₃ →L[ℝ] V₂ :=
  (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0).smulRight (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
    (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 1).smulRight (EuclideanSpace.basisFun (Fin 2) ℝ 1)

/-- Cartesian projection is a genuine left inverse of the graph. -/
@[simp]
theorem cartesianProjection_graph (x : V₂) : cartesianProjection (paraboloidGraph x) = x := by
  ext i
  fin_cases i <;>
    simp [cartesianProjection, paraboloidGraph, EuclideanSpace.basisFun_apply]

/-- The graph does not identify distinct Cartesian points with the same height. -/
theorem injective_graph : Function.Injective paraboloidGraph :=
  Function.LeftInverse.injective cartesianProjection_graph

private def horizontal : V₂ →L[ℝ] E₃ :=
  (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0).smulRight (EuclideanSpace.basisFun (Fin 3) ℝ 0) +
    (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1).smulRight (EuclideanSpace.basisFun (Fin 3) ℝ 1)

private theorem horizontal_apply (x : V₂) :
    horizontal x = x 0 • EuclideanSpace.basisFun (Fin 3) ℝ 0 +
      x 1 • EuclideanSpace.basisFun (Fin 3) ℝ 1 := by
  rfl

/-- The Euclidean squared radius is the sum of the two Cartesian coordinate squares. -/
theorem norm_sq (x : V₂) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply]
  ring

/-- The graph is smooth on the whole Cartesian coordinate plane. -/
theorem contDiff_graph : ContDiff ℝ ∞ paraboloidGraph := by
  have heq : paraboloidGraph = fun x : V₂ ↦ horizontal x +
      ‖x‖ ^ 2 • EuclideanSpace.basisFun (Fin 3) ℝ 2 := by
    funext x
    rfl
  rw [heq]
  exact horizontal.contDiff.add ((contDiff_norm_sq ℝ).smul contDiff_const)

/-- The Cartesian graph is a topological embedding with its actual ambient inverse projection. -/
theorem isEmbedding_graph : Topology.IsEmbedding paraboloidGraph :=
  Function.LeftInverse.isEmbedding cartesianProjection_graph
    cartesianProjection.continuous contDiff_graph.continuous

/-- The genuine differential of the Cartesian graph, including the height derivative. -/
theorem fderiv_graph (x w : V₂) :
    fderiv ℝ paraboloidGraph x w =
      w 0 • EuclideanSpace.basisFun (Fin 3) ℝ 0 +
      w 1 • EuclideanSpace.basisFun (Fin 3) ℝ 1 +
      (2 * inner ℝ x w) • EuclideanSpace.basisFun (Fin 3) ℝ 2 := by
  have h := (horizontal.hasFDerivAt.add
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.smul_const
      (EuclideanSpace.basisFun (Fin 3) ℝ 2))).congr_of_eventuallyEq
        (f₁ := paraboloidGraph) (.of_forall fun _ ↦ rfl)
  rw [h.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
    coe_innerSL_apply, nsmul_eq_mul, Nat.cast_ofNat, horizontal_apply]

/-- The full induced metric, with the nonflat height contribution retained. -/
theorem inner_fderiv_graph (x w z : V₂) :
    inner ℝ (fderiv ℝ paraboloidGraph x w) (fderiv ℝ paraboloidGraph x z) =
      inner ℝ w z + 4 * inner ℝ x w * inner ℝ x z := by
  rw [fderiv_graph, fderiv_graph]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  norm_num
  simp only [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply]
  ring

/-- The Cartesian graph is a regular immersion everywhere, including the vertex. -/
theorem injective_fderiv_graph (x : V₂) : Function.Injective (fderiv ℝ paraboloidGraph x) := by
  intro w z h
  apply sub_eq_zero.mp
  by_contra hne
  have hi := inner_fderiv_graph x (w - z) (w - z)
  rw [map_sub, h, sub_self, inner_zero_left] at hi
  have hp : 0 < inner ℝ (w - z) (w - z) := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hne)
  nlinarith [sq_nonneg (inner ℝ x (w - z))]

/-- The Cartesian vertex maps to the ambient origin. -/
@[simp]
theorem graph_zero : paraboloidGraph 0 = 0 := by
  simp [paraboloidGraph]

/-- The vertex differential is the horizontal plane inclusion. -/
theorem fderiv_graph_zero (w : V₂) : fderiv ℝ paraboloidGraph 0 w =
    w 0 • EuclideanSpace.basisFun (Fin 3) ℝ 0 +
      w 1 • EuclideanSpace.basisFun (Fin 3) ℝ 1 := by
  simp [fderiv_graph]

end Paraboloid
end TauCeti.Manifold
