/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Tangent.Plane
public import TauCeti.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Calculus.Rademacher
import TauCeti.Geometry.Euclidean.Volume.Density

/-!
# Approximate tangent planes of graphs in every codimension

Let `E` and `F` be finite-dimensional real inner product spaces and `φ : E → F`, with graph
parametrization `G(x) = (x, φ x)` into the `L²` product `WithLp 2 (E × F)`. At every point `x`
where `φ` is differentiable, the approximate tangent `(dim E)`-plane of the graph `G(E)` at `G(x)`
exists, is unique, and is the graph `{(v, Dφ(x) v)}` of the derivative
(`HasFDerivAt.approximateTangentPlane_range_graph_eq`); the same holds for the graph over any
neighbourhood of `x`, and, for differentiability within a set `s`, over `s` at points of Lebesgue
density one of `s`. Hence for a Lipschitz `φ` this holds at almost every point, by Rademacher's
theorem (`LipschitzWith.ae_approximateTangentPlane_range_graph_eq`), and for a differentiable `φ`,
for instance a `C¹` one, at every point
(`DifferentiableAt.approximateTangentPlane_range_graph_eq`).

The graph parametrization is `1`-antilipschitz (`TauCeti.antilipschitzWith_graph`) and its
derivative is the injective linear graph `ContinuousLinearMap.graphL`, so this is
`HasFDerivWithinAt.approximateTangentPlane_image_eq_range`. For `F = ℝ` and the normal graph
`x ↦ (φ x, x)` the corresponding statements are in
`TauCeti.Geometry.MeasureTheory.Rectifiable.Graph.Basic`.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (approximate tangent planes).
-/

public section

open Filter Metric MeasureTheory Set Module TauCeti
open scoped Topology ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] {φ : E → F} {A : E →L[ℝ] F}
  {s : Set E} {x : E}
  {Q : Submodule ℝ (WithLp 2 (E × F))}

namespace HasFDerivWithinAt

variable (hφ : HasFDerivWithinAt φ A s x) (hx : x ∈ s)
  (hdens : Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall (0 : E) r))
    (𝓝[>] 0) (𝓝 1))
include hφ hx hdens

/-- **Uniqueness of the approximate tangent plane of a graph.** If `φ` is differentiable within
`s` at a point `x ∈ s` of Lebesgue density one of `s`, the only approximate tangent `(dim E)`-plane
of the graph of `φ` over `s` at `(x, φ x)` is the graph of the derivative. -/
theorem isApproximateTangentPlane_graph_image_iff :
    IsApproximateTangentPlane (finrank ℝ E) ((fun y => WithLp.toLp 2 (y, φ y)) '' s)
        (WithLp.toLp 2 (x, φ x)) Q ↔ Q = LinearMap.range A.graphL.toLinearMap :=
  hφ.graph.isApproximateTangentPlane_image_iff A.injective_graphL
    ((antilipschitzWith_graph φ).domRestrict s) hx hdens

/-- **The approximate tangent plane of a graph** over `s`, at a point `x ∈ s` of density one where
`φ` is differentiable within `s`, is the graph of the derivative. -/
theorem approximateTangentPlane_graph_image_eq :
    approximateTangentPlane (finrank ℝ E) ((fun y => WithLp.toLp 2 (y, φ y)) '' s)
        (WithLp.toLp 2 (x, φ x)) = LinearMap.range A.graphL.toLinearMap :=
  hφ.graph.approximateTangentPlane_image_eq_range A.injective_graphL
    ((antilipschitzWith_graph φ).domRestrict s) hx hdens

end HasFDerivWithinAt

namespace HasFDerivAt

variable (hφ : HasFDerivAt φ A x)
include hφ

/-- Over a neighbourhood `s` of a point of differentiability `x`, the only approximate tangent
`(dim E)`-plane of the graph of `φ` at `(x, φ x)` is the graph of the derivative. -/
theorem isApproximateTangentPlane_graph_image_iff (hs : s ∈ 𝓝 x) :
    IsApproximateTangentPlane (finrank ℝ E) ((fun y => WithLp.toLp 2 (y, φ y)) '' s)
        (WithLp.toLp 2 (x, φ x)) Q ↔ Q = LinearMap.range A.graphL.toLinearMap :=
  hφ.hasFDerivWithinAt.isApproximateTangentPlane_graph_image_iff (mem_of_mem_nhds hs)
    (tendsto_volume_inter_closedBall_div_of_mem_nhds hs)

/-- The approximate tangent plane of the graph of `φ` over a neighbourhood `s` of a point of
differentiability `x` is the graph of the derivative. -/
theorem approximateTangentPlane_graph_image_eq (hs : s ∈ 𝓝 x) :
    approximateTangentPlane (finrank ℝ E) ((fun y => WithLp.toLp 2 (y, φ y)) '' s)
        (WithLp.toLp 2 (x, φ x)) = LinearMap.range A.graphL.toLinearMap :=
  hφ.hasFDerivWithinAt.approximateTangentPlane_graph_image_eq (mem_of_mem_nhds hs)
    (tendsto_volume_inter_closedBall_div_of_mem_nhds hs)

/-- **The approximate tangent plane of the whole graph** at a point of differentiability is the
graph of the derivative, and it is the only approximate tangent `(dim E)`-plane there. -/
theorem isApproximateTangentPlane_range_graph_iff :
    IsApproximateTangentPlane (finrank ℝ E) (range fun y => WithLp.toLp 2 (y, φ y))
        (WithLp.toLp 2 (x, φ x)) Q ↔ Q = LinearMap.range A.graphL.toLinearMap := by
  rw [← image_univ]
  exact hφ.isApproximateTangentPlane_graph_image_iff univ_mem

/-- The approximate tangent plane of the whole graph at a point of differentiability is the graph
of the derivative. -/
theorem approximateTangentPlane_range_graph_eq :
    approximateTangentPlane (finrank ℝ E) (range fun y => WithLp.toLp 2 (y, φ y))
        (WithLp.toLp 2 (x, φ x)) = LinearMap.range A.graphL.toLinearMap := by
  rw [← image_univ]
  exact hφ.approximateTangentPlane_graph_image_eq univ_mem

end HasFDerivAt

/-- If `φ` is differentiable at `x`, the approximate tangent plane of the graph at `(x, φ x)` is
the graph of `Dφ(x)`. For a differentiable `φ`, for instance a `C¹` one, this holds at every
point. -/
theorem DifferentiableAt.approximateTangentPlane_range_graph_eq (hφ : DifferentiableAt ℝ φ x) :
    approximateTangentPlane (finrank ℝ E) (range fun y => WithLp.toLp 2 (y, φ y))
        (WithLp.toLp 2 (x, φ x)) = LinearMap.range (fderiv ℝ φ x).graphL.toLinearMap :=
  hφ.hasFDerivAt.approximateTangentPlane_range_graph_eq

/-- **Graphs of Lipschitz maps in every codimension.** For a Lipschitz `φ : E → F`, at almost every
`x` the approximate tangent `(dim E)`-plane of the graph of `φ` at `(x, φ x)` is the graph of
`Dφ(x)`. -/
theorem LipschitzWith.ae_approximateTangentPlane_range_graph_eq {K : NNReal}
    (hφ : LipschitzWith K φ) :
    ∀ᵐ x, approximateTangentPlane (finrank ℝ E) (range fun y => WithLp.toLp 2 (y, φ y))
        (WithLp.toLp 2 (x, φ x)) = LinearMap.range (fderiv ℝ φ x).graphL.toLinearMap := by
  filter_upwards [hφ.ae_differentiableAt] with x hx
  exact hx.approximateTangentPlane_range_graph_eq
