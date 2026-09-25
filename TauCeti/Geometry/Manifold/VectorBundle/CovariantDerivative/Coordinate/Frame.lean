/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import TauCeti.Geometry.Manifold.VectorField.CoordinateFrame

/-!
# Symmetry of the Christoffel symbols in a coordinate frame

Torsion-freedom of a covariant derivative on the tangent bundle says that `∇_X Y - ∇_Y X` is the
Lie bracket `[X, Y]`.  Since the vector fields of a coordinate frame commute, a torsion-free
connection satisfies `∇_{∂ᵢ} ∂ⱼ = ∇_{∂ⱼ} ∂ᵢ`.  This is the classical symmetry
`Γᵏᵢⱼ = Γᵏⱼᵢ` of the Christoffel symbols in a chart, and gives the corresponding symmetry of the
model-space Christoffel map.

## Main results

* `TauCeti.Manifold.covariantDerivative_localFrame_comm`: a torsion-free covariant derivative
  differentiates a coordinate frame symmetrically.
* `TauCeti.Manifold.christoffelSymbol_comm` and `TauCeti.Manifold.christoffelMap_comm`: the
  Christoffel symbols and Christoffel map of a torsion-free covariant derivative are symmetric in
  their two lower arguments.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 2, §3, the symmetry of the
  Riemannian connection in a coordinate system.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2nd ed., 2018, Problem 4-6(b).
-/

public section

open Bundle Manifold Module
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type*} {x : M}
  [IsManifold I (minSmoothness 𝕜 2) M]

section Christoffel

variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}

/-- **A torsion-free connection differentiates the coordinate frame symmetrically**: in the chart
at `x₀`, `∇_{∂ᵢ} ∂ⱼ = ∇_{∂ⱼ} ∂ᵢ`. -/
theorem covariantDerivative_localFrame_comm (ht : cov.IsTorsionFree) (b : Basis ι 𝕜 E) (x₀ : M)
    (hx : x ∈ (extChartAt I x₀).source) (i j : ι) :
    cov ((trivializationAt E (TangentSpace I) x₀).localFrame b j) x
        ((trivializationAt E (TangentSpace I) x₀).localFrame b i x) =
      cov ((trivializationAt E (TangentSpace I) x₀).localFrame b i) x
        ((trivializationAt E (TangentSpace I) x₀).localFrame b j x) := by
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simpa using hx
  have hframe (l : ι) :
      MDiffAt (T% ((trivializationAt E (TangentSpace I) x₀).localFrame b l)) x :=
    (contMDiffAt_localFrame_of_mem 1 _ b l hbase).mdifferentiableAt one_ne_zero
  have h := (CovariantDerivative.isTorsionFree_iff cov).mp ht (hframe i) (hframe j)
  rwa [mlieBracket_localFrame_trivializationAt b x₀ hx i j, sub_eq_zero] at h

/-- **The Christoffel symbols of a torsion-free connection are symmetric in their lower indices**:
`Γᵏᵢⱼ = Γᵏⱼᵢ` in the frame of the canonical tangent-bundle trivialization at `x₀`. -/
theorem christoffelSymbol_comm (ht : cov.IsTorsionFree) (b : Basis ι 𝕜 E) (x₀ : M)
    (hx : x ∈ (extChartAt I x₀).source) (i j k : ι) :
    christoffelSymbol I b (trivializationAt E (TangentSpace I) x₀) cov i j k x =
      christoffelSymbol I b (trivializationAt E (TangentSpace I) x₀) cov j i k x := by
  rw [christoffelSymbol_apply, christoffelSymbol_apply,
    covariantDerivative_localFrame_comm ht b x₀ hx i j]

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [Fintype ι]

/-- **The Christoffel map of a torsion-free connection is symmetric.**  Read in the canonical
tangent-bundle trivialization at `x₀`, the model-space Christoffel map of a torsion-free covariant
derivative is a symmetric bilinear map. -/
theorem christoffelMap_comm (ht : cov.IsTorsionFree) (b : Basis ι 𝕜 E) (x₀ : M)
    (hx : x ∈ (extChartAt I x₀).source) (v w : E) :
    christoffelMap b (cov.isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) x₀).baseSet)) x v w =
      christoffelMap b (cov.isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) x₀).baseSet)) x w v := by
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simpa using hx
  -- A continuous bilinear map is determined by its values on a pair of basis vectors.
  have hsymm : christoffelMap b (cov.isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) x₀).baseSet)) x =
      (christoffelMap b (cov.isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) x₀).baseSet)) x).flip := by
    refine ContinuousLinearMap.coe_injective (b.ext fun j ↦ ?_)
    simp only [ContinuousLinearMap.coe_coe]
    refine ContinuousLinearMap.coe_injective (b.ext fun i ↦ ?_)
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.flip_apply]
    rw [christoffelMap_apply_basis b _ hbase i j, christoffelMap_apply_basis b _ hbase j i]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [christoffelSymbol_comm ht b x₀ hx i j k]
  conv_lhs => rw [hsymm]
  rw [ContinuousLinearMap.flip_apply]

end Christoffel

end TauCeti.Manifold
