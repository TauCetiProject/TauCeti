/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.Perfect
import Mathlib.Topology.Algebra.Module.PerfectSpace
import TauCeti.Geometry.Manifold.ChartedSpace

/-!
# Basic facts about manifolds and tangent spaces

Every charted space over a `ModelWithCorners` on a nontrivial normed space has no isolated points
(`ModelWithCorners.perfectSpace`), even when the model has boundary or corners and without any
Hausdorff assumption on the manifold.

The tangent space `TangentSpace I x` of a manifold modelled on `I : ModelWithCorners 𝕜 E H` is
linearly equivalent to the model vector space `E`, so its dimension is that of `E`. Tangent spaces
at propositionally equal points are identified by `tangentSpaceCast`.

## Main results

* `ModelWithCorners.perfectSpace`: a manifold modelled on a nontrivial normed space is a perfect
  space.
* `TauCeti.finrank_tangentSpace`: the tangent space at any point has the dimension of the model
  vector space.
* `TauCeti.heq_tangentSpaceCast`: over equal base points, `tangentSpaceCast` is heterogeneously
  the identity.
-/

public section

namespace ModelWithCorners

/-- Every manifold modelled on a nontrivial normed space is a perfect space (has no isolated
points), even if it has boundary or corners or is not Hausdorff. -/
protected theorem perfectSpace {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Nontrivial E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : PerfectSpace M := by
  have : PerfectSpace E := perfectSpace_of_module 𝕜 E
  have hrange : Perfect (Set.range I) :=
    I.range_eq_closure_interior ▸ isOpen_interior.perfect_closure
  have : PerfectSpace H := perfectSpace_iff_forall_not_isolated.2 fun x ↦ by
    have hacc : (nhdsWithin (I x) (I '' {x}ᶜ)).NeBot := by
      rw [Set.image_compl_eq_range_sdiff_image I.injective, Set.image_singleton,
        Set.sdiff_eq_compl_inter, nhdsWithin, ← Filter.inf_principal, ← inf_assoc]
      exact hrange.acc (I x) (Set.mem_range_self x)
    rw [← I.symm_map_nhdsWithin_image]
    exact hacc.map I.symm
  exact ChartedSpace.perfectSpace (H := H)

end ModelWithCorners

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The tangent space at any point of a manifold has the dimension of the model vector space. -/
@[simp]
theorem finrank_tangentSpace (x : M) : Module.finrank 𝕜 (TangentSpace I x) = Module.finrank 𝕜 E :=
  (tangentSpaceCastModel I x).toLinearEquiv.finrank_eq

/-- Over equal base points, `tangentSpaceCast` is heterogeneously the identity. This identifies
tangent vectors over base points that agree only propositionally, for instance when comparing
points of tangent bundles with `Bundle.TotalSpace.ext`. -/
theorem heq_tangentSpaceCast {x y : M} (hxy : x = y) (w : TangentSpace I x) :
    HEq (tangentSpaceCast I x y w) w := by
  subst hxy
  rfl

end TauCeti
