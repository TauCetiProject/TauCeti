/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Covering.Countable
public import TauCeti.AlgebraicTopology.UniversalCover.Compact
public import TauCeti.Geometry.Manifold.Instances.UniversalCover
public import TauCeti.Geometry.Manifold.Topology
public import TauCeti.Topology.SeparatedMap

/-!
# The universal covering manifold

Let `M` be a connected, Hausdorff, second-countable smooth manifold without further assumptions on
its model, and let `x₀ ∈ M`. The based-path universal cover `UniversalCover x₀`, whose points are
the endpoint-fixed homotopy classes of paths starting at `x₀`, carries the charts of `M` pulled
back along the endpoint projection `UniversalCover.proj`, which is a covering map. With this atlas
it is a smooth manifold and the projection is a smooth local diffeomorphism
(`TauCeti.UniversalCover.instIsManifold`, `TauCeti.UniversalCover.isLocalDiffeomorph_proj`).
It is path-connected and simply connected, and the fibre over `x₀` is in bijection with the loop
classes `π₁(M, x₀)` (`TauCeti.UniversalCover.fiberEquivFundamentalGroup`).

This file adds the standing hypotheses of manifold theory upstairs.

* The universal cover of a Hausdorff space is Hausdorff, since a covering map is separated
  (`TauCeti.UniversalCover.instT2Space`).
* The universal cover of a second-countable space is second countable, since it is a connected
  covering space (`TauCeti.UniversalCover.instSecondCountableTopology`). The fibre over `x₀` is a
  discrete subspace of a second-countable space, hence countable, so `π₁(M, x₀)` is countable
  (`TauCeti.UniversalCover.countable_fundamentalGroup`). No countability of the fundamental group is
  assumed: it is a consequence.
* Over a connected base the projection is surjective, since a connected, locally path-connected
  space is path-connected (`TauCeti.UniversalCover.proj_surjective_of_connectedSpace`).
* If the universal cover is compact, the fundamental group is finite: the fibre over `x₀` is closed
  and discrete in a compact space
  (`TauCeti.UniversalCover.finite_fundamentalGroup_of_compactSpace`).

The covering theorem requires the base to be locally path-connected and semilocally simply
connected. A manifold is both, by its convex coordinate balls
(`ModelWithCorners.locallyPathConnectedSpace_of_chartedSpace`,
`ModelWithCorners.semilocallySimplyConnectedSpace`). Since the model with corners cannot be found
by instance search, these two properties appear as instance arguments of the statements about the
concrete carrier `UniversalCover x₀`. The theorem `TauCeti.Manifold.exists_universalCover`
packages everything for a manifold without these two arguments.

## Main results

* `IsCoveringMap.secondCountableTopology`, in the imported file: a connected covering
  space of a second-countable space is second countable.
* `TauCeti.UniversalCover.countable_fundamentalGroup`: a locally path-connected, semilocally simply
  connected, second-countable space has countable fundamental group;
  `ModelWithCorners.countable_fundamentalGroup` is the version for manifolds.
* `TauCeti.Manifold.exists_universalCover`: a connected, Hausdorff, second-countable `C^n`
  manifold has a simply connected, Hausdorff, second-countable `C^n` manifold covering it by a
  surjective `C^n` local diffeomorphism, whose fibre over the basepoint is in bijection with the
  fundamental group, and which is compact only if the fundamental group is finite.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Proposition 4.40 and Corollary 4.43.
* Allen Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.3.
-/

public section

open Topology

universe u

namespace TauCeti.UniversalCover

section Topology

variable {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X] (x₀ : X)

/-- The universal cover of a Hausdorff space is Hausdorff. -/
instance instT2Space [T2Space X] : T2Space (UniversalCover x₀) :=
  (isCoveringMap x₀).t2Space

/-- The universal cover of a second-countable space is second countable. -/
instance instSecondCountableTopology [SecondCountableTopology X] :
    SecondCountableTopology (UniversalCover x₀) :=
  (isCoveringMap x₀).secondCountableTopology

/-- The fibre of the universal cover over the basepoint of a second-countable space is
countable. -/
theorem countable_fiber [SecondCountableTopology X] :
    Countable ((proj : UniversalCover x₀ → X) ⁻¹' {x₀}) :=
  (isCoveringMap x₀).countable_fiber x₀

/-- A locally path-connected, semilocally simply connected, second-countable space has countable
fundamental group. -/
theorem countable_fundamentalGroup [SecondCountableTopology X] :
    Countable (FundamentalGroup X x₀) :=
  have := countable_fiber x₀
  Countable.of_equiv _ (fiberEquivFundamentalGroup x₀)

omit [SemilocallySimplyConnectedSpace X] in
/-- The projection of the universal cover of a connected, locally path-connected space is
surjective. -/
theorem proj_surjective_of_connectedSpace [ConnectedSpace X] :
    Function.Surjective (proj : UniversalCover x₀ → X) :=
  have := pathConnectedSpace_iff_connectedSpace.mpr ‹ConnectedSpace X›
  proj_surjective

end Topology

end TauCeti.UniversalCover

section Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

include I in
/-- A second-countable manifold has countable fundamental group. -/
theorem ModelWithCorners.countable_fundamentalGroup [SecondCountableTopology M] (x₀ : M) :
    Countable (FundamentalGroup M x₀) :=
  have := I.locallyPathConnectedSpace_of_chartedSpace M
  have := I.semilocallySimplyConnectedSpace M
  TauCeti.UniversalCover.countable_fundamentalGroup x₀

/-- **The universal covering manifold.** Let `M` be a connected, Hausdorff, second-countable
`C^n` manifold and `x₀ ∈ M`. There is a simply connected, Hausdorff, second-countable `C^n`
manifold `Y` over the same model and a surjective covering map `p : Y → M` which is a `C^n` local
diffeomorphism, whose fibre over `x₀` is in bijection with the homotopy classes of loops at `x₀`,
and such that if `Y` is compact then the fundamental group of `M` is finite. The based-path
universal cover `TauCeti.UniversalCover x₀`, with the atlas pulled back along its projection, is
such a manifold. -/
theorem TauCeti.Manifold.exists_universalCover {n : WithTop ℕ∞} [IsManifold I n M] [T2Space M]
    [SecondCountableTopology M] [ConnectedSpace M] (x₀ : M) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace H Y) (p : Y → M),
      IsManifold I n Y ∧ IsCoveringMap p ∧ Function.Surjective p ∧
        IsLocalDiffeomorph I I n p ∧ T2Space Y ∧ SecondCountableTopology Y ∧
          SimplyConnectedSpace Y ∧ Nonempty (p ⁻¹' {x₀} ≃ FundamentalGroup M x₀) ∧
            (CompactSpace Y → Finite (FundamentalGroup M x₀)) := by
  have := I.locallyPathConnectedSpace_of_chartedSpace M
  have := I.semilocallySimplyConnectedSpace M
  exact ⟨TauCeti.UniversalCover x₀, inferInstance, inferInstance, TauCeti.UniversalCover.proj,
    inferInstance, TauCeti.UniversalCover.isCoveringMap x₀,
    TauCeti.UniversalCover.proj_surjective_of_connectedSpace x₀,
    TauCeti.UniversalCover.isLocalDiffeomorph_proj x₀, inferInstance, inferInstance,
    inferInstance, ⟨TauCeti.UniversalCover.fiberEquivFundamentalGroup x₀⟩,
    fun _ ↦ TauCeti.UniversalCover.finite_fundamentalGroup_of_compactSpace x₀⟩

end Manifold
