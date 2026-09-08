/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Covering
public import TauCeti.AlgebraicTopology.UniversalCover.Covering

/-!
# Semilocal simple connectivity is exactly the existence of a universal cover

The universal cover of `X` is built over a base assumed path-connected, locally path-connected,
and semilocally simply connected. Semilocal simple connectivity is not merely convenient there:
by the local-homeomorphism results in
`TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Covering`, it is forced by the existence of
a simply connected cover. This file packages the two directions as an equivalence.

## Main results

* `TauCeti.semilocallySimplyConnectedSpace_iff_exists_isCoveringMap_and_simplyConnectedSpace`: a
  path-connected, locally path-connected space is semilocally simply connected if and only if it
  admits a simply connected covering space. This is the sense in which "`X` has a universal
  cover" and "`X` is semilocally simply connected" are the same condition.

## References

The construction of the universal cover consumed by the forward direction is adapted from Kim
Morrison's mathlib4 [#38292](https://github.com/leanprover-community/mathlib4/pull/38292); it is
credited where it lives, in `TauCeti/AlgebraicTopology/UniversalCover/`. The converse is supplied
by `TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Covering`.
-/

public section

namespace TauCeti

universe u

/-- **A path-connected, locally path-connected space is semilocally simply connected if and only
if it admits a simply connected covering space.**

The forward direction is the universal-cover construction, the reverse direction is
`TauCeti.SemilocallySimplyConnectedSpace.of_isCoveringMap`; surjectivity of the covering map is
automatic here, by `IsCoveringMap.comp_subtypeVal_pathComponent_surjective`, because the base is
path-connected and a simply connected total space is nonempty. -/
theorem semilocallySimplyConnectedSpace_iff_exists_isCoveringMap_and_simplyConnectedSpace
    (X : Type u) [TopologicalSpace X]
    [PathConnectedSpace X] [LocallyPathConnectedSpace X] :
    SemilocallySimplyConnectedSpace X ↔
      ∃ (E : Type u) (_ : TopologicalSpace E) (p : E → X),
        IsCoveringMap p ∧ SimplyConnectedSpace E := by
  refine ⟨fun _ ↦ ?_, ?_⟩
  · obtain ⟨x₀⟩ := PathConnectedSpace.nonempty (X := X)
    exact ⟨UniversalCover x₀, inferInstance, UniversalCover.proj,
      UniversalCover.isCoveringMap x₀, UniversalCover.simplyConnectedSpace x₀⟩
  · rintro ⟨E, _, p, hp, hE⟩
    have : PathConnectedSpace E := (simply_connected_iff_loops_nullhomotopic.mp hE).1
    obtain ⟨e⟩ := PathConnectedSpace.nonempty (X := E)
    refine .of_isCoveringMap hp fun x ↦ ?_
    obtain ⟨e', he'⟩ := hp.comp_subtypeVal_pathComponent_surjective e x
    exact ⟨e', he'⟩

end TauCeti
