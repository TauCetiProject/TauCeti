/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.AlgebraicTopology.UniversalCover.Group
public import TauCeti.Geometry.Manifold.Instances.Comap

/-!
# The universal cover of a manifold and of a Lie group

Let `X` be a charted space that is locally path-connected and semilocally simply connected. The
endpoint projection `UniversalCover.proj : UniversalCover x₀ → X` is a covering map, hence a local
homeomorphism, and pulling the charts of `X` back along it makes the universal cover a charted space
over the same model. When `X` is a `C^n` manifold, so is its universal cover, and the projection is
a `C^n` local diffeomorphism. A map into the universal cover is `C^n` exactly when it is continuous
and its composite with the projection is `C^n`.

For a Lie group `G`, the universal cover `UniversalCover (1 : G)` based at the identity is a group
under pointwise multiplication of paths, and its multiplication and inversion lie over those of
`G`. The criterion above therefore makes them `C^n`, so the universal cover is a Lie group, and the
covering homomorphism `UniversalCover.projHom`, whose underlying map is the projection, is a `C^n`
local diffeomorphism. This is the smooth half of the simply connected covering group of a connected
Lie group.

## Main results

* `TauCeti.UniversalCover.instChartedSpace`, `TauCeti.UniversalCover.instIsManifold`: the universal
  cover of a `C^n` manifold is a `C^n` manifold over the same model.
* `TauCeti.UniversalCover.isLocalDiffeomorph_proj`: the projection is a `C^n` local
  diffeomorphism.
* `TauCeti.UniversalCover.contMDiff_iff`: a map into the universal cover is `C^n` if and only if it
  is continuous and its composite with the projection is `C^n`.
* `TauCeti.UniversalCover.instLieGroup`: the universal cover of a Lie group is a Lie group.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 4, "Smooth Covering Maps", and Chapter 7,
  "Covering Groups".
-/

public section

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

namespace TauCeti.UniversalCover

section Manifold

variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X] (x₀ : X)

/-- The universal cover of a charted space carries the charts of the base pulled back along the
covering projection. -/
noncomputable instance instChartedSpace : ChartedSpace H (UniversalCover x₀) :=
  (isCoveringMap x₀).isLocalHomeomorph.chartedSpaceComap

/-- The universal cover of a `C^n` manifold is a `C^n` manifold. -/
instance instIsManifold [IsManifold I n X] : IsManifold I n (UniversalCover x₀) :=
  (isCoveringMap x₀).isLocalHomeomorph.isManifold_chartedSpaceComap

/-- The covering projection of the universal cover is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_proj : IsLocalDiffeomorph I I n (proj : UniversalCover x₀ → X) :=
  (isCoveringMap x₀).isLocalHomeomorph.isLocalDiffeomorph_chartedSpaceComap

/-- The covering projection of the universal cover is `C^n`. -/
theorem contMDiff_proj : ContMDiff I I n (proj : UniversalCover x₀ → X) :=
  (isCoveringMap x₀).isLocalHomeomorph.contMDiff_chartedSpaceComap

variable {x₀} {f : N → UniversalCover x₀} {s : Set N} {z : N}

/-- A map into the universal cover is `C^n` within `s` at `z` if and only if it is continuous
within `s` at `z` and its composite with the projection is `C^n` within `s` at `z`. -/
theorem contMDiffWithinAt_iff :
    ContMDiffWithinAt I' I n f s z ↔ ContinuousWithinAt f s z ∧
      ContMDiffWithinAt I' I n (proj ∘ f) s z :=
  (isCoveringMap x₀).isLocalHomeomorph.contMDiffWithinAt_chartedSpaceComap_iff

/-- A map into the universal cover is `C^n` at `z` if and only if it is continuous at `z` and its
composite with the projection is `C^n` at `z`. -/
theorem contMDiffAt_iff :
    ContMDiffAt I' I n f z ↔ ContinuousAt f z ∧ ContMDiffAt I' I n (proj ∘ f) z :=
  (isCoveringMap x₀).isLocalHomeomorph.contMDiffAt_chartedSpaceComap_iff

/-- A map into the universal cover is `C^n` on `s` if and only if it is continuous on `s` and its
composite with the projection is `C^n` on `s`. -/
theorem contMDiffOn_iff :
    ContMDiffOn I' I n f s ↔ ContinuousOn f s ∧ ContMDiffOn I' I n (proj ∘ f) s :=
  (isCoveringMap x₀).isLocalHomeomorph.contMDiffOn_chartedSpaceComap_iff

/-- A map into the universal cover is `C^n` if and only if it is continuous and its composite with
the projection is `C^n`. -/
theorem contMDiff_iff :
    ContMDiff I' I n f ↔ Continuous f ∧ ContMDiff I' I n (proj ∘ f) :=
  (isCoveringMap x₀).isLocalHomeomorph.contMDiff_chartedSpaceComap_iff

end Manifold

section LieGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace H G]
  [LocallyPathConnectedSpace G] [SemilocallySimplyConnectedSpace G] [LieGroup I n G]

/-- The universal cover of a Lie group, based at the identity, is a Lie group: its multiplication
and inversion are continuous and lie over the `C^n` multiplication and inversion of `G`. -/
instance instLieGroup : LieGroup I n (UniversalCover (1 : G)) where
  contMDiff_mul := contMDiff_iff.2 ⟨continuous_mul,
    ((contMDiff_proj (1 : G)).comp contMDiff_fst).mul ((contMDiff_proj (1 : G)).comp contMDiff_snd)⟩
  contMDiff_inv :=
    contMDiff_iff.2 ⟨continuous_inv, ((contMDiff_proj (1 : G)).comp contMDiff_id).inv⟩

end LieGroup

end TauCeti.UniversalCover
