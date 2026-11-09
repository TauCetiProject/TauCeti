/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Complex
public import Mathlib.Topology.Perfect

import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Compact open sets and injective holomorphic maps

By the maximum modulus principle, a holomorphic map from a complex manifold to a complex normed
space is constant on every connected compact open subset
(`MDifferentiableOn.apply_eq_of_isPreconnected_isCompact_isOpen`). If the map is injective, such a
subset is therefore a single point, which is open. On a complex manifold without isolated points,
for instance one of positive dimension, this is impossible, so every compact open subset is empty.

In particular a nonempty compact complex manifold of positive dimension admits no injective
holomorphic map to a complex normed space, so it is not a complex submanifold of `ℂᴺ`. Applied to
the affine charts of projective space, this shows that a hyperplane section of a projective
variety meets each of its connected components of positive dimension.

## Main results

* `MDifferentiableOn.eq_empty_of_injOn_of_isCompact_of_isOpen`: a compact open set on which a
  holomorphic map is injective is empty, on a complex manifold without isolated points.
* `MDifferentiable.isEmpty_of_injective`: a compact complex manifold without isolated points with an
  injective holomorphic map to a complex normed space is empty.
-/

public section

open Set
open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [PerfectSpace M]
  {f : M → F}

/-- **Compact open sets carry no injective holomorphic map.** On a complex manifold without
isolated points, a compact open set on which a holomorphic map to a complex normed space is
injective is empty. -/
theorem MDifferentiableOn.eq_empty_of_injOn_of_isCompact_of_isOpen {U : Set M}
    (hf : MDifferentiableOn I 𝓘(ℂ, F) f U) (hinj : InjOn f U) (hc : IsCompact U)
    (ho : IsOpen U) : U = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun a ha ↦ ?_
  have : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  have : CompactSpace U := isCompact_iff_compactSpace.1 hc
  -- The connected component of `a` in `U` is open, compact and connected, so `f` is constant
  -- on it; injectivity makes it the open singleton `{a}`.
  set K := connectedComponentIn U a with hKdef
  have hKo : IsOpen K := ho.connectedComponentIn
  have hKc : IsCompact K := by
    rw [hKdef, connectedComponentIn_eq_image ha]
    exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  have hK : K = {a} := by
    refine eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponentIn ha, fun x hx ↦ hinj
      (connectedComponentIn_subset U a hx) ha ?_⟩
    exact (hf.mono (connectedComponentIn_subset U a)).apply_eq_of_isPreconnected_isCompact_isOpen
      isPreconnected_connectedComponentIn hKc hKo hx (mem_connectedComponentIn ha)
  exact not_isOpen_singleton a (hK ▸ hKo)

/-- **No compact complex submanifolds of a normed space.** A compact complex manifold without
isolated points which admits an injective holomorphic map to a complex normed space is empty. -/
theorem MDifferentiable.isEmpty_of_injective [CompactSpace M] (hf : MDifferentiable I 𝓘(ℂ, F) f)
    (hinj : Function.Injective f) : IsEmpty M :=
  univ_eq_empty_iff.1 <| hf.mdifferentiableOn.eq_empty_of_injOn_of_isCompact_of_isOpen
    hinj.injOn isCompact_univ isOpen_univ
