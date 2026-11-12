/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Properties
public import TauCeti.Topology.Sober

/-!
# Gluing bijections of irreducible components

A morphism of schemes induces a bijection on irreducible components by closure of image
if it does so after restriction to an open cover of the target. In particular, component
labels for a scalar extension can be constructed on affine charts and glued by this result.
No finiteness, properness, or nodality hypotheses are needed for the gluing step.

The argument uses the unique generic points of irreducible components: they are preserved
and reflected by open immersions, and bijections of these points glue on an open cover.
-/

public section

open CategoryTheory Limits Set

namespace AlgebraicGeometry.Scheme.Hom

universe u v

/-- Bijections on irreducible components, given by closure of image under a scheme morphism,
glue from the inverse images of an arbitrary open cover of the target. -/
theorem bijOn_closure_image_irreducibleComponents_of_openCover
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Y.OpenCover.{v})
    (h : ∀ i, Set.BijOn (fun Z ↦ closure (pullback.snd f (𝒰.f i) '' Z))
      (irreducibleComponents (pullback f (𝒰.f i) : Scheme)) (irreducibleComponents (𝒰.X i))) :
    Set.BijOn (fun Z ↦ closure (f '' Z)) (irreducibleComponents X)
      (irreducibleComponents Y) := by
  apply f.continuous.bijOn_genericPoints_iff.mp
  apply TauCeti.bijOn_genericPoints_of_openCover
    (j := fun i ↦ pullback.fst f (𝒰.f i)) (k := fun i ↦ 𝒰.f i)
    (g := fun i ↦ pullback.snd f (𝒰.f i))
    (fun i ↦ (pullback.fst f (𝒰.f i)).isOpenEmbedding)
    (fun i ↦ (𝒰.f i).isOpenEmbedding)
  · intro y
    exact ⟨𝒰.idx y, 𝒰.covers y⟩
  · intro i
    exact Scheme.Pullback.range_fst f (𝒰.f i)
  · intro i x
    exact congrArg (fun g : pullback f (𝒰.f i) ⟶ Y ↦ g x) pullback.condition
  · intro i
    exact (pullback.snd f (𝒰.f i)).continuous.bijOn_genericPoints_iff.mpr (h i)

end AlgebraicGeometry.Scheme.Hom
