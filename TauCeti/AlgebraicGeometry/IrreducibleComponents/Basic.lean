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
exactly when it does so after base change to the charts of an open cover of the target; such a
bijection also restricts along any pullback square over an open immersion. In particular,
component labels for a scalar extension can be constructed on affine charts and glued by this
result. No finiteness, properness, or nodality hypotheses are needed for the gluing step.

The argument uses the unique generic points of irreducible components: they are preserved
and reflected by open immersions, and bijections of these points glue on an open cover.
-/

public section

open CategoryTheory Limits Set

namespace AlgebraicGeometry.Scheme.Hom

universe u v

/-- Bijections on irreducible components, given by closure of image under a scheme morphism,
restrict along a pullback square whose base map is an open immersion. -/
theorem bijOn_closure_image_irreducibleComponents_of_isPullback
    {X Y U V : Scheme.{u}} (f : X ⟶ Y) {j : U ⟶ X} {g : U ⟶ V} {k : V ⟶ Y}
    [IsOpenImmersion k] (hp : IsPullback j g f k)
    (h : BijOn (fun Z ↦ closure (f '' Z)) (irreducibleComponents X)
      (irreducibleComponents Y)) :
    BijOn (fun Z ↦ closure (g '' Z)) (irreducibleComponents U) (irreducibleComponents V) := by
  have : IsOpenImmersion j := MorphismProperty.of_isPullback hp.flip inferInstance
  refine g.continuous.bijOn_genericPoints_iff.mp
    (TauCeti.bijOn_genericPoints_of_isOpenEmbedding j.isOpenEmbedding k.isOpenEmbedding
      (fun x ⟨v, hv⟩ ↦ (exists_preimage_of_isPullback hp x v hv.symm).imp fun _ ↦ And.left)
      (fun x ↦ ?_) (f.continuous.bijOn_genericPoints_iff.mpr h))
  rw [← Scheme.Hom.comp_apply, hp.w, Scheme.Hom.comp_apply]

/-- A scheme morphism induces a bijection on irreducible components by closure of image exactly
when its base changes along the charts of an open cover of the target do, for arbitrary pullback
squares over the charts. -/
theorem bijOn_closure_image_irreducibleComponents_iff_of_isPullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Y.OpenCover.{v}) {U : 𝒰.I₀ → Scheme.{u}}
    {j : ∀ i, U i ⟶ X} {g : ∀ i, U i ⟶ 𝒰.X i} (hp : ∀ i, IsPullback (j i) (g i) f (𝒰.f i)) :
    BijOn (fun Z ↦ closure (f '' Z)) (irreducibleComponents X) (irreducibleComponents Y) ↔
      ∀ i, BijOn (fun Z ↦ closure (g i '' Z)) (irreducibleComponents (U i))
        (irreducibleComponents (𝒰.X i)) := by
  have (i : 𝒰.I₀) : IsOpenImmersion (j i) :=
    MorphismProperty.of_isPullback (hp i).flip inferInstance
  rw [← f.continuous.bijOn_genericPoints_iff,
    TauCeti.bijOn_genericPoints_iff_of_isOpenEmbedding (fun i ↦ (j i).isOpenEmbedding)
      (fun i ↦ (𝒰.f i).isOpenEmbedding) (fun y ↦ ⟨𝒰.idx y, 𝒰.covers y⟩)
      (fun i x ⟨v, hv⟩ ↦ (exists_preimage_of_isPullback (hp i) x v hv.symm).imp
        fun _ ↦ And.left)
      (fun i x ↦ by rw [← Scheme.Hom.comp_apply, (hp i).w, Scheme.Hom.comp_apply])]
  exact forall_congr' fun i ↦ (g i).continuous.bijOn_genericPoints_iff

/-- A scheme morphism induces a bijection on irreducible components by closure of image exactly
when its restrictions to the inverse images of the charts of an open cover of the target do. -/
theorem bijOn_closure_image_irreducibleComponents_iff_of_openCover
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Y.OpenCover.{v}) :
    BijOn (fun Z ↦ closure (f '' Z)) (irreducibleComponents X) (irreducibleComponents Y) ↔
      ∀ i, BijOn (fun Z ↦ closure (pullback.snd f (𝒰.f i) '' Z))
        (irreducibleComponents (pullback f (𝒰.f i) : Scheme)) (irreducibleComponents (𝒰.X i)) :=
  f.bijOn_closure_image_irreducibleComponents_iff_of_isPullback 𝒰
    fun i ↦ IsPullback.of_hasPullback f (𝒰.f i)

end AlgebraicGeometry.Scheme.Hom
