/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import TauCeti.Topology.Algebra.Nonarchimedean.Completion.Basic

/-!
# Ring homomorphisms between completions

This file provides transport lemmas for ring homomorphisms between completions when the source and
target uniformities are equal. The resulting completion types and ring structures are only
heterogeneously equal before those equalities are eliminated, so the map comparison is naturally
stated using `HEq`.

## Main results

* `TauCeti.completionRingHom_heq_of_uniformSpace_eq`: transports the characterization of a
  continuous ring homomorphism between completions across equal source and target uniformities.
* `TauCeti.ringHom_flat_of_completion_heq`: transports flatness across the resulting heterogeneous
  equality of ring homomorphisms.
-/

public section

namespace TauCeti

/-- Two completion ring homomorphisms are heterogeneously equal when their source and target
uniformities agree and the first map satisfies the characterization that uniquely determines the
second. -/
theorem completionRingHom_heq_of_uniformSpace_eq
    {A S S' : Type*} [CommRing A] [CommRing S] [CommRing S']
    {u₁ u₂ : UniformSpace S} (hu : u₂ = u₁) {v₁ v₂ : UniformSpace S'} (hv : v₂ = v₁)
    (g₁ : @IsUniformAddGroup S u₁ _) (g₂ : @IsUniformAddGroup S u₂ _)
    (t₁ : @IsTopologicalRing S u₁.toTopologicalSpace _)
    (t₂ : @IsTopologicalRing S u₂.toTopologicalSpace _)
    (g₁' : @IsUniformAddGroup S' v₁ _) (g₂' : @IsUniformAddGroup S' v₂ _)
    (t₁' : @IsTopologicalRing S' v₁.toTopologicalSpace _)
    (t₂' : @IsTopologicalRing S' v₂.toTopologicalSpace _) :
    let B₁ := @UniformSpace.Completion S u₁
    let B₂ := @UniformSpace.Completion S u₂
    let C₁ := @UniformSpace.Completion S' v₁
    let C₂ := @UniformSpace.Completion S' v₂
    let b₁ := @UniformSpace.Completion.commRing S _ u₁ g₁ t₁
    let b₂ := @UniformSpace.Completion.commRing S _ u₂ g₂ t₂
    let c₁ := @UniformSpace.Completion.commRing S' _ v₁ g₁' t₁'
    let c₂ := @UniformSpace.Completion.commRing S' _ v₂ g₂' t₂'
    ∀ (f₂ : @RingHom B₂ C₂ b₂.toNonAssocSemiring c₂.toNonAssocSemiring)
      (f₁ : @RingHom B₁ C₁ b₁.toNonAssocSemiring c₁.toNonAssocSemiring)
      (a₂ : @RingHom A B₂ _ b₂.toNonAssocSemiring)
      (a₁ : @RingHom A B₁ _ b₁.toNonAssocSemiring)
      (d₂ : @RingHom A C₂ _ c₂.toNonAssocSemiring)
      (d₁ : @RingHom A C₁ _ c₁.toNonAssocSemiring),
      @Continuous B₂ C₂ (@UniformSpace.Completion.uniformSpace S u₂).toTopologicalSpace
        (@UniformSpace.Completion.uniformSpace S' v₂).toTopologicalSpace f₂ →
      HEq a₂ a₁ → HEq d₂ d₁ → f₂.comp a₂ = d₂ →
      (∀ f : @RingHom B₁ C₁ b₁.toNonAssocSemiring c₁.toNonAssocSemiring,
        @Continuous B₁ C₁
          (@UniformSpace.Completion.uniformSpace S u₁).toTopologicalSpace
          (@UniformSpace.Completion.uniformSpace S' v₁).toTopologicalSpace f →
        f.comp a₁ = d₁ → f = f₁) →
      HEq f₂ f₁ := by
  subst hu
  subst hv
  dsimp only
  intro f₂ f₁ a₂ a₁ d₂ d₁ hf₂ ha hd hcomp₂ huniq
  apply heq_of_eq
  apply huniq f₂ hf₂
  rw [← eq_of_heq ha, hcomp₂, eq_of_heq hd]

/-- Flatness passes across a heterogeneous equality between ring homomorphisms of completions
whose source and target uniformities agree. -/
theorem ringHom_flat_of_completion_heq
    {S S' : Type*} [CommRing S] [CommRing S']
    {u₁ u₂ : UniformSpace S} (hu : u₂ = u₁) {v₁ v₂ : UniformSpace S'} (hv : v₂ = v₁)
    (g₁ : @IsUniformAddGroup S u₁ _) (g₂ : @IsUniformAddGroup S u₂ _)
    (t₁ : @IsTopologicalRing S u₁.toTopologicalSpace _)
    (t₂ : @IsTopologicalRing S u₂.toTopologicalSpace _)
    (g₁' : @IsUniformAddGroup S' v₁ _) (g₂' : @IsUniformAddGroup S' v₂ _)
    (t₁' : @IsTopologicalRing S' v₁.toTopologicalSpace _)
    (t₂' : @IsTopologicalRing S' v₂.toTopologicalSpace _) :
    let R₁ := @UniformSpace.Completion S u₁
    let R₂ := @UniformSpace.Completion S u₂
    let B₁ := @UniformSpace.Completion S' v₁
    let B₂ := @UniformSpace.Completion S' v₂
    let r₁ := @UniformSpace.Completion.commRing S _ u₁ g₁ t₁
    let r₂ := @UniformSpace.Completion.commRing S _ u₂ g₂ t₂
    let b₁ := @UniformSpace.Completion.commRing S' _ v₁ g₁' t₁'
    let b₂ := @UniformSpace.Completion.commRing S' _ v₂ g₂' t₂'
    ∀ (f₂ : @RingHom R₂ B₂ r₂.toNonAssocSemiring b₂.toNonAssocSemiring)
      (f₁ : @RingHom R₁ B₁ r₁.toNonAssocSemiring b₁.toNonAssocSemiring),
      HEq f₂ f₁ → @RingHom.Flat R₂ B₂ r₂ b₂ f₂ →
        @RingHom.Flat R₁ B₁ r₁ b₁ f₁ := by
  subst hu
  subst hv
  dsimp only
  intro f₂ f₁ hf hflat
  rwa [eq_of_heq hf] at hflat

end TauCeti

end
