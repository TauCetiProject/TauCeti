/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.GlobalCoordinates

/-!
# Graded changes of global projective coordinates

Postcomposing a morphism defined by global homogeneous coordinates with a graded
projective map amounts to precomposing its coordinate homomorphism. The comparison
holds as an equality of scheme morphisms, including the maps on structure sheaves.
It allows coordinate identities for linear actions to give equivariance of projective
orbit morphisms.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.d–7.f.
-/

public section

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry.Proj

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] {X : Scheme.{u}}

/-- A graded projective map transforms a global homogeneous-coordinate morphism by
precomposition of its coordinates. -/
@[reassoc]
theorem fromOfGlobalSections_map (F : 𝒜 →+*ᵍ ℬ)
    (hF : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map F)
    (f : B →+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal.map f = ⊤) :
    fromOfGlobalSections ℬ f hf ≫ map F hF =
      fromOfGlobalSections 𝒜 (f.comp F.toRingHom) (by
        apply top_unique
        rw [← hf, ← Ideal.map_map]
        exact Ideal.map_mono ((SetLike.coe_subset_coe).mpr hF)) := by
  have hcomp : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (f.comp F.toRingHom) = ⊤ := by
    apply top_unique
    rw [← hf, ← Ideal.map_map]
    exact Ideal.map_mono ((SetLike.coe_subset_coe).mpr hF)
  refine (openCoverOfMapIrrelevantEqTop 𝒜 (f.comp F.toRingHom) hcomp).hom_ext _ _
    fun ⟨n, s, hn, hs⟩ ↦ ?_
  -- The cover stores its opens behind a sealed construction. Present its inclusion
  -- explicitly so chart restriction lemmas can rewrite the goal.
  change (X.basicOpen (f (F s))).ι ≫ _ = (X.basicOpen (f (F s))).ι ≫ _
  have hleft := fromOfGlobalSections_resLE ℬ f hf hn (F.2 hs)
  have hright := fromOfGlobalSections_resLE 𝒜 (f.comp F.toRingHom) hcomp hn hs
  have hleft' := congrArg (fun e ↦ e ≫ (basicOpen ℬ (F s)).ι ≫ map F hF) hleft
  have hright' := congrArg (fun e ↦ e ≫ (basicOpen 𝒜 s).ι) hright
  simp only [GradedRingHom.coe_toRingHom] at hleft'
  rw [Scheme.Hom.resLE_comp_ι_assoc] at hleft'
  simp only [Scheme.Hom.resLE_comp_ι] at hright'
  simp only [RingHom.comp_apply, GradedRingHom.coe_toRingHom] at hright'
  rw [hleft', hright']
  rw [TauCeti.ProjectiveSpectrum.toBasicOpenOfGlobalSections_eq,
    TauCeti.ProjectiveSpectrum.toBasicOpenOfGlobalSections_eq]
  simp only [Category.assoc, basicOpenIsoSpec_inv_ι, basicOpenIsoSpec_inv_ι_assoc]
  have hmap := awayι_comp_map F hF hn s hs
  -- Global-section charts use the ringed-space section-ring instances.
  erw [hmap]
  simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    RingHom.comp_apply, GradedRingHom.coe_toRingHom]
  apply congrArg (fun φ ↦ (X.basicOpen (f (F s))).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom φ) ≫ awayι 𝒜 s hs hn)
  erw [Away.lift_comp_map]
  simp only [RingHom.comp_assoc]

end AlgebraicGeometry.Proj
