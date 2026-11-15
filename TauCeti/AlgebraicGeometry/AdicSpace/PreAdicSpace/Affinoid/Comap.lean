/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.GlobalSections

/-!
# Affinoid morphisms are induced by their maps of global sections

Let `(A, A⁺)` and `(B, B⁺)` be Huber pairs with `A` and `B` complete and Hausdorff, and suppose the
structure presheaf of `Spa(B, B⁺)` is a sheaf. A morphism of pre-adic spaces
`f : Spa(B, B⁺) ⟶ Spa(A, A⁺)` gives a continuous ring homomorphism `A → B` by pullback on global
sections (`presentationLimitHomRingHom`). This file shows that `f` is determined by it, and that it
recovers `φ` from the morphism `Spa(φ)` induced by a continuous ring homomorphism `φ`. Hence `f` is
the morphism induced by its global-sections map. This is the affinoid case of the universal
property of `Spa(A, A⁺)`.

## Main results

* `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpace_hom_ext`: two morphisms
  `Spa(B, B⁺) ⟶ Spa(A, A⁺)` with the same global-sections map are equal.
* `TauCeti.ValuationSpectrum.presentationLimitHomRingHom_presentationLimitPreAdicSpaceComap`: the
  global-sections map of `Spa(φ)` is `φ`.
* `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceComap_presentationLimitHomRingHom`: a
  morphism is `Spa` of its global-sections map.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994),
  513–551, Proposition 2.1.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition

universe u

variable {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [CompleteSpace A] [T0Space A]
  {P : PairOfDefinition A} {Aplus : Subring A}

variable (P Aplus) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
  (hP : P.ringOfDefinition ≤ Aplus)

variable {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsTopologicalRing B] [CompleteSpace B] [T0Space B]
  (P' : PairOfDefinition B) (Bplus : Subring B)
  (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b) (hP' : P'.ringOfDefinition ≤ Bplus)

/-- **A morphism into an affinoid pre-adic spectrum is determined by its map of global sections**:
for complete Hausdorff `A` and `B`, two morphisms `Spa(B, B⁺) ⟶ Spa(A, A⁺)` of pre-adic spaces
with the same global-sections map `A → B` are equal, provided the structure presheaf of
`Spa(B, B⁺)` is a sheaf. -/
theorem presentationLimitPreAdicSpace_hom_ext
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus))
    {f g : presentationLimitPreAdicSpace P' Bplus hBplus hP' ⟶
      presentationLimitPreAdicSpace P Aplus hAplus hP}
    (h : presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP' f =
      presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP' g) : f = g := by
  apply presentationLimitAppTop_injective P Aplus hAplus hP
    (X := presentationLimitPreAdicSpace P' Bplus hBplus hP') hsheaf
  rw [presentationLimitHomRingHom_eq_comp_presentationLimitAppTop,
    presentationLimitHomRingHom_eq_comp_presentationLimitAppTop] at h
  exact (RingHom.cancel_left (Function.LeftInverse.injective (g :=
    (presentationLimitPreAdicSpaceTopIso P' Bplus hBplus hP').inv.1) fun b ↦
      Iso.hom_inv_id_apply (presentationLimitPreAdicSpaceTopIso P' Bplus hBplus hP') b)).mp h

/-- **The global-sections map of `Spa(φ)` is `φ`**: for complete Hausdorff `A` and `B`, pullback on
global sections recovers a continuous ring homomorphism `φ : A → B` from the morphism
`Spa(B, B⁺) ⟶ Spa(A, A⁺)` it induces. -/
@[simp]
theorem presentationLimitHomRingHom_presentationLimitPreAdicSpaceComap
    (φ : A →+* B) (hφ : Continuous φ)
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus)) :
    presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP'
      (presentationLimitPreAdicSpaceComap φ hφ hplus hAplus hBplus hP hP' hsheaf) = φ := by
  have hc0 : toPresentationLimit (P := P) Aplus ⊤ ≫
      eqToHom (presentationLimitPresheaf_obj P Aplus (Opposite.op ⊤)).symm ≫
      (presentationLimitPresheafComap φ hφ hplus hBplus hsheaf).app (Opposite.op ⊤) =
      ObjectProperty.homMk (eqToHom (CompleteSeparatedTopCommRingCat.of_obj A) ≫
          (⟨φ, hφ⟩ : _root_.TopCommRingCat.of A ⟶ _root_.TopCommRingCat.of B) ≫
          eqToHom (CompleteSeparatedTopCommRingCat.of_obj B).symm) ≫
        toPresentationLimit (P := P') Bplus ⊤ ≫
        eqToHom (presentationLimitPresheaf_obj P' Bplus (Opposite.op ⊤)).symm := by
    rw [presentationLimitPresheafComap_app]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [toPresentationLimit_comp_presentationLimitComap_assoc]
    -- the preimage `(Opens.map f).obj ⊤` of the whole spectrum is definitionally `⊤`
    rfl
  have h : (presentationLimitPreAdicSpaceTopIso P Aplus hAplus hP).inv ≫
      TopCommRingCat.isCompleteSeparated.ι.map
        ((presentationLimitPreAdicSpaceComap φ hφ hplus hAplus hBplus hP hP'
          hsheaf).toHom.c.app (Opposite.op ⊤)) =
      (⟨φ, hφ⟩ : _root_.TopCommRingCat.of A ⟶ _root_.TopCommRingCat.of B) ≫
        (presentationLimitPreAdicSpaceTopIso P' Bplus hBplus hP').inv := by
    have hg := presentationLimitPreAdicSpaceComap_toHom φ hφ hplus hAplus hBplus hP hP' hsheaf
    generalize presentationLimitPreAdicSpaceComap φ hφ hplus hAplus hBplus hP hP' hsheaf = g
      at hg ⊢
    rw [hg, presentationLimitPresheafedSpaceComap_c, presentationLimitPreAdicSpaceTopIso_inv,
      presentationLimitPreAdicSpaceTopIso_inv]
    have := congrArg (fun k ↦ eqToHom (CompleteSeparatedTopCommRingCat.of_obj A).symm ≫
      TopCommRingCat.isCompleteSeparated.ι.map k) hc0
    simp only [Functor.map_comp, eqToHom_map] at this
    refine (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (this.trans ?_))
    -- `erw`: the composite is typed with target `(f_* 𝒪_{Spa B})(⊤)`, which is `𝒪_{Spa B}(⊤)` only
    -- up to unfolding the pushforward, so `rw` does not see `Functor.map_comp` apply
    erw [Functor.map_comp, Functor.map_comp, eqToHom_map]
    simp only [ObjectProperty.ι_map, ObjectProperty.homMk_hom, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp, Category.assoc]
    -- the remaining transports have the same endpoints up to the same unfolding
    rfl
  rw [presentationLimitHomRingHom_def, Iso.homCongr_apply]
  -- `presentationLimitHomRingHom_def` types `Γ.map` with the objects of
  -- `presentationLimitPreAdicSpaceTopIso` rather than `forgetToPresheafedSpace.obj _`, so `rw`
  -- cannot apply `PresheafedSpace.Γ_map_op` there; it is applied under `congrArg` instead
  refine (congrArg (fun k ↦ ((forget₂ _root_.TopCommRingCat CommRingCat).map
    (k ≫ (presentationLimitPreAdicSpaceTopIso P' Bplus hBplus hP').hom)).hom)
    ((congrArg (fun k ↦ (presentationLimitPreAdicSpaceTopIso P Aplus hAplus hP).inv ≫
      TopCommRingCat.isCompleteSeparated.ι.map k) (PresheafedSpace.Γ_map_op _)).trans h)).trans ?_
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  -- forgetting continuity of `⟨φ, hφ⟩` gives back `φ`
  rfl

/-- **A morphism into an affinoid pre-adic spectrum is induced by its map of global sections**:
for complete Hausdorff `A` and `B` and `Spa(B, B⁺)` with a sheaf as structure presheaf, a morphism
`f : Spa(B, B⁺) ⟶ Spa(A, A⁺)` is the morphism induced by its global-sections map. The plus rings
are preserved when `B⁺` is open and integrally closed (`presentationLimitHomRingHom_mem_plus`). -/
theorem presentationLimitPreAdicSpaceComap_presentationLimitHomRingHom
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus))
    (f : presentationLimitPreAdicSpace P' Bplus hBplus hP' ⟶
      presentationLimitPreAdicSpace P Aplus hAplus hP)
    (hplus : ∀ a ∈ Aplus, presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP' f a ∈
      Bplus) :
    presentationLimitPreAdicSpaceComap
        (presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP' f)
        (continuous_presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP' f)
        hplus hAplus hBplus hP hP' hsheaf = f :=
  presentationLimitPreAdicSpace_hom_ext P Aplus hAplus hP P' Bplus hBplus hP' hsheaf
    (presentationLimitHomRingHom_presentationLimitPreAdicSpaceComap P Aplus hAplus hP P' Bplus
      hBplus hP' _ _ hplus hsheaf)

end TauCeti.ValuationSpectrum

end
