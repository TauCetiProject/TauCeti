/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.Functors
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Hom
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.ClosedImmersion.Basic

/-!
# Affinoid morphisms are induced by their maps of global sections

Let `(A, A⁺)` and `(B, B⁺)` be Huber pairs with `A` and `B` complete and Hausdorff, and suppose the
structure presheaf of `Spa(B, B⁺)` is a sheaf. A morphism of pre-adic spaces
`f : Spa(B, B⁺) ⟶ Spa(A, A⁺)` gives a continuous ring homomorphism `A → B` by pullback on global
sections (`presentationLimitHomRingHom`). This file shows that `f` is determined by it, and that it
recovers `φ` from the morphism `Spa(φ)` induced by a continuous ring homomorphism `φ`. Hence `f` is
the morphism induced by its global-sections map whenever that map carries open ideals to ideals
generating open ideals, the condition under which `Spa(φ)` is constructed. That condition holds,
for instance, when `A` is a Tate ring (`TauCeti.Huber.IsTateRing.isOpen_map_of_isOpen`). This is
the affinoid case of the universal property of `Spa(A, A⁺)`.

The proof that `f` is determined by its global sections compares maps of structure presheaves on
the rational opens of `Spa(A, A⁺)`, which form a basis, and the target `f_* 𝒪_{Spa B}` is a sheaf.
On a rational open `R(T/s)` the sections are `A⟨T/s⟩`, and maps out of it are determined on `A`
(`presentationLimit_spaBasicOpen_hom_ext`); by naturality they are determined by the map on global
sections.

As an application, a morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` whose global-sections map kills an ideal
`J` factors through the quotient morphism `Spa(A ⧸ J, (A ⧸ J)⁺) ⟶ Spa(A, A⁺)`. This is the existence
half of the factorisation property of closed immersions, for affinoid sources.

## Main results

* `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpace_hom_ext`: two morphisms
  `Spa(B, B⁺) ⟶ Spa(A, A⁺)` with the same global-sections map are equal.
* `TauCeti.ValuationSpectrum.presentationLimitHomRingHom_presentationLimitPreAdicSpaceComap`: the
  global-sections map of `Spa(φ)` is `φ`.
* `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceComap_presentationLimitHomRingHom`: a
  morphism is `Spa` of its global-sections map.
* `TauCeti.ValuationSpectrum.exists_comp_presentationLimitPreAdicSpaceQuotientComap_eq`: a
  morphism whose global-sections map kills `J` factors through the quotient morphism by `J`.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994),
  513–551, Proposition 2.1.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1 and Proposition 7.38.
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

/-- Equal recovered ring homomorphisms come from equal maps of global sections. -/
private theorem Γ_map_eq_of_presentationLimitHomRingHom_eq
    {f g : presentationLimitPreAdicSpace P' Bplus hBplus hP' ⟶
      presentationLimitPreAdicSpace P Aplus hAplus hP}
    (h : presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP' f =
      presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP' g) :
    PresheafedSpace.Γ.map (PreAdicSpace.forgetToPresheafedSpace.map f).op =
      PresheafedSpace.Γ.map (PreAdicSpace.forgetToPresheafedSpace.map g).op := by
  rw [presentationLimitHomRingHom_def, presentationLimitHomRingHom_def] at h
  exact TopCommRingCat.isCompleteSeparated.ι.map_injective <| (Iso.homCongr _ _).injective <|
    (forget₂ _root_.TopCommRingCat CommRingCat).map_injective <| CommRingCat.hom_ext h

omit [IsUniformAddGroup A] [CompleteSpace A] [T0Space A] in
/-- The rational opens `R(i)` presented by the indices `i` of the whole spectrum form a basis of
`Spa(A, A⁺)`. -/
private theorem isBasis_range_spaBasicOpen :
    Opens.IsBasis (Set.range fun i : PresentationIndex (P := P) Aplus ⊤ ↦
      spaBasicOpen Aplus i.pres.num i.pres.den) := by
  refine Opens.isBasis_iff_nbhd.mpr fun {U x} hx ↦ ?_
  obtain ⟨p, hp, hxp, hle⟩ := exists_presentation_mem_spaBasicOpen_le P hx
  exact ⟨_, ⟨⟨p, hp, le_top⟩, rfl⟩, hxp, hle⟩

/-- By naturality, the image of `A` under the component on a rational open of a morphism of
presheaves out of `𝒪_{Spa A}` is determined by the component on the whole spectrum. -/
private theorem toPresentationLimit_comp_app_spaBasicOpen {C : TopCat.{u}}
    (b : C ⟶ TopCat.of ↥(spa Aplus)) (F : C.Presheaf CompleteSeparatedTopCommRingCat.{u})
    (c : presentationLimitPresheaf P Aplus ⟶
      (TopCat.Presheaf.pushforward CompleteSeparatedTopCommRingCat b).obj F)
    (i : PresentationIndex (P := P) Aplus ⊤) :
    toPresentationLimit Aplus _ ≫
        eqToHom (presentationLimitPresheaf_obj P Aplus
          (Opposite.op (spaBasicOpen Aplus i.pres.num i.pres.den))).symm ≫
        c.app (Opposite.op (spaBasicOpen Aplus i.pres.num i.pres.den)) =
      toPresentationLimit Aplus ⊤ ≫
        eqToHom (presentationLimitPresheaf_obj P Aplus (Opposite.op ⊤)).symm ≫
        c.app (Opposite.op ⊤) ≫
        ((TopCat.Presheaf.pushforward CompleteSeparatedTopCommRingCat b).obj F).map
          (homOfLE le_top).op := by
  rw [← c.naturality, presentationLimitPresheaf_map]
  simp

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
  -- the maps of points agree, since each is pullback along the recovered ring homomorphism
  have hbase : f.base = g.base := by
    ext x
    exact Subtype.ext (by
      rw [base_eq_comap_presentationLimitHomRingHom, base_eq_comap_presentationLimitHomRingHom, h])
  have htop := Γ_map_eq_of_presentationLimitHomRingHom_eq P Aplus hAplus hP P' Bplus hBplus hP' h
  -- `Γ.map (forget.map f).op` is by definition the component of `f` on the whole space
  replace htop : f.toHom.c.app (Opposite.op ⊤) = g.toHom.c.app (Opposite.op ⊤) := htop
  ext1
  clear h
  generalize f.toHom = F at hbase htop ⊢
  generalize g.toHom = G at hbase htop ⊢
  rcases F with ⟨fb, fc⟩
  rcases G with ⟨gb, gc⟩
  dsimp only at hbase htop
  subst hbase
  congr 1
  -- compare the maps of presheaves `𝒪_{Spa A} ⟶ f_* 𝒪_{Spa B}` on the rational basis
  refine TopCat.Sheaf.hom_ext (X := TopCat.of ↥(spa Aplus)) _
    ⟨_, TopCat.Sheaf.pushforward_sheaf_of_sheaf fb hsheaf⟩ (isBasis_range_spaBasicOpen P Aplus)
    fun i ↦ ?_
  refine (cancel_epi (eqToHom (presentationLimitPresheaf_obj P Aplus
    (Opposite.op (spaBasicOpen Aplus i.pres.num i.pres.den))).symm)).mp
      (presentationLimit_spaBasicOpen_hom_ext Aplus hAplus i.pres i.isOpen_span ?_)
  exact (toPresentationLimit_comp_app_spaBasicOpen P Aplus fb _ fc i).trans
    (Eq.trans (congrArg (fun k ↦ toPresentationLimit Aplus ⊤ ≫
      eqToHom (presentationLimitPresheaf_obj P Aplus (Opposite.op ⊤)).symm ≫ k ≫
        ((TopCat.Presheaf.pushforward CompleteSeparatedTopCommRingCat fb).obj
          (presentationLimitPresheaf P' Bplus)).map (homOfLE le_top).op) htop)
      (toPresentationLimit_comp_app_spaBasicOpen P Aplus fb _ gc i).symm)

/-- **The global-sections map of `Spa(φ)` is `φ`**: for complete Hausdorff `A` and `B`, pullback on
global sections recovers a continuous ring homomorphism `φ : A → B` from the morphism
`Spa(B, B⁺) ⟶ Spa(A, A⁺)` it induces. -/
@[simp]
theorem presentationLimitHomRingHom_presentationLimitPreAdicSpaceComap
    (φ : A →+* B) (hφ : Continuous φ)
    (hopen : ∀ ⦃J : Ideal A⦄, IsOpen (J : Set A) → IsOpen (J.map φ : Set B))
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus)) :
    presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP'
      (presentationLimitPreAdicSpaceComap φ hφ hopen hplus hAplus hBplus hP hP' hsheaf) = φ := by
  have hc0 : toPresentationLimit (P := P) Aplus ⊤ ≫
      eqToHom (presentationLimitPresheaf_obj P Aplus (Opposite.op ⊤)).symm ≫
      (presentationLimitPresheafComap φ hφ hopen hplus hBplus hsheaf).app (Opposite.op ⊤) =
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
      TopCommRingCat.isCompleteSeparated.ι.map (PresheafedSpace.Γ.map
        (PreAdicSpace.forgetToPresheafedSpace.map
          (presentationLimitPreAdicSpaceComap φ hφ hopen hplus hAplus hBplus hP hP' hsheaf)).op) =
      (⟨φ, hφ⟩ : _root_.TopCommRingCat.of A ⟶ _root_.TopCommRingCat.of B) ≫
        (presentationLimitPreAdicSpaceTopIso P' Bplus hBplus hP').inv := by
    have hg := presentationLimitPreAdicSpaceComap_toHom φ hφ hopen hplus hAplus hBplus hP hP' hsheaf
    generalize presentationLimitPreAdicSpaceComap φ hφ hopen hplus hAplus hBplus hP hP' hsheaf = g
      at hg ⊢
    -- `Γ.map (forget.map g).op` is by definition the component of `g` on the whole space
    change _ ≫ TopCommRingCat.isCompleteSeparated.ι.map (g.toHom.c.app (Opposite.op ⊤)) = _
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
  refine (congrArg (fun k ↦ ((forget₂ _root_.TopCommRingCat CommRingCat).map
    (k ≫ (presentationLimitPreAdicSpaceTopIso P' Bplus hBplus hP').hom)).hom) h).trans ?_
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  -- forgetting continuity of `⟨φ, hφ⟩` gives back `φ`
  rfl

/-- **A morphism into an affinoid pre-adic spectrum is induced by its map of global sections**:
for complete Hausdorff `A` and `B` and `Spa(B, B⁺)` with a sheaf as structure presheaf, a morphism
`f : Spa(B, B⁺) ⟶ Spa(A, A⁺)` is the morphism induced by its global-sections map, as soon as that
map carries open ideals to ideals generating open ideals (so that the induced morphism is
defined). The plus rings are preserved when `B⁺` is open and integrally closed
(`presentationLimitHomRingHom_mem_plus`). -/
theorem presentationLimitPreAdicSpaceComap_presentationLimitHomRingHom
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus))
    (f : presentationLimitPreAdicSpace P' Bplus hBplus hP' ⟶
      presentationLimitPreAdicSpace P Aplus hAplus hP)
    (hopen : ∀ ⦃J : Ideal A⦄, IsOpen (J : Set A) →
      IsOpen (J.map (presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP' f) : Set B))
    (hplus : ∀ a ∈ Aplus, presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP' f a ∈
      Bplus) :
    presentationLimitPreAdicSpaceComap
        (presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP' f)
        (continuous_presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP' f)
        hopen hplus hAplus hBplus hP hP' hsheaf = f :=
  presentationLimitPreAdicSpace_hom_ext P Aplus hAplus hP P' Bplus hBplus hP' hsheaf
    (presentationLimitHomRingHom_presentationLimitPreAdicSpaceComap P Aplus hAplus hP P' Bplus
      hBplus hP' _ _ hopen hplus hsheaf)

section Quotient

variable [IsHuberRing A] [IsHuberRing B] (S : Pair A) (T : Pair B)
  (hS : P.ringOfDefinition ≤ S.plus) (hT : P'.ringOfDefinition ≤ T.plus) (J : Ideal A)

/-- **The factorisation property of the quotient morphism, for affinoid sources**: for complete
Hausdorff `A` and `B`, a morphism `f : Spa(B, B⁺) ⟶ Spa(A, A⁺)` of pre-adic spaces whose
global-sections map kills `J`, and carries open ideals to ideals generating open ideals, factors
through the quotient morphism `Spa(A ⧸ J, (A ⧸ J)⁺) ⟶ Spa(A, A⁺)`. The structure presheaves of
`Spa(B, B⁺)` and `Spa(A ⧸ J, (A ⧸ J)⁺)` are assumed to be sheaves. -/
theorem exists_comp_presentationLimitPreAdicSpaceQuotientComap_eq
    (hsheafJ : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa (S.quotient J).plus))
      (presentationLimitPresheaf (P.quotient J) (S.quotient J).plus))
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (f : presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem
        hT ⟶
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hS)
    (hf : J ≤ RingHom.ker (presentationLimitHomPairHom P P' S T hS hT f).toRingHom)
    (hopen : ∀ ⦃I : Ideal A⦄, IsOpen (I : Set A) →
      IsOpen (I.map (presentationLimitHomPairHom P P' S T hS hT f).toRingHom : Set B)) :
    ∃ g, g ≫ presentationLimitPreAdicSpaceQuotientComap S P hS J hsheafJ = f := by
  -- the factorisation is induced by the factorisation of the global-sections map through `A ⧸ J`
  let φ := presentationLimitHomPairHom P P' S T hS hT f
  refine ⟨presentationLimitPreAdicSpaceComap (φ.quotientLift J hf).toRingHom
    (φ.quotientLift J hf).continuous_toRingHom (fun _ hI ↦ φ.isOpen_map_quotientLift J hf hopen hI)
    (φ.quotientLift J hf).map_mem_plus (S.quotient J).isRingOfIntegralElements.isPowerBounded_of_mem
    T.isRingOfIntegralElements.isPowerBounded_of_mem
    (P.quotient_ringOfDefinition_le_quotient_plus hS J) hT hsheafT,
    presentationLimitPreAdicSpace_hom_ext P S.plus _ hS P' T.plus _ hT hsheafT ?_⟩
  rw [presentationLimitPreAdicSpaceComap_quotientLift_comp_quotientComap S P hS J hsheafJ P' hT _
    hf hopen hsheafT, presentationLimitHomRingHom_presentationLimitPreAdicSpaceComap,
    presentationLimitHomPairHom_toRingHom]

end Quotient

end TauCeti.ValuationSpectrum

end
