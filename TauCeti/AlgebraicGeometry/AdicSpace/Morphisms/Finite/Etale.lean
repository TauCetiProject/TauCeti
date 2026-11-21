/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.Finite.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyTate
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.FiniteAlgebra
import TauCeti.RingTheory.Huber.ModuleTopology.FiniteEtale

/-!
# Finite étale morphisms of adic spaces

A morphism `f : X ⟶ Y` of adic spaces is *finite étale* (Kedlaya–Liu, Definition 8.2.16) if every
point of `Y` has an open neighbourhood `V` such that `V ≅ Spa(A, A⁺)` for a complete Hausdorff Tate
Huber pair and `f⁻¹(V) ≅ Spa(B, B⁺)` for a complete Hausdorff Huber pair, under which `f`
restricted to `f⁻¹(V) → V` is the morphism induced by a finite étale morphism of Huber pairs
`φ : (A, A⁺) → (B, B⁺)` (`TauCeti.Huber.Pair.Hom.IsFiniteEtale`): `B` is a finite étale
`A`-algebra with its natural topology and `B⁺` is the integral closure of the image of `A⁺`.

This is the notion of finite étale morphism for analytic adic spaces that need not be locally
noetherian, where Huber's infinitesimal definition is not available. The condition is local on the
target, and no particular cover is fixed. The plus ring is part of the condition: for a finite étale
`A`-algebra `B` the pair `(B, B°)` is in general not the one attached to `B`. The Tate charts force
both spaces to be analytic. Sheafiness is not automatic: the definition asks that `Spa(B, B⁺)` be an
adic space, and that `Spa(A, A⁺)` be one follows from its being an open subspace of `Y`.

A finite étale morphism of Huber pairs over a complete Hausdorff Tate ring is finite
(`TauCeti.Huber.Pair.Hom.IsFiniteEtale.isFinite`), so finite étale morphisms of adic spaces are
finite in Huber's sense (`TauCeti.AdicSpace.IsFinite`), hence quasi-compact
(`TauCeti.AdicSpace.IsFinite.quasiCompact`) and of weakly finite type
(`TauCeti.AdicSpace.IsFinite.isWeaklyFiniteType`). The fibres of `Spa(B, B⁺) → Spa(A, A⁺)` have
at most as many points as the local rank of `B`
(`TauCeti.Huber.Pair.Hom.IsFiniteEtale.finite_fibre`), so finite étale morphisms have finite
fibres.

## Main definitions

* `TauCeti.AdicSpace.IsFiniteEtale`: finite étale morphisms of adic spaces.

## Main results

* `TauCeti.AdicSpace.isFiniteEtale_presentationLimitPreAdicSpaceComap`: the morphism
  `Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by a finite étale morphism of complete Hausdorff Huber pairs
  over a Tate ring, both of whose spectra are adic spaces, is finite étale.
* `TauCeti.AdicSpace.IsFiniteEtale.isFinite`: finite étale morphisms are finite.
* `TauCeti.AdicSpace.IsFiniteEtale.finite_preimage_singleton`: finite étale morphisms have finite
  fibres.
* `TauCeti.AdicSpace.IsFiniteEtale.isAnalytic_source`,
  `TauCeti.AdicSpace.IsFiniteEtale.isAnalytic_target`: the source and the target of a finite étale
  morphism are analytic.
* `TauCeti.AdicSpace.IsFiniteEtale.of_iSup_eq_top`: being finite étale descends along open covers
  of the target.
* `TauCeti.AdicSpace.IsFiniteEtale.respectsIso`: being finite étale is invariant under isomorphisms
  of the source and of the target.
* `TauCeti.AdicSpace.isFiniteEtale_id` and `TauCeti.AdicSpace.isFiniteEtale_of_isIso`: the
  identity of an analytic adic space, and every isomorphism onto one, are finite étale.

## Implementation notes

The definition and the proofs of descent along open covers and of isomorphism invariance are
adapted from those of the target-local predicate `TauCeti.AdicSpace.IsFinite`
(`Morphisms/Finite/Basic.lean`), with `TauCeti.Huber.Pair.Hom.IsFiniteEtale` in place of
`TauCeti.Huber.Pair.Hom.IsFinite` and Tate charts on the target.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §8.2, Definition 8.2.16.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §7, Definition 7.1(ii).
* P. Scholze and J. Weinstein, *Berkeley lectures on p-adic geometry*, Annals of Mathematics
  Studies 207 (2020), Lecture 7, Definition 7.5.1(1).
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber

universe u

namespace AdicSpace

open PreAdicSpace ValuationSpectrum

/-- **Finite étale morphisms** (Kedlaya–Liu, Definition 8.2.16): a morphism `f : X ⟶ Y` of adic
spaces is *finite étale* when every point `y` of `Y` has an open neighbourhood `V` together with a
complete Hausdorff Tate Huber pair `(A, A⁺)`, a complete Hausdorff Huber pair `(B, B⁺)` such that
`Spa(B, B⁺)` has a sheaf as structure presheaf, a finite étale morphism `φ : (A, A⁺) → (B, B⁺)` of
Huber pairs, and isomorphisms identifying `Y` restricted to `V` with `Spa(A, A⁺)` and `X` restricted
to `f⁻¹(V)` with `Spa(B, B⁺)`, under which `f` becomes the morphism induced by `φ`. -/
def IsFiniteEtale {X Y : AdicSpace.{u}} (f : X ⟶ Y) : Prop :=
  ∀ y : Y.obj, ∃ (V : Opens Y.obj) (_ : y ∈ V) (A : Type u) (_ : CommRing A)
    (_ : UniformSpace A) (_ : IsUniformAddGroup A) (_ : IsTopologicalRing A) (_ : CompleteSpace A)
    (_ : T2Space A) (_ : IsTateRing A) (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus)
    (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
    (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
    (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
    (φ : Pair.Hom S T) (_ : φ.IsFiniteEtale)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (eV : Y.obj.restrict V.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP)
    (eU : X.obj.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ≅
      presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem
        hP'),
    X.obj.ofRestrict _ ≫ f.hom =
      eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
        φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫
        Y.obj.ofRestrict _

variable {X Y : AdicSpace.{u}}

/-- Unfolding lemma for `TauCeti.AdicSpace.IsFiniteEtale`. -/
theorem isFiniteEtale_iff (f : X ⟶ Y) : IsFiniteEtale f ↔
    ∀ y : Y.obj, ∃ (V : Opens Y.obj) (_ : y ∈ V) (A : Type u) (_ : CommRing A)
      (_ : UniformSpace A) (_ : IsUniformAddGroup A) (_ : IsTopologicalRing A)
      (_ : CompleteSpace A) (_ : T2Space A) (_ : IsTateRing A) (S : Pair A)
      (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
      (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
      (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
      (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
      (φ : Pair.Hom S T) (_ : φ.IsFiniteEtale)
      (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
        (presentationLimitPresheaf P' T.plus))
      (eV : Y.obj.restrict V.isOpenEmbedding ≅
        presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem
          hP)
      (eU : X.obj.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ≅
        presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem
          hP'),
      X.obj.ofRestrict _ ≫ f.hom =
        eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
          φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
          T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫
          Y.obj.ofRestrict _ :=
  Iff.rfl

/-! ### Finite étale morphisms are finite, with finite fibres -/

/-- **Finite étale morphisms are finite**: over a complete Hausdorff Tate ring, a finite étale
morphism of Huber pairs is finite (`TauCeti.Huber.Pair.Hom.IsFiniteEtale.isFinite`). -/
theorem IsFiniteEtale.isFinite {f : X ⟶ Y} (hf : IsFiniteEtale f) : IsFinite f :=
  (isFinite_iff f).mpr fun y ↦ by
    obtain ⟨V, hy, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
      hsheaf, eV, eU, hfac⟩ := hf y
    exact ⟨V, hy, A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, S, P, hP, B, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, T, P', hP', φ, hφ.isFinite,
      hsheaf, eV, eU, hfac⟩

/-- **The fibres of a finite étale morphism are finite.** Over a neighbourhood `V` supplied by the
definition, the morphism is, up to homeomorphisms, the map `Spa(B, B⁺) → Spa(A, A⁺)` induced by a
finite étale morphism of Huber pairs, whose fibres are finite
(`TauCeti.Huber.Pair.Hom.IsFiniteEtale.finite_fibre`). -/
theorem IsFiniteEtale.finite_preimage_singleton {f : X ⟶ Y} (hf : IsFiniteEtale f) (y : Y.obj) :
    (f.hom.base ⁻¹' {y}).Finite := by
  obtain ⟨V, hy, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eV, eU, hfac⟩ := hf y
  let g := presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom φ.map_mem_plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem
    T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf
  let eU' := TopCat.homeoOfIso (forgetToTop.mapIso eU)
  let eV' := TopCat.homeoOfIso (forgetToTop.mapIso eV)
  -- on points, `Spa(φ)` is `φ.spaComap`, whose fibres are finite
  have hg : ⇑(ConcreteCategory.hom g.base) = φ.spaComap := funext fun w ↦ Subtype.ext <|
    (presentationLimitPreAdicSpaceComap_base_val _ _ _ _ _ _ _ _ w).trans (φ.spaComap_val w).symm
  have hfin : (⇑(ConcreteCategory.hom g.base) ⁻¹' {eV' ⟨y, hy⟩}).Finite :=
    hg ▸ (hφ.finite_fibre _).1
  -- the defining square, on points
  have hfac' := congrArg (fun h ↦ ConcreteCategory.hom (forgetToTop.map h)) hfac
  simp only [Functor.map_comp, TopCat.hom_comp] at hfac'
  -- the fibre of `f` over `y` is the image of the fibre of `Spa(φ)` over the point of `y`
  refine (hfin.image fun w ↦ (eU'.symm w).val).subset fun x hx ↦ ?_
  have hxV : f.hom.base x ∈ V := (Set.mem_singleton_iff.mp hx).symm ▸ hy
  have h := congrArg (fun h ↦ h ⟨x, hxV⟩) hfac'
  exact ⟨eU' ⟨x, hxV⟩, eV'.symm_apply_eq.mp (Subtype.ext (h.symm.trans hx)),
    congrArg Subtype.val (eU'.symm_apply_apply _)⟩

/-! ### Finite étale morphisms have analytic source and target -/

/-- **The target of a finite étale morphism is analytic**: the neighbourhoods supplied by the
definition are open Tate affinoid subspaces. -/
theorem IsFiniteEtale.isAnalytic_target {f : X ⟶ Y} (hf : IsFiniteEtale f) : Y.IsAnalytic :=
  isAnalytic_iff.mpr fun y ↦ by
    obtain ⟨V, hy, A, _, _, _, _, _, _, _, S, P, hP, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      eV, _⟩ := hf y
    exact ⟨V, (mem_propOpens_iff _).mpr <| (isTateAffinoid_iff _).mpr ⟨A, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      S, P, hP, ⟨eV⟩⟩, hy⟩

/-- **The source of a finite étale morphism is analytic**: the preimages of the neighbourhoods
supplied by the definition are open Tate affinoid subspaces, a finite algebra over a Tate ring being
Tate. -/
theorem IsFiniteEtale.isAnalytic_source {f : X ⟶ Y} (hf : IsFiniteEtale f) : X.IsAnalytic :=
  isAnalytic_iff.mpr fun x ↦ by
    obtain ⟨V, hy, _, _, _, _, _, _, _, _, _, _, _, B, _, _, _, _, _, _, _, T, P', hP', φ, _, _,
      _, eU, _⟩ := hf (f.hom.base x)
    have : IsTateRing B := IsTateRing.of_continuous (φ := φ.toRingHom) φ.continuous_toRingHom
    exact ⟨(Opens.map f.hom.base).obj V, (mem_propOpens_iff _).mpr <| (isTateAffinoid_iff _).mpr
      ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, T, P', hP', ⟨eU⟩⟩, hy⟩

/-! ### Descent along open covers of the target -/

/-- **Being finite étale descends along open covers of the target**: if `Y` is covered by opens
`V i` over which the restrictions `f⁻¹(V i) → V i` of `f` are finite étale, then `f` is finite
étale. A neighbourhood supplied by a restriction is an open of `V i`, hence an open of `Y`, with the
same preimage in `X`. -/
theorem IsFiniteEtale.of_iSup_eq_top {f : X ⟶ Y} {ι : Type*} (V : ι → Opens Y.obj)
    (hV : iSup V = ⊤)
    (hf : ∀ i, IsFiniteEtale
      (X := ⟨_, isAdic_restrict ((Opens.map f.hom.base).obj (V i)).isOpenEmbedding X.property⟩)
      (Y := ⟨_, isAdic_restrict (V i).isOpenEmbedding Y.property⟩)
      (ObjectProperty.homMk (f.hom.restrictPreimage (V i)))) :
    IsFiniteEtale f := by
  intro y
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hV.symm ▸ Set.mem_univ y : y ∈ iSup V)
  obtain ⟨W, hy, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eW, eU, hfac⟩ := hf i ⟨y, hi⟩
  let V' : Opens Y.obj := (V i).isOpenEmbedding.isOpenMap.functor.obj W
  let U := (Opens.map f.hom.base).obj (V i)
  let U' := (Opens.map (f.hom.restrictPreimage (V i)).base).obj W
  -- both open subspaces of `X` have precisely the points mapping into the image of `W`
  have hr : Set.range ((X.obj.restrict U.isOpenEmbedding).ofRestrict U'.isOpenEmbedding ≫
      X.obj.ofRestrict U.isOpenEmbedding).base =
      Set.range (X.obj.ofRestrict ((Opens.map f.hom.base).obj V').isOpenEmbedding).base := by
    have h := range_restrictPreimage_comp_eq_preimage_range (eV := Iso.refl _)
      (eU := Iso.refl _) (q := f.hom.restrictPreimage (V i)) (by simp) W
    simp only [Iso.refl_inv, Category.id_comp, IsOpenImmersion.range_ofRestrict_comp_base] at h ⊢
    rw [h]
    ext x
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨⟨x, (hz ▸ z.property : f.hom.base x ∈ V')⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨⟨_, z.property⟩, rfl⟩
  let e := IsOpenImmersion.isoOfRangeEq
    ((X.obj.restrict U.isOpenEmbedding).ofRestrict U'.isOpenEmbedding ≫
      X.obj.ofRestrict U.isOpenEmbedding)
    (X.obj.ofRestrict ((Opens.map f.hom.base).obj V').isOpenEmbedding) hr
  refine ⟨V', ⟨⟨y, hi⟩, hy, rfl⟩, A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, S, P, hP, B, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, T, P', hP', φ, hφ,
    hsheaf, (restrictRestrictIso Y.obj (V i).isOpenEmbedding W).symm ≪≫ eW, e.symm ≪≫ eU, ?_⟩
  -- transport the local square through the two identifications of open subspaces, composing the
  -- identities as terms: rewriting inside the restricted objects would require identifying the
  -- topology of a restriction with its underlying subtype topology
  have hsource := congrArg (fun g ↦ g ≫ f.hom)
    (IsOpenImmersion.isoOfRangeEq_inv_comp _ _ hr)
  have hsquare := congrArg (fun g ↦ g ≫ Y.obj.ofRestrict (V i).isOpenEmbedding) hfac
  have htarget := congrArg
    (fun g ↦ eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
      φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eW.inv ≫ g)
    (restrictRestrictIso_hom_ofRestrict Y.obj (V i).isOpenEmbedding W)
  simp only [Category.assoc] at hsource htarget
  simp only [Category.assoc, ObjectProperty.homMk_hom, Hom.restrictPreimage_ofRestrict] at hsquare
  simpa only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Category.assoc] using
    hsource.symm.trans (congrArg (fun g ↦ e.inv ≫ g) (hsquare.trans htarget.symm))

/-! ### Affinoid morphisms, identities and isomorphisms -/

/-- **Affinoid morphisms**: for a finite étale morphism of Huber pairs `φ : (A, A⁺) → (B, B⁺)`
between complete Hausdorff pairs, with `A` a Tate ring and both adic spectra adic spaces, the
morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by `φ` is finite étale, witnessed over the whole of
`Spa(A, A⁺)`. -/
theorem isFiniteEtale_presentationLimitPreAdicSpaceComap {A : Type u} [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T2Space A]
    [IsTateRing A] {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [CompleteSpace B] [T2Space B] [IsHuberRing B] {S : Pair A} {T : Pair B}
    (P : PairOfDefinition A) (P' : PairOfDefinition B) (hP : P.ringOfDefinition ≤ S.plus)
    (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (hA : PreAdicSpace.isAdic (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)) (φ : Pair.Hom S T)
    (hφ : φ.IsFiniteEtale) :
    IsFiniteEtale (X := ⟨_, isAdic_presentationLimitPreAdicSpace P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP' hsheaf⟩) (Y := ⟨_, hA⟩)
      (ObjectProperty.homMk (presentationLimitPreAdicSpaceComap φ.toRingHom
        φ.continuous_toRingHom φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf)) := by
  refine fun _ ↦ ⟨⊤, trivial, A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, S, P, hP, B, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, T, P', hP', φ, hφ,
    hsheaf, restrictTopIso _,
    restrictIsoOfRangeEq _ _ (Opens.isOpenEmbedding ⊤) ?_ ≪≫ restrictTopIso _, ?_⟩
  · rw [Opens.map_top]
  · simp only [Iso.trans_hom, Category.assoc, restrictIsoOfRangeEq_hom_ofRestrict_assoc,
      restrictTopIso_hom, ObjectProperty.homMk_hom]
    simp [← restrictTopIso_hom]

/-- Precomposing a finite étale morphism with an isomorphism gives a finite étale morphism: over
the same neighbourhoods, `e` identifies the restrictions of the two sources. -/
private theorem IsFiniteEtale.iso_hom_comp {X' : AdicSpace.{u}} (e : X' ≅ X) {f : X ⟶ Y}
    (hf : IsFiniteEtale f) : IsFiniteEtale (e.hom ≫ f) := by
  intro y
  obtain ⟨V, hy, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eV, eU, hfac⟩ := hf y
  let e' : X'.obj ≅ X.obj := (ObjectProperty.ι _).mapIso e
  -- `e⁻¹((e.hom ≫ f)⁻¹(V)) = f⁻¹(V)`
  have key := Opens.map_inv_obj_map_hom_obj (forgetToTop.mapIso e') ((Opens.map f.hom.base).obj V)
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, forgetToTop_map] at key
  have hr : Set.range
      ((Opens.map e'.inv.base).obj ((Opens.map (e.hom ≫ f).hom.base).obj V)).inclusion' =
        Set.range ((Opens.map f.hom.base).obj V).inclusion' := by
    rw [Opens.set_range_inclusion', Opens.set_range_inclusion']
    exact congrArg SetLike.coe key
  refine ⟨V, hy, A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, S, P, hP, B, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, T, P', hP', φ, hφ, hsheaf, eV,
    restrictIso e' _ ≪≫
      restrictIsoOfRangeEq _ (Opens.isOpenEmbedding _) (Opens.isOpenEmbedding _) hr ≪≫ eU, ?_⟩
  simp only [Iso.trans_hom, Category.assoc, ← hfac, restrictIsoOfRangeEq_hom_ofRestrict_assoc,
    restrictIso_hom_ofRestrict_assoc]
  simp [e']

/-- Postcomposing a finite étale morphism with an isomorphism `e : Y ≅ Y'` gives a finite étale
morphism: `e` carries the neighbourhoods of the definition to neighbourhoods in `Y'`, identifying
the restrictions of `Y` and `Y'` to them. -/
private theorem IsFiniteEtale.comp_iso_hom {Y' : AdicSpace.{u}} (e : Y ≅ Y') {f : X ⟶ Y}
    (hf : IsFiniteEtale f) : IsFiniteEtale (f ≫ e.hom) := by
  intro y
  let e' : Y.obj ≅ Y'.obj := (ObjectProperty.ι _).mapIso e
  obtain ⟨V, hy, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eV, eU, hfac⟩ := hf (e'.inv.base y)
  -- `(f ≫ e.hom)⁻¹(e(V)) = f⁻¹(V)`
  have key := Opens.map_hom_obj_map_inv_obj (forgetToTop.mapIso e') V
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, forgetToTop_map] at key
  have hr : Set.range
      ((Opens.map (f ≫ e.hom).hom.base).obj ((Opens.map e'.inv.base).obj V)).inclusion' =
        Set.range ((Opens.map f.hom.base).obj V).inclusion' := by
    rw [Opens.set_range_inclusion', Opens.set_range_inclusion']
    exact congrArg (fun U ↦ ((Opens.map f.hom.base).obj U : Set X.obj)) key
  refine ⟨(Opens.map e'.inv.base).obj V, hy, A, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP, B, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, T, P',
    hP', φ, hφ, hsheaf, (restrictIso e' V).symm ≪≫ eV,
    restrictIsoOfRangeEq _ (Opens.isOpenEmbedding _) (Opens.isOpenEmbedding _) hr ≪≫ eU, ?_⟩
  rw [← restrictIsoOfRangeEq_hom_ofRestrict X.obj (Opens.isOpenEmbedding _)
    (Opens.isOpenEmbedding _) hr, Category.assoc]
  simp [e', reassoc_of% hfac]

/-- **Being finite étale is invariant under isomorphisms** of the source and of the target. -/
instance IsFiniteEtale.respectsIso : MorphismProperty.RespectsIso @IsFiniteEtale.{u} :=
  MorphismProperty.RespectsIso.mk _ (fun e _ hf ↦ hf.iso_hom_comp e)
    (fun e _ hf ↦ hf.comp_iso_hom e)

/-- **The identity of an analytic adic space is finite étale**: every point has an open Tate
affinoid neighbourhood `Spa(A, A⁺)`, over which the identity is the morphism induced by the
identity of `(A, A⁺)`, a finite étale morphism of Huber pairs. Analyticity is necessary, since the
target of a finite étale morphism is analytic
(`TauCeti.AdicSpace.IsFiniteEtale.isAnalytic_target`). -/
theorem isFiniteEtale_id (hX : X.IsAnalytic) : IsFiniteEtale (𝟙 X) := fun y ↦ by
  obtain ⟨V, hV, hyV⟩ := isAnalytic_iff.mp hX y
  obtain ⟨A, _, _, _, _, _, _, _, S, P, hP, ⟨eV⟩⟩ :=
    (isTateAffinoid_iff _).mp ((mem_propOpens_iff _).mp hV)
  have hsheaf := (isSheafy_presentationLimitPreAdicSpace_iff P S.plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem hP).mp
      (ObjectProperty.prop_of_iso isSheafy eV
        (isSheafy_restrict V.isOpenEmbedding X.property.isSheafy))
  refine ⟨V, hyV, A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, S, P, hP, A, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP, Pair.Hom.id S,
    Pair.Hom.isFiniteEtale_id S, hsheaf, eV,
    restrictIsoOfRangeEq _ (Opens.isOpenEmbedding _) V.isOpenEmbedding ?_ ≪≫ eV, ?_⟩
  · -- the preimage of `V` under the identity is `V`, by definition of `Opens.map`
    rw [Opens.set_range_inclusion', Opens.set_range_inclusion']
    rfl
  · simpa using (restrictIsoOfRangeEq_hom_ofRestrict X.obj _ _ _).symm

/-- **Isomorphisms onto analytic adic spaces are finite étale.** -/
theorem isFiniteEtale_of_isIso (f : X ⟶ Y) [IsIso f] (hY : Y.IsAnalytic) : IsFiniteEtale f := by
  simpa using MorphismProperty.RespectsIso.precomp @IsFiniteEtale.{u} f (𝟙 Y)
    (isFiniteEtale_id hY)

end AdicSpace

end TauCeti
