/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Basic
public import TauCeti.RingTheory.AdicRing.CompletedAway.Iterate

/-!
# Basic open subsets of the formal spectrum

Let `A` be an adic ring of finite ideal type and `f ∈ A`. The basic open set `D(f)` of the formal
spectrum `Spf A`, with the restriction of the structure sheaf, is the formal spectrum of the
completed localisation `A_{f}` (EGA I, Ch. I, 10.1.4). So every basic open subset of an affine
formal scheme is again an affine formal scheme, and the basic open sets form a basis of affine
formal opens.

On underlying spaces, pulling back open primes along the canonical map `A → A_{f}` is an open
embedding `Spf A_{f} → Spf A` with image `D(f)`: modulo an ideal of definition `I` it is the
open embedding `Spec ((A ⧸ I)_f) → Spec (A ⧸ I)`, because `A_{f} ⧸ I A_{f} ≃ (A ⧸ I)_f`. It carries
the basic open set `D(a)` of `Spf A_{f}`, for `a ∈ A`, onto `D(f a)`, and these sets form a basis of
`Spf A_{f}`. On them the sections of the two structure sheaves are the completed localisations
`A_{f a}` and `(A_{f})_{a}`, which are identified by
`TauCeti.AdicRing.CompletedAway.iterateEquiv` compatibly with the restriction maps.
Since both structure sheaves are sheaves and the comparison is an isomorphism on a basis, it extends
to an isomorphism of sheaves.

## Main definitions

* `TauCeti.FormalScheme.Spf.restrictBasicOpenIso`: the isomorphism of locally ringed spaces
  `(D(f), O_{Spf A}|_{D(f)}) ≅ Spf A_{f}`.
* `TauCeti.FormalScheme.Spf.basicOpenι`: the open immersion `Spf A_{f} → Spf A` with image `D(f)`.

## Main results

* `TauCeti.FormalScheme.Spf.isOpenEmbedding_comap_completedAway`,
  `TauCeti.FormalScheme.Spf.range_comap_completedAway`: the map `Spf A_{f} → Spf A` of
  underlying spaces is an open embedding with image `D(f)`.
* `TauCeti.FormalScheme.Spf.image_comap_completedAway_basicOpen`: it carries `D(a)` onto `D(f a)`.
* `TauCeti.FormalScheme.Spf.isBasis_basicOpen_algebraMap`: the sets `D(a)`, `a ∈ A`, form a basis
  of `Spf A_{f}`.
* `TauCeti.FormalScheme.Spf.basicOpenι_base`, `TauCeti.FormalScheme.Spf.basicOpenι_c_app`: the
  open immersion `Spf A_{f} → Spf A` on points and on sections over basic open sets.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, §10.1 (10.1.4).
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

namespace TauCeti.FormalScheme.Spf

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  (f : A)

/-- Modulo the ideal of definition `I`, the map `Spf A_{f} → Spf A` is the open embedding
`Spec ((A ⧸ I)_f) → Spec (A ⧸ I)`. -/
private theorem comap_completedAway_eq :
    ⇑(comap (algebraMap A (AdicRing.CompletedAway A f))
        (AdicRing.CompletedAway.continuous_algebraMap A f)) =
      (homeomorphSpecQuotient (is_ideal_adic_pow (IsAdicRing.ideal_spec A).2.1 one_pos)).symm ∘
        PrimeSpectrum.comap (algebraMap (A ⧸ IsAdicRing.ideal A ^ 1)
          (Localization.Away (Ideal.Quotient.mk (IsAdicRing.ideal A ^ 1) f))) ∘
        PrimeSpectrum.comap ((AdicRing.CompletedAway.quotientPowEquiv A f 1).symm : _ →+* _) ∘
        homeomorphSpecQuotient (is_ideal_adic_pow (AdicRing.CompletedAway.isAdic A f) one_pos) := by
  funext q
  obtain ⟨r, rfl⟩ := (homeomorphSpecQuotient
    (is_ideal_adic_pow (AdicRing.CompletedAway.isAdic A f) one_pos)).symm.surjective q
  apply Subtype.ext
  simp only [Function.comp_apply, Homeomorph.apply_symm_apply, coe_comap_apply,
    coe_homeomorphSpecQuotient_symm_apply, ← PrimeSpectrum.comap_comp_apply]
  congr 1
  ext a
  simp [IsScalarTower.algebraMap_apply A (A ⧸ IsAdicRing.ideal A ^ 1)]

/-- Pulling back open primes along `A → A_{f}` is an open embedding `Spf A_{f} → Spf A`. -/
theorem isOpenEmbedding_comap_completedAway :
    IsOpenEmbedding (comap (algebraMap A (AdicRing.CompletedAway A f))
      (AdicRing.CompletedAway.continuous_algebraMap A f)) := by
  rw [comap_completedAway_eq]
  exact (Homeomorph.isOpenEmbedding _).comp <|
    (PrimeSpectrum.localization_away_isOpenEmbedding _
      (Ideal.Quotient.mk (IsAdicRing.ideal A ^ 1) f)).comp <|
      (PrimeSpectrum.isHomeomorph_comap_of_bijective
        (AdicRing.CompletedAway.quotientPowEquiv A f 1).symm.bijective).isOpenEmbedding.comp
        (Homeomorph.isOpenEmbedding _)

/-- The image of the open embedding `Spf A_{f} → Spf A` is `D(f)`. -/
theorem range_comap_completedAway :
    Set.range (comap (algebraMap A (AdicRing.CompletedAway A f))
      (AdicRing.CompletedAway.continuous_algebraMap A f)) = basicOpen f := by
  rw [comap_completedAway_eq, Set.range_comp, Set.range_comp, Set.range_comp,
    Homeomorph.range_coe, Set.image_univ,
    (PrimeSpectrum.isHomeomorph_comap_of_bijective
        (AdicRing.CompletedAway.quotientPowEquiv A f 1).symm.bijective).surjective.range_eq,
    Set.image_univ, PrimeSpectrum.localization_away_comap_range _
      (Ideal.Quotient.mk (IsAdicRing.ideal A ^ 1) f), Homeomorph.image_symm]
  ext p
  simp [Ideal.mem_quotient_iff_mem ((mem_carrier_iff_le
    (is_ideal_adic_pow (IsAdicRing.ideal_spec A).2.1 one_pos)).mp p.2)]

/-- The open embedding `Spf A_{f} → Spf A` carries the basic open set `D(a)` of `Spf A_{f}`, for
`a ∈ A`, onto the basic open set `D(f a)` of `Spf A`. -/
theorem image_comap_completedAway_basicOpen (a : A) :
    comap (algebraMap A (AdicRing.CompletedAway A f))
        (AdicRing.CompletedAway.continuous_algebraMap A f) ''
      basicOpen (algebraMap A (AdicRing.CompletedAway A f) a) = basicOpen (f * a) := by
  rw [← comap_basicOpen _ (AdicRing.CompletedAway.continuous_algebraMap A f), Opens.coe_comap,
    Set.image_preimage_eq_inter_range, range_comap_completedAway, basicOpen_mul, inf_comm,
    Opens.coe_inf]

/-- The basic open sets `D(a)` of `Spf A_{f}` for `a ∈ A` form a basis of its topology. -/
theorem isBasis_basicOpen_algebraMap :
    Opens.IsBasis
      (Set.range fun a : A ↦ basicOpen (algebraMap A (AdicRing.CompletedAway A f) a)) := by
  convert isBasis_basicOpen.of_isInducing (isOpenEmbedding_comap_completedAway f).isInducing
    using 1
  ext V
  simp only [Set.mem_range, Set.mem_ofPred_eq, exists_exists_eq_and,
    ← comap_basicOpen _ (AdicRing.CompletedAway.continuous_algebraMap A f)]
  rfl

section Sheaf

/-- The inclusion `Spf A_{f} → Spf A` of underlying spaces, as a morphism of `TopCat`. -/
private noncomputable abbrev ι :
    TopCat.of (carrier (AdicRing.CompletedAway A f)) ⟶ TopCat.of (carrier A) :=
  TopCat.ofHom (comap (algebraMap A (AdicRing.CompletedAway A f))
    (AdicRing.CompletedAway.continuous_algebraMap A f))

private theorem isOpenEmbedding_ι : IsOpenEmbedding (ι f) :=
  isOpenEmbedding_comap_completedAway f

/-- The basic open sets `D(a)`, `a ∈ A`, of `Spf A_{f}`. -/
private noncomputable abbrev basis (a : A) : Opens (carrier (AdicRing.CompletedAway A f)) :=
  basicOpen (algebraMap A (AdicRing.CompletedAway A f) a)

private theorem functor_obj_basis (a : A) :
    (isOpenEmbedding_ι f).functor.obj (basis f a) = basicOpen (f * a) :=
  Opens.ext (image_comap_completedAway_basicOpen f a)

/-- On `D(a)`, the comparison of the sections of `O_{Spf A}` over the image `D(f a)` with the
sections of `O_{Spf A_{f}}`. -/
private noncomputable def basisApp (a : A) :
    (structureSheaf (IsAdicRing.ideal_spec A).2.1).obj.obj
        (op ((isOpenEmbedding_ι f).functor.obj (basis f a))) ⟶
      (structureSheaf (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).2.1).obj.obj
        (op (basis f a)) :=
  (structureSheaf (IsAdicRing.ideal_spec A).2.1).obj.map
      (eqToHom (congrArg op (functor_obj_basis f a))) ≫
    (basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 (f * a)).hom ≫
    (AdicRing.CompletedAway.iterateEquiv f a).symm.toCommRingCatIso.hom ≫
    (basicOpenSectionsIso (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).2.1
      (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).1 _).inv

/-- The comparisons on basic open sets commute with the restriction maps: both become restriction
maps of completed localisations, which `iterateEquiv` intertwines. -/
private theorem basisApp_naturality (a b : A) (hba : basis f b ≤ basis f a) :
    (structureSheaf (IsAdicRing.ideal_spec A).2.1).obj.map
        ((isOpenEmbedding_ι f).functor.map (homOfLE hba)).op ≫ basisApp f b =
      basisApp f a ≫
        (structureSheaf (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).2.1).obj.map
          (homOfLE hba).op := by
  have hfba : basicOpen (f * b) ≤ basicOpen (f * a) := by
    rw [← functor_obj_basis, ← functor_obj_basis]
    exact leOfHom ((isOpenEmbedding_ι f).functor.map (homOfLE hba))
  rw [← cancel_mono (basicOpenSectionsIso (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).2.1
    (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).1 _).hom]
  simp only [basisApp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  -- transport along `functor_obj_basis` turns the restriction from the image of `D(a)` to that of
  -- `D(b)` into the restriction from `D(f a)` to `D(f b)`; morphisms between opens are unique
  have hres : ((isOpenEmbedding_ι f).functor.map (homOfLE hba)).op ≫
        eqToHom (congrArg op (functor_obj_basis f b)) =
      eqToHom (congrArg op (functor_obj_basis f a)) ≫ (homOfLE hfba).op :=
    Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [map_comp_basicOpenSectionsIso_hom, Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc, hres,
    Functor.map_comp_assoc, map_comp_basicOpenSectionsIso_hom_assoc]
  congr 2
  ext x
  exact AdicRing.CompletedAway.iterateEquiv_symm_restrict f a _ _ x

/-- The comparisons on the basic open sets `D(a)`, `a ∈ A`, of `Spf A_{f}`. -/
private noncomputable def basisHom :
    (inducedFunctor (basis f)).op ⋙ ((Spf A).restrict (isOpenEmbedding_ι f)).presheaf ⟶
      (inducedFunctor (basis f)).op ⋙ (Spf (AdicRing.CompletedAway A f)).presheaf where
  app a := basisApp f a.unop
  naturality a b g := basisApp_naturality f a.unop b.unop (leOfHom g.unop.hom)

/-- The comparison `O_{Spf A}|_{D(f)} → O_{Spf A_{f}}` of sheaves on `Spf A_{f}`, extended from
the basic open sets `D(a)`. -/
private noncomputable def sheafHom :
    ((Spf A).restrict (isOpenEmbedding_ι f)).presheaf ⟶
      (Spf (AdicRing.CompletedAway A f)).presheaf :=
  TopCat.Sheaf.restrictHomEquivHom _ (structureSheaf _) (isBasis_basicOpen_algebraMap f)
    (basisHom f)

private theorem sheafHom_app_basis (a : A) :
    (sheafHom f).app (op (basis f a)) = basisApp f a :=
  TopCat.Sheaf.extend_hom_app _ _ _ (basisHom f) a

private instance : IsIso (sheafHom f) := by
  let F : TopCat.Sheaf CommRingCat (TopCat.of (carrier (AdicRing.CompletedAway A f))) :=
    ((Spf A).restrict (isOpenEmbedding_ι f)).sheaf
  let φ : F ⟶ structureSheaf (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).2.1 :=
    ObjectProperty.homMk (sheafHom f)
  -- the comparison is an isomorphism on every basic open set `D(a)`
  have : IsIso φ := TopCat.Sheaf.isIso_iff_isIso_basis (isBasis_basicOpen_algebraMap f) fun a ↦ by
    have : IsIso (basisApp f a) := by unfold basisApp; infer_instance
    exact ((sheafHom_app_basis f a).symm ▸ inferInstanceAs (IsIso (basisApp f a)) :
      IsIso ((sheafHom f).app (op (basis f a))))
  exact inferInstanceAs (IsIso ((sheafToPresheaf _ _).map φ))

private noncomputable def sheafIso :
    ((Spf A).restrict (isOpenEmbedding_ι f)).presheaf ≅
      (Spf (AdicRing.CompletedAway A f)).presheaf :=
  asIso (sheafHom f)

/-- `Spf A_{f}` is the restriction of `Spf A` along the open embedding `Spf A_{f} → Spf A`. -/
private noncomputable def restrictIsoAux :
    Spf (AdicRing.CompletedAway A f) ≅ (Spf A).restrict (isOpenEmbedding_ι f) :=
  LocallyRingedSpace.isoOfSheafedSpaceIso <| SheafedSpace.isoMk <|
    PresheafedSpace.isoOfComponents (Iso.refl _) (sheafIso f).symm

end Sheaf

/-- **The basic open set `D(f)` of `Spf A` is `Spf A_{f}`**: the restriction of the locally ringed
space `Spf A` to `D(f)` is isomorphic to the formal spectrum of the completed localisation
`A_{f}` (EGA I, Ch. I, 10.1.4). -/
noncomputable def restrictBasicOpenIso :
    (Spf A).restrict (basicOpen f : Opens (Spf A).toTopCat).isOpenEmbedding ≅
      Spf (AdicRing.CompletedAway A f) :=
  -- the two restrictions along open embeddings with image `D(f)` agree; the open-immersion
  -- instances are passed explicitly because the targets of the embeddings are `Spf A` only after
  -- unfolding `Spf`, which instance search does not do
  (restrictIsoAux f ≪≫ LocallyRingedSpace.isoOfSheafedSpaceIso (SheafedSpace.isoMk
    (@PresheafedSpace.IsOpenImmersion.isoOfRangeEq _ _ _ _ _
      ((Spf A).toPresheafedSpace.ofRestrict (isOpenEmbedding_ι f))
      (PresheafedSpace.IsOpenImmersion.ofRestrict _ _)
      ((Spf A).toPresheafedSpace.ofRestrict
        (basicOpen f : Opens (Spf A).toTopCat).isOpenEmbedding)
      (PresheafedSpace.IsOpenImmersion.ofRestrict _ _)
      (by exact (range_comap_completedAway f).trans Subtype.range_coe.symm)))).symm

/-- The sheaf component of `restrictIsoAux` is, by its construction from `isoOfComponents`, the
comparison `sheafHom`. -/
private theorem restrictIsoAux_hom_c_app (V) :
    (restrictIsoAux f).hom.c.app V = (sheafHom f).app V :=
  rfl

/-- The open immersion `Spf A_{f} → Spf A` with image `D(f)`: the isomorphism
`restrictBasicOpenIso` followed by the inclusion of `D(f)`. -/
noncomputable def basicOpenι : Spf (AdicRing.CompletedAway A f) ⟶ Spf A :=
  (restrictBasicOpenIso f).inv ≫
    (Spf A).ofRestrict (basicOpen f : Opens (Spf A).toTopCat).isOpenEmbedding

/-- The inverse of `restrictBasicOpenIso` followed by the inclusion of `D(f)` is the open immersion
`basicOpenι f`. -/
@[reassoc (attr := simp)]
theorem restrictBasicOpenIso_inv_ofRestrict :
    (restrictBasicOpenIso f).inv ≫
        (Spf A).ofRestrict (basicOpen f : Opens (Spf A).toTopCat).isOpenEmbedding =
      basicOpenι f :=
  (rfl)

/-- The morphism `basicOpenι f` is an open immersion. -/
instance isOpenImmersion_basicOpenι : LocallyRingedSpace.IsOpenImmersion (basicOpenι f) := by
  unfold basicOpenι
  infer_instance

/-- The open immersion `Spf A_{f} → Spf A` is the comparison isomorphism followed by the inclusion
along the open embedding of underlying spaces. -/
private theorem basicOpenι_eq :
    basicOpenι f = (restrictIsoAux f).hom ≫ (Spf A).ofRestrict (isOpenEmbedding_ι f) := by
  rw [basicOpenι, restrictBasicOpenIso, Iso.symm_inv, Iso.trans_hom, Category.assoc]
  refine congrArg ((restrictIsoAux f).hom ≫ ·) (LocallyRingedSpace.Hom.ext' ?_)
  simp only [LocallyRingedSpace.isoOfSheafedSpaceIso, LocallyRingedSpace.ofRestrict,
    LocallyRingedSpace.comp_toHom, LocallyRingedSpace.homOfSheafedSpaceHomOfIsIso_toHom,
    SheafedSpace.isoMk_hom, InducedCategory.homMk_hom]
  exact @PresheafedSpace.IsOpenImmersion.lift_fac _ _ _ _ _ _
    (PresheafedSpace.IsOpenImmersion.ofRestrict _ _) _
    (by exact (Subtype.range_coe.trans (range_comap_completedAway f).symm).ge)

/-- On underlying spaces, the open immersion `Spf A_{f} → Spf A` is the map `q ↦ q ∩ A` of open
primes. -/
@[simp]
theorem basicOpenι_base :
    (basicOpenι f).base = TopCat.ofHom (comap (algebraMap A (AdicRing.CompletedAway A f))
      (AdicRing.CompletedAway.continuous_algebraMap A f)) := by
  rw [basicOpenι_eq, LocallyRingedSpace.comp_base]
  exact Category.id_comp _

/-- The preimage of the basic open set `D(a)` of `Spf A` under the open immersion
`Spf A_{f} → Spf A` is the basic open set of `Spf A_{f}` defined by the image of `a`. -/
theorem basicOpenι_preimage_basicOpen (a : A) :
    (Opens.map (basicOpenι f).base).obj (basicOpen a) =
      basicOpen (algebraMap A (AdicRing.CompletedAway A f) a) := by
  rw [basicOpenι_base]
  exact comap_basicOpen _ _ a

/-- On sections over `D(a)`, the open immersion `Spf A_{f} → Spf A` is the restriction to
`D(f a)` followed by the isomorphism `A_{f a} ≃ (A_{f})_{a}` of completed localisations. -/
theorem basicOpenι_c_app (a : A) :
    (basicOpenι f).c.app (op (basicOpen a)) ≫
        (Spf (AdicRing.CompletedAway A f)).presheaf.map
          (eqToHom (congrArg op (basicOpenι_preimage_basicOpen f a))) ≫
        (basicOpenSectionsIso (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).2.1
          (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).1
            (algebraMap A (AdicRing.CompletedAway A f) a)).hom =
      (Spf A).presheaf.map (homOfLE ((basicOpen_mul f a).le.trans inf_le_right) :
          basicOpen (f * a) ⟶ basicOpen a).op ≫
        (basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1
          (f * a)).hom ≫
        (AdicRing.CompletedAway.iterateEquiv f a).symm.toCommRingCatIso.hom := by
  rw [PresheafedSpace.congr_app (congrArg LocallyRingedSpace.Hom.toHom (basicOpenι_eq f))
    (op (basicOpen a))]
  simp only [Category.assoc]
  -- `erw` is needed because the presheaf of `Spf A` is the structure sheaf only after unfolding
  -- `Spf`, so the rewritten terms are type-correct only up to that unfolding. Move to the basic
  -- open set `D(a)` of `Spf A_{f}`, where the sheaf comparison is `basisApp`.
  erw [← Functor.map_comp_assoc, eqToHom_trans, LocallyRingedSpace.comp_c_app, Category.assoc,
    restrictIsoAux_hom_c_app, ← (sheafHom f).naturality_assoc, sheafHom_app_basis]
  simp only [basisApp, LocallyRingedSpace.ofRestrict]
  -- what remains are restriction maps of `O_{Spf A}` from `D(a)` to `D(f a)`, which agree
  erw [Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  exact congrArg (fun i ↦ (Spf A).presheaf.map i ≫ _) (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

end TauCeti.FormalScheme.Spf
