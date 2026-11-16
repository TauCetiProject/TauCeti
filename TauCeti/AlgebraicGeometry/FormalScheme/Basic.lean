/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Restrict
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Discrete
public import Mathlib.AlgebraicGeometry.Scheme
public import TauCeti.Geometry.RingedSpace.OpenImmersion

/-!
# Formal schemes of finite ideal type

A formal scheme is a locally ringed space covered by open formal spectra of complete
separated adic rings with a finitely generated ideal of definition. No noetherian
hypothesis is imposed. Its morphisms are the morphisms of the underlying locally ringed
spaces; no topology on sections is added to the carrier.

We construct the category, its fully faithful forgetful functor, affine formal schemes,
and the fully faithful inclusion of ordinary schemes. Completed localization supplies
arbitrarily small affine formal neighbourhoods, so open restrictions are formal schemes.
These constructions provide the carrier on which ideals and thickenings can be defined.

The category construction follows Mathlib's `AlgebraicGeometry.Scheme`, using
`CategoryTheory.InducedCategory` for the morphisms.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*,
  Ch. I, 10.4.2–10.4.4 and 10.4.8.
-/

public section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace TauCeti

/-- A formal scheme of finite ideal type: a locally ringed space covered by open formal
spectra of complete separated adic rings admitting finitely generated ideals of definition.
The atlas is a property, not a choice of charts. -/
structure FormalScheme extends LocallyRingedSpace.{u} where
  local_spf : ∀ x : toLocallyRingedSpace,
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsAdicRing A) (f : FormalScheme.Spf A ⟶ toLocallyRingedSpace),
      LocallyRingedSpace.IsOpenImmersion f ∧ x ∈ Set.range f.base

namespace FormalScheme

instance : CoeSort FormalScheme Type* := ⟨fun X ↦ X.toLocallyRingedSpace⟩

instance (X : FormalScheme) : TopologicalSpace X :=
  inferInstanceAs (TopologicalSpace X.toLocallyRingedSpace)

/-- Formal schemes have exactly the morphisms of their underlying locally ringed spaces. -/
instance : Category FormalScheme :=
  inferInstanceAs (Category (InducedCategory LocallyRingedSpace toLocallyRingedSpace))

/-- Forget the formal atlas, retaining the locally ringed space and all its morphisms.
The body is exposed so the types of its morphisms use the original locally ringed spaces. -/
@[expose] def forgetToLocallyRingedSpace : FormalScheme ⥤ LocallyRingedSpace :=
  inducedFunctor toLocallyRingedSpace

@[simp]
theorem forgetToLocallyRingedSpace_obj (X : FormalScheme) :
    forgetToLocallyRingedSpace.obj X = X.toLocallyRingedSpace := (rfl)

-- Keep this rewrite explicit so it does not preempt the specialized simp lemmas below.
theorem forgetToLocallyRingedSpace_map {X Y : FormalScheme} (f : X ⟶ Y) :
    forgetToLocallyRingedSpace.map f = f.hom := (rfl)

/-- The formal-scheme category is a full subcategory of locally ringed spaces. -/
def fullyFaithfulForgetToLocallyRingedSpace : forgetToLocallyRingedSpace.FullyFaithful :=
  fullyFaithfulInducedFunctor toLocallyRingedSpace

instance : forgetToLocallyRingedSpace.Full :=
  fullyFaithfulForgetToLocallyRingedSpace.full

instance : forgetToLocallyRingedSpace.Faithful :=
  fullyFaithfulForgetToLocallyRingedSpace.faithful

/-- The formal spectrum with its affine formal atlas.
The carrier is exposed so the opens and points of `Spf A` apply directly to `ofSpf A`. -/
@[expose] noncomputable def ofSpf (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] : FormalScheme where
  toLocallyRingedSpace := Spf A
  local_spf x := ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    𝟙 _, inferInstance, x, rfl⟩

@[simp]
theorem ofSpf_toLocallyRingedSpace (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    (ofSpf A).toLocallyRingedSpace = Spf A := (rfl)

/-- An open is affine formal if it is the image of an open immersion from a formal spectrum.
This definition does not choose a presentation or a topology on its ring of sections. -/
def IsAffineOpen (X : FormalScheme) (U : Opens X) : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
    (_ : IsAdicRing A) (f : Spf A ⟶ X.toLocallyRingedSpace),
    LocallyRingedSpace.IsOpenImmersion f ∧ Set.range f.base = (U : Set X)

/-- An open is affine formal exactly when its restricted locally ringed space is isomorphic
to a formal spectrum. -/
theorem isAffineOpen_iff (X : FormalScheme) (U : Opens X) :
    X.IsAffineOpen U ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
        (_ : IsAdicRing A),
        Nonempty (X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf A) := by
  constructor
  · rintro ⟨A, _, _, _, _, f, hf, hrange⟩
    have := hf
    let j := X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
    have : LocallyRingedSpace.IsOpenImmersion j := inferInstance
    refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
    exact (LocallyRingedSpace.isoOfSheafedSpaceIso <| SheafedSpace.isoMk <|
      PresheafedSpace.IsOpenImmersion.isoOfRangeEq f.toHom j.toHom
        (hrange.trans Subtype.range_coe.symm)).symm
  · rintro ⟨A, _, _, _, _, ⟨e⟩⟩
    let j := X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
    have : LocallyRingedSpace.IsOpenImmersion j := inferInstance
    refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
      e.inv ≫ j, inferInstance, ?_⟩
    exact (LocallyRingedSpace.range_iso_inv_comp e j).trans
      Subtype.range_coe

/-- Every formal spectrum is an affine formal open in itself. -/
@[simp]
theorem isAffineOpen_top_ofSpf (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] : IsAffineOpen (ofSpf A) ⊤ :=
  ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, 𝟙 _,
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (𝟙 (Spf A))), Set.range_id⟩

/-- Every neighbourhood contains a formal-spectrum chart through the given point. -/
theorem exists_spf_mem_range_and_range_subset (X : FormalScheme) (U : Opens X)
    (x : X) (hx : x ∈ U) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsAdicRing A) (f : Spf A ⟶ X.toLocallyRingedSpace),
      LocallyRingedSpace.IsOpenImmersion f ∧ x ∈ Set.range f.base ∧
        Set.range f.base ⊆ (U : Set X) := by
  obtain ⟨A, _, _, _, _, i, hi, y, hy⟩ := X.local_spf x
  have := hi
  -- The explicit preimage open tells the basis lemma which neighbourhood to shrink;
  -- membership in `Opens.map` is membership of the image point, where `hy` applies.
  obtain ⟨V, ⟨a, rfl⟩, hyV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp Spf.isBasis_basicOpen)
    (show y ∈ (Opens.map i.base).obj U from
      (congrArg (fun z ↦ z ∈ U) hy).mpr hx)
  obtain ⟨z, hz⟩ := (Spf.range_basicOpenι a).ge hyV
  refine ⟨AdicRing.CompletedAway A a, inferInstance, inferInstance, inferInstance,
    inferInstance, Spf.basicOpenι a ≫ i, inferInstance, ⟨z, ?_⟩, ?_⟩
  · simpa only [LocallyRingedSpace.comp_base, TopCat.coe_comp, Function.comp_apply, hz] using hy
  · rintro _ ⟨w, rfl⟩
    exact hVU ((Spf.range_basicOpenι a).le (Set.mem_range_self w))

/-- The affine formal opens form a basis of the topology. -/
theorem isBasis_affineOpens (X : FormalScheme) :
    Opens.IsBasis {U : Opens X | X.IsAffineOpen U} := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨A, _, _, _, _, f, hf, hx, hU⟩ := X.exists_spf_mem_range_and_range_subset U x hx
  exact ⟨⟨Set.range f.base, hf.base_open.isOpen_range⟩,
    ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, f, hf, rfl⟩, hx, hU⟩

/-- Restrict a formal scheme to an open subset, using the restriction of its locally ringed
space. The affine atlas is obtained by shrinking charts using completed localizations.
The carrier is exposed so the underlying restriction morphisms retain their types. -/
@[expose] noncomputable def restrict (X : FormalScheme) (U : Opens X) : FormalScheme where
  toLocallyRingedSpace := X.toLocallyRingedSpace.restrict U.isOpenEmbedding
  local_spf x := by
    obtain ⟨A, _, _, _, _, f, hf, hx, hU⟩ :=
      X.exists_spf_mem_range_and_range_subset U x.val x.property
    have := hf
    let j := X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
    have hj : LocallyRingedSpace.IsOpenImmersion j := inferInstance
    have hfj : Set.range f.base ⊆ Set.range j.base := by
      intro z hz
      exact ⟨⟨z, hU hz⟩, rfl⟩
    let g := LocallyRingedSpace.IsOpenImmersion.lift j f hfj
    have hg : LocallyRingedSpace.IsOpenImmersion g :=
      LocallyRingedSpace.IsOpenImmersion.isOpenImmersion_lift j f hfj
    refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, g, hg, ?_⟩
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, Subtype.ext ?_⟩
    have h := congrArg (fun t : Spf A ⟶ X.toLocallyRingedSpace ↦ t.base y)
      (LocallyRingedSpace.IsOpenImmersion.lift_fac j f hfj)
    exact h.trans hy

@[simp]
theorem restrict_toLocallyRingedSpace (X : FormalScheme) (U : Opens X) :
    (X.restrict U).toLocallyRingedSpace =
      X.toLocallyRingedSpace.restrict U.isOpenEmbedding := (rfl)

/-- The inclusion of an open formal subscheme. -/
noncomputable def ofRestrict (X : FormalScheme) (U : Opens X) : X.restrict U ⟶ X :=
  InducedCategory.homMk (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding)

-- Keep this rewrite explicit so `range_ofRestrict` remains in simp normal form.
theorem forgetToLocallyRingedSpace_map_ofRestrict (X : FormalScheme) (U : Opens X) :
    forgetToLocallyRingedSpace.map (X.ofRestrict U) =
      X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding := (rfl)

/-- The underlying inclusion of an open formal subscheme is an open immersion. -/
instance (X : FormalScheme) (U : Opens X) :
    LocallyRingedSpace.IsOpenImmersion (forgetToLocallyRingedSpace.map (X.ofRestrict U)) :=
  inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
    (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding))

/-- The image of the inclusion of an open formal subscheme is precisely that open. -/
@[simp]
theorem range_ofRestrict (X : FormalScheme) (U : Opens X) :
    Set.range (forgetToLocallyRingedSpace.map (X.ofRestrict U)).base = (U : Set X) :=
  Subtype.range_coe

/-- Restricting to the full open does not change a formal scheme. -/
noncomputable def restrictTopIso (X : FormalScheme) : X.restrict ⊤ ≅ X :=
  InducedCategory.isoMk X.toLocallyRingedSpace.restrictTopIso

@[simp]
theorem restrictTopIso_hom (X : FormalScheme) :
    X.restrictTopIso.hom = X.ofRestrict ⊤ := (rfl)

@[simp]
theorem forgetToLocallyRingedSpace_map_restrictTopIso_inv (X : FormalScheme) :
    forgetToLocallyRingedSpace.map X.restrictTopIso.inv =
      X.toLocallyRingedSpace.restrictTopIso.inv := (rfl)

/-- The restriction of an affine formal scheme to `D(f)` is the formal spectrum of its
completed localization. -/
noncomputable def restrictBasicOpenIso (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (f : A) :
    (ofSpf A).restrict (Spf.basicOpen f) ≅ ofSpf (AdicRing.CompletedAway A f) :=
  InducedCategory.isoMk (Spf.restrictBasicOpenIso f)

@[simp]
theorem forgetToLocallyRingedSpace_map_restrictBasicOpenIso_hom (A : Type u)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] (f : A) :
    forgetToLocallyRingedSpace.map (restrictBasicOpenIso A f).hom =
      (Spf.restrictBasicOpenIso f).hom := (rfl)

@[simp]
theorem forgetToLocallyRingedSpace_map_restrictBasicOpenIso_inv (A : Type u)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] (f : A) :
    forgetToLocallyRingedSpace.map (restrictBasicOpenIso A f).inv =
      (Spf.restrictBasicOpenIso f).inv := (rfl)

/-- The completed-localization comparison factors the inclusion of the basic open. -/
@[reassoc (attr := simp)]
theorem restrictBasicOpenIso_inv_ofRestrict (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (f : A) :
    (restrictBasicOpenIso A f).inv ≫ (ofSpf A).ofRestrict (Spf.basicOpen f) =
      InducedCategory.homMk (Spf.basicOpenι f) :=
  InducedCategory.hom_ext (Spf.restrictBasicOpenIso_inv_ofRestrict f)

/-- Every basic open in a formal spectrum is affine formal. -/
@[simp]
theorem isAffineOpen_basicOpen (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (f : A) :
    IsAffineOpen (ofSpf A) (Spf.basicOpen f) := by
  exact ⟨AdicRing.CompletedAway A f, inferInstance, inferInstance, inferInstance,
    inferInstance, Spf.basicOpenι f,
    Spf.isOpenImmersion_basicOpenι f, Spf.range_basicOpenι f⟩

instance (X : FormalScheme) : Subsingleton (X.presheaf.obj (Opposite.op (⊥ : Opens X))) :=
  CommRingCat.subsingleton_of_isTerminal X.sheaf.isTerminalOfEmpty

/-- Every affine formal scheme `ofSpf A` has a quasi-compact underlying space. -/
instance compactSpace_ofSpf (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] : CompactSpace (ofSpf A) :=
  Spf.compactSpace_carrier (IsAdicRing.ideal_spec A).2.1

/-- Every affine formal open of a formal scheme is quasi-compact. -/
theorem IsAffineOpen.isCompact {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    IsCompact (U : Set X) := by
  obtain ⟨A, _, _, _, _, ⟨e⟩⟩ := (isAffineOpen_iff X U).mp hU
  have : CompactSpace (LocallyRingedSpace.forgetToTop.obj (Spf A)) :=
    Spf.compactSpace_carrier (IsAdicRing.ideal_spec A).2.1
  have : CompactSpace U :=
    (TopCat.homeoOfIso (LocallyRingedSpace.forgetToTop.mapIso e)).symm.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

/-- The affine formal opens of `X` cover `X`. -/
theorem iSup_affineOpens_eq_top (X : FormalScheme) :
    (⨆ U : {U : Opens X // X.IsAffineOpen U}, U.1) = ⊤ :=
  eq_top_iff.mpr fun x _ ↦ by
    obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (Opens.mem_top x)
    exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hx⟩

/-- Every quasi-compact formal scheme admits a finite cover by affine formal opens. -/
theorem exists_finite_affine_cover (X : FormalScheme) [CompactSpace X] :
    ∃ (n : ℕ) (U : Fin n → Opens X), (∀ i, X.IsAffineOpen (U i)) ∧ ⨆ i, U i = ⊤ := by
  classical
  obtain ⟨Us, hsub, hfin, htop⟩ :=
    X.isBasis_affineOpens.exists_finite_of_isCompact (U := ⊤) isCompact_univ
  let e := hfin.toFinset.equivFin
  refine ⟨_, fun i ↦ (e.symm i).1, fun i ↦ hsub (hfin.mem_toFinset.mp (e.symm i).2),
    eq_top_iff.mpr fun x _ ↦ ?_⟩
  obtain ⟨V, hV, hxV⟩ := Opens.mem_sSup.mp (htop ▸ Opens.mem_top x)
  exact Opens.mem_iSup.mpr ⟨e ⟨V, hfin.mem_toFinset.mpr hV⟩, by simpa using hxV⟩

/-- An affine formal open `U` of `X` makes `⊤` an affine formal open of `X.restrict U`. -/
theorem IsAffineOpen.top_restrict {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    (X.restrict U).IsAffineOpen ⊤ := by
  obtain ⟨A, _, _, _, _, ⟨e⟩⟩ := (isAffineOpen_iff X U).mp hU
  rw [isAffineOpen_iff]
  exact ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨(X.restrict U).toLocallyRingedSpace.restrictTopIso ≪≫ e⟩⟩

/-- Sections over `⊤` on the open restriction `X.restrict U` agree with sections of `X` over `U`. -/
noncomputable def restrictTopSectionsIso (X : FormalScheme) (U : Opens X) :
    (X.restrict U).presheaf.obj (Opposite.op ⊤) ≅ X.presheaf.obj (Opposite.op U) :=
  X.presheaf.mapIso (eqToIso (congrArg Opposite.op (Opens.isOpenEmbedding_obj_top U)))

-- Keep `_hom` and `_inv` explicit so `@[simp]` lemmas on `restrictTopSectionsIso` are not
-- preempted.
theorem restrictTopSectionsIso_hom (X : FormalScheme) (U : Opens X) :
    (restrictTopSectionsIso X U).hom =
      X.presheaf.map (eqToHom (congrArg Opposite.op (Opens.isOpenEmbedding_obj_top U))) :=
  (rfl)

theorem restrictTopSectionsIso_inv (X : FormalScheme) (U : Opens X) :
    (restrictTopSectionsIso X U).inv =
      X.presheaf.map (eqToHom (congrArg Opposite.op (Opens.isOpenEmbedding_obj_top U)).symm) :=
  (rfl)

/-- On global sections, `X.ofRestrict U` followed by `restrictTopSectionsIso X U` is the
presheaf restriction from `⊤` to `U`. -/
@[reassoc (attr := simp)]
theorem ofRestrict_c_app_top_comp_restrictTopSectionsIso_hom (X : FormalScheme) (U : Opens X) :
    (forgetToLocallyRingedSpace.map (X.ofRestrict U)).c.app (Opposite.op ⊤) ≫
        (restrictTopSectionsIso X U).hom =
      X.presheaf.map (homOfLE le_top).op := by
  have hjc : (forgetToLocallyRingedSpace.map (X.ofRestrict U)).c.app (Opposite.op ⊤) =
      (X.toPresheafedSpace.ofRestrict U.isOpenEmbedding).c.app (Opposite.op ⊤) := rfl
  rw [hjc, PresheafedSpace.ofRestrict_c_app, restrictTopSectionsIso_hom]
  exact (X.presheaf.map_comp _ _).symm.trans (congrArg X.presheaf.map (Subsingleton.elim _ _))

/-- Global sections of `ofSpf A` are isomorphic to `A`. This wraps `Spf.globalSectionsIso` with
syntactic source `(ofSpf A).presheaf.obj (op ⊤)`. -/
noncomputable def ofSpfGlobalSectionsIso (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    (ofSpf A).presheaf.obj (Opposite.op ⊤) ≅ CommRingCat.of A :=
  haveI := (IsAdicRing.ideal_spec A).2.2
  Spf.globalSectionsIso (IsAdicRing.ideal_spec A).2.1

-- Keep these bridge lemmas explicit so `@[simp]` lemmas on `ofSpfGlobalSectionsIso` (such as
-- `IsAffineOpen.isoSpf_inv_globalSections`) remain in simp normal form.
theorem ofSpfGlobalSectionsIso_eq (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    have := (IsAdicRing.ideal_spec A).2.2
    ofSpfGlobalSectionsIso A = Spf.globalSectionsIso (IsAdicRing.ideal_spec A).2.1 :=
  (rfl)

theorem ofSpfGlobalSectionsIso_hom (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    have := (IsAdicRing.ideal_spec A).2.2
    (ofSpfGlobalSectionsIso A).hom = (Spf.globalSectionsIso (IsAdicRing.ideal_spec A).2.1).hom :=
  (rfl)

theorem ofSpfGlobalSectionsIso_inv (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    have := (IsAdicRing.ideal_spec A).2.2
    (ofSpfGlobalSectionsIso A).inv = (Spf.globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv :=
  (rfl)

/-- Being an affine formal scheme (`IsAffineOpen ⊤`) is preserved under isomorphism. -/
theorem isAffineOpen_top_of_iso {X Y : FormalScheme} (e : X ≅ Y) (hX : X.IsAffineOpen ⊤) :
    Y.IsAffineOpen ⊤ := by
  obtain ⟨A, _, _, _, _, ⟨eA⟩⟩ := (isAffineOpen_iff X ⊤).mp hX
  let eRestr : Y.restrict ⊤ ≅ X.restrict ⊤ := Y.restrictTopIso ≪≫ e.symm ≪≫ X.restrictTopIso.symm
  exact (isAffineOpen_iff Y ⊤).mpr
    ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
      ⟨forgetToLocallyRingedSpace.mapIso eRestr ≪≫ eA⟩⟩

/-- Two isomorphic formal schemes have `⊤` affine simultaneously. -/
theorem isAffineOpen_top_iff_of_iso {X Y : FormalScheme} (e : X ≅ Y) :
    X.IsAffineOpen ⊤ ↔ Y.IsAffineOpen ⊤ :=
  ⟨isAffineOpen_top_of_iso e, isAffineOpen_top_of_iso e.symm⟩

/-- The isomorphism on global sections `Γ(Y, O_Y) ≅ Γ(X, O_X)` induced by an isomorphism
`e : X ≅ Y` of formal schemes. -/
noncomputable def globalSectionsIsoOfIso {X Y : FormalScheme} (e : X ≅ Y) :
    Y.presheaf.obj (Opposite.op ⊤) ≅ X.presheaf.obj (Opposite.op ⊤) :=
  LocallyRingedSpace.Γ.mapIso (forgetToLocallyRingedSpace.mapIso e).op

@[simp]
theorem globalSectionsIsoOfIso_hom {X Y : FormalScheme} (e : X ≅ Y) :
    (globalSectionsIsoOfIso e).hom =
      (forgetToLocallyRingedSpace.map e.hom).c.app (Opposite.op ⊤) :=
  (rfl)

@[simp]
theorem globalSectionsIsoOfIso_inv {X Y : FormalScheme} (e : X ≅ Y) :
    (globalSectionsIsoOfIso e).inv =
      (forgetToLocallyRingedSpace.map e.inv).c.app (Opposite.op ⊤) :=
  (rfl)

end FormalScheme
end TauCeti

namespace AlgebraicGeometry.Scheme

open TauCeti TauCeti.FormalScheme

/-- An ordinary scheme, regarded as a formal scheme by giving its affine coordinate rings
the discrete topology. The carrier is exposed so its points and morphisms retain their types. -/
@[expose] noncomputable def toFormalScheme (X : Scheme.{u}) : FormalScheme where
  toLocallyRingedSpace := X.toLocallyRingedSpace
  local_spf x := by
    obtain ⟨U, R, ⟨e⟩⟩ := X.local_affine x
    let : TopologicalSpace R := ⊥
    have : DiscreteTopology R := ⟨rfl⟩
    let e' := e ≪≫ (Spf.discreteIsoSpec R).symm
    let j := X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
    have : LocallyRingedSpace.IsOpenImmersion j :=
      LocallyRingedSpace.IsOpenImmersion.ofRestrict _ _
    refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance,
      e'.inv ≫ j, inferInstance, ?_⟩
    exact (LocallyRingedSpace.range_iso_inv_comp e' j).ge
      ⟨⟨x, U.2⟩, rfl⟩

@[simp]
theorem toFormalScheme_toLocallyRingedSpace (X : Scheme.{u}) :
    X.toFormalScheme.toLocallyRingedSpace = X.toLocallyRingedSpace := (rfl)

end AlgebraicGeometry.Scheme

namespace TauCeti.FormalScheme

/-- The fully faithful inclusion of ordinary schemes into formal schemes.
The body is exposed so morphisms have the original schemes' underlying types. -/
@[expose] noncomputable def ofScheme : Scheme ⥤ FormalScheme where
  obj := Scheme.toFormalScheme
  map f := InducedCategory.homMk f.toLRSHom

@[simp]
theorem ofScheme_obj (X : Scheme.{u}) : ofScheme.obj X = X.toFormalScheme := (rfl)

-- Keep this rewrite explicit so the underlying-morphism simp lemma below can fire.
theorem ofScheme_map {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ofScheme.map f =
      InducedCategory.homMk (X := ofScheme.obj X) (Y := ofScheme.obj Y) f.toLRSHom := (rfl)

@[simp]
theorem forgetToLocallyRingedSpace_map_ofScheme_map {X Y : Scheme.{u}} (f : X ⟶ Y) :
    forgetToLocallyRingedSpace.map (ofScheme.map f) = f.toLRSHom := (rfl)

/-- For a discrete coordinate ring, the ordinary affine scheme is its affine formal scheme. -/
noncomputable def ofSchemeSpecIso (R : Type u) [CommRing R] [TopologicalSpace R]
    [DiscreteTopology R] : ofScheme.obj (Spec (CommRingCat.of R)) ≅ ofSpf R :=
  InducedCategory.isoMk (Spf.discreteIsoSpec R).symm

@[simp]
theorem forgetToLocallyRingedSpace_map_ofSchemeSpecIso_hom (R : Type u) [CommRing R]
    [TopologicalSpace R] [DiscreteTopology R] :
    forgetToLocallyRingedSpace.map (ofSchemeSpecIso R).hom =
      (Spf.discreteIsoSpec R).inv := (rfl)

@[simp]
theorem forgetToLocallyRingedSpace_map_ofSchemeSpecIso_inv (R : Type u) [CommRing R]
    [TopologicalSpace R] [DiscreteTopology R] :
    forgetToLocallyRingedSpace.map (ofSchemeSpecIso R).inv =
      (Spf.discreteIsoSpec R).hom := (rfl)

/-- Viewing schemes as formal schemes does not change their morphisms. -/
noncomputable def fullyFaithfulOfScheme : ofScheme.FullyFaithful where
  preimage f := ⟨f.hom⟩

instance : ofScheme.Full := fullyFaithfulOfScheme.full

instance : ofScheme.Faithful := fullyFaithfulOfScheme.faithful

/-- Forgetting the formal atlas of an ordinary scheme recovers the original scheme's
locally ringed space, on objects and morphisms. -/
@[simp]
theorem ofScheme_comp_forgetToLocallyRingedSpace :
    ofScheme ⋙ forgetToLocallyRingedSpace = Scheme.forgetToLocallyRingedSpace := (rfl)

end TauCeti.FormalScheme
