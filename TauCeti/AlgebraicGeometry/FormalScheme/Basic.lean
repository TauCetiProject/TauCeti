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
