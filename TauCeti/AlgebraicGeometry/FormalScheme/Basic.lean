/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Restrict
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Discrete
public import Mathlib.AlgebraicGeometry.Scheme

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
The object and morphism maps are exposed so sections and points retain their types. -/
@[expose] def forgetToLocallyRingedSpace : FormalScheme ⥤ LocallyRingedSpace :=
  inducedFunctor toLocallyRingedSpace

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
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact (e.inv.base y).property
    · intro hz
      refine ⟨e.hom.base ⟨z, hz⟩, ?_⟩
      -- Expose composition on points before cancelling the isomorphism.
      erw [LocallyRingedSpace.comp_base, TopCat.coe_comp, Function.comp_apply,
        LocallyRingedSpace.iso_hom_base_inv_base_apply]
      rfl

/-- Every formal spectrum is an affine formal open in itself. -/
@[simp]
theorem isAffineOpen_top_ofSpf (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] : IsAffineOpen (ofSpf A) ⊤ :=
  ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, 𝟙 _,
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (𝟙 (Spf A))), Set.range_id⟩

/-- Every neighbourhood contains a formal-spectrum chart through the given point. -/
theorem exists_spf_le (X : FormalScheme) (U : Opens X) (x : X) (hx : x ∈ U) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsAdicRing A) (f : Spf A ⟶ X.toLocallyRingedSpace),
      LocallyRingedSpace.IsOpenImmersion f ∧ x ∈ Set.range f.base ∧
        Set.range f.base ⊆ (U : Set X) := by
  obtain ⟨A, _, _, _, _, i, hi, y, hy⟩ := X.local_spf x
  have := hi
  obtain ⟨V, ⟨a, rfl⟩, hyV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp Spf.isBasis_basicOpen)
    (show y ∈ (Opens.map i.base).obj U from
      (congrArg (fun z ↦ z ∈ U) hy).mpr hx)
  have hrange : Set.range (Spf.basicOpenι a).base = (Spf.basicOpen a : Set (Spf.carrier A)) := by
    rw [Spf.basicOpenι_base]
    exact Spf.range_comap_completedAway a
  obtain ⟨z, hz⟩ := hrange.ge hyV
  refine ⟨AdicRing.CompletedAway A a, inferInstance, inferInstance, inferInstance,
    inferInstance, Spf.basicOpenι a ≫ i, inferInstance, ⟨z, ?_⟩, ?_⟩
  · simpa only [LocallyRingedSpace.comp_base, TopCat.coe_comp, Function.comp_apply, hz] using hy
  · rintro _ ⟨w, rfl⟩
    exact hVU (hrange.le (Set.mem_range_self w))

/-- The affine formal opens form a basis of the topology. -/
theorem isBasis_affineOpens (X : FormalScheme) :
    Opens.IsBasis {U : Opens X | X.IsAffineOpen U} := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨A, _, _, _, _, f, hf, hx, hU⟩ := X.exists_spf_le U x hx
  exact ⟨⟨Set.range f.base, hf.base_open.isOpen_range⟩,
    ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, f, hf, rfl⟩, hx, hU⟩

/-- Restrict a formal scheme to an open subset, using the restriction of its locally ringed
space. The affine atlas is obtained by shrinking charts using completed localizations. -/
noncomputable def restrict (X : FormalScheme) (U : Opens X) : FormalScheme where
  toLocallyRingedSpace := X.toLocallyRingedSpace.restrict U.isOpenEmbedding
  local_spf x := by
    obtain ⟨A, _, _, _, _, f, hf, hx, hU⟩ := X.exists_spf_le U x.val x.property
    have := hf
    let j := X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
    have hj : LocallyRingedSpace.IsOpenImmersion j := inferInstance
    have hfj : Set.range f.base ⊆ Set.range j.base := by
      intro z hz
      exact ⟨⟨z, hU hz⟩, rfl⟩
    let g := LocallyRingedSpace.IsOpenImmersion.lift j f hfj
    have hg : LocallyRingedSpace.IsOpenImmersion g := by
      have := LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset j f hfj
      -- The lift is an inverse pullback projection followed by an open immersion.
      dsimp only [g, LocallyRingedSpace.IsOpenImmersion.lift]
      infer_instance
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

/-- The restriction of an affine formal scheme to `D(f)` is the formal spectrum of its
completed localization. -/
noncomputable def restrictBasicOpenIso (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (f : A) :
    (ofSpf A).restrict (Spf.basicOpen f) ≅ ofSpf (AdicRing.CompletedAway A f) :=
  InducedCategory.isoMk (Spf.restrictBasicOpenIso f)

/-- Every basic open in a formal spectrum is affine formal. -/
@[simp]
theorem isAffineOpen_basicOpen (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (f : A) :
    IsAffineOpen (ofSpf A) (Spf.basicOpen f) := by
  refine ⟨AdicRing.CompletedAway A f, inferInstance, inferInstance, inferInstance,
    inferInstance, Spf.basicOpenι f,
    Spf.isOpenImmersion_basicOpenι f, ?_⟩
  rw [Spf.basicOpenι_base]
  exact Spf.range_comap_completedAway f

end FormalScheme
end TauCeti

namespace AlgebraicGeometry.Scheme

open TauCeti TauCeti.FormalScheme

/-- An ordinary scheme, regarded as a formal scheme by giving its affine coordinate rings
the discrete topology. -/
noncomputable def toFormalScheme (X : Scheme.{u}) : FormalScheme where
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
      e'.inv ≫ j, inferInstance, e'.hom.base ⟨x, U.2⟩, ?_⟩
    -- Composition on points must be exposed before the isomorphism cancellation applies.
    erw [LocallyRingedSpace.comp_base, TopCat.coe_comp, Function.comp_apply,
      LocallyRingedSpace.iso_hom_base_inv_base_apply]
    rfl

end AlgebraicGeometry.Scheme

namespace TauCeti.FormalScheme

/-- The fully faithful inclusion of ordinary schemes into formal schemes. -/
noncomputable def ofScheme : Scheme ⥤ FormalScheme where
  obj := Scheme.toFormalScheme
  map f := InducedCategory.homMk f.toLRSHom

/-- For a discrete coordinate ring, the ordinary affine scheme is its affine formal scheme. -/
noncomputable def ofSchemeSpecIso (R : Type u) [CommRing R] [TopologicalSpace R]
    [DiscreteTopology R] : ofScheme.obj (Spec (CommRingCat.of R)) ≅ ofSpf R :=
  InducedCategory.isoMk (Spf.discreteIsoSpec R).symm

/-- Viewing schemes as formal schemes does not change their morphisms. -/
noncomputable def fullyFaithfulOfScheme : ofScheme.FullyFaithful where
  preimage f := ⟨f.hom⟩

instance : ofScheme.Full := fullyFaithfulOfScheme.full

instance : ofScheme.Faithful := fullyFaithfulOfScheme.faithful

/-- Forgetting the formal atlas of an ordinary scheme recovers the original scheme's
locally ringed space, on objects and morphisms. -/
@[simp]
theorem ofScheme_comp_forget :
    ofScheme ⋙ forgetToLocallyRingedSpace = Scheme.forgetToLocallyRingedSpace := (rfl)

end TauCeti.FormalScheme
