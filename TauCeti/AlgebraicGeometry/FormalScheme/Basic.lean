/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Morphism
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Restrict
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Discrete
public import Mathlib.AlgebraicGeometry.AffineScheme
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

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

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

/-- The underlying space of a formal scheme is T₀: two inseparable points lie in a common open
formal spectrum, whose underlying space is a subspace of a prime spectrum. -/
instance (X : FormalScheme) : T0Space X := by
  refine (t0Space_iff_inseparable X).mpr fun x y h ↦ ?_
  obtain ⟨A, _, _, _, _, f, hf, x', rfl⟩ := X.local_spf x
  obtain ⟨y', rfl⟩ := (h.mem_open_iff hf.base_open.isOpen_range).mp ⟨x', rfl⟩
  -- the points of `Spf A` are open primes of `A`, with the subspace topology of `Spec A`
  have : T0Space (Spf A).toPresheafedSpace := inferInstanceAs (T0Space (Spf.carrier A))
  exact congrArg f.base (hf.base_open.isInducing.inseparable_iff.mp h).eq

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

section OfSpfMap
variable {A B C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B] [CommRing C]
  [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C]

/-- Morphism `ofSpf B ⟶ ofSpf A` attached to a continuous ring homomorphism `φ : A →+* B`. -/
noncomputable def ofSpfMap (φ : A →+* B) (hφ : Continuous φ) : ofSpf B ⟶ ofSpf A :=
  InducedCategory.homMk (Spf.map φ hφ)

@[simp] theorem forgetToLocallyRingedSpace_map_ofSpfMap (φ : A →+* B) (hφ : Continuous φ) :
    forgetToLocallyRingedSpace.map (ofSpfMap φ hφ) = Spf.map φ hφ := (rfl)
@[simp] theorem ofSpfMap_id : ofSpfMap (RingHom.id A) continuous_id = 𝟙 (ofSpf A) :=
  InducedCategory.hom_ext Spf.map_id
@[reassoc] theorem ofSpfMap_comp (φ : B →+* C) (hφ : Continuous φ) (ψ : A →+* B)
    (hψ : Continuous ψ) : ofSpfMap (φ.comp ψ) (hφ.comp hψ) = ofSpfMap φ hφ ≫ ofSpfMap ψ hψ :=
  InducedCategory.hom_ext (Spf.map_comp φ hφ ψ hψ)
end OfSpfMap

/-- An open is affine formal if it is the image of an open immersion from a formal spectrum.
This definition does not choose a presentation or a topology on its ring of sections. -/
def IsAffineOpen (X : FormalScheme) (U : Opens X) : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
    (_ : IsAdicRing A) (f : Spf A ⟶ X.toLocallyRingedSpace),
    LocallyRingedSpace.IsOpenImmersion f ∧ Set.range f.base = (U : Set X)

/-- An open is affine formal exactly when it is the image of an open immersion from a formal
spectrum. -/
theorem isAffineOpen_def (X : FormalScheme) (U : Opens X) :
    X.IsAffineOpen U ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
        (_ : IsAdicRing A) (f : Spf A ⟶ X.toLocallyRingedSpace),
        LocallyRingedSpace.IsOpenImmersion f ∧ Set.range f.base = (U : Set X) :=
  Iff.rfl

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

/-- If a morphism from a formal spectrum `Spf A` hits a point `x`, then every neighbourhood of `x`
contains the image of a basic open set `D(a) ≅ Spf A_{a}` of `Spf A` whose image contains `x`. -/
theorem exists_basicOpenι_comp_mem_range_and_range_subset {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] {X : LocallyRingedSpace.{u}}
    (i : Spf A ⟶ X) (U : Opens X) {x : X} (hx : x ∈ U) (hxi : x ∈ Set.range i.base) :
    ∃ a : A, x ∈ Set.range (Spf.basicOpenι a ≫ i).base ∧
      Set.range (Spf.basicOpenι a ≫ i).base ⊆ (U : Set X) := by
  obtain ⟨y, hy⟩ := hxi
  -- The explicit preimage open tells the basis lemma which neighbourhood to shrink;
  -- membership in `Opens.map` is membership of the image point, where `hy` applies.
  obtain ⟨V, ⟨a, rfl⟩, hyV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp Spf.isBasis_basicOpen)
    (show y ∈ (Opens.map i.base).obj U from
      (congrArg (fun z ↦ z ∈ U) hy).mpr hx)
  obtain ⟨z, hz⟩ := (Spf.range_basicOpenι a).ge hyV
  refine ⟨a, ⟨z, ?_⟩, ?_⟩
  · simpa only [LocallyRingedSpace.comp_base, TopCat.coe_comp, Function.comp_apply, hz] using hy
  · rintro _ ⟨w, rfl⟩
    exact hVU ((Spf.range_basicOpenι a).le (Set.mem_range_self w))

/-- Every neighbourhood contains a formal-spectrum chart through the given point. -/
theorem exists_spf_mem_range_and_range_subset (X : FormalScheme) (U : Opens X)
    (x : X) (hx : x ∈ U) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsAdicRing A) (f : Spf A ⟶ X.toLocallyRingedSpace),
      LocallyRingedSpace.IsOpenImmersion f ∧ x ∈ Set.range f.base ∧
        Set.range f.base ⊆ (U : Set X) := by
  obtain ⟨A, _, _, _, _, i, hi, hxi⟩ := X.local_spf x
  have := hi
  obtain ⟨a, hxa, haU⟩ := exists_basicOpenι_comp_mem_range_and_range_subset i U hx hxi
  exact ⟨AdicRing.CompletedAway A a, inferInstance, inferInstance, inferInstance,
    inferInstance, Spf.basicOpenι a ≫ i, inferInstance, hxa, haU⟩

/-- The affine formal opens form a basis of the topology. -/
theorem isBasis_affineOpens (X : FormalScheme) :
    Opens.IsBasis {U : Opens X | X.IsAffineOpen U} := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨A, _, _, _, _, f, hf, hx, hU⟩ := X.exists_spf_mem_range_and_range_subset U x hx
  exact ⟨⟨Set.range f.base, hf.base_open.isOpen_range⟩,
    ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, f, hf, rfl⟩, hx, hU⟩

/-- Every point of an open `W` in a formal scheme has an affine formal neighbourhood contained in
`W`. -/
theorem exists_isAffineOpen_mem_le (X : FormalScheme) {W : Opens X} {x : X} (hx : x ∈ W) :
    ∃ U : Opens X, X.IsAffineOpen U ∧ x ∈ U ∧ U ≤ W :=
  Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx

/-- Every point of a formal scheme lies in an affine formal open. -/
theorem exists_isAffineOpen_mem (X : FormalScheme) (x : X) :
    ∃ U : Opens X, X.IsAffineOpen U ∧ x ∈ U :=
  let ⟨U, hU, hx, _⟩ := X.exists_isAffineOpen_mem_le (W := ⊤) (x := x) trivial
  ⟨U, hU, hx⟩

/-- The affine formal opens of any formal scheme `X` cover `X`. -/
theorem iSup_affineOpens_eq_top (X : FormalScheme) :
    (⨆ U : {U : Opens X // X.IsAffineOpen U}, U.val) = ⊤ := by
  apply Opens.ext; rw [Opens.coe_iSup]; refine Set.eq_univ_iff_forall.mpr fun x ↦ ?_
  obtain ⟨U, hU, hx⟩ := X.exists_isAffineOpen_mem x
  exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hx⟩

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
      ⟨⟨x, U.property⟩, rfl⟩

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

/-- Every affine open of an ordinary scheme `X` is an affine formal open of `ofScheme.obj X`. -/
theorem isAffineOpen_ofScheme {X : Scheme.{u}} {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) : (ofScheme.obj X).IsAffineOpen U := by
  let R : Type u := X.presheaf.obj (op U)
  let _ : TopologicalSpace R := ⊥; have : DiscreteTopology R := ⟨rfl⟩
  exact ((ofScheme.obj X).isAffineOpen_iff U).mpr ⟨R, inferInstance, ⊥, inferInstance,
    inferInstance, ⟨Scheme.forgetToLocallyRingedSpace.mapIso hU.isoSpec ≪≫
      (Spf.discreteIsoSpec R).symm⟩⟩

/-- Viewing schemes as formal schemes does not change their morphisms. -/
noncomputable def fullyFaithfulOfScheme : ofScheme.FullyFaithful where
  preimage f := ⟨f.hom⟩

instance : ofScheme.Full := fullyFaithfulOfScheme.full

instance : ofScheme.Faithful := fullyFaithfulOfScheme.faithful

/-- An affine open `U` of a scheme `X` is an affine formal open of `X` regarded as a formal
scheme: it is the image of the formal spectrum of the discrete ring `Γ(X, U)`. -/
theorem _root_.AlgebraicGeometry.IsAffineOpen.isAffineOpen_toFormalScheme {X : Scheme.{u}}
    {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) : X.toFormalScheme.IsAffineOpen U := by
  let : TopologicalSpace Γ(X, U) := ⊥
  have : DiscreteTopology Γ(X, U) := ⟨rfl⟩
  let e := (Spf.discreteIsoSpec Γ(X, U)).symm
  -- `X.toFormalScheme` has the locally ringed space of `X`, so `hU.fromSpec` lands in it
  exact (isAffineOpen_def X.toFormalScheme U).mpr ⟨Γ(X, U), inferInstance, inferInstance,
    inferInstance, inferInstance, e.inv ≫ hU.fromSpec.toLRSHom,
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ e.inv inferInstance hU.fromSpec.toLRSHom
      hU.isOpenImmersion_fromSpec,
    (LocallyRingedSpace.range_iso_inv_comp e _).trans hU.range_fromSpec⟩

/-- Forgetting the formal atlas of an ordinary scheme recovers the original scheme's
locally ringed space, on objects and morphisms. -/
@[simp]
theorem ofScheme_comp_forgetToLocallyRingedSpace :
    ofScheme ⋙ forgetToLocallyRingedSpace = Scheme.forgetToLocallyRingedSpace := (rfl)

end TauCeti.FormalScheme
