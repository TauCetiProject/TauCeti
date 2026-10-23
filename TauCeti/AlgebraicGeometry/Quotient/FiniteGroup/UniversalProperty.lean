/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.Affine
public import TauCeti.RingTheory.Invariant.Localization
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Pullbacks
import TauCeti.AlgebraicGeometry.Morphisms.Epi

/-!
# The universal property of the affine invariant quotient by a finite group

Let a finite group `G` act on a commutative ring `A`. This file shows that the invariant-spectrum
projection `π : Spec A ⟶ Spec Aᴳ` is a categorical quotient in the category of all schemes: every
morphism `f : Spec A ⟶ X` to an arbitrary scheme `X` which is invariant under the action of `G`
factors uniquely through `π`. The case of an affine `X`, where only a monoid action is needed, is
`TauCeti.AffineInvariantQuotient.existsUnique_desc`.

Uniqueness holds because `π` is an epimorphism of schemes: it is surjective, and its stalk maps
`(Aᴳ)_P → A_Q` are injective (`TauCeti.FixedPoints.localRingHom_injective`).

For existence, `f` is constant on the fibres of `π`, which are the `G`-orbits, so it descends to a
continuous map `b : Spec Aᴳ → X` because `π` is a topological quotient map. Cover `Spec Aᴳ` by basic
opens `D(r)` with `r` invariant and `b(D(r))` inside an affine open `V` of `X`. Over `D(r)`, the
projection is the affine invariant quotient of the localization `A[1/r]`: invariants commute with
this localization (`TauCeti.FixedPoints.isLocalization`), so the square formed by
`Spec A[1/r] ⟶ Spec A`, the two projections and `Spec A[1/r]ᴳ ⟶ Spec Aᴳ` is a pullback square
(`TauCeti.AffineInvariantQuotient.isPullback_away`). The restriction of `f` to `Spec A[1/r]` lands
in `V`, so it descends by the affine universal property. The local descents agree on overlaps
because `π` remains an epimorphism over every open subscheme of `Spec Aᴳ`, and they glue
(`AlgebraicGeometry.Scheme.Hom.exists_comp_eq_of_openCover`).

The construction follows the proof of Mathlib's
`AlgebraicGeometry.isRegularEpi_of_flat_of_surjective_of_isAffine`, where flat descent plays the
role of the affine invariant quotient.

## Main definitions

* `TauCeti.AffineInvariantQuotient.descOfFinite`: the morphism `Spec Aᴳ ⟶ X` induced by an
  invariant morphism `Spec A ⟶ X`.

## Main results

* `TauCeti.AffineInvariantQuotient.stalkMap_projection_injective`: the stalk maps of the projection
  are injective.
* `TauCeti.AffineInvariantQuotient.instEpiProjection`: the projection is an epimorphism of schemes.
* `TauCeti.AffineInvariantQuotient.isPullback_away`: over the basic open `D(r)`, the projection is
  the projection of `A[1/r]`.
* `TauCeti.AffineInvariantQuotient.hom_ext_of_finite`: morphisms out of the quotient to an
  arbitrary scheme are determined by their composition with the projection.
* `TauCeti.AffineInvariantQuotient.existsUnique_desc_of_finite`: the universal property for
  arbitrary target schemes.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §1.
* D. Mumford, *Abelian Varieties*, §7, Theorem 1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AffineInvariantQuotient

universe u v

variable (A : Type u) (G : Type v) [CommRing A] [Group G] [MulSemiringAction G A] [Finite G]

/-- The stalk maps `(Aᴳ)_P → A_Q` of the invariant-spectrum projection are injective for a finite
group action. -/
theorem stalkMap_projection_injective (x : Spec (CommRingCat.of A)) :
    Function.Injective ((projection A G).stalkMap x) := by
  have : x.asIdeal.IsPrime := PrimeSpectrum.isPrime x
  have : Mono (CommRingCat.ofHom (Localization.localRingHom
      (PrimeSpectrum.comap (algebraMap (FixedPoints.subring A G) A) x).asIdeal x.asIdeal
      (algebraMap (FixedPoints.subring A G) A) rfl)) :=
    ConcreteCategory.mono_of_injective _ (FixedPoints.localRingHom_injective _ _ rfl)
  rw [projection_def]
  have hmono : Mono ((Spec.map (CommRingCat.ofHom
      (algebraMap (FixedPoints.subring A G) A))).stalkMap x) :=
    ((MorphismProperty.monomorphisms CommRingCat).arrow_mk_iso_iff
      (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom
        (algebraMap (FixedPoints.subring A G) A)) x)).mpr this
  exact ConcreteCategory.injective_of_mono_of_preservesPullback _

/-- The invariant-spectrum projection of a finite group action is an epimorphism of schemes. -/
instance instEpiProjection : Epi (projection A G) :=
  Scheme.Hom.epi_of_surjective_of_stalkMap_injective _ (stalkMap_projection_injective A G)

variable {A} in
/-- Over the basic open `D(r)` of an invariant `r`, the invariant-spectrum projection is the
projection of the localization `A[1/r]`: the square formed by the two projections and the maps
induced by `A → A[1/r]` and `Aᴳ → A[1/r]ᴳ` is a pullback square. -/
theorem isPullback_away (r : FixedPoints.subring A G) :
    IsPullback (Spec.algebraMap A (Localization (Algebra.algebraMapSubmonoid A (.powers r))))
      (projection (Localization (Algebra.algebraMapSubmonoid A (.powers r))) G) (projection A G)
      (Spec.algebraMap (FixedPoints.subring A G)
        (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A (.powers r))) G)) := by
  have : IsLocalization ((Submonoid.powers r).map (algebraMap (FixedPoints.subring A G) A))
      (Localization (Algebra.algebraMapSubmonoid A (.powers r))) :=
    Localization.isLocalization
  rw [projection_def, projection_def]
  exact isPullback_SpecMap_of_isPushout _ _ _ _ <| CommRingCat.isPushout_of_isLocalization
    (algebraMap (FixedPoints.subring A G) A)
    (algebraMap (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A (.powers r))) G)
      (Localization (Algebra.algebraMapSubmonoid A (.powers r))))
    rfl (Submonoid.powers r)

variable {A} in
/-- The map `Spec A[1/r]ᴳ ⟶ Spec Aᴳ` is an open immersion. -/
instance isOpenImmersion_away (r : FixedPoints.subring A G) :
    IsOpenImmersion (Spec.algebraMap (FixedPoints.subring A G)
      (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A (.powers r))) G)) :=
  IsOpenImmersion.of_isLocalization r

variable {A} in
/-- The image of `Spec A[1/r]ᴳ ⟶ Spec Aᴳ` is the basic open `D(r)`. -/
theorem range_specAlgebraMap_away (r : FixedPoints.subring A G) :
    Set.range (Spec.algebraMap (FixedPoints.subring A G)
      (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A (.powers r))) G)) =
      (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum (FixedPoints.subring A G))) :=
  PrimeSpectrum.localization_away_comap_range _ r

omit [Finite G] in
variable {A G} in
/-- The map `Spec A[1/r] ⟶ Spec A` is equivariant. -/
@[reassoc]
theorem specComap_comp_specAlgebraMap_away (r : FixedPoints.subring A G) (g : G) :
    specComap (Localization (Algebra.algebraMapSubmonoid A (.powers r))) G g ≫
        Spec.algebraMap A (Localization (Algebra.algebraMapSubmonoid A (.powers r))) =
      Spec.algebraMap A (Localization (Algebra.algebraMapSubmonoid A (.powers r))) ≫
        specComap A G g := by
  rw [specComap_def, specComap_def, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  exact FixedPoints.smul_algebraMap_localization _ g a

variable {A G}

/-- An invariant morphism is constant on the fibres of the projection, so it descends to a
continuous map on the invariant quotient. -/
private theorem exists_continuousMap_comp_projection {X : Scheme.{u}}
    (f : Spec (CommRingCat.of A) ⟶ X) (hf : ∀ g : G, specComap A G g ≫ f = f) :
    ∃ b : C(quotient A G, X), ∀ x, b (projection A G x) = f x := by
  have hfac : Function.FactorsThrough f.base.hom (projection A G) := fun x y hxy ↦ by
    obtain ⟨g, rfl⟩ := (projection_eq_iff_exists_smul A G x y).mp hxy
    have h := congrArg (fun k : Spec (CommRingCat.of A) ⟶ X ↦ k x) (hf g⁻¹)
    have h2 := specComap_base_apply A G g⁻¹ x
    rw [inv_inv] at h2
    simp only [Scheme.Hom.comp_apply] at h
    exact h.symm.trans (congrArg _ h2)
  refine ⟨(isQuotientMap_projection A G).lift _ hfac, fun x ↦ ?_⟩
  exact DFunLike.congr_fun ((isQuotientMap_projection A G).lift_comp _ hfac) x

/-- The local descent of an invariant morphism: over a basic open `D(r)` which the induced
continuous map sends into an affine open `V`, the base change of `f` descends. -/
private theorem exists_desc_away {X : Scheme.{u}} (f : Spec (CommRingCat.of A) ⟶ X)
    (hf : ∀ g : G, specComap A G g ≫ f = f) (b : C(quotient A G, X))
    (hb : ∀ x, b (projection A G x) = f x) (r : FixedPoints.subring A G) (V : X.affineOpens)
    (hrV : ∀ y ∈ PrimeSpectrum.basicOpen r, b y ∈ (V : Set X)) :
    ∃ u : quotient (Localization (Algebra.algebraMapSubmonoid A (.powers r))) G ⟶ X,
      pullback.fst (projection A G) (Spec.algebraMap (FixedPoints.subring A G)
        (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A (.powers r))) G)) ≫ f =
        pullback.snd _ _ ≫ u := by
  have hpb := isPullback_away G r
  have hV : Set.range
      (Spec.algebraMap A (Localization (Algebra.algebraMapSubmonoid A (.powers r))) ≫ f) ⊆
      Set.range V.1.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, ← hb, ← Scheme.Hom.comp_apply, hpb.w,
      Scheme.Hom.comp_apply]
    exact hrV _ ((range_specAlgebraMap_away G r).le ⟨_, rfl⟩)
  let f' := IsOpenImmersion.lift V.1.ι _ hV
  have hf' (g : G) :
      specComap (Localization (Algebra.algebraMapSubmonoid A (.powers r))) G g ≫ f' = f' := by
    rw [← cancel_mono V.1.ι]
    simp [f', specComap_comp_specAlgebraMap_away_assoc, hf]
  refine ⟨desc f' hf' ≫ V.1.ι, ?_⟩
  rw [← cancel_epi hpb.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc,
    IsPullback.isoPullback_hom_snd_assoc, projection_desc_assoc, IsOpenImmersion.lift_fac]

/-- The universal property for arbitrary target schemes, as an existence statement. -/
private theorem exists_projection_comp_eq {X : Scheme.{u}} (f : Spec (CommRingCat.of A) ⟶ X)
    (hf : ∀ g : G, specComap A G g ≫ f = f) :
    ∃ h : quotient A G ⟶ X, projection A G ≫ h = f := by
  obtain ⟨b, hb⟩ := exists_continuousMap_comp_projection f hf
  -- Basic opens `D(r)` sent by `b` into affine opens of `X` cover the quotient.
  let I := {p : FixedPoints.subring A G × X.affineOpens //
    ∀ y ∈ PrimeSpectrum.basicOpen p.1, b y ∈ (p.2 : Set X)}
  have hcov (y : quotient A G) : ∃ i : I, y ∈ PrimeSpectrum.basicOpen i.1.1 := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hbV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (b y)) isOpen_univ
    obtain ⟨_, ⟨r, rfl⟩, hyr, hrV⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (Set.mem_preimage.mpr hbV) ((V : X.Opens).isOpen.preimage b.continuous)
    exact ⟨⟨(r, ⟨V, hV⟩), fun z hz ↦ hrV hz⟩, hyr⟩
  let 𝒰 : (quotient A G).OpenCover :=
    { I₀ := I
      X i := quotient (Localization (Algebra.algebraMapSubmonoid A (.powers i.1.1))) G
      f i := Spec.algebraMap (FixedPoints.subring A G)
        (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A (.powers i.1.1))) G)
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun y ↦ ?_, inferInstance⟩
        obtain ⟨i, hi⟩ := hcov y
        obtain ⟨z, hz⟩ := (range_specAlgebraMap_away G i.1.1).ge hi
        exact ⟨i, z, hz⟩ }
  choose u hu using fun i : I ↦ exists_desc_away f hf b hb i.1.1 i.1.2 i.2
  -- The local descents glue, since the projection stays an epimorphism over open subschemes.
  exact Scheme.Hom.exists_comp_eq_of_openCover (projection A G)
    (fun _ g _ ↦ Scheme.Hom.epi_pullback_snd_of_isOpenImmersion _ g
      (stalkMap_projection_injective A G)) 𝒰 f u hu

/-- The morphism `Spec Aᴳ ⟶ X` induced by a `G`-invariant morphism `Spec A ⟶ X` to an arbitrary
scheme, for a finite group `G`. -/
noncomputable def descOfFinite {X : Scheme.{u}} (f : Spec (CommRingCat.of A) ⟶ X)
    (hf : ∀ g : G, specComap A G g ≫ f = f) : quotient A G ⟶ X :=
  (exists_projection_comp_eq f hf).choose

/-- Morphisms from the invariant quotient by a finite group to an arbitrary scheme are determined by
their composition with the projection. -/
@[ext]
theorem hom_ext_of_finite {X : Scheme.{u}} {f h : quotient A G ⟶ X}
    (e : projection A G ≫ f = projection A G ≫ h) : f = h :=
  (cancel_epi (projection A G)).mp e

/-- The induced morphism factors the given invariant morphism. -/
@[reassoc (attr := simp)]
theorem projection_descOfFinite {X : Scheme.{u}} (f : Spec (CommRingCat.of A) ⟶ X)
    (hf : ∀ g : G, specComap A G g ≫ f = f) :
    projection A G ≫ descOfFinite f hf = f :=
  (exists_projection_comp_eq f hf).choose_spec

/-- **The universal property of the affine invariant quotient by a finite group.** Every
`G`-invariant morphism from `Spec A` to an arbitrary scheme factors uniquely through the
projection `Spec A ⟶ Spec Aᴳ`. -/
theorem existsUnique_desc_of_finite {X : Scheme.{u}} (f : Spec (CommRingCat.of A) ⟶ X)
    (hf : ∀ g : G, specComap A G g ≫ f = f) :
    ∃! h : quotient A G ⟶ X, projection A G ≫ h = f :=
  ⟨descOfFinite f hf, projection_descOfFinite f hf, fun _ hh ↦
    hom_ext_of_finite (hh.trans (projection_descOfFinite f hf).symm)⟩

/-- Descending the composite of the projection with a morphism to an arbitrary scheme recovers
that morphism. -/
@[simp]
theorem descOfFinite_projection {X : Scheme.{u}} (f : quotient A G ⟶ X) :
    descOfFinite (projection A G ≫ f) (fun g ↦ by simp) = f :=
  hom_ext_of_finite (projection_descOfFinite _ _)

/-- For an affine target, `descOfFinite` is the affine descent `desc`. -/
theorem descOfFinite_eq_desc {X : Scheme.{u}} [IsAffine X] (f : Spec (CommRingCat.of A) ⟶ X)
    (hf : ∀ g : G, specComap A G g ≫ f = f) :
    descOfFinite f hf = desc f hf :=
  hom_ext_of_finite (by simp)

end TauCeti.AffineInvariantQuotient
