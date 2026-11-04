/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Invariant.Basic
public import TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.Fppf
public import TauCeti.AlgebraicGeometry.RelativeSpec.Equalizer
import Mathlib.RingTheory.RingHom.Injective
import TauCeti.AlgebraicGeometry.Morphisms.Epi
import TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.UniversalProperty
import TauCeti.RingTheory.Invariant.Localization

/-!
# Relative invariant quotients by finite groups

Let `A` be a quasi-coherent commutative `𝒪ₓ`-algebra on a scheme `X`, so that `Y = Spec_X(A)` is
an arbitrary scheme affine over `X`, and let a finite group `G` act on `A` by algebra
automorphisms `ρ : G →* Aut A`, that is, on `Y` by automorphisms over `X`. This file constructs
the quotient `Y/G` over `X` by gluing the affine invariant quotients over the affine opens of `X`.

Over each open `U` of `X`, the sections of `A` fixed by every `g : G` form a `Γ(X, U)`-subalgebra
`CommMon.invariantSections ρ U` of `Γ(A.X, U)`. Over a basic open `X.basicOpen r` of an affine
open `U`, these invariants are the localization away from `r` of the invariants over `U`: a section
`x / rⁿ` fixed by every `g` satisfies `rᵐ (g • x - x) = 0` for some `m` depending on `g`, and
since `G` is finite a single `m` works for all `g`, so that `rᵐ x` is invariant. Hence the
presheaf of invariant subalgebras `Q = CommMon.invariantSubalgebraPresheaf ρ` is coequifibered, and
the affine schemes `Spec (CommMon.invariantSections ρ U)` glue, with Mathlib's relative gluing on
the small affine Zariski site, to its relative spectrum `Q.relativeSpec`, affine over `X`
(`CommMon.SubalgebraPresheaf.relativeSpec`). The inclusions of the invariants glue to the quotient
projection `Q.relativeSpecπ : Spec_X(A) ⟶ Q.relativeSpec` over `X`, which is invariant under the
action of `G` on `Spec_X(A)`.

Over every affine open `U` of `X`, the projection is the affine invariant quotient
`Spec Γ(A.X, U) ⟶ Spec Γ(A.X, U)ᴳ` (`CommMon.SubalgebraPresheaf.isPullback_relativeSpecπ`).
Since `G` is finite, `Γ(A.X, U)` is integral over its invariants, so the projection is integral
and surjective, and it is finite when `Spec_X(A)` is of finite type over `X`. No flatness of the
projection is asserted: for actions which are not free it can fail.

The construction needs no hypothesis on `X`, and in particular the quotient of a scheme affine
over a non-affine base is obtained without choosing a global invariant affine cover: the
preimages of the affine opens of `X` form one.

The projection is a categorical quotient in the category of all schemes: every `G`-invariant
morphism `f : Spec_X(A) ⟶ Z` to an arbitrary scheme `Z` factors uniquely through it
(`CommMon.existsUnique_relativeSpecπ_comp_eq`). Over each affine open `U` of `X`, the base change of
`f` descends by the universal property of the affine invariant quotient,
`TauCeti.AffineInvariantQuotient.existsUnique_desc_of_finite`. The stalk maps of the projection are
injective, because they are on each affine chart, so the projection stays an epimorphism after base
change to every open subscheme of `Spec_X(A)/G`; hence the local descents agree on overlaps and glue
(`AlgebraicGeometry.Scheme.Hom.exists_comp_eq_of_openCover`).

When the action is free, in the sense that over every affine open `U` of `X` and for every `g ≠ 1`
the sections `g • a - a` with `a` in `Γ(A.X, U)` generate the unit ideal, the projection is a finite
étale `G`-torsor and `Spec_X(A)/G` is the fppf quotient. Over each affine open `U` this is the
affine statement (`TauCeti.AffineInvariantQuotient.etale_projection`,
`TauCeti.AffineInvariantQuotient.isPullback_of_free`). Étaleness is local on the target. The torsor
square, which identifies `∐_g Spec_X(A)` with `Spec_X(A) ×_{Spec_X(A)/G} Spec_X(A)`, is local on
the source of the projection (`AlgebraicGeometry.Scheme.isPullback_of_openCover`): over the chart
`Spec Γ(A.X, U)`, finite coproducts are stable under base change and the chart of `Spec_X(A)/G`
over `U` has preimage the chart of `Spec_X(A)`, so the square restricts to the affine torsor
square. The étale surjective projection generates an fppf covering sieve, and the fppf quotient
statement follows from the kernel pair by `CategoryTheory.IsKernelPair.isColimitYonedaCofork`.

The points of the quotient with values in a field are the orbits of `G` on such points of
`Spec_X(A)`: a point of `Spec_X(A)` with values in a field lies over a single affine open `U` of
`X`, hence factors through the chart `Spec Γ(A.X, U)`, where this is the affine statement
`TauCeti.AffineInvariantQuotient.exists_comp_specComap_eq`.

The localization statement is a case of `TauCeti.FixedPoints.isLocalization_of_mem_range_iff`,
which also gives `TauCeti.FixedPoints.isLocalization`, and the gluing is the relative spectrum of
a presheaf of subalgebras, which also gives the relative spectrum of an equalizer,
`CommMon.equalizerSubalgebraPresheaf`.

## Main definitions

* `CommMon.sectionsAction ρ U`: the action of `G` on `Γ(A.X, U)` by `Γ(X, U)`-algebra
  automorphisms.
* `CommMon.sectionsMulSemiringAction ρ U`: the same action as a `MulSemiringAction`, not an
  instance since it depends on `ρ`.
* `CommMon.invariantSections ρ U`: the invariant sections over `U`, which are
  `FixedPoints.subalgebra Γ(X, U) Γ(A.X, U) G` for that action
  (`CommMon.invariantSections_eq_fixedPoints`).
* `CommMon.invariantSubalgebraPresheaf ρ`: the presheaf of invariant subalgebras, whose relative
  spectrum is the relative invariant quotient `Spec_X(A)/G` and whose `relativeSpecπ` is the
  quotient projection.
* `CommMon.invariantQuotientDesc f hf`: the morphism `Spec_X(A)/G ⟶ Z` induced by a `G`-invariant
  morphism `f : Spec_X(A) ⟶ Z`.

## Main results

* `CommMon.isLocalization_invariantSections_basicOpen`: invariants commute with localization at
  a basic open of an affine open, so that `CommMon.invariantSubalgebraPresheaf ρ` is coequifibered
  (`CommMon.isCoequifibered_invariantSubalgebraPresheaf`).
* `CommMon.relativeSpecMap_invariantSubalgebraPresheaf_relativeSpecπ`: the projection is
  `G`-invariant.
* `CommMon.isIntegral_invariantSections`: the sections are integral over the invariant sections.
* The projection is integral and surjective, and
  `CommMon.isFinite_invariantSubalgebraPresheaf_relativeSpecπ`: it is finite when `Spec_X(A)` is
  locally of finite type over `X`.
* `CommMon.stalkMap_invariantSubalgebraPresheaf_relativeSpecπ_injective`: the stalk maps of the
  projection are injective, so the projection is an epimorphism of schemes.
* `CommMon.existsUnique_relativeSpecπ_comp_eq`: the universal property of the quotient for
  arbitrary target schemes.
* `CommMon.exists_comp_relativeSpecMap_eq`: two points of `Spec_X(A)` with values in a field and
  the same image in the quotient differ by the action of an element of `G`.
* `CommMon.etale_invariantSubalgebraPresheaf_relativeSpecπ_of_free` and
  `CommMon.isFinite_invariantSubalgebraPresheaf_relativeSpecπ_of_free`: for a free action, the
  projection is finite étale.
* `CommMon.isPullback_invariantSubalgebraPresheaf_relativeSpecπ_of_free`: for a free action,
  `∐_g Spec_X(A)` is the kernel pair of the projection.
* `CommMon.isColimitInvariantQuotientFppfYonedaCofork`: for a free action, `Spec_X(A)/G` represents
  the fppf quotient sheaf of `Spec_X(A)` by `G`.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §1 (quotients of
  affine schemes by finite groups) and §4 (free actions and fppf quotients).
* D. Mumford, *Abelian Varieties*, §7, Theorem 1 (quotients by finite groups as categorical
  quotients).
* The Stacks Project, [Tag 01LL](https://stacks.math.columbia.edu/tag/01LL) (relative spectrum
  via gluing).
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme.AffineZariskiSite

namespace CategoryTheory.CommMon

universe u v

noncomputable section

variable {X : Scheme.{u}}

variable {A : CommMon X.Modules} {G : Type v} [Group G] (ρ : G →* Aut A)

/-- The action of `G` on the sections of `A` over `U` through `ρ`, by `Γ(X, U)`-algebra
automorphisms. -/
def sectionsAction (U : X.Opens) : G →* (Γ(A.X, U) ≃ₐ[Γ(X, U)] Γ(A.X, U)) where
  toFun g := sectionsAlgEquiv (ρ g).asIso U
  map_one' := AlgEquiv.ext fun x ↦ by simp
  map_mul' g h := AlgEquiv.ext fun x ↦ by
    simp only [AlgEquiv.mul_apply, sectionsAlgEquiv_apply, map_mul, Aut.mul_asIso, Iso.trans_hom,
      sectionsAlgHom_comp, AlgHom.comp_apply]

@[simp]
lemma sectionsAction_apply (U : X.Opens) (g : G) (x : Γ(A.X, U)) :
    sectionsAction ρ U g x = sectionsAlgHom (ρ g).asIso.hom U x :=
  sectionsAlgEquiv_apply _ U x

/-- The action of `G` on the sections of `A` over `U` through `ρ`, as a `MulSemiringAction`.
It is not an instance, since `ρ` does not occur in the type `Γ(A.X, U)`. -/
@[instance_reducible]
def sectionsMulSemiringAction (U : X.Opens) : MulSemiringAction G Γ(A.X, U) :=
  MulSemiringAction.compHom _ (sectionsAction ρ U)

@[simp]
lemma sectionsMulSemiringAction_smul (U : X.Opens) (g : G) (x : Γ(A.X, U)) :
    letI := sectionsMulSemiringAction ρ U
    g • x = sectionsAlgHom (ρ g).asIso.hom U x :=
  sectionsAction_apply ρ U g x

/-- The action of `G` on the sections over `U` commutes with the action of `Γ(X, U)`. -/
lemma smulCommClass_sectionsMulSemiringAction (U : X.Opens) :
    letI := sectionsMulSemiringAction ρ U
    SMulCommClass G Γ(X, U) Γ(A.X, U) :=
  letI := sectionsMulSemiringAction ρ U
  ⟨fun g r x ↦ by simp only [sectionsMulSemiringAction_smul, map_smul]⟩

/-- The `Γ(X, U)`-subalgebra of sections of `A` over `U` fixed by every element of `G`. -/
def invariantSections (U : X.Opens) : Subalgebra Γ(X, U) Γ(A.X, U) :=
  ⨅ g, CommMon.equalizerSections (ρ g).asIso.hom (𝟙 A) U

variable {ρ} in
@[simp]
lemma mem_invariantSections {U : X.Opens} {x : Γ(A.X, U)} :
    x ∈ invariantSections ρ U ↔ ∀ g, sectionsAlgHom (ρ g).asIso.hom U x = x := by
  simp [invariantSections]

/-- The invariant sections over `U` are the fixed points of `sectionsMulSemiringAction ρ U`, the
form in which the affine invariant quotient `AffineInvariantQuotient` is stated. -/
lemma invariantSections_eq_fixedPoints (U : X.Opens) :
    letI := sectionsMulSemiringAction ρ U
    haveI := smulCommClass_sectionsMulSemiringAction ρ U
    invariantSections ρ U = FixedPoints.subalgebra Γ(X, U) Γ(A.X, U) G := by
  let _ := sectionsMulSemiringAction ρ U
  have := smulCommClass_sectionsMulSemiringAction ρ U
  ext x
  simp [FixedPoints.mem_subalgebra]

open TauCeti.AffineInvariantQuotient in
/-- The spectrum of the invariant sections over `U` is the affine invariant quotient of the
sections, through the identification of the invariant sections with the fixed subalgebra. -/
private def chartIso (U : X.Opens) :
    letI := sectionsMulSemiringAction ρ U
    quotient Γ(A.X, U) G ≅ Spec (CommRingCat.of (invariantSections ρ U)) :=
  letI := sectionsMulSemiringAction ρ U
  haveI := smulCommClass_sectionsMulSemiringAction ρ U
  Scheme.Spec.mapIso
    (Subalgebra.equivOfEq _ _
      (invariantSections_eq_fixedPoints ρ U)).toRingEquiv.toCommRingCatIso.op

variable {ρ} in
open TauCeti.AffineInvariantQuotient in
/-- `Spec` of the inclusion of the invariant sections over `U` is the affine invariant quotient
projection of the sections over `U`, up to `chartIso`. -/
private lemma specMap_invariantSections (U : X.Opens) :
    letI := sectionsMulSemiringAction ρ U
    Spec.map (CommRingCat.ofHom (algebraMap (invariantSections ρ U) Γ(A.X, U))) =
      projection Γ(A.X, U) G ≫ (chartIso ρ U).hom := by
  let := sectionsMulSemiringAction ρ U
  have := smulCommClass_sectionsMulSemiringAction ρ U
  rw [projection_def]
  exact Spec.map_comp
    (Subalgebra.equivOfEq _ _
      (invariantSections_eq_fixedPoints ρ U)).toRingEquiv.toCommRingCatIso.hom
    (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra Γ(X, U) Γ(A.X, U) G) Γ(A.X, U)))

/-- Restriction of sections preserves invariant sections. -/
lemma restrictSections_mem_invariantSections {U V : X.Opens} (i : V ⟶ U) {x : Γ(A.X, U)}
    (hx : x ∈ invariantSections ρ U) : A.restrictSections i x ∈ invariantSections ρ V := by
  rw [mem_invariantSections] at hx ⊢
  intro g
  rw [sectionsAlgHom_restrictSections, hx g]

/-- The presheaf of subalgebras of invariant sections of `A`. -/
def invariantSubalgebraPresheaf : A.SubalgebraPresheaf where
  sections := invariantSections ρ
  restrictSections_mem i _ := restrictSections_mem_invariantSections ρ i

@[simp]
lemma invariantSubalgebraPresheaf_sections (U : X.Opens) :
    (invariantSubalgebraPresheaf ρ).sections U = invariantSections ρ U :=
  (rfl)

/-- Over the basic open `X.basicOpen r` of an affine open `U`, the invariant sections of `A` are
the localization away from `r` of those over `U`. This is the counterpart of
`CommMon.isLocalization_basicOpen` for invariants, and uses that `G` is finite. -/
theorem isLocalization_invariantSections_basicOpen [Finite G] [A.X.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U)) :
    letI := ((A.restrictSections (homOfLE (X.basicOpen_le r))).restrict
      (invariantSections ρ U) (invariantSections ρ (X.basicOpen r))
      fun _ ↦ restrictSections_mem_invariantSections ρ _).toAlgebra
    IsLocalization.Away (algebraMap Γ(X, U) (invariantSections ρ U) r)
      (invariantSections ρ (X.basicOpen r)) := by
  set i : X.basicOpen r ⟶ U := homOfLE (X.basicOpen_le r)
  let _ := (A.restrictSections i).toAlgebra
  let _ : Algebra (invariantSections ρ U) (invariantSections ρ (X.basicOpen r)) :=
    ((A.restrictSections i).restrict _ _
      fun _ ↦ restrictSections_mem_invariantSections ρ _).toAlgebra
  -- The images of the invariant sections are the sections fixed by every `g`.
  have hmem (V : X.Opens) (x : Γ(A.X, V)) : x ∈ Set.range (algebraMap (invariantSections ρ V) _) ↔
      ∀ g, (sectionsAlgHom (ρ g).asIso.hom V).toRingHom x = x := by
    rw [Subalgebra.setRange_algebraMap]
    exact mem_invariantSections
  have : IsLocalization (Algebra.algebraMapSubmonoid Γ(A.X, U)
      (.powers (algebraMap Γ(X, U) (invariantSections ρ U) r))) Γ(A.X, X.basicOpen r) := by
    rw [Algebra.algebraMapSubmonoid_powers]
    exact A.isLocalization_basicOpen hU r
  exact TauCeti.FixedPoints.isLocalization_of_mem_range_iff _
    (fun g ↦ (sectionsAlgHom (ρ g).asIso.hom U).toRingHom)
    (fun g ↦ (sectionsAlgHom (ρ g).asIso.hom (X.basicOpen r)).toRingHom)
    (fun g ↦ sectionsAlgHom_restrictSections _ i) Subtype.val_injective (hmem U)
    Subtype.val_injective (hmem _) fun _ ↦ rfl

/-- On the affine opens of `X`, the presheaf of invariant sections is coequifibered over the
structure presheaf: its sections over basic opens are localizations. -/
instance isCoequifibered_invariantSubalgebraPresheaf [Finite G] [A.X.IsQuasicoherent] :
    (invariantSubalgebraPresheaf ρ).IsCoequifibered :=
  .of_isLocalizationAway fun hU r ↦ isLocalization_invariantSections_basicOpen ρ hU r

/-- The sections of `A` are integral over the invariant sections, since `G` is finite. -/
instance isIntegral_invariantSections [Finite G] (U : X.Opens) :
    Algebra.IsIntegral (invariantSections ρ U) Γ(A.X, U) := by
  let _ := sectionsMulSemiringAction ρ U
  have := smulCommClass_sectionsMulSemiringAction ρ U
  rw [invariantSections_eq_fixedPoints]
  exact Algebra.IsInvariant.isIntegral _ _ G

variable [Finite G] [A.X.IsQuasicoherent]

/-- The quotient projection `Spec_X(A) ⟶ Spec_X(A)/G` is invariant under the action of `G` on
`Spec_X(A)`. -/
@[reassoc (attr := simp)]
lemma relativeSpecMap_invariantSubalgebraPresheaf_relativeSpecπ (g : G) :
    relativeSpecMap (ρ g).asIso.hom ≫ (invariantSubalgebraPresheaf ρ).relativeSpecπ =
      (invariantSubalgebraPresheaf ρ).relativeSpecπ := by
  rw [(invariantSubalgebraPresheaf ρ).relativeSpecMap_relativeSpecπ (g := 𝟙 A)
    fun U x hx ↦ by rw [mem_invariantSections.mp hx g, sectionsAlgHom_id, AlgHom.id_apply],
    relativeSpecMap_id, Category.id_comp]

/-- The quotient projection is integral. -/
instance : IsIntegralHom (invariantSubalgebraPresheaf ρ).relativeSpecπ := by
  have : IsZariskiLocalAtTarget @IsIntegralHom.{u} :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ IsIntegralHom.hasAffineProperty
  refine ((invariantSubalgebraPresheaf ρ).relativeSpecπ_iff @IsIntegralHom).mpr fun U ↦ ?_
  exact IsIntegralHom.SpecMap_iff.mpr
    (algebraMap_isIntegral_iff.mpr (isIntegral_invariantSections ρ U.1))

/-- The quotient projection is surjective. -/
instance : Surjective (invariantSubalgebraPresheaf ρ).relativeSpecπ := by
  refine ((invariantSubalgebraPresheaf ρ).relativeSpecπ_iff @Surjective).mpr fun U ↦ ?_
  have := isIntegral_invariantSections ρ U.1
  exact ⟨Algebra.IsIntegral.comap_surjective (invariantSections ρ U.1) Γ(A.X, U.1)⟩

/-- The quotient projection is finite when `Spec_X(A)` is locally of finite type over `X`. -/
instance isFinite_invariantSubalgebraPresheaf_relativeSpecπ
    [LocallyOfFiniteType A.relativeSpecToBase] :
    IsFinite (invariantSubalgebraPresheaf ρ).relativeSpecπ := by
  have : LocallyOfFiniteType ((invariantSubalgebraPresheaf ρ).relativeSpecπ ≫
      (invariantSubalgebraPresheaf ρ).relativeSpecToBase) := by
    rwa [SubalgebraPresheaf.relativeSpecπ_relativeSpecToBase]
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
    ⟨inferInstance,
      locallyOfFiniteType_of_comp _ (invariantSubalgebraPresheaf ρ).relativeSpecToBase⟩

/-! ### The universal property of the quotient -/

section UniversalProperty

variable {ρ}

open TauCeti.AffineInvariantQuotient in
/-- Over an affine open `U` of `X`, the quotient projection is the affine invariant quotient
projection of the sections over `U`. -/
private lemma isPullback_projection (U : X.AffineZariskiSite) :
    letI := sectionsMulSemiringAction ρ U.toOpens
    IsPullback (projection Γ(A.X, U.toOpens) G ≫ (chartIso ρ U.toOpens).hom)
      (A.relativeSpecCover.f U) ((invariantSubalgebraPresheaf ρ).relativeSpecCover.f U)
      (invariantSubalgebraPresheaf ρ).relativeSpecπ := by
  have h := (invariantSubalgebraPresheaf ρ).isPullback_relativeSpecπ U
  rw [SubalgebraPresheaf.sectionsPresheafι_app_eq_algebraMap] at h
  rw [← specMap_invariantSections]
  exact h

omit [Finite G] in
open TauCeti.AffineInvariantQuotient in
/-- On an affine chart, the action of `g` on `Spec_X(A)` is the action on the spectrum of the
sections. -/
private lemma specComap_relativeSpecCover_f (U : X.AffineZariskiSite) (g : G) :
    letI := sectionsMulSemiringAction ρ U.toOpens
    specComap Γ(A.X, U.toOpens) G g ≫ A.relativeSpecCover.f U =
      A.relativeSpecCover.f U ≫ relativeSpecMap (ρ g).asIso.hom := by
  let := sectionsMulSemiringAction ρ U.toOpens
  rw [relativeSpecCover_f_relativeSpecMap, specComap_def]
  congr 2
  ext x
  exact sectionsMulSemiringAction_smul ρ U.toOpens g x

open TauCeti.AffineInvariantQuotient in
/-- **Points of the relative invariant quotient are orbits.** Two morphisms from the spectrum of a
field to `Spec_X(A)` with the same image in `Spec_X(A)/G` differ by the action of an element of
`G`. -/
theorem exists_comp_relativeSpecMap_eq {K : Type u} [Field K]
    {x₁ x₂ : Spec (CommRingCat.of K) ⟶ A.relativeSpec}
    (h : x₁ ≫ (invariantSubalgebraPresheaf ρ).relativeSpecπ =
      x₂ ≫ (invariantSubalgebraPresheaf ρ).relativeSpecπ) :
    ∃ g : G, x₁ ≫ relativeSpecMap (ρ g).asIso.hom = x₂ := by
  -- Both points lie over the same point of `X`; choose an affine open `U` containing it.
  have hbase : x₁ ≫ A.relativeSpecToBase = x₂ ≫ A.relativeSpecToBase := by
    simpa using congr($h ≫ (invariantSubalgebraPresheaf ρ).relativeSpecToBase)
  let pt : Spec (CommRingCat.of K) := default
  obtain ⟨V, hV, hmem, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top ((x₁ ≫ A.relativeSpecToBase) pt))
  let U : X.AffineZariskiSite := ⟨V, hV⟩
  -- Rebind the charts over `U` at their explicit sources, as in
  -- `SubalgebraPresheaf.relativeSpecπ_relativeSpecToBase`.
  let ι : Spec (CommRingCat.of Γ(A.X, U.toOpens)) ⟶ A.relativeSpec := A.relativeSpecCover.f U
  let ιQ : Spec (CommRingCat.of (invariantSections ρ U.toOpens)) ⟶
      (invariantSubalgebraPresheaf ρ).relativeSpec :=
    (invariantSubalgebraPresheaf ρ).relativeSpecCover.f U
  have : IsOpenImmersion ι := A.isOpenImmersion_relativeSpecCover_f U
  have : IsOpenImmersion ιQ :=
    (invariantSubalgebraPresheaf ρ).isOpenImmersion_relativeSpecCover_f U
  -- Over `U`, both points factor through the chart `Spec Γ(A.X, U) ⟶ Spec_X(A)`.
  have hrange (x : Spec (CommRingCat.of K) ⟶ A.relativeSpec)
      (hx : (x ≫ A.relativeSpecToBase) pt ∈ V) : Set.range x ⊆ Set.range ι := by
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y pt]
    exact (congrArg (fun W : A.relativeSpec.Opens ↦ x pt ∈ W)
      (relativeSpecToBase_preimage A U)).mp hx
  let y₁ := IsOpenImmersion.lift ι x₁ (hrange x₁ hmem)
  let y₂ := IsOpenImmersion.lift ι x₂ (hrange x₂ (hbase ▸ hmem))
  let := sectionsMulSemiringAction ρ U.toOpens
  -- The chart points have the same image in the affine invariant quotient of `Γ(A.X, U)`.
  have hw : (projection Γ(A.X, U.toOpens) G ≫ (chartIso ρ U.toOpens).hom) ≫ ιQ =
      ι ≫ (invariantSubalgebraPresheaf ρ).relativeSpecπ :=
    (isPullback_projection (ρ := ρ) U).w
  have key (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of Γ(A.X, U.toOpens))) :
      y ≫ projection Γ(A.X, U.toOpens) G ≫ (chartIso ρ U.toOpens).hom ≫ ιQ =
        y ≫ ι ≫ (invariantSubalgebraPresheaf ρ).relativeSpecπ := by
    rw [← hw, Category.assoc]
  have hy : y₁ ≫ projection Γ(A.X, U.toOpens) G = y₂ ≫ projection Γ(A.X, U.toOpens) G := by
    refine (cancel_mono ((chartIso ρ U.toOpens).hom ≫ ιQ)).mp ?_
    rw [Category.assoc, Category.assoc, key, key, IsOpenImmersion.lift_fac_assoc,
      IsOpenImmersion.lift_fac_assoc, h]
  obtain ⟨g, hg⟩ := exists_comp_specComap_eq Γ(A.X, U.toOpens) G hy
  have hι : specComap Γ(A.X, U.toOpens) G g ≫ ι = ι ≫ relativeSpecMap (ρ g).asIso.hom :=
    specComap_relativeSpecCover_f (ρ := ρ) U g
  refine ⟨g, ?_⟩
  rw [← IsOpenImmersion.lift_fac ι x₁ (hrange x₁ hmem), Category.assoc, ← hι,
    ← Category.assoc]
  exact (congrArg (· ≫ ι) hg).trans (IsOpenImmersion.lift_fac _ _ _)

/-- The stalk maps of the quotient projection `Spec_X(A) ⟶ Spec_X(A)/G` are injective. -/
theorem stalkMap_invariantSubalgebraPresheaf_relativeSpecπ_injective (x : A.relativeSpec) :
    Function.Injective ((invariantSubalgebraPresheaf ρ).relativeSpecπ.stalkMap x) := by
  have hP := RingHom.injective_respectsIso
  have := stalkwiseIsZariskiLocalAtTarget_of_respectsIso hP
  have := stalkwise_respectsIso hP
  refine ((invariantSubalgebraPresheaf ρ).relativeSpecπ_iff
    (stalkwise fun f ↦ Function.Injective f)).mpr (fun U ↦ ?_) x
  let := sectionsMulSemiringAction ρ U.toOpens
  have := smulCommClass_sectionsMulSemiringAction ρ U.toOpens
  rw [invariantSubalgebraPresheaf_sections, specMap_invariantSections]
  exact MorphismProperty.RespectsIso.postcomp _ _ _
    (TauCeti.AffineInvariantQuotient.stalkMap_projection_injective _ G)

/-- The quotient projection `Spec_X(A) ⟶ Spec_X(A)/G` is an epimorphism of schemes. -/
instance : Epi (invariantSubalgebraPresheaf ρ).relativeSpecπ :=
  Scheme.Hom.epi_of_surjective_of_stalkMap_injective _
    stalkMap_invariantSubalgebraPresheaf_relativeSpecπ_injective

open TauCeti.AffineInvariantQuotient in
/-- The universal property for arbitrary target schemes, as an existence statement. -/
private theorem exists_relativeSpecπ_comp_eq {Z : Scheme.{u}} (f : A.relativeSpec ⟶ Z)
    (hf : ∀ g : G, relativeSpecMap (ρ g).asIso.hom ≫ f = f) :
    ∃ h, (invariantSubalgebraPresheaf ρ).relativeSpecπ ≫ h = f := by
  -- Over each affine chart, `f` descends by the universal property of the affine quotient.
  have hloc (U : X.AffineZariskiSite) :
      ∃ u : (invariantSubalgebraPresheaf ρ).relativeSpecCover.X U ⟶ Z,
        pullback.fst (invariantSubalgebraPresheaf ρ).relativeSpecπ
            ((invariantSubalgebraPresheaf ρ).relativeSpecCover.f U) ≫ f =
          pullback.snd _ _ ≫ u := by
    let := sectionsMulSemiringAction ρ U.toOpens
    have := smulCommClass_sectionsMulSemiringAction ρ U.toOpens
    have hpb := (isPullback_projection (ρ := ρ) U).flip
    have hfU (g : G) : specComap Γ(A.X, U.toOpens) G g ≫ A.relativeSpecCover.f U ≫ f =
        A.relativeSpecCover.f U ≫ f :=
      (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ f) (specComap_relativeSpecCover_f (ρ := ρ) U g)).trans <|
          (Category.assoc _ _ _).trans (congrArg _ (hf g))
    refine ⟨(chartIso ρ U.toOpens).inv ≫ descOfFinite _ hfU, ?_⟩
    refine (cancel_epi hpb.isoPullback.hom).mp ?_
    have e1 := congrArg (· ≫ f) hpb.isoPullback_hom_fst
    have e2 := congrArg (· ≫ (chartIso ρ U.toOpens).inv ≫ descOfFinite _ hfU)
      hpb.isoPullback_hom_snd
    simp only [Category.assoc, Iso.hom_inv_id_assoc] at e1 e2
    exact e1.trans ((projection_descOfFinite _ hfU).symm.trans e2.symm)
  choose u hu using hloc
  -- The local descents glue, since the projection stays an epimorphism over open subschemes.
  exact Scheme.Hom.exists_comp_eq_of_openCover _
    (fun _ g _ ↦ Scheme.Hom.epi_pullback_snd_of_isOpenImmersion _ g
      stalkMap_invariantSubalgebraPresheaf_relativeSpecπ_injective)
    (invariantSubalgebraPresheaf ρ).relativeSpecCover f u hu

/-- The morphism `Spec_X(A)/G ⟶ Z` induced by a `G`-invariant morphism `Spec_X(A) ⟶ Z` to an
arbitrary scheme. -/
def invariantQuotientDesc {Z : Scheme.{u}} (f : A.relativeSpec ⟶ Z)
    (hf : ∀ g : G, relativeSpecMap (ρ g).asIso.hom ≫ f = f) :
    (invariantSubalgebraPresheaf ρ).relativeSpec ⟶ Z :=
  (exists_relativeSpecπ_comp_eq f hf).choose

/-- The induced morphism factors the given invariant morphism through the quotient projection. -/
@[reassoc (attr := simp)]
lemma relativeSpecπ_invariantQuotientDesc {Z : Scheme.{u}} (f : A.relativeSpec ⟶ Z)
    (hf : ∀ g : G, relativeSpecMap (ρ g).asIso.hom ≫ f = f) :
    (invariantSubalgebraPresheaf ρ).relativeSpecπ ≫ invariantQuotientDesc f hf = f :=
  (exists_relativeSpecπ_comp_eq f hf).choose_spec

/-- Morphisms from the quotient `Spec_X(A)/G` to an arbitrary scheme are determined by their
composition with the quotient projection. -/
@[ext]
lemma invariantQuotient_hom_ext {Z : Scheme.{u}}
    {h₁ h₂ : (invariantSubalgebraPresheaf ρ).relativeSpec ⟶ Z}
    (e : (invariantSubalgebraPresheaf ρ).relativeSpecπ ≫ h₁ =
      (invariantSubalgebraPresheaf ρ).relativeSpecπ ≫ h₂) : h₁ = h₂ :=
  (cancel_epi _).mp e

/-- **The universal property of the relative invariant quotient by a finite group.** Every
`G`-invariant morphism from `Spec_X(A)` to an arbitrary scheme factors uniquely through the
quotient projection `Spec_X(A) ⟶ Spec_X(A)/G`. -/
theorem existsUnique_relativeSpecπ_comp_eq {Z : Scheme.{u}} (f : A.relativeSpec ⟶ Z)
    (hf : ∀ g : G, relativeSpecMap (ρ g).asIso.hom ≫ f = f) :
    ∃! h, (invariantSubalgebraPresheaf ρ).relativeSpecπ ≫ h = f :=
  ⟨invariantQuotientDesc f hf, relativeSpecπ_invariantQuotientDesc f hf, fun _ hh ↦
    invariantQuotient_hom_ext (hh.trans (relativeSpecπ_invariantQuotientDesc f hf).symm)⟩

/-- Descending the composite of the quotient projection with a morphism to an arbitrary scheme
recovers that morphism. -/
@[simp]
lemma invariantQuotientDesc_relativeSpecπ_comp {Z : Scheme.{u}}
    (h : (invariantSubalgebraPresheaf ρ).relativeSpec ⟶ Z) :
    invariantQuotientDesc ((invariantSubalgebraPresheaf ρ).relativeSpecπ ≫ h)
      (fun g ↦ by simp) = h :=
  invariantQuotient_hom_ext (relativeSpecπ_invariantQuotientDesc _ _)

end UniversalProperty

/-! ### Free actions -/

section Free

variable {ρ}

omit [Finite G] [A.X.IsQuasicoherent] in
/-- Over an affine open `U` of `X`, freeness of the action on the sections over `U`, in the form
used by the affine invariant quotient. -/
private lemma free_sectionsMulSemiringAction
    (hG : ∀ (U : X.affineOpens) (g : G), g ≠ 1 →
      Ideal.span (Set.range fun x : Γ(A.X, U) ↦ sectionsAlgHom (ρ g).asIso.hom U x - x) = ⊤)
    (U : X.AffineZariskiSite) :
    letI := sectionsMulSemiringAction ρ U.toOpens
    ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun x : Γ(A.X, U.toOpens) ↦ g • x - x) = ⊤ := by
  let := sectionsMulSemiringAction ρ U.toOpens
  intro g hg
  simpa only [sectionsMulSemiringAction_smul] using hG ⟨U.1, U.2⟩ g hg

variable
    (hG : ∀ (U : X.affineOpens) (g : G), g ≠ 1 →
      Ideal.span (Set.range fun x : Γ(A.X, U) ↦ sectionsAlgHom (ρ g).asIso.hom U x - x) = ⊤)
include hG

/-- For a free action, the quotient projection `Spec_X(A) ⟶ Spec_X(A)/G` is étale. -/
theorem etale_invariantSubalgebraPresheaf_relativeSpecπ_of_free :
    Etale (invariantSubalgebraPresheaf ρ).relativeSpecπ := by
  have := HasRingHomProperty.instIsZariskiLocalAtTarget @Etale.{u} (Q := RingHom.Etale)
  refine ((invariantSubalgebraPresheaf ρ).relativeSpecπ_iff @Etale).mpr fun U ↦ ?_
  let := sectionsMulSemiringAction ρ U.toOpens
  have := TauCeti.AffineInvariantQuotient.etale_projection (free_sectionsMulSemiringAction hG U)
  rw [invariantSubalgebraPresheaf_sections, specMap_invariantSections]
  infer_instance

/-- For a free action, the quotient projection `Spec_X(A) ⟶ Spec_X(A)/G` is finite, with no
finiteness hypothesis on `Spec_X(A)` over `X`. -/
theorem isFinite_invariantSubalgebraPresheaf_relativeSpecπ_of_free :
    IsFinite (invariantSubalgebraPresheaf ρ).relativeSpecπ := by
  have := etale_invariantSubalgebraPresheaf_relativeSpecπ_of_free hG
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨inferInstance, inferInstance⟩

open TauCeti.AffineInvariantQuotient in
/-- **The torsor square of a free relative quotient.** For a free action, the identity and the
action of `g` on the component of `g` exhibit `∐_g Spec_X(A)` as the kernel pair
`Spec_X(A) ×_{Spec_X(A)/G} Spec_X(A)` of the quotient projection. -/
theorem isPullback_invariantSubalgebraPresheaf_relativeSpecπ_of_free :
    IsPullback (Sigma.desc fun _ : G ↦ 𝟙 A.relativeSpec)
      (Sigma.desc fun g : G ↦ relativeSpecMap (ρ g).asIso.hom)
      (invariantSubalgebraPresheaf ρ).relativeSpecπ
      (invariantSubalgebraPresheaf ρ).relativeSpecπ := by
  refine Scheme.isPullback_of_openCover _ _ _ _ A.relativeSpecCover fun U ↦ ?_
  let := sectionsMulSemiringAction ρ U.toOpens
  -- Rebind the charts over `U` at their explicit sources, as in
  -- `SubalgebraPresheaf.relativeSpecπ_relativeSpecToBase`.
  let ι : Spec (CommRingCat.of Γ(A.X, U.toOpens)) ⟶ A.relativeSpec := A.relativeSpecCover.f U
  let ιQ : Spec (CommRingCat.of (invariantSections ρ U.toOpens)) ⟶
      (invariantSubalgebraPresheaf ρ).relativeSpec :=
    (invariantSubalgebraPresheaf ρ).relativeSpecCover.f U
  let e := chartIso ρ U.toOpens
  -- The base change of `∐_g Spec_X(A)` along the chart over `U` is `∐_g` of the chart.
  have hb : IsPullback (Sigma.desc fun g : G ↦ ι ≫ Sigma.ι (fun _ : G ↦ A.relativeSpec) g)
      (Sigma.desc fun _ : G ↦ 𝟙 (Spec (CommRingCat.of Γ(A.X, U.toOpens))))
      (Sigma.desc fun _ : G ↦ 𝟙 A.relativeSpec) ι := by
    have hd (Z : Scheme.{u}) (f : G → (Spec (CommRingCat.of Γ(A.X, U.toOpens)) ⟶ Z)) :
        Cofan.IsColimit.desc (coproductIsCoproduct _) f = Sigma.desc f :=
      Sigma.hom_ext _ _ fun g ↦ (Cofan.IsColimit.fac _ _ g).trans (Sigma.ι_comp_desc _ g).symm
    have h := IsUniversalColimit.isPullback_of_isColimit_right
      (FinitaryPreExtensive.isUniversal_finiteCoproducts
        (coproductIsCoproduct fun _ : G ↦ A.relativeSpec))
      (fun _ ↦ 𝟙 _) (Sigma.desc fun _ : G ↦ 𝟙 A.relativeSpec) ι (fun _ ↦ ι) (fun _ ↦ 𝟙 _)
      (fun _ ↦ IsPullback.id_vert ι)
      (coproductIsCoproduct fun _ : G ↦ Spec (CommRingCat.of Γ(A.X, U.toOpens)))
      (fun g ↦ Sigma.ι_comp_desc _ g)
    rwa [hd, hd] at h
  -- Over the chart, the square is the torsor square of the affine quotient, followed by the
  -- chart of the quotient projection.
  have hchart : IsPullback ι (projection Γ(A.X, U.toOpens) G)
      (invariantSubalgebraPresheaf ρ).relativeSpecπ (e.hom ≫ ιQ) :=
    ((isPullback_projection (ρ := ρ) U).of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
      (by simp [e]) ((Category.comp_id _).trans (Category.id_comp _).symm)
      (by rw [Iso.symm_hom, Iso.inv_hom_id_assoc]; exact Category.comp_id _) (by simp)).flip
  have hpaste :=
    (isPullback_of_free Γ(A.X, U.toOpens) G (free_sectionsMulSemiringAction hG U)).flip.paste_horiz
      hchart
  refine hpaste.flip.of_iso hb.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans hb.isoPullback_hom_snd.symm
  · -- The components of the pulled-back cover are the first projections, as in
    -- `PreZeroHypercover.pullback₁_f`, and `ι` is the chart over `U`.
    refine Sigma.hom_ext _ _ fun g ↦ ?_
    calc _ = specComap Γ(A.X, U.toOpens) G g ≫ ι := by simp
      _ = ι ≫ relativeSpecMap (ρ g).asIso.hom := specComap_relativeSpecCover_f U g
      _ = Sigma.ι _ g ≫ (hb.isoPullback.hom ≫ pullback.fst _ ι) ≫
          Sigma.desc fun g ↦ relativeSpecMap (ρ g).asIso.hom := by
        rw [hb.isoPullback_hom_fst]; simp
      _ = _ := by rw [Category.assoc]; rfl
  · exact (Category.comp_id _).trans (((Category.assoc _ _ _).symm.trans
      (isPullback_projection (ρ := ρ) U).w).trans (Category.id_comp _).symm)
  · simp

/-- **The fppf quotient of a free relative action.** For a free action, under the Yoneda embedding
into fppf sheaves, the quotient projection `Spec_X(A) ⟶ Spec_X(A)/G` is the coequalizer of the two
maps `∐_g Spec_X(A) ⇉ Spec_X(A)` given by the identity and by the action of `g` on the component
of `g`. Thus `Spec_X(A)/G` represents the fppf quotient sheaf of `Spec_X(A)` by `G`. -/
def isColimitInvariantQuotientFppfYonedaCofork :
    IsColimit (Cofork.ofπ
        (Scheme.fppfTopology.yoneda.map (invariantSubalgebraPresheaf ρ).relativeSpecπ)
        (by simp only [← Functor.map_comp,
          (isPullback_invariantSubalgebraPresheaf_relativeSpecπ_of_free hG).w]) :
      Cofork (Scheme.fppfTopology.yoneda.map (Sigma.desc fun _ : G ↦ 𝟙 A.relativeSpec))
        (Scheme.fppfTopology.yoneda.map
          (Sigma.desc fun g : G ↦ relativeSpecMap (ρ g).asIso.hom))) :=
  have := etale_invariantSubalgebraPresheaf_relativeSpecπ_of_free hG
  IsKernelPair.isColimitYonedaCofork Scheme.fppfTopology
    (isPullback_invariantSubalgebraPresheaf_relativeSpecπ_of_free hG)
    (Precoverage.generate_mem_toGrothendieck (Scheme.Hom.singleton_mem_fppfPrecoverage _))

end Free

end

end CategoryTheory.CommMon
