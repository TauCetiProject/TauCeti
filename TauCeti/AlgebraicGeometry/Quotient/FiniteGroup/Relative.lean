/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Invariant.Basic
public import TauCeti.AlgebraicGeometry.RelativeSpec.Equalizer
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
preimages of the affine opens of `X` form one. The universal property of the quotient and the
étaleness of the projection for free actions are not proved in this file.

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

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §1 (quotients of
  affine schemes by finite groups).
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

end

end CategoryTheory.CommMon
