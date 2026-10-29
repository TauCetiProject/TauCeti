/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Descent.Invariants
public import TauCeti.AlgebraicGeometry.Restrict
public import TauCeti.AlgebraicGeometry.RelativeSpec.Affine
public import TauCeti.AlgebraicGeometry.RelativeSpec.Counit
public import TauCeti.AlgebraicGeometry.RelativeSpec.Equalizer

/-!
# The descended scheme of a descent datum on an affine morphism

Let `p : S' ⟶ S` be an affine morphism of schemes and `D` a descent datum relative to `p`, in the
sense of `TauCeti.DescentDatum p X`, on a scheme `X ⟶ S'` affine over `S'`. Write
`π = X.hom ≫ p : X ⟶ S`, an affine morphism. The datum gives two morphisms over `S`
from `S' ×_S X` to `X`: the action `(s, x) ↦ s · x` and the second projection `(s, x) ↦ x`. On
functions, these are two morphisms of quasi-coherent `𝒪_S`-algebras `π_* 𝒪_X ⟶ (π')_* 𝒪_{S' ×_S X}`,
and this file defines the *descended scheme* `D.descended` as the relative spectrum over `S` of
their equalizer (`CommMon.equalizerSubalgebraPresheaf`). Over an affine open `U` of `S` it is
the spectrum of the functions on `π⁻¹ U` which are invariant under the descent datum
(`CommMon.SubalgebraPresheaf.isPullback_relativeSpecCover`); this is the global form of the
invariant subalgebra `TauCeti.Algebra.DescentDatum.descended` used over an affine base.

The quotient map `D.toDescended : X ⟶ D.descended` lies over `S` and is invariant under the
action (`DescentDatum.act_toDescended`). Consequently it induces a morphism of descent data
`D.toBaseChangeDescended : Hom D (baseChange p D.descended)` from `D` to the canonical descent
datum on `D.descended ×_S S'`. Faithfully flat descent for affine morphisms asserts that this
comparison is an isomorphism when `p` is flat, so that `D` is then effective with descended
scheme `D.descended`.

This file constructs the comparison and proves that it is an isomorphism whenever `p` is flat
(`DescentDatum.isIso_toBaseChangeDescended_hom`), over an arbitrary base `S`. Being an
isomorphism is local on `S`, so it suffices to work over an affine open `U` of `S`. There the
descent datum restricts to the descent datum `D.pullbackAlong U.ι` relative to `U ×_S S' ⟶ U`,
on `X ×_{S'} (U ×_S S')`, the part of `X` over `U`. Its invariant functions are the equalizer
sections over `U`, by which the chart of `D.descended` over `U` is defined. Effective descent for
affine schemes in terms of invariant functions (`DescentDatum.isPushout_invariants`) then shows
that the part of `X` over `U` is the base change of this chart.

## Main declarations

* `TauCeti.DescentDatum.actAlgebraMap D` and `TauCeti.DescentDatum.sndAlgebraMap p X`: pullback
  of functions along the action and along the second projection;
* `TauCeti.DescentDatum.descended D`: the descended scheme, affine over `S`, identified with the
  relative spectrum of the equalizer by `TauCeti.DescentDatum.descended_left` and
  `TauCeti.DescentDatum.descended_hom`;
* `TauCeti.DescentDatum.toDescended D`: the quotient map `X ⟶ D.descended` over `S`, with
  `TauCeti.DescentDatum.relativeSpecFunctionsToScheme_toDescended` and
  `TauCeti.DescentDatum.act_toDescended`;
* `TauCeti.DescentDatum.toBaseChangeDescended D`: the comparison morphism of descent data from `D`
  to the canonical descent datum on the base change of `D.descended`;
* `TauCeti.DescentDatum.isIso_toBaseChangeDescended_hom`: for `p` flat, the comparison is an
  isomorphism, so that `D` is effective with descended scheme `D.descended`.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII,
  Théorème 2.1.
* The Stacks Project, Chapter *Descent*, Section *Descent data for schemes over schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

namespace DescentDatum

universe u

noncomputable section

variable {S S' : Scheme.{u}} {p : S' ⟶ S} [IsAffineHom p] {X : Over S'} [IsAffineHom X.hom]
  (D : DescentDatum p X)

omit [IsAffineHom X.hom] in
/-- The structure morphism `S' ×_S X ⟶ S` is affine. -/
instance isAffineHom_pullback_snd_comp :
    IsAffineHom (pullback.snd p (X.hom ≫ p) ≫ X.hom ≫ p) :=
  have : IsAffineHom (pullback.snd p (X.hom ≫ p)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  inferInstance

/-- Pullback of functions along the action of `D`, as a morphism of function algebras over `S`. -/
abbrev actAlgebraMap :
    (X.hom ≫ p).pushforwardStructureAlgebra ⟶
      (pullback.snd p (X.hom ≫ p) ≫ X.hom ≫ p).pushforwardStructureAlgebra :=
  Scheme.Hom.pushforwardStructureAlgebraMap D.act D.act_comp_hom_comp

variable (p X) in
/-- Pullback of functions along the second projection `S' ×_S X ⟶ X`, as a morphism of function
algebras over `S`. -/
abbrev sndAlgebraMap :
    (X.hom ≫ p).pushforwardStructureAlgebra ⟶
      (pullback.snd p (X.hom ≫ p) ≫ X.hom ≫ p).pushforwardStructureAlgebra :=
  Scheme.Hom.pushforwardStructureAlgebraMap (pullback.snd p (X.hom ≫ p)) rfl

/-- The scheme descended from a descent datum `D` on an affine morphism `X ⟶ S'`: the relative
spectrum over `S` of the functions on `X` whose pullbacks along the action and along the second
projection `S' ×_S X ⟶ X` agree. -/
-- Implicitly reducible, so that morphisms into `D.descended.left` unify with morphisms into the
-- relative spectrum of the equalizer, and the equalizer lemmas rewrite them.
@[expose, implicit_reducible]
def descended : Over S :=
  Over.mk
    (CommMon.equalizerSubalgebraPresheaf D.actAlgebraMap (sndAlgebraMap p X)).relativeSpecToBase

/-- The underlying scheme of the descended scheme is the relative spectrum of the equalizer of
`D.actAlgebraMap` and `sndAlgebraMap p X`. -/
theorem descended_left :
    D.descended.left =
      (CommMon.equalizerSubalgebraPresheaf D.actAlgebraMap (sndAlgebraMap p X)).relativeSpec :=
  (rfl)

/-- The structure morphism of the descended scheme is that of the relative spectrum of the
equalizer. -/
theorem descended_hom :
    D.descended.hom = CommMon.SubalgebraPresheaf.relativeSpecToBase
      (CommMon.equalizerSubalgebraPresheaf D.actAlgebraMap (sndAlgebraMap p X)) :=
  (rfl)

/-- The descended scheme is affine over `S`. -/
instance isAffineHom_descended_hom : IsAffineHom D.descended.hom := by
  rw [descended_hom]
  infer_instance

/-- The quotient map from `X` to the scheme descended from `D`. -/
def toDescended : X.left ⟶ D.descended.left :=
  inv (X.hom ≫ p).relativeSpecFunctionsToScheme ≫
    (CommMon.equalizerSubalgebraPresheaf D.actAlgebraMap (sndAlgebraMap p X)).relativeSpecπ

/-- Through the identification of `X` with the relative spectrum of its functions over `S`, the
quotient map is the projection `CommMon.SubalgebraPresheaf.relativeSpecπ`. -/
@[reassoc]
theorem relativeSpecFunctionsToScheme_toDescended :
    (X.hom ≫ p).relativeSpecFunctionsToScheme ≫ D.toDescended =
      (CommMon.equalizerSubalgebraPresheaf D.actAlgebraMap (sndAlgebraMap p X)).relativeSpecπ := by
  rw [toDescended, IsIso.hom_inv_id_assoc]

/-- The quotient map lies over `S`. -/
@[reassoc (attr := simp)]
theorem toDescended_hom : D.toDescended ≫ D.descended.hom = X.hom ≫ p := by
  rw [← cancel_epi (X.hom ≫ p).relativeSpecFunctionsToScheme,
    relativeSpecFunctionsToScheme_toDescended_assoc, descended_hom,
    CommMon.SubalgebraPresheaf.relativeSpecπ_relativeSpecToBase,
    Scheme.Hom.relativeSpecFunctionsToScheme_comp]

/-- The quotient map is invariant under the descent datum: `s · x` and `x` have the same image. -/
@[reassoc]
theorem act_toDescended :
    D.act ≫ D.toDescended = pullback.snd p (X.hom ≫ p) ≫ D.toDescended := by
  -- Both maps are, through the identifications of affine schemes over `S` with the relative
  -- spectra of their function algebras, the relative spectra of the two algebra maps, which
  -- the projection to the relative spectrum of the equalizer coequalizes.
  rw [toDescended,
    Scheme.Hom.inv_relativeSpecFunctionsToScheme_naturality_assoc D.act D.act_comp_hom_comp,
    Scheme.Hom.inv_relativeSpecFunctionsToScheme_naturality_assoc _ rfl,
    CommMon.relativeSpecMap_equalizerSubalgebraPresheaf_relativeSpecπ]

/-- The comparison morphism from `D` to the canonical descent datum on the base change
`D.descended ×_S S'` of the descended scheme, `x ↦ (D.toDescended x, X.hom x)`. When it is an
isomorphism, the descent datum `D` is effective with descended scheme `D.descended`. -/
def toBaseChangeDescended : Hom D (baseChange p D.descended) where
  hom := Over.homMk (pullback.lift D.toDescended X.hom D.toDescended_hom) (pullback.lift_snd _ _ _)
  map_act := by
    apply pullback.hom_ext
    · simp [act_toDescended]
    · simp

/-- The first component of the comparison morphism is the quotient map. -/
@[reassoc (attr := simp)]
theorem toBaseChangeDescended_hom_left_fst :
    D.toBaseChangeDescended.hom.left ≫ pullback.fst D.descended.hom p = D.toDescended :=
  pullback.lift_fst _ _ _

/-- The second component of the comparison morphism is the structure morphism `X ⟶ S'`. -/
@[reassoc (attr := simp)]
theorem toBaseChangeDescended_hom_left_snd :
    D.toBaseChangeDescended.hom.left ≫ pullback.snd D.descended.hom p = X.hom :=
  pullback.lift_snd _ _ _

section Effective

open Opposite

omit [IsAffineHom p] [IsAffineHom X.hom] in
variable {D} in
/-- Over an open `U` of `S`, the equalizer sections of the function algebra of `X ⟶ S` are the
functions on the inverse image of `U` which become invariant under the restriction
`D.pullbackAlong U.ι` of `D` over `U`, once pulled back to its carrier
`X ×_{S'} (U ×_S S') ≅ (X.hom ≫ p) ⁻¹ᵁ U`. -/
private theorem mem_equalizerSections_iff {U : S.Opens} {x : Γ(X.left, (X.hom ≫ p) ⁻¹ᵁ U)} :
    ((X.hom ≫ p).pushforwardStructureAlgebraSectionsRingEquiv U).symm x ∈
        CommMon.equalizerSections D.actAlgebraMap (sndAlgebraMap p X) U ↔
      (pullback.fst X.hom (pullback.snd U.ι p)).appLE _ ⊤
          (isPullback_pullbackAlongObj U.ι X).toCommSq.top_le_preimage_preimage x ∈
        (D.pullbackAlong U.ι).invariants := by
  have hP := isPullback_pullbackAlongActionComparison (p := p) U.ι X
  have : IsIso ((pullbackAlongActionComparison (p := p) U.ι X).appLE _ ⊤
      hP.toCommSq.top_le_preimage_preimage) := hP.isIso_appLE
  -- Pulling back along a morphism `aU` of the restricted action space which the comparisons
  -- intertwine with a morphism `a` of the action space is restriction of the pullback along `a`.
  have key (a : pullback p (X.hom ≫ p) ⟶ X.left)
      (ha : a ≫ X.hom ≫ p = pullback.snd p (X.hom ≫ p) ≫ X.hom ≫ p) (aU)
      (hU : aU ≫ pullback.fst X.hom (pullback.snd U.ι p) =
        pullbackAlongActionComparison (p := p) U.ι X ≫ a) :
      aU.appTop ((pullback.fst X.hom (pullback.snd U.ι p)).appLE _ ⊤
          (isPullback_pullbackAlongObj U.ι X).toCommSq.top_le_preimage_preimage x) =
        (pullbackAlongActionComparison (p := p) U.ι X).appLE _ ⊤
          hP.toCommSq.top_le_preimage_preimage
          (a.appLE ((X.hom ≫ p) ⁻¹ᵁ U) ((pullback.snd p (X.hom ≫ p) ≫ X.hom ≫ p) ⁻¹ᵁ U)
            (by rw [← Scheme.Hom.comp_preimage, ha]) x) := by
    -- `Scheme.Hom.app_eq_appLE` states this with the open `aU ⁻¹ᵁ ⊤`, which is `⊤` only up to
    -- defeq; the `show` retypes it with `⊤` so that the composite below is well-typed.
    rw [show aU.appTop = aU.appLE ⊤ ⊤ (Scheme.Hom.preimage_top aU).ge from
        Scheme.Hom.app_eq_appLE _,
      ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE]
    exact congr($(Scheme.Hom.congr_appLE _ hU _ _ _ _) x)
  rw [CommMon.mem_equalizerSections, mem_invariants_iff,
    Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply,
    Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply, RingEquiv.apply_symm_apply,
    EmbeddingLike.apply_eq_iff_eq,
    key D.act D.act_comp_hom_comp _ (pullbackAlong_act_fst U.ι D),
    key (pullback.snd p (X.hom ≫ p)) rfl _ (pullbackAlongActionComparison_snd U.ι X).symm,
    (ConcreteCategory.bijective_of_isIso
      ((pullbackAlongActionComparison (p := p) U.ι X).appLE _ ⊤ _)).injective.eq_iff]

omit [IsAffineHom p] [IsAffineHom X.hom] in
/-- The equalizer sections over an open `U` of `S` are isomorphic to the invariant functions of
the restriction of `D` over `U`, by pullback along `X ×_{S'} (U ×_S S') ⟶ X`. -/
private noncomputable def equalizerSectionsEquiv (U : S.Opens) :
    (CommMon.equalizerSubalgebraPresheaf D.actAlgebraMap (sndAlgebraMap p X)).sections U ≃+*
      (D.pullbackAlong U.ι).invariants :=
  have := (isPullback_pullbackAlongObj (p := p) U.ι X).isIso_appLE
  (((X.hom ≫ p).pushforwardStructureAlgebraSectionsRingEquiv U).trans
    (RingEquiv.ofBijective _ (ConcreteCategory.bijective_of_isIso
      ((pullback.fst X.hom (pullback.snd U.ι p)).appLE _ ⊤
        (isPullback_pullbackAlongObj U.ι X).toCommSq.top_le_preimage_preimage)))).restrict _ _
    fun x ↦ by
      have h := mem_equalizerSections_iff (D := D)
        (x := (X.hom ≫ p).pushforwardStructureAlgebraSectionsRingEquiv U x)
      rwa [RingEquiv.symm_apply_apply, ← CommMon.equalizerSubalgebraPresheaf_sections] at h

omit [IsAffineHom p] [IsAffineHom X.hom] in
/-- The isomorphism `equalizerSectionsEquiv` is pullback of functions along the inclusion of the
part of `X` over `U`. -/
private theorem coe_equalizerSectionsEquiv_apply (U : S.Opens)
    (x : (CommMon.equalizerSubalgebraPresheaf D.actAlgebraMap (sndAlgebraMap p X)).sections U) :
    (D.equalizerSectionsEquiv U x : Γ((pullbackAlongObj (p := p) U.ι X).left, ⊤)) =
      (pullback.fst X.hom (pullback.snd U.ι p)).appLE _ ⊤
        (isPullback_pullbackAlongObj U.ι X).toCommSq.top_le_preimage_preimage
        ((X.hom ≫ p).pushforwardStructureAlgebraSectionsRingEquiv U x) :=
  (rfl)

/-- Over an affine open `U` of `S`, effective descent for the restriction `D.pullbackAlong U.ι` of
`D`, with its invariant functions replaced by the equalizer sections over `U`: the carrier
`X ×_{S'} (U ×_S S')` is the base change of `Spec` of the equalizer sections along
`U ×_S S' ⟶ U`. -/
private theorem isPullback_spec_equalizerSections [Flat p] {U : S.Opens} (hU : IsAffineOpen U) :
    IsPullback ((pullbackAlongObj (p := p) U.ι X).left.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (D.pullbackAlong U.ι).invariants.subtype) ≫
          Spec.map (CommRingCat.ofHom (D.equalizerSectionsEquiv U).toRingHom))
      (pullbackAlongObj (p := p) U.ι X).hom
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) ((CommMon.equalizerSubalgebraPresheaf
        D.actAlgebraMap (sndAlgebraMap p X)).sections U))) ≫ hU.isoSpec.inv)
      (pullback.fst U.ι p) := by
  have : IsAffine U := hU
  have : IsAffineHom (pullback.fst U.ι p) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip ‹_›
  have : IsAffineHom (pullback.snd X.hom (pullback.snd U.ι p)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  have : IsAffine (pullback U.ι p) := isAffine_of_isAffineHom (pullback.fst U.ι p)
  have : IsAffine (pullbackAlongObj (p := p) U.ι X).left :=
    isAffine_of_isAffineHom (pullback.snd X.hom (pullback.snd U.ι p) ≫ pullback.fst U.ι p)
  -- Effective descent for the restricted datum over the affine scheme `U`.
  have hpb : IsPullback ((pullbackAlongObj (p := p) U.ι X).left.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (D.pullbackAlong U.ι).invariants.subtype))
      (pullbackAlongObj (p := p) U.ι X).hom
      (Spec.map (CommRingCat.ofHom (D.pullbackAlong U.ι).toInvariants) ≫
        (U : Scheme).isoSpec.inv)
      (pullback.fst U.ι p) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (D.pullbackAlong U.ι).isPushout_invariants).of_iso
      (pullbackAlongObj (p := p) U.ι X).left.isoSpec.symm (Iso.refl _)
      (pullback U.ι p).isoSpec.symm (U : Scheme).isoSpec.symm (by simp)
      (by simp [Scheme.isoSpec_inv_naturality]) (by simp) (by simp [Scheme.isoSpec_inv_naturality])
  refine hpb.of_iso (Iso.refl _)
    (Scheme.Spec.mapIso (D.equalizerSectionsEquiv U).toCommRingCatIso.op) (Iso.refl _)
    (Iso.refl _) (by simp) (by simp) ?_ (by simp)
  -- It remains to see that the functions on `S` restricted to `U` map to the invariant functions
  -- of the restricted datum as they do through the equalizer sections.
  have hr : (U.topIso.hom ≫ CommRingCat.ofHom (algebraMap Γ(S, U)
      ((CommMon.equalizerSubalgebraPresheaf D.actAlgebraMap (sndAlgebraMap p X)).sections U)) ≫
        CommRingCat.ofHom (D.equalizerSectionsEquiv U).toRingHom :
      Γ(U, ⊤) ⟶ CommRingCat.of (D.pullbackAlong U.ι).invariants) =
        CommRingCat.ofHom (D.pullbackAlong U.ι).toInvariants := by
    ext r
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, D.coe_equalizerSectionsEquiv_apply,
      Subalgebra.coe_algebraMap, Scheme.Hom.pushforwardStructureAlgebraSectionsRingEquiv_apply,
      Scheme.Hom.pushforwardStructureAlgebra_algebraMap, coe_toInvariants]
    exact (isPullback_pullbackAlongObj (p := p) U.ι X).toCommSq.appLE_app_topIso_hom r
  rw [← hr]
  simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, Iso.op_hom,
    IsAffineOpen.isoSpec_inv, Scheme.Spec_map, Quiver.Hom.unop_op, Spec.map_comp, Category.assoc]
  rfl

/-- On the chart of the descended scheme over an affine open `U` of `S`, the quotient map
`X ⟶ D.descended` restricted to `X ×_{S'} (U ×_S S')` is `Spec` of the inclusion of the
equalizer sections, read as invariant functions of the restricted datum. -/
private theorem toSpecΓ_comp_relativeSpecCover {U : S.Opens} (hU : IsAffineOpen U) :
    ((pullbackAlongObj (p := p) U.ι X).left.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (D.pullbackAlong U.ι).invariants.subtype) ≫
          Spec.map (CommRingCat.ofHom (D.equalizerSectionsEquiv U).toRingHom)) ≫
        (CommMon.equalizerSubalgebraPresheaf D.actAlgebraMap
          (sndAlgebraMap p X)).relativeSpecCover.f ⟨U, hU⟩ =
      pullback.fst X.hom (pullback.snd U.ι p) ≫ D.toDescended := by
  have : IsAffine U := hU
  have : IsAffineHom (pullback.fst U.ι p) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip ‹_›
  have : IsAffineHom (pullback.snd X.hom (pullback.snd U.ι p)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  have : IsAffine (pullbackAlongObj (p := p) U.ι X).left :=
    isAffine_of_isAffineHom (pullback.snd X.hom (pullback.snd U.ι p) ≫ pullback.fst U.ι p)
  -- Rebind the charts over `U` and the maps of rings between them at their explicit sources and
  -- targets, so that ordinary rewriting applies.
  let E := CommMon.equalizerSubalgebraPresheaf D.actAlgebraMap (sndAlgebraMap p X)
  let cA : Spec (CommRingCat.of Γ((X.hom ≫ p).pushforwardStructureAlgebra.X, U)) ⟶
      (X.hom ≫ p).pushforwardStructureAlgebra.relativeSpec :=
    (X.hom ≫ p).pushforwardStructureAlgebra.relativeSpecCover.f ⟨U, hU⟩
  let cE : Spec (CommRingCat.of (E.sections U)) ⟶ D.descended.left :=
    E.relativeSpecCover.f ⟨U, hU⟩
  let iE : CommRingCat.of (E.sections U) ⟶
      CommRingCat.of Γ((X.hom ≫ p).pushforwardStructureAlgebra.X, U) :=
    E.sectionsPresheafι.app (op U)
  let e : CommRingCat.of Γ((X.hom ≫ p).pushforwardStructureAlgebra.X, U) ≅
      Γ(X.left, (X.hom ≫ p) ⁻¹ᵁ U) :=
    ((X.hom ≫ p).pushforwardStructureAlgebraSectionsRingEquiv U).toCommRingCatIso
  let γ := (pullback.fst X.hom (pullback.snd U.ι p)).appLE _ ⊤
    (isPullback_pullbackAlongObj (p := p) U.ι X).toCommSq.top_le_preimage_preimage
  have hA : cA ≫ (X.hom ≫ p).relativeSpecFunctionsToScheme =
      Spec.map e.inv ≫ (hU.preimage (X.hom ≫ p)).fromSpec := by
    have h := Scheme.Hom.relativeSpecCover_f_relativeSpecFunctionsToScheme (X.hom ≫ p) ⟨U, hU⟩
    rw [Scheme.Hom.pushforwardStructureAlgebraPresheafIso_inv_app] at h
    exact h
  have hA' : Spec.map e.hom ≫ cA ≫ (X.hom ≫ p).relativeSpecFunctionsToScheme =
      (hU.preimage (X.hom ≫ p)).fromSpec := by
    rw [hA, ← Spec.map_comp_assoc, e.inv_hom_id, Spec.map_id, Category.id_comp]
  have hπ : cA ≫ E.relativeSpecπ = Spec.map iE ≫ cE := E.relativeSpecCover_f_relativeSpecπ ⟨U, hU⟩
  have hq : (X.hom ≫ p).relativeSpecFunctionsToScheme ≫ D.toDescended = E.relativeSpecπ :=
    D.relativeSpecFunctionsToScheme_toDescended
  -- Through `X ≅ Spec_S (π_* 𝒪_X)`, the inclusion of `(X.hom ≫ p) ⁻¹ᵁ U` followed by the
  -- quotient map is the chart of `π_* 𝒪_X` over `U` followed by the projection to the relative
  -- spectrum of the equalizer.
  have hk : (hU.preimage (X.hom ≫ p)).fromSpec ≫ D.toDescended =
      Spec.map e.hom ≫ Spec.map iE ≫ cE := by
    rw [← hA', Category.assoc, Category.assoc, hq, hπ]
  have hj : (pullbackAlongObj (p := p) U.ι X).left.toSpecΓ ≫ Spec.map γ ≫
      (hU.preimage (X.hom ≫ p)).fromSpec = pullback.fst X.hom (pullback.snd U.ι p) := by
    rw [IsAffineOpen.SpecMap_appLE_fromSpec _ _ (isAffineOpen_top _), IsAffineOpen.fromSpec_top]
    exact (pullbackAlongObj (p := p) U.ι X).left.toSpecΓ_isoSpec_inv_assoc _
  have hring : CommRingCat.ofHom (D.equalizerSectionsEquiv U).toRingHom ≫
      CommRingCat.ofHom (D.pullbackAlong U.ι).invariants.subtype = iE ≫ e.hom ≫ γ := by
    ext x
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, iE, e,
      CommMon.SubalgebraPresheaf.sectionsPresheafι_app, RingEquiv.toCommRingCatIso_hom]
    exact D.coe_equalizerSectionsEquiv_apply U x
  -- State the goal with the rebound chart `cE`, so that `hk` and `hring` rewrite it.
  suffices h : ((pullbackAlongObj (p := p) U.ι X).left.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (D.pullbackAlong U.ι).invariants.subtype) ≫
        Spec.map (CommRingCat.ofHom (D.equalizerSectionsEquiv U).toRingHom)) ≫ cE =
      pullback.fst X.hom (pullback.snd U.ι p) ≫ D.toDescended from h
  refine Eq.trans ?_ (congrArg (· ≫ D.toDescended) hj)
  simp only [Category.assoc]
  rw [hk, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hring]

/-- Over an affine open `U` of `S`, the restriction `X ×_{S'} (U ×_S S')` of `X` is the base
change of the descended scheme along `U ×_S S' ⟶ S`, through the quotient map. -/
private theorem isPullback_restrict [Flat p] {U : S.Opens} (hU : IsAffineOpen U) :
    IsPullback (pullback.fst X.hom (pullback.snd U.ι p) ≫ D.toDescended)
      (pullbackAlongObj (p := p) U.ι X).hom D.descended.hom (pullback.snd U.ι p ≫ p) := by
  have hB := (CommMon.equalizerSubalgebraPresheaf D.actAlgebraMap
    (sndAlgebraMap p X)).isPullback_relativeSpecCover ⟨U, hU⟩
  rw [CommMon.SubalgebraPresheaf.toSectionsPresheaf_app] at hB
  have := (D.isPullback_spec_equalizerSections hU).paste_horiz hB.flip
  rwa [D.toSpecΓ_comp_relativeSpecCover hU, pullback.condition] at this

/-- **Effective descent for affine morphisms.** If `p : S' ⟶ S` is affine and flat, the comparison
from a descent datum `D` on a scheme `X` affine over `S'` to the canonical descent datum on the
base change of the descended scheme `D.descended` is an isomorphism, over an arbitrary base `S`.
So `D` is effective, with descended scheme `D.descended`. -/
instance isIso_toBaseChangeDescended_hom [Flat p] : IsIso D.toBaseChangeDescended.hom := by
  suffices IsIso ((Over.forget S').map D.toBaseChangeDescended.hom) from
    isIso_of_reflects_iso _ (Over.forget S')
  rw [Over.forget_map]
  -- Cover `D.descended ×_S S'` by its parts over `U ×_S S'` for the affine opens `U` of `S`.
  let 𝒱 := ((Scheme.AffineZariskiSite.directedCover S).pullback₂ p).pullback₁
    (pullback.snd D.descended.hom p)
  refine MorphismProperty.IsLocalAtTarget.of_zeroHypercover (P := .isomorphisms Scheme) 𝒱
    fun V ↦ ?_
  -- Over `U ×_S S'`, the comparison is the comparison of two pullbacks of `D.descended ⟶ S` along
  -- `U ×_S S' ⟶ S`, which commutes with their projections.
  obtain ⟨U, hU⟩ := V
  let g : (pullbackAlongObj (p := p) U.ι X).left ⟶
      pullback (pullback.snd D.descended.hom p) (pullback.snd U.ι p) :=
    pullback.map _ _ _ _ D.toBaseChangeDescended.hom.left (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hsq : IsPullback (pullback.fst X.hom (pullback.snd U.ι p)) g
      D.toBaseChangeDescended.hom.left
      (pullback.fst (pullback.snd D.descended.hom p) (pullback.snd U.ι p)) := by
    refine IsPullback.of_bot ?_ (by simp [g]) (IsPullback.of_hasPullback _ _)
    simpa [g] using IsPullback.of_hasPullback X.hom (pullback.snd U.ι p)
  have hQ := (IsPullback.of_hasPullback (pullback.snd D.descended.hom p)
    (pullback.snd U.ι p)).paste_horiz (IsPullback.of_hasPullback D.descended.hom p)
  have hg : g = ((D.isPullback_restrict hU).isoIsPullback _ _ hQ).hom := by
    apply hQ.hom_ext <;> simp [g]
  have : IsIso g := by rw [hg]; infer_instance
  exact hsq.isoPullback_inv_snd ▸ inferInstanceAs (IsIso (hsq.isoPullback.inv ≫ g))

end Effective

end

end DescentDatum

end TauCeti
