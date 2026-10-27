/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Descent.Invariants
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

This file constructs the comparison and proves that it is an isomorphism when `p` is flat and `S`
is affine (`DescentDatum.isIso_toBaseChangeDescended_hom`). Over an affine base, the chart of the
relative spectrum over all of `S` identifies `D.descended` with the spectrum of the equalizer
sections over `S`. These are the invariant global functions `D.invariants` on the affine scheme
`X`, and effective descent for affine schemes in terms of invariant functions
(`DescentDatum.isPushout_invariants`) shows that `X` is the base change of their spectrum.

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
* `TauCeti.DescentDatum.isIso_toBaseChangeDescended_hom`: over an affine base and for `p` flat,
  the comparison is an isomorphism, so that `D` is effective with descended scheme `D.descended`.

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

omit [IsAffineHom p] [IsAffineHom X.hom] in
/-- The equalizer sections over `S` of the function algebra of `X ⟶ S` are the invariant
functions on `X`, restricted to `(X.hom ≫ p) ⁻¹ᵁ ⊤ = ⊤`. -/
private theorem mem_equalizerSections_top_iff {b : Γ(X.left, ⊤)} :
    ((X.hom ≫ p).pushforwardStructureAlgebraSectionsRingEquiv ⊤).symm
        (X.left.presheaf.map (homOfLE le_top).op b) ∈
      CommMon.equalizerSections D.actAlgebraMap (sndAlgebraMap p X) ⊤ ↔ b ∈ D.invariants := by
  -- The restriction to `(pullback.snd p (X.hom ≫ p) ≫ X.hom ≫ p) ⁻¹ᵁ ⊤ = ⊤` is injective.
  have : IsIso (homOfLE (le_top : (pullback.snd p (X.hom ≫ p) ≫ X.hom ≫ p) ⁻¹ᵁ ⊤ ≤ ⊤)) :=
    ⟨homOfLE (by simp), Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  rw [CommMon.mem_equalizerSections,
    Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply,
    Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply, EmbeddingLike.apply_eq_iff_eq,
    RingEquiv.apply_symm_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.map_appLE, Scheme.Hom.map_appLE, mem_invariants_iff,
    ← (ConcreteCategory.bijective_of_isIso
      ((pullback p (X.hom ≫ p)).presheaf.map (homOfLE (le_top :
        (pullback.snd p (X.hom ≫ p) ≫ X.hom ≫ p) ⁻¹ᵁ ⊤ ≤ ⊤)).op)).injective.eq_iff,
    ← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  -- Both sides are now the same restrictions of `D.act.appTop b` and of the projection, written
  -- once with `Scheme.Hom.appLE` and once as `appTop` followed by restriction.
  rfl

omit [IsAffineHom p] [IsAffineHom X.hom] in
/-- The identification of the global functions on `X` with the sections over `S` of the function
algebra of `X ⟶ S`: restriction to `(X.hom ≫ p) ⁻¹ᵁ ⊤ = ⊤`, then the section-ring equivalence. -/
private def globalSectionsRingEquiv :
    Γ(X.left, ⊤) ≃+* Γ((X.hom ≫ p).pushforwardStructureAlgebra.X, ⊤) :=
  have : IsIso (homOfLE (le_top : (X.hom ≫ p) ⁻¹ᵁ ⊤ ≤ ⊤)) :=
    ⟨homOfLE (by simp), Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  (asIso (X.left.presheaf.map (homOfLE (le_top : (X.hom ≫ p) ⁻¹ᵁ ⊤ ≤ ⊤)).op)
    ).commRingCatIsoToRingEquiv.trans
    ((X.hom ≫ p).pushforwardStructureAlgebraSectionsRingEquiv ⊤).symm

/-- Over an affine base, the descended scheme is the spectrum of the invariant functions: there
is an isomorphism `θ : Spec D.invariants ≅ D.descended` over `S` through which the quotient map
`X ⟶ D.descended` is `Spec` of the inclusion of the invariant functions. -/
private theorem exists_isIso_spec_invariants [IsAffine S] [IsAffine X.left] :
    ∃ θ : Spec (CommRingCat.of D.invariants) ⟶ D.descended.left, IsIso θ ∧
      θ ≫ D.descended.hom = Spec.map (CommRingCat.ofHom D.toInvariants) ≫ S.isoSpec.inv ∧
      X.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom D.invariants.subtype) ≫ θ =
        D.toDescended := by
  let A := (X.hom ≫ p).pushforwardStructureAlgebra
  let E := CommMon.equalizerSubalgebraPresheaf D.actAlgebraMap (sndAlgebraMap p X)
  -- The charts over the whole base of the relative spectra of `A` and `E`.
  obtain ⟨cA, cE, _, _, hcA, hcE, hcAE⟩ : ∃ (cA : Spec (CommRingCat.of Γ(A.X, ⊤)) ⟶ A.relativeSpec)
      (cE : Spec (CommRingCat.of (E.sections ⊤)) ⟶ D.descended.left), IsIso cA ∧ IsIso cE ∧
      cA ≫ (X.hom ≫ p).relativeSpecFunctionsToScheme =
        Spec.map (CommRingCat.ofHom
          ((X.hom ≫ p).pushforwardStructureAlgebraSectionsRingEquiv ⊤).symm.toRingHom) ≫
          ((isAffineOpen_top S).preimage (X.hom ≫ p)).fromSpec ∧
      cE ≫ D.descended.hom =
        Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (E.sections ⊤))) ≫ S.isoSpec.inv ∧
      cA ≫ E.relativeSpecπ =
        Spec.map (CommRingCat.ofHom (E.sections ⊤).val.toRingHom) ≫ cE := by
    have : IsIso (Scheme.Opens.ι (⊤ : S.Opens)) := inferInstanceAs (IsIso S.topIso.hom)
    refine ⟨A.relativeSpecCover.f ⟨⊤, isAffineOpen_top S⟩,
      E.relativeSpecCover.f ⟨⊤, isAffineOpen_top S⟩, CommMon.isIso_relativeSpecCover_f_top A,
      (E.isPullback_relativeSpecCover ⟨⊤, isAffineOpen_top S⟩).isIso_snd_of_isIso,
      ?_, ?_, ?_⟩
    · have h := Scheme.Hom.relativeSpecCover_f_relativeSpecFunctionsToScheme (X.hom ≫ p)
        ⟨⊤, isAffineOpen_top S⟩
      rw [Scheme.Hom.pushforwardStructureAlgebraPresheafIso_inv_app] at h
      exact h
    · have h := E.relativeSpecCover_f_relativeSpecToBase ⟨⊤, isAffineOpen_top S⟩
      rw [CommMon.SubalgebraPresheaf.toSectionsPresheaf_app] at h
      rw [← IsAffineOpen.fromSpec_top]
      exact h
    · have h := E.relativeSpecCover_f_relativeSpecπ ⟨⊤, isAffineOpen_top S⟩
      rw [CommMon.SubalgebraPresheaf.sectionsPresheafι_app] at h
      exact h
  -- The equalizer sections over `S` are the invariant functions.
  let ψ := globalSectionsRingEquiv (p := p) (X := X)
  have hE (b : Γ(X.left, ⊤)) : ψ b ∈ E.sections ⊤ ↔ b ∈ D.invariants := by
    rw [CommMon.equalizerSubalgebraPresheaf_sections]
    exact D.mem_equalizerSections_top_iff
  let φ : E.sections ⊤ ≃+* D.invariants :=
    { toFun x := ⟨ψ.symm x.1, (hE _).1 ((ψ.apply_symm_apply x.1).symm ▸ x.2)⟩
      invFun b := ⟨ψ b.1, (hE b.1).2 b.2⟩
      left_inv x := Subtype.ext (ψ.apply_symm_apply x.1)
      right_inv b := Subtype.ext (ψ.symm_apply_apply b.1)
      map_mul' a b := Subtype.ext (map_mul ψ.symm a.1 b.1)
      map_add' a b := Subtype.ext (map_add ψ.symm a.1 b.1) }
  have : IsIso (CommRingCat.ofHom φ.toRingHom) := φ.toCommRingCatIso.isIso_hom
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ cE, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, hcE, ← Spec.map_comp_assoc]
    congr 2
    ext r
    rw [CommRingCat.hom_ofHom, coe_toInvariants]
    -- `φ` is defined by `ψ.symm` on underlying elements, and the algebra map into a subalgebra
    -- is the algebra map into the ambient ring.
    change ψ.symm (algebraMap Γ(S, ⊤) Γ(A.X, ⊤) r) = (X.hom ≫ p).appTop r
    rw [RingEquiv.symm_apply_eq, Scheme.Hom.pushforwardStructureAlgebra_algebraMap]
    -- Unfold `ψ` into the restriction to `(X.hom ≫ p) ⁻¹ᵁ ⊤` followed by the section-ring
    -- equivalence of the function algebra.
    change _ = ((X.hom ≫ p).pushforwardStructureAlgebraSectionsRingEquiv ⊤).symm
      (((X.hom ≫ p).appTop ≫ X.left.presheaf.map (homOfLE le_top).op) r)
    rw [Scheme.Hom.pushforwardStructureAlgebraSectionsRingEquiv_symm_apply,
      ← Scheme.Hom.appLE_eq_app]
    -- `appLE ⊤ ((X.hom ≫ p) ⁻¹ᵁ ⊤)` is by definition `app ⊤` followed by this restriction.
    rfl
  · -- Compare both sides on the chart `Spec Γ(A.X, ⊤) ≅ X`, where the quotient map is `Spec` of
    -- the inclusion of the equalizer sections.
    rw [← cancel_epi (cA ≫ (X.hom ≫ p).relativeSpecFunctionsToScheme)]
    simp only [Category.assoc]
    rw [relativeSpecFunctionsToScheme_toDescended, hcAE, reassoc_of% hcA, Scheme.isoSpec_hom,
      IsAffineOpen.fromSpec_toSpecΓ_assoc]
    simp only [← Spec.map_comp_assoc, Category.assoc]
    congr 2
    ext x
    exact ψ.apply_symm_apply x.1

/-- **Effective descent for affine morphisms over an affine base.** If `S` is affine and `p` is
flat, the comparison from `D` to the canonical descent datum on the base change of the descended
scheme `D.descended` is an isomorphism. -/
instance isIso_toBaseChangeDescended_hom [IsAffine S] [Flat p] :
    IsIso D.toBaseChangeDescended.hom := by
  suffices IsIso ((Over.forget S').map D.toBaseChangeDescended.hom) from
    isIso_of_reflects_iso _ (Over.forget S')
  rw [Over.forget_map]
  have : IsAffine S' := isAffine_of_isAffineHom p
  have : IsAffine X.left := isAffine_of_isAffineHom (X.hom ≫ p)
  obtain ⟨θ, _, hθ, hθ'⟩ := D.exists_isIso_spec_invariants
  -- By effective descent for affine schemes, `X` is the base change of `Spec D.invariants`, and
  -- `θ` identifies the latter with `D.descended` over `S`.
  have hpb : IsPullback (X.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom D.invariants.subtype))
      X.hom (Spec.map (CommRingCat.ofHom D.toInvariants) ≫ S.isoSpec.inv) p :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ D.isPushout_invariants).of_iso X.left.isoSpec.symm
      (Iso.refl _) S'.isoSpec.symm S.isoSpec.symm (by simp)
      (by simp [Scheme.isoSpec_inv_naturality]) (by simp) (by simp [Scheme.isoSpec_inv_naturality])
  have hc : D.toBaseChangeDescended.hom.left = hpb.isoPullback.hom ≫
      pullback.map _ _ _ _ θ (𝟙 _) (𝟙 _) (by simp [hθ]) (by simp) := by
    apply pullback.hom_ext <;> simp [hθ']
  rw [hc]
  infer_instance

end

end DescentDatum

end TauCeti
