/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import TauCeti.AlgebraicGeometry.RelativeSpec.UniversalProperty

/-!
# Base change of relative spectra

An affine morphism remains affine after arbitrary base change. Consequently, pulling back a
scheme affine over `X` along `f : Y ⟶ X` gives a scheme affine over `Y`. This file packages
that construction as the functor `baseChangeAffineSchemeOver`.

Relative Spec commutes with this base change: for a quasicoherent algebra `A` on `X`, the
relative spectrum over `Y` of the pullback algebra `f^* A` is the fibre product
`Y ×_X Spec_X A`. The projection `Spec_Y (f^* A) ⟶ Spec_X A` is the morphism over `X`
corresponding to the algebra map `A ⟶ f_* (p_* 𝒪)` adjoint to the identification of `f^* A`
with the functions on `Spec_Y (f^* A)`. The square is cartesian because, for every scheme
`q : T ⟶ Y`, the universal property of relative Spec, the adjunction between pullback and
pushforward of algebras, and the identification `f_* q_* 𝒪_T ≅ (q ≫ f)_* 𝒪_T` give a bijection
between morphisms `T ⟶ Spec_Y (f^* A)` over `Y` and morphisms `T ⟶ Spec_X A` over `X`, and this
bijection is composition with the projection. The resulting isomorphism is natural in `A`.

Base change of relative spectra is compatible with identities and composition of base
morphisms, through the identity and composition isomorphisms of algebra pullback. Along the
identity, the projection `Spec_X (𝟙^* A) ⟶ Spec_X A` is induced by `A ≅ 𝟙^* A`. For `g : Z ⟶ Y`
and `f : Y ⟶ X`, the projection `Spec_Z ((g ≫ f)^* A) ⟶ Spec_X A` is the identification
`Spec_Z ((g ≫ f)^* A) ≅ Spec_Z (g^* f^* A)` followed by the projections
`Spec_Z (g^* f^* A) ⟶ Spec_Y (f^* A) ⟶ Spec_X A`. Correspondingly, the isomorphism for `g ≫ f` is
the composite of those for `g` and `f` with Mathlib's `MorphismProperty.Over.pullbackComp`.

The base-change functor specializes Mathlib's pullback functor on morphism-property
over-categories to the property `IsAffineHom`; no new choice of fibre product is made.

## Main declarations

* `TauCeti.AlgebraicGeometry.baseChangeAffineSchemeOver`: base change of affine schemes over a
  fixed base;
* `TauCeti.AlgebraicGeometry.relativeSpecPullbackFst`: the projection
  `Spec_Y (f^* A) ⟶ Spec_X A`;
* `TauCeti.AlgebraicGeometry.isPullback_relativeSpecPullbackFst`: the square formed by this
  projection and the structure morphisms over `f` is cartesian;
* `TauCeti.AlgebraicGeometry.relativeSpecPullbackIso`: the isomorphism of affine schemes over
  `Y` between `Spec_Y (f^* A)` and the base change of `Spec_X A`;
* `TauCeti.AlgebraicGeometry.relativeSpecBaseChangeIso`: the same isomorphism, natural in `A`;
* `TauCeti.AlgebraicGeometry.relativeSpecPullbackFst_id`,
  `TauCeti.AlgebraicGeometry.relativeSpecPullbackFst_comp` and
  `TauCeti.AlgebraicGeometry.relativeSpecPullbackIso_comp`: compatibility of base change with
  identities and composition of base morphisms.

## References

* The Stacks Project, Tag 01SD (affine morphisms are stable under base change).
* The Stacks Project, Tag 01LQ (relative spectrum as a functor), where the relative spectrum of
  a pulled-back algebra is identified with the base change of the relative spectrum.
-/

public section

open CategoryTheory Limits Opposite
open _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {X Y : Scheme.{u}}

/-- Every morphism of schemes has pullbacks along `f`, in particular the affine ones. -/
local instance (f : Y ⟶ X) :
    MorphismProperty.HasPullbacksAlong
      (@IsAffineHom : MorphismProperty Scheme.{u}) f where
  hasPullback _ _ := inferInstance

/-- Affine morphisms are stable under base change along `f`. -/
local instance (f : Y ⟶ X) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsAffineHom : MorphismProperty Scheme.{u}) f where
  of_isPullback h hg := isAffineHom_isStableUnderBaseChange.of_isPullback h hg

/-- Pullback of schemes affine over `X` along an arbitrary morphism `f : Y ⟶ X`.

The underlying scheme is the chosen fibre product, and its structure morphism is the second
projection to `Y`. -/
abbrev baseChangeAffineSchemeOver (f : Y ⟶ X) :
    AffineSchemeOver X ⥤ AffineSchemeOver Y :=
  MorphismProperty.Over.pullback (@IsAffineHom : MorphismProperty Scheme.{u}) ⊤ f

/-- The induced map between base changes commutes with projection to the original total spaces. -/
@[simp]
theorem baseChangeAffineSchemeOver_map_left_fst (f : Y ⟶ X) {V W : AffineSchemeOver X}
    (g : V ⟶ W) :
    ((baseChangeAffineSchemeOver f).map g).left ≫ pullback.fst W.hom f =
      pullback.fst V.hom f ≫ g.left :=
  -- The generated `MorphismProperty.Over.pullback_map_left` does not rewrite here: `@IsAffineHom`
  -- only has type `MorphismProperty Scheme` after unfolding the semireducible `MorphismProperty`,
  -- so the rewrite fails to match. The map is identified with `pullback.lift` by unfolding.
  pullback.lift_fst _ _ _

/-- The induced map between base changes lies over the identity of the new base. -/
@[simp]
theorem baseChangeAffineSchemeOver_map_left_snd (f : Y ⟶ X) {V W : AffineSchemeOver X}
    (g : V ⟶ W) :
    ((baseChangeAffineSchemeOver f).map g).left ≫ pullback.snd W.hom f =
      pullback.snd V.hom f :=
  -- Definitional unfolding, as in `baseChangeAffineSchemeOver_map_left_fst`.
  pullback.lift_snd _ _ _

variable (A : QuasicoherentAlgebra X) (f : Y ⟶ X)

/-- For `q : T ⟶ Y`, morphisms `T ⟶ Spec_Y (f^* A)` over `Y` correspond to morphisms
`T ⟶ Spec_X A` over `X`: both correspond to algebra maps `A ⟶ f_* q_* 𝒪_T ≅ (q ≫ f)_* 𝒪_T`. -/
private def baseChangeHomEquiv {T : Scheme.{u}} (q : T ⟶ Y) :
    {t : T ⟶ ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpec //
        t ≫ ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpecToBase = q} ≃
      {s : T ⟶ A.obj.relativeSpec // s ≫ A.obj.relativeSpecToBase = q ≫ f} :=
  ((((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpecHomEquiv q).trans
    (QuasicoherentAlgebra.pullbackHomEquiv f A q.pushforwardStructureAlgebra)).trans
    ((q.pushforwardStructureAlgebraCompIso f).homToEquiv.trans
      (A.obj.relativeSpecHomEquiv (q ≫ f)).symm)

private lemma baseChangeHomEquiv_comp {T T' : Scheme.{u}} {q : T ⟶ Y} (g : T' ⟶ T)
    (t : {t : T ⟶ ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpec //
      t ≫ ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpecToBase = q}) :
    (baseChangeHomEquiv A f (g ≫ q) ⟨g ≫ t.1, by rw [Category.assoc, t.2]⟩).1 =
      g ≫ (baseChangeHomEquiv A f q t).1 := by
  simp only [baseChangeHomEquiv, Equiv.trans_apply, CommMon.relativeSpecHomEquiv_apply,
    CommMon.relativeSpecHomEquiv_symm_apply_coe, Iso.homToEquiv_apply]
  rw [← CommMon.relativeSpecLift_comp_pushforwardStructureAlgebraMap g (Category.assoc _ _ _).symm]
  congr 1
  -- The categories are named so that `rw` does not rewrite the composite `(g ≫ q) ≫ f` of
  -- schemes, on which the types of the algebra maps depend.
  rw [Category.assoc (obj := CommMon X.Modules),
    ← Scheme.Hom.pushforwardStructureAlgebraCompIso_hom_naturality f g rfl,
    ← Category.assoc (obj := CommMon X.Modules),
    ← QuasicoherentAlgebra.pullbackHomEquiv_naturality_right,
    Category.assoc (obj := CommMon Y.Modules), ← Scheme.Hom.pushforwardStructureAlgebraMap_comp]

private lemma baseChangeHomEquiv_relativeSpecMap {A' : QuasicoherentAlgebra X} (b : A' ⟶ A)
    {T : Scheme.{u}} {q : T ⟶ Y}
    (t : {t : T ⟶ ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpec //
      t ≫ ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpecToBase = q}) :
    (baseChangeHomEquiv A' f q ⟨t.1 ≫
        CommMon.relativeSpecMap ((QuasicoherentAlgebra.pullback f).map b).hom, by
          rw [Category.assoc, CommMon.relativeSpecMap_relativeSpecToBase, t.2]⟩).1 =
      (baseChangeHomEquiv A f q t).1 ≫ CommMon.relativeSpecMap b.hom := by
  simp only [baseChangeHomEquiv, Equiv.trans_apply, Iso.homToEquiv_apply,
    CommMon.relativeSpecHomEquiv_symm_apply_coe]
  rw [← CommMon.relativeSpecLift_comp, CommMon.relativeSpecHomEquiv_comp_relativeSpecMap,
    QuasicoherentAlgebra.pullbackHomEquiv_naturality_left, Category.assoc]

/-- The projection `Spec_Y (f^* A) ⟶ Spec_X A` from the relative spectrum of a pulled-back
algebra. It is the morphism over `X` whose algebra map `A ⟶ f_* (p_* 𝒪)` is adjoint to the
identification of `f^* A` with the functions on `Spec_Y (f^* A)`
(`relativeSpecPullbackFst_eq_relativeSpecLift`). -/
def relativeSpecPullbackFst :
    ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpec ⟶ A.obj.relativeSpec :=
  (baseChangeHomEquiv A f ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpecToBase
    ⟨𝟙 _, Category.id_comp _⟩).1

/-- The projection `Spec_Y (f^* A) ⟶ Spec_X A` is the lift of the algebra map adjoint to the
identification of `f^* A` with the functions on its relative spectrum, followed by the
identification `f_* p_* 𝒪 ≅ (p ≫ f)_* 𝒪`. -/
lemma relativeSpecPullbackFst_eq_relativeSpecLift :
    relativeSpecPullbackFst A f = CommMon.relativeSpecLift
      (QuasicoherentAlgebra.pullbackHomEquiv f A _
          ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpecPushforwardIso.inv ≫
        (Scheme.Hom.pushforwardStructureAlgebraCompIso
          ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpecToBase f).hom) := by
  rw [relativeSpecPullbackFst]
  simp only [baseChangeHomEquiv, Equiv.trans_apply, CommMon.relativeSpecHomEquiv_apply,
    Scheme.Hom.pushforwardStructureAlgebraMap_id, Category.comp_id, Iso.homToEquiv_apply,
    CommMon.relativeSpecHomEquiv_symm_apply_coe]

/-- The projection `Spec_Y (f^* A) ⟶ Spec_X A` lies over `f`. -/
@[reassoc (attr := simp)]
lemma relativeSpecPullbackFst_relativeSpecToBase :
    relativeSpecPullbackFst A f ≫ A.obj.relativeSpecToBase =
      ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpecToBase ≫ f :=
  (baseChangeHomEquiv A f ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpecToBase
    ⟨𝟙 _, Category.id_comp _⟩).2

private lemma baseChangeHomEquiv_apply {T : Scheme.{u}} {q : T ⟶ Y}
    (t : {t : T ⟶ ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpec //
      t ≫ ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpecToBase = q}) :
    (baseChangeHomEquiv A f q t).1 = t.1 ≫ relativeSpecPullbackFst A f := by
  obtain ⟨t, rfl⟩ := t
  have h : (⟨t ≫ 𝟙 _, by rw [Category.comp_id]⟩ :
      {s : T ⟶ ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpec //
        s ≫ ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpecToBase =
          t ≫ ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpecToBase}) =
        ⟨t, rfl⟩ := Subtype.ext (Category.comp_id t)
  rw [← h]
  exact baseChangeHomEquiv_comp A f t ⟨𝟙 _, Category.id_comp _⟩

/-- **Relative Spec commutes with base change.** For a quasicoherent algebra `A` on `X` and any
morphism `f : Y ⟶ X`, the relative spectrum of the pullback algebra `f^* A` is the fibre product
`Y ×_X Spec_X A`, with projections `relativeSpecPullbackFst A f` and the structure morphism. -/
theorem isPullback_relativeSpecPullbackFst :
    IsPullback (relativeSpecPullbackFst A f)
      ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpecToBase
      A.obj.relativeSpecToBase f :=
  ⟨⟨relativeSpecPullbackFst_relativeSpecToBase A f⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s ↦ ((baseChangeHomEquiv A f s.snd).symm ⟨s.fst, s.condition⟩).1)
    (fun s ↦ by rw [← baseChangeHomEquiv_apply, Equiv.apply_symm_apply])
    (fun s ↦ ((baseChangeHomEquiv A f s.snd).symm ⟨s.fst, s.condition⟩).2)
    (fun s m hfst hsnd ↦ congrArg Subtype.val
      (((baseChangeHomEquiv A f s.snd).symm_apply_apply ⟨m, hsnd⟩).symm.trans (congrArg _
        (Subtype.ext ((baseChangeHomEquiv_apply A f _).trans hfst)))))⟩⟩

/-- The projection `Spec_Y (f^* A) ⟶ Spec_X A` is natural in the algebra `A`. -/
@[reassoc]
lemma relativeSpecMap_pullback_map_relativeSpecPullbackFst {A' : QuasicoherentAlgebra X}
    (b : A' ⟶ A) :
    CommMon.relativeSpecMap ((QuasicoherentAlgebra.pullback f).map b).hom ≫
        relativeSpecPullbackFst A' f =
      relativeSpecPullbackFst A f ≫ CommMon.relativeSpecMap b.hom := by
  refine (congrArg (· ≫ relativeSpecPullbackFst A' f) (Category.id_comp _).symm).trans ?_
  exact (baseChangeHomEquiv_apply A' f _).symm.trans
    (baseChangeHomEquiv_relativeSpecMap A f b ⟨𝟙 _, Category.id_comp _⟩)

/-- The relative spectrum of `f^* A` over `Y` is the base change along `f` of the relative
spectrum of `A`, as affine schemes over `Y`. -/
def relativeSpecPullbackIso :
    (relativeSpec Y).obj (op ((QuasicoherentAlgebra.pullback f).obj A)) ≅
      (baseChangeAffineSchemeOver f).obj ((relativeSpec X).obj (op A)) :=
  MorphismProperty.Over.isoMk (isPullback_relativeSpecPullbackFst A f).isoPullback
    (IsPullback.isoPullback_hom_snd _)

/-- The isomorphism `relativeSpecPullbackIso` followed by the first projection of the fibre
product is the projection `Spec_Y (f^* A) ⟶ Spec_X A`. -/
@[simp, reassoc]
lemma relativeSpecPullbackIso_hom_left_fst :
    (relativeSpecPullbackIso A f).hom.left ≫ pullback.fst A.obj.relativeSpecToBase f =
      relativeSpecPullbackFst A f :=
  IsPullback.isoPullback_hom_fst _

/-- The isomorphism `relativeSpecPullbackIso` followed by the second projection of the fibre
product is the structure morphism of `Spec_Y (f^* A)`. -/
@[simp, reassoc]
lemma relativeSpecPullbackIso_hom_left_snd :
    (relativeSpecPullbackIso A f).hom.left ≫ pullback.snd A.obj.relativeSpecToBase f =
      ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpecToBase :=
  IsPullback.isoPullback_hom_snd _

/-- The inverse of `relativeSpecPullbackIso`, followed by the projection
`Spec_Y (f^* A) ⟶ Spec_X A`, is the first projection of the fibre product. -/
@[simp, reassoc]
lemma relativeSpecPullbackIso_inv_left_relativeSpecPullbackFst :
    (relativeSpecPullbackIso A f).inv.left ≫ relativeSpecPullbackFst A f =
      pullback.fst A.obj.relativeSpecToBase f :=
  IsPullback.isoPullback_inv_fst _

/-- The inverse of `relativeSpecPullbackIso`, followed by the structure morphism of
`Spec_Y (f^* A)`, is the second projection of the fibre product. -/
@[simp, reassoc]
lemma relativeSpecPullbackIso_inv_left_relativeSpecToBase :
    (relativeSpecPullbackIso A f).inv.left ≫
        ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpecToBase =
      pullback.snd A.obj.relativeSpecToBase f :=
  IsPullback.isoPullback_inv_snd _

/-- **Relative Spec commutes with base change, naturally in the algebra.** For `f : Y ⟶ X`,
taking the relative spectrum of the pullback of a quasicoherent algebra is naturally isomorphic
to base changing its relative spectrum along `f`. -/
def relativeSpecBaseChangeIso :
    (QuasicoherentAlgebra.pullback f).op ⋙ relativeSpec Y ≅
      relativeSpec X ⋙ baseChangeAffineSchemeOver f :=
  NatIso.ofComponents (fun A ↦ relativeSpecPullbackIso A.unop f) fun {A A'} b ↦ by
    apply MorphismProperty.Over.Hom.ext
    -- `MorphismProperty.Comma.comp_left` does not rewrite here: `@IsAffineHom` only has type
    -- `MorphismProperty Scheme` after unfolding, as in `baseChangeAffineSchemeOver_map_left_fst`.
    -- `change` states the composite of the underlying scheme morphisms.
    change CommMon.relativeSpecMap ((QuasicoherentAlgebra.pullback f).map b.unop).hom ≫
        (relativeSpecPullbackIso A'.unop f).hom.left =
      (relativeSpecPullbackIso A.unop f).hom.left ≫
        ((baseChangeAffineSchemeOver f).map ((relativeSpec X).map b)).left
    -- Both chains pass through `isoPullback.hom`, the underlying morphism of
    -- `relativeSpecPullbackIso`: its source is `Spec_Y (f^* A)` itself rather than the `.left` of
    -- an affine scheme over `Y`, so every intermediate composite has the same hom type. The steps
    -- are terms because `rw` meets the same `IsAffineHom` unfolding as above.
    apply pullback.hom_ext
    · calc _ = CommMon.relativeSpecMap ((QuasicoherentAlgebra.pullback f).map b.unop).hom ≫
              (relativeSpecPullbackIso A'.unop f).hom.left ≫
                pullback.fst A'.unop.obj.relativeSpecToBase f := Category.assoc _ _ _
        _ = CommMon.relativeSpecMap ((QuasicoherentAlgebra.pullback f).map b.unop).hom ≫
              relativeSpecPullbackFst A'.unop f :=
            congrArg (_ ≫ ·) (relativeSpecPullbackIso_hom_left_fst A'.unop f)
        _ = relativeSpecPullbackFst A.unop f ≫ CommMon.relativeSpecMap b.unop.hom :=
            relativeSpecMap_pullback_map_relativeSpecPullbackFst A.unop f b.unop
        _ = (isPullback_relativeSpecPullbackFst A.unop f).isoPullback.hom ≫
              pullback.fst A.unop.obj.relativeSpecToBase f ≫ CommMon.relativeSpecMap b.unop.hom :=
            (IsPullback.isoPullback_hom_fst_assoc _ _).symm
        _ = (isPullback_relativeSpecPullbackFst A.unop f).isoPullback.hom ≫
              ((baseChangeAffineSchemeOver f).map ((relativeSpec X).map b)).left ≫
                pullback.fst A'.unop.obj.relativeSpecToBase f :=
            congrArg (_ ≫ ·)
              (baseChangeAffineSchemeOver_map_left_fst f ((relativeSpec X).map b)).symm
        _ = _ := (Category.assoc _ _ _).symm
    · calc _ = CommMon.relativeSpecMap ((QuasicoherentAlgebra.pullback f).map b.unop).hom ≫
              (relativeSpecPullbackIso A'.unop f).hom.left ≫
                pullback.snd A'.unop.obj.relativeSpecToBase f := Category.assoc _ _ _
        _ = CommMon.relativeSpecMap ((QuasicoherentAlgebra.pullback f).map b.unop).hom ≫
              ((QuasicoherentAlgebra.pullback f).obj A'.unop).obj.relativeSpecToBase :=
            congrArg (_ ≫ ·) (relativeSpecPullbackIso_hom_left_snd A'.unop f)
        _ = ((QuasicoherentAlgebra.pullback f).obj A.unop).obj.relativeSpecToBase :=
            CommMon.relativeSpecMap_relativeSpecToBase _
        _ = (isPullback_relativeSpecPullbackFst A.unop f).isoPullback.hom ≫
              pullback.snd A.unop.obj.relativeSpecToBase f :=
            (IsPullback.isoPullback_hom_snd _).symm
        _ = (isPullback_relativeSpecPullbackFst A.unop f).isoPullback.hom ≫
              ((baseChangeAffineSchemeOver f).map ((relativeSpec X).map b)).left ≫
                pullback.snd A'.unop.obj.relativeSpecToBase f :=
            congrArg (_ ≫ ·)
              (baseChangeAffineSchemeOver_map_left_snd f ((relativeSpec X).map b)).symm
        _ = _ := (Category.assoc _ _ _).symm

/-- The components of `relativeSpecBaseChangeIso` are `relativeSpecPullbackIso`. -/
@[simp]
lemma relativeSpecBaseChangeIso_app (A : (QuasicoherentAlgebra X)ᵒᵖ) :
    (relativeSpecBaseChangeIso f).app A = relativeSpecPullbackIso A.unop f :=
  (rfl)

/-- The algebra map of a morphism `t : T ⟶ Spec_Y (f^* A)` over `q : T ⟶ Y`, followed by the
projection to `Spec_X A`, is the transpose along `f` of the algebra map of `t`, followed by the
identification `f_* q_* 𝒪_T ≅ (q ≫ f)_* 𝒪_T`. -/
lemma relativeSpecHomEquiv_comp_relativeSpecPullbackFst {T : Scheme.{u}} {q : T ⟶ Y}
    (t : {t : T ⟶ ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpec //
      t ≫ ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpecToBase = q}) :
    A.obj.relativeSpecHomEquiv (q ≫ f) ⟨t.1 ≫ relativeSpecPullbackFst A f, by
        rw [Category.assoc, relativeSpecPullbackFst_relativeSpecToBase, reassoc_of% t.2]⟩ =
      QuasicoherentAlgebra.pullbackHomEquiv f A _
          (((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpecHomEquiv q t) ≫
        (q.pushforwardStructureAlgebraCompIso f).hom :=
  (congrArg (A.obj.relativeSpecHomEquiv (q ≫ f))
    (Subtype.ext (baseChangeHomEquiv_apply A f t).symm)).trans (Equiv.apply_symm_apply _ _)

variable {Z : Scheme.{u}} (g : Z ⟶ Y)

/-- **Base change of relative spectra is compatible with composition.** For `g : Z ⟶ Y` and
`f : Y ⟶ X`, the projection `Spec_Z ((g ≫ f)^* A) ⟶ Spec_X A` is the composite of the
identification `Spec_Z ((g ≫ f)^* A) ≅ Spec_Z (g^* f^* A)` induced by the composition isomorphism
of pullback with the projections `Spec_Z (g^* f^* A) ⟶ Spec_Y (f^* A) ⟶ Spec_X A`. -/
theorem relativeSpecPullbackFst_comp :
    relativeSpecPullbackFst A (g ≫ f) =
      CommMon.relativeSpecMap ((QuasicoherentAlgebra.pullbackComp g f).hom.app A).hom ≫
        relativeSpecPullbackFst ((QuasicoherentAlgebra.pullback f).obj A) g ≫
          relativeSpecPullbackFst A f := by
  let B := (QuasicoherentAlgebra.pullback f).obj A
  let C := (QuasicoherentAlgebra.pullback (g ≫ f)).obj A
  let c := (QuasicoherentAlgebra.pullbackComp g f).hom.app A
  let p := C.obj.relativeSpecToBase
  have ht : (CommMon.relativeSpecMap c.hom ≫ relativeSpecPullbackFst B g) ≫
      B.obj.relativeSpecToBase = p ≫ g := by
    rw [Category.assoc, relativeSpecPullbackFst_relativeSpecToBase]
    exact CommMon.relativeSpecMap_relativeSpecToBase_assoc c.hom g
  -- The algebra map of the morphism `Spec_Z ((g ≫ f)^* A) ⟶ Spec_Y (f^* A)` over `g`.
  have hB : B.obj.relativeSpecHomEquiv (p ≫ g) ⟨_, ht⟩ =
      QuasicoherentAlgebra.pullbackHomEquiv g B _ (c.hom ≫ C.obj.relativeSpecPushforwardIso.inv) ≫
        (p.pushforwardStructureAlgebraCompIso g).hom := by
    refine (relativeSpecHomEquiv_comp_relativeSpecPullbackFst B g
      ⟨CommMon.relativeSpecMap c.hom, CommMon.relativeSpecMap_relativeSpecToBase _⟩).trans ?_
    rw [← CommMon.relativeSpecHomEquiv_id, ← CommMon.relativeSpecHomEquiv_comp_relativeSpecMap]
    -- The two subtype values are `𝟙 ≫ relativeSpecMap c.hom` and `relativeSpecMap c.hom`, which
    -- agree definitionally for morphisms of schemes.
    rfl
  have hc : ((QuasicoherentAlgebra.pullbackComp g f).inv.app A).hom ≫ c.hom = 𝟙 _ :=
    congrArg (·.hom) ((QuasicoherentAlgebra.pullbackComp g f).inv_hom_id_app A)
  refine congrArg Subtype.val ((A.obj.relativeSpecHomEquiv (p ≫ g ≫ f)).injective
    (a₁ := ⟨_, relativeSpecPullbackFst_relativeSpecToBase A (g ≫ f)⟩)
    (a₂ := ⟨(CommMon.relativeSpecMap c.hom ≫ relativeSpecPullbackFst B g) ≫
      relativeSpecPullbackFst A f, by
        rw [Category.assoc, relativeSpecPullbackFst_relativeSpecToBase, ← Category.assoc, ht,
          Category.assoc]⟩) ?_)
  -- Both algebra maps are computed by `relativeSpecHomEquiv_comp_relativeSpecPullbackFst`; the
  -- composites of schemes over `X` agree definitionally up to associativity and units.
  refine (relativeSpecHomEquiv_comp_relativeSpecPullbackFst A (g ≫ f)
    ⟨𝟙 _, Category.id_comp p⟩).trans (Eq.trans ?_
      (relativeSpecHomEquiv_comp_relativeSpecPullbackFst A f ⟨_, ht⟩).symm)
  have hι : C.obj.relativeSpecPushforwardIso.inv = ((QuasicoherentAlgebra.pullbackComp g f).inv.app
      A).hom ≫ c.hom ≫ C.obj.relativeSpecPushforwardIso.inv := by
    rw [reassoc_of% hc]
  rw [CommMon.relativeSpecHomEquiv_id, hB, QuasicoherentAlgebra.pullbackHomEquiv_naturality_right]
  conv_lhs => rw [hι]
  rw [QuasicoherentAlgebra.pullbackHomEquiv_comp, Category.assoc, Category.assoc, Category.assoc]
  refine congrArg (QuasicoherentAlgebra.pullbackHomEquiv f A _
    (QuasicoherentAlgebra.pullbackHomEquiv g B _ (c.hom ≫ C.obj.relativeSpecPushforwardIso.inv)) ≫
      ·) ?_
  apply CommMon.hom_ext
  apply Scheme.Modules.hom_ext
  intro U
  simp only [CommMon.comp_hom, Functor.mapCommMon_map_hom_hom,
    Scheme.Hom.pushforwardStructureAlgebraCompIso_hom_hom_hom,
    Functor.mapCommMonCompIso_inv_app_hom_hom, Functor.mapCommMonNatIso_hom_app_hom_hom]
  -- On sections over `U`, every composition isomorphism of pushforwards is the identity of
  -- `Γ(Spec_Z ((g ≫ f)^* A), (p ≫ g ≫ f)⁻¹ U)`.
  rfl

/-- **Base change of relative spectra along the identity.** The projection
`Spec_X (𝟙^* A) ⟶ Spec_X A` is the identification induced by the identity isomorphism
`A ≅ 𝟙^* A` of pullback. -/
@[simp]
theorem relativeSpecPullbackFst_id :
    relativeSpecPullbackFst A (𝟙 X) =
      CommMon.relativeSpecMap ((QuasicoherentAlgebra.pullbackId X).inv.app A).hom := by
  let C := (QuasicoherentAlgebra.pullback (𝟙 X)).obj A
  let i := (QuasicoherentAlgebra.pullbackId X).inv.app A
  let p := C.obj.relativeSpecToBase
  have hi : ((QuasicoherentAlgebra.pullbackId X).hom.app A).hom ≫ i.hom = 𝟙 _ :=
    congrArg (·.hom) ((QuasicoherentAlgebra.pullbackId X).hom_inv_id_app A)
  refine congrArg Subtype.val ((A.obj.relativeSpecHomEquiv (p ≫ 𝟙 X)).injective
    (a₁ := ⟨_, relativeSpecPullbackFst_relativeSpecToBase A (𝟙 X)⟩)
    (a₂ := ⟨_, CommMon.relativeSpecMap_relativeSpecToBase i.hom⟩) ?_)
  -- As in `relativeSpecPullbackFst_comp`, using that `p ≫ 𝟙 X` is definitionally `p`.
  refine (relativeSpecHomEquiv_comp_relativeSpecPullbackFst A (𝟙 X)
    ⟨𝟙 _, Category.id_comp p⟩).trans (Eq.trans ?_
      (CommMon.relativeSpecHomEquiv_comp_relativeSpecMap i.hom ⟨𝟙 _, Category.id_comp p⟩).symm)
  rw [CommMon.relativeSpecHomEquiv_id]
  conv_lhs => rw [← Category.id_comp C.obj.relativeSpecPushforwardIso.inv, ← hi, Category.assoc]
  apply CommMon.hom_ext
  rw [CommMon.comp_hom, QuasicoherentAlgebra.pullbackHomEquiv_id_hom_hom,
    Scheme.Hom.pushforwardStructureAlgebraCompIso_hom_hom_hom]
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ?_).trans (Category.comp_id _))
  apply Scheme.Modules.hom_ext
  intro U
  -- On sections, the identity and composition isomorphisms of pushforward are identities.
  rfl

/-- **Relative Spec commutes with base change, compatibly with composition.** For `g : Z ⟶ Y`
and `f : Y ⟶ X`, the isomorphism `Spec_Z ((g ≫ f)^* A) ≅ Z ×_X Spec_X A` is the composite of the
identification `Spec_Z ((g ≫ f)^* A) ≅ Spec_Z (g^* f^* A)`, the isomorphisms for `g` and for `f`,
and the canonical isomorphism `Z ×_Y (Y ×_X Spec_X A) ≅ Z ×_X Spec_X A`. -/
theorem relativeSpecPullbackIso_comp :
    (relativeSpecPullbackIso A (g ≫ f)).hom =
      (relativeSpec Z).map ((QuasicoherentAlgebra.pullbackComp g f).hom.app A).op ≫
        (relativeSpecPullbackIso ((QuasicoherentAlgebra.pullback f).obj A) g).hom ≫
          (baseChangeAffineSchemeOver g).map (relativeSpecPullbackIso A f).hom ≫
            (MorphismProperty.Over.pullbackComp g f).inv.app ((relativeSpec X).obj (op A)) := by
  let B := (QuasicoherentAlgebra.pullback f).obj A
  let V := (relativeSpec X).obj (op A)
  let e := MorphismProperty.Over.pullbackComp (P := @IsAffineHom) (Q := ⊤) g f
  have hid : (e.inv.app V).left ≫ (e.hom.app V).left = 𝟙 _ :=
    congrArg (·.left) (e.inv_hom_id_app V)
  have h : (e.inv.app V).left ≫ pullback.fst A.obj.relativeSpecToBase (g ≫ f) =
      pullback.fst (pullback.snd A.obj.relativeSpecToBase f) g ≫
        pullback.fst A.obj.relativeSpecToBase f :=
    (congrArg (_ ≫ ·) (MorphismProperty.Over.pullbackComp_left_fst_fst g f V).symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hid).trans (Category.id_comp _)))
  let c := (QuasicoherentAlgebra.pullbackComp g f).hom.app A
  have hinv : (e.inv.app V).left ≫ pullback.snd A.obj.relativeSpecToBase (g ≫ f) =
      pullback.snd (pullback.snd A.obj.relativeSpecToBase f) g :=
    MorphismProperty.Over.w (e.inv.app V)
  let r := CommMon.relativeSpecMap c.hom
  let s₁ := (relativeSpecPullbackIso B g).hom.left
  let s₂ := ((baseChangeAffineSchemeOver g).map (relativeSpecPullbackIso A f).hom).left
  let s₃ := (e.inv.app V).left
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · refine (relativeSpecPullbackIso_hom_left_fst A (g ≫ f)).trans
      ((relativeSpecPullbackFst_comp A f g).trans (Eq.symm ?_))
    -- Composition in affine schemes over `Z` is composition of the underlying morphisms.
    change (r ≫ s₁ ≫ s₂ ≫ s₃) ≫ pullback.fst A.obj.relativeSpecToBase (g ≫ f) = _
    -- `simp` and `rw` cannot reassociate these composites of underlying morphisms, so the
    -- associativity steps are stated as terms.
    calc _ = r ≫ s₁ ≫ s₂ ≫ s₃ ≫ pullback.fst A.obj.relativeSpecToBase (g ≫ f) :=
          (Category.assoc _ _ _).trans (congrArg (r ≫ ·) ((Category.assoc _ _ _).trans
            (congrArg (s₁ ≫ ·) (Category.assoc _ _ _))))
      _ = r ≫ s₁ ≫ (s₂ ≫ pullback.fst (pullback.snd A.obj.relativeSpecToBase f) g) ≫
            pullback.fst A.obj.relativeSpecToBase f :=
          congrArg (fun x ↦ r ≫ s₁ ≫ x) ((congrArg (s₂ ≫ ·) h).trans (Category.assoc _ _ _).symm)
      _ = r ≫ (s₁ ≫ pullback.fst B.obj.relativeSpecToBase g) ≫
            (relativeSpecPullbackIso A f).hom.left ≫ pullback.fst A.obj.relativeSpecToBase f :=
          congrArg (r ≫ ·) ((congrArg (fun x ↦ s₁ ≫ x ≫ pullback.fst A.obj.relativeSpecToBase f)
            (baseChangeAffineSchemeOver_map_left_fst g (relativeSpecPullbackIso A f).hom)).trans
              ((congrArg (s₁ ≫ ·) (Category.assoc _ _ _)).trans (Category.assoc _ _ _).symm))
      _ = _ := congrArg₂ (fun x y ↦ r ≫ x ≫ y)
          (relativeSpecPullbackIso_hom_left_fst B g) (relativeSpecPullbackIso_hom_left_fst A f)
  · refine (relativeSpecPullbackIso_hom_left_snd A (g ≫ f)).trans (Eq.symm ?_)
    change (r ≫ s₁ ≫ s₂ ≫ s₃) ≫ pullback.snd A.obj.relativeSpecToBase (g ≫ f) = _
    calc _ = r ≫ s₁ ≫ s₂ ≫ s₃ ≫ pullback.snd A.obj.relativeSpecToBase (g ≫ f) :=
          (Category.assoc _ _ _).trans (congrArg (r ≫ ·) ((Category.assoc _ _ _).trans
            (congrArg (s₁ ≫ ·) (Category.assoc _ _ _))))
      _ = r ≫ s₁ ≫ pullback.snd B.obj.relativeSpecToBase g :=
          congrArg (fun x ↦ r ≫ s₁ ≫ x) ((congrArg (s₂ ≫ ·) hinv).trans
            (baseChangeAffineSchemeOver_map_left_snd g (relativeSpecPullbackIso A f).hom))
      _ = _ := (congrArg (r ≫ ·) (relativeSpecPullbackIso_hom_left_snd B g)).trans
          (CommMon.relativeSpecMap_relativeSpecToBase c.hom)

end

end TauCeti.AlgebraicGeometry
