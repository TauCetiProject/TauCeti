/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks

/-!
# Relative gluing of schemes over two open subschemes

Given a scheme `S` and two opens `U, W : S.Opens`, the union `(U ⊔ W).toScheme` is covered by `U`,
`W` and their intersection `U ⊓ W`, indexed by the thin span category
`WidePushoutShape (ULift WalkingPair)`. Equipping this cover with its `Scheme.Cover.LocallyDirected`
instance allows us to instantiate Mathlib's `Scheme.Cover.RelativeGluingData`: two morphisms
`leftHom : left ⟶ U.toScheme` and `rightHom : right ⟶ W.toScheme` equipped with an isomorphism
between their pullbacks to `(U ⊓ W).toScheme` glue to a scheme `D.glued` with structure morphism
`D.toBase : D.glued ⟶ (U ⊔ W).toScheme`, universal map constructor `D.desc` out of `D.glued`,
canonical pullback squares over `U` and `W`, and transfer of Zariski-target-local morphism
properties.

## Main definitions

* `AlgebraicGeometry.Scheme.Opens.supOpenCover`: the locally directed open cover of
  `(U ⊔ W).toScheme` by `U ⊓ W`, `U` and `W`.
* `TauCeti.BinaryOpenGluingData`: relative gluing datum over `U` and `W` along `U ⊓ W`.
* `TauCeti.BinaryOpenGluingData.glued`, `TauCeti.BinaryOpenGluingData.toBase`: the glued scheme and
  its morphism to `(U ⊔ W).toScheme`.
* `TauCeti.BinaryOpenGluingData.desc`: universal morphism out of `D.glued` from compatible maps on
  `D.left` and `D.right`.
* `TauCeti.BinaryOpenGluingData.pullbackLeftIso`, `TauCeti.BinaryOpenGluingData.pullbackRightIso`:
  identifications of the restrictions of `D.glued` to `U` and `W` with `D.left` and `D.right`.

## Main results

* `TauCeti.BinaryOpenGluingData.hom_ext`: morphisms out of `D.glued` are determined by their
  compositions with `D.ιLeft` and `D.ιRight`.
* `TauCeti.BinaryOpenGluingData.isPullback_left`, `TauCeti.BinaryOpenGluingData.isPullback_right`:
  the inclusions of `D.left` and `D.right` into `D.glued` form pullback squares over `U ⊔ W`.
* `TauCeti.BinaryOpenGluingData.morphismProperty_toBase`: any Zariski-target-local morphism
  property satisfied by `D.leftHom` and `D.rightHom` holds for `D.toBase`.
* `AlgebraicGeometry.Scheme.Opens.hom_ext_of_sup`: uniqueness of morphisms from a scheme over
  `(U ⊔ W).toScheme` determined by their pullbacks over `U` and `W`.

## References

* [Stacks Project, Lemma 26.14.4](https://stacks.math.columbia.edu/tag/01LH)
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Opens

variable {S : Scheme.{u}} (U W : S.Opens)

/-- The open cover of `(U ⊔ W).toScheme` indexed by `WidePushoutShape (ULift WalkingPair)`, sending
`none` to `U ⊓ W`, `some ⟨.left⟩` to `U`, and `some ⟨.right⟩` to `W`. -/
abbrev supOpenCover : (U ⊔ W).toScheme.OpenCover where
  I₀ := WidePushoutShape (ULift.{u} WalkingPair)
  X
    | none => (U ⊓ W).toScheme
    | some ⟨.left⟩ => U.toScheme
    | some ⟨.right⟩ => W.toScheme
  f
    | none => S.homOfLE (inf_le_left.trans le_sup_left)
    | some ⟨.left⟩ => S.homOfLE le_sup_left
    | some ⟨.right⟩ => S.homOfLE le_sup_right
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ ?_⟩
    · rcases x.2 with hxU | hxW
      · exact ⟨some ⟨.left⟩, ⟨x.1, hxU⟩, Subtype.ext (Scheme.homOfLE_apply le_sup_left ⟨x.1, hxU⟩)⟩
      · exact ⟨some ⟨.right⟩, ⟨x.1, hxW⟩,
          Subtype.ext (Scheme.homOfLE_apply le_sup_right ⟨x.1, hxW⟩)⟩
    · cases i with
      | none => infer_instance
      | some j =>
        rcases j with ⟨j⟩
        cases j <;> infer_instance

/-- The transition open immersions between charts of `U.supOpenCover W`. -/
abbrev supOpenCoverTrans {i j : (U.supOpenCover W).I₀} (hij : i ⟶ j) :
    (U.supOpenCover W).X i ⟶ (U.supOpenCover W).X j :=
  match hij with
  | .id _ => 𝟙 _
  | .init ⟨.left⟩ => S.homOfLE inf_le_left
  | .init ⟨.right⟩ => S.homOfLE inf_le_right

instance {i j : (U.supOpenCover W).I₀} (hij : i ⟶ j) :
    IsOpenImmersion (U.supOpenCoverTrans W hij) := by
  cases hij with
  | id => infer_instance
  | init a =>
    rcases a with ⟨a⟩
    cases a <;> infer_instance

theorem supOpenCoverTrans_w {i j : (U.supOpenCover W).I₀} (hij : i ⟶ j) :
    U.supOpenCoverTrans W hij ≫ (U.supOpenCover W).f j = (U.supOpenCover W).f i := by
  cases hij with
  | id => exact Category.id_comp _
  | init a =>
    rcases a with ⟨a⟩
    cases a
    · exact S.homOfLE_homOfLE inf_le_left le_sup_left
    · exact S.homOfLE_homOfLE inf_le_right le_sup_right

private theorem supOpenCover_directed_of_hom_right {i j : (U.supOpenCover W).I₀} (h : i ⟶ j)
    (x : ↥(pullback ((U.supOpenCover W).f i) ((U.supOpenCover W).f j))) :
    ∃ (k : (U.supOpenCover W).I₀) (gi : k ⟶ i) (gj : k ⟶ j) (y : ↥((U.supOpenCover W).X k)),
      (pullback.lift (U.supOpenCoverTrans W gi) (U.supOpenCoverTrans W gj)
        ((U.supOpenCoverTrans_w W gi).trans (U.supOpenCoverTrans_w W gj).symm)).base y = x := by
  have : IsOpenImmersion ((U.supOpenCover W).f j) := (U.supOpenCover W).map_prop j
  refine ⟨i, 𝟙 i, h, (pullback.fst ((U.supOpenCover W).f i) ((U.supOpenCover W).f j)).base x,
    (pullback.fst ((U.supOpenCover W).f i) ((U.supOpenCover W).f j)).isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, pullback.lift_fst]; rfl

private theorem supOpenCover_directed_of_hom_left {i j : (U.supOpenCover W).I₀} (h : j ⟶ i)
    (x : ↥(pullback ((U.supOpenCover W).f i) ((U.supOpenCover W).f j))) :
    ∃ (k : (U.supOpenCover W).I₀) (gi : k ⟶ i) (gj : k ⟶ j) (y : ↥((U.supOpenCover W).X k)),
      (pullback.lift (U.supOpenCoverTrans W gi) (U.supOpenCoverTrans W gj)
        ((U.supOpenCoverTrans_w W gi).trans (U.supOpenCoverTrans_w W gj).symm)).base y = x := by
  have : IsOpenImmersion ((U.supOpenCover W).f i) := (U.supOpenCover W).map_prop i
  refine ⟨j, h, 𝟙 j, (pullback.snd ((U.supOpenCover W).f i) ((U.supOpenCover W).f j)).base x,
    (pullback.snd ((U.supOpenCover W).f i) ((U.supOpenCover W).f j)).isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, pullback.lift_snd]; rfl

instance : (U.supOpenCover W).LocallyDirected where
  trans hij := U.supOpenCoverTrans W hij
  trans_id _ := rfl
  trans_comp {i j k} hij hjk := by
    cases hij with
    | id => rw [WidePushoutShape.hom_id, Category.id_comp]; exact (Category.id_comp _).symm
    | init a =>
      cases hjk; rw [WidePushoutShape.hom_id, Category.comp_id]; exact (Category.comp_id _).symm
  w hij := U.supOpenCoverTrans_w W hij
  property_trans _ := inferInstance
  directed {i j} x := by
    have : IsOpenImmersion ((U.supOpenCover W).f j) := (U.supOpenCover W).map_prop j
    have hcond :
        ((U.supOpenCover W).f i).base
            ((pullback.fst ((U.supOpenCover W).f i) ((U.supOpenCover W).f j)).base x) =
          ((U.supOpenCover W).f j).base
            ((pullback.snd ((U.supOpenCover W).f i) ((U.supOpenCover W).f j)).base x) := by
      simpa [Scheme.Hom.comp_apply] using
        congr($(pullback.condition (f := (U.supOpenCover W).f i)
          (g := (U.supOpenCover W).f j)).base x)
    cases i with
    | none =>
      cases j with
      | none => exact supOpenCover_directed_of_hom_right U W (𝟙 _) x
      | some b => exact supOpenCover_directed_of_hom_right U W (WidePushoutShape.Hom.init b) x
    | some a =>
      cases j with
      | none => exact supOpenCover_directed_of_hom_left U W (WidePushoutShape.Hom.init a) x
      | some b =>
        rcases a with ⟨_ | _⟩ <;> rcases b with ⟨_ | _⟩
        · exact supOpenCover_directed_of_hom_right U W (𝟙 _) x
        · let u : ↥U := (pullback.fst ((U.supOpenCover W).f (some ⟨.left⟩))
            ((U.supOpenCover W).f (some ⟨.right⟩))).base x
          let w : ↥W := (pullback.snd ((U.supOpenCover W).f (some ⟨.left⟩))
            ((U.supOpenCover W).f (some ⟨.right⟩))).base x
          have huw : u.1 = w.1 := (Scheme.homOfLE_apply le_sup_left u).symm.trans
            ((congrArg Subtype.val hcond).trans (Scheme.homOfLE_apply le_sup_right w))
          let y₀ : ↥(U ⊓ W) := ⟨u.1, u.2, huw ▸ w.2⟩
          refine ⟨none, WidePushoutShape.Hom.init (ULift.up WalkingPair.left),
            WidePushoutShape.Hom.init (ULift.up WalkingPair.right),
            id (α := ↥((U.supOpenCover W).X none)) y₀,
            (pullback.fst ((U.supOpenCover W).f (some ⟨.left⟩))
              ((U.supOpenCover W).f (some ⟨.right⟩))).isOpenEmbedding.injective ?_⟩
          rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
          exact Subtype.ext (Scheme.homOfLE_apply inf_le_left y₀)
        · let w : ↥W := (pullback.fst ((U.supOpenCover W).f (some ⟨.right⟩))
            ((U.supOpenCover W).f (some ⟨.left⟩))).base x
          let u : ↥U := (pullback.snd ((U.supOpenCover W).f (some ⟨.right⟩))
            ((U.supOpenCover W).f (some ⟨.left⟩))).base x
          have hwu : w.1 = u.1 := (Scheme.homOfLE_apply le_sup_right w).symm.trans
            ((congrArg Subtype.val hcond).trans (Scheme.homOfLE_apply le_sup_left u))
          let y₀ : ↥(U ⊓ W) := ⟨w.1, hwu ▸ u.2, w.2⟩
          refine ⟨none, WidePushoutShape.Hom.init (ULift.up WalkingPair.right),
            WidePushoutShape.Hom.init (ULift.up WalkingPair.left),
            id (α := ↥((U.supOpenCover W).X none)) y₀,
            (pullback.fst ((U.supOpenCover W).f (some ⟨.right⟩))
              ((U.supOpenCover W).f (some ⟨.left⟩))).isOpenEmbedding.injective ?_⟩
          rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
          exact Subtype.ext (Scheme.homOfLE_apply inf_le_right y₀)
        · exact supOpenCover_directed_of_hom_right U W (𝟙 _) x

@[simp]
theorem supOpenCover_trans_init_left :
    (U.supOpenCover W).trans (WidePushoutShape.Hom.init ⟨.left⟩) = S.homOfLE inf_le_left := rfl

@[simp]
theorem supOpenCover_trans_init_right :
    (U.supOpenCover W).trans (WidePushoutShape.Hom.init ⟨.right⟩) = S.homOfLE inf_le_right := rfl

/-- The two-chart open cover of a scheme `p : Y ⟶ (U ⊔ W).toScheme` by its pullbacks over `U` and
`W`. -/
def supPullbackOpenCover {Y : Scheme.{u}} (p : Y ⟶ (U ⊔ W).toScheme) : Y.OpenCover where
  I₀ := ULift.{u} WalkingPair
  X j := match j.down with
    | .left => pullback p (S.homOfLE le_sup_left)
    | .right => pullback p (S.homOfLE le_sup_right)
  f j := match j.down with
    | .left => pullback.fst p (S.homOfLE le_sup_left)
    | .right => pullback.fst p (S.homOfLE le_sup_right)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun y ↦ ?_, fun ⟨b⟩ ↦ by cases b <;> infer_instance⟩
    rcases (p.base y).2 with hyU | hyW
    · obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p)
        (g := S.homOfLE le_sup_left) y (⟨(p.base y).1, hyU⟩ : ↥U)
        (Subtype.ext (Scheme.homOfLE_apply le_sup_left ⟨(p.base y).1, hyU⟩).symm)
      exact ⟨⟨.left⟩, z, hz⟩
    · obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p)
        (g := S.homOfLE le_sup_right) y (⟨(p.base y).1, hyW⟩ : ↥W)
        (Subtype.ext (Scheme.homOfLE_apply le_sup_right ⟨(p.base y).1, hyW⟩).symm)
      exact ⟨⟨.right⟩, z, hz⟩

/-- Two morphisms into any scheme `Z` from a scheme `p : Y ⟶ (U ⊔ W).toScheme` over `U ⊔ W` are
equal if their pullbacks over `U` and `W` agree. -/
theorem hom_ext_of_sup {Y Z : Scheme.{u}} (p : Y ⟶ (U ⊔ W).toScheme) (g₁ g₂ : Y ⟶ Z)
    (hU : pullback.fst p (S.homOfLE le_sup_left) ≫ g₁ =
      pullback.fst p (S.homOfLE le_sup_left) ≫ g₂)
    (hW : pullback.fst p (S.homOfLE le_sup_right) ≫ g₁ =
      pullback.fst p (S.homOfLE le_sup_right) ≫ g₂) :
    g₁ = g₂ :=
  Cover.hom_ext (supPullbackOpenCover U W p) g₁ g₂ fun ⟨b⟩ ↦ by cases b; exacts [hU, hW]

end AlgebraicGeometry.Scheme.Opens

namespace TauCeti

open AlgebraicGeometry

/-- Relative gluing datum for two schemes over open subschemes `U` and `W` of `S` along an
isomorphism of their restrictions to `(U ⊓ W).toScheme`. -/
structure BinaryOpenGluingData {S : Scheme.{u}} (U W : S.Opens) where
  /-- The scheme over `U`. -/
  left : Scheme.{u}
  /-- The structure morphism to `U.toScheme`. -/
  leftHom : left ⟶ U.toScheme
  /-- The scheme over `W`. -/
  right : Scheme.{u}
  /-- The structure morphism to `W.toScheme`. -/
  rightHom : right ⟶ W.toScheme
  /-- The gluing isomorphism over `(U ⊓ W).toScheme`. -/
  iso : pullback leftHom (S.homOfLE inf_le_left) ≅ pullback rightHom (S.homOfLE inf_le_right)
  /-- The gluing isomorphism commutes with the structure morphisms to `(U ⊓ W).toScheme`. -/
  iso_hom_snd :
    iso.hom ≫ pullback.snd rightHom (S.homOfLE inf_le_right) =
      pullback.snd leftHom (S.homOfLE inf_le_left) := by cat_disch

namespace BinaryOpenGluingData

variable {S : Scheme.{u}} {U W : S.Opens} (D : BinaryOpenGluingData U W)

attribute [reassoc (attr := simp)] iso_hom_snd

@[reassoc (attr := simp)]
theorem iso_inv_snd :
    D.iso.inv ≫ pullback.snd D.leftHom (S.homOfLE inf_le_left) =
      pullback.snd D.rightHom (S.homOfLE inf_le_right) := by
  rw [Iso.inv_comp_eq, D.iso_hom_snd]

/-- The underlying `Scheme.Cover.RelativeGluingData` over `U.supOpenCover W`. -/
def toRelativeGluingData : (U.supOpenCover W).RelativeGluingData where
  functor :=
    WidePushoutShape.wideSpan (pullback D.leftHom (S.homOfLE inf_le_left))
      (fun j ↦ match j.down with | .left => D.left | .right => D.right)
      (fun j ↦ match j.down with
        | .left => pullback.fst D.leftHom (S.homOfLE inf_le_left)
        | .right => D.iso.hom ≫ pullback.fst D.rightHom (S.homOfLE inf_le_right))
  natTrans :=
    { app := fun i ↦ match i with
        | none => pullback.snd D.leftHom (S.homOfLE inf_le_left)
        | some ⟨.left⟩ => D.leftHom
        | some ⟨.right⟩ => D.rightHom
      naturality := fun {i j} f ↦ by
        cases f with
        | id =>
          rw [WidePushoutShape.hom_id, CategoryTheory.Functor.map_id,
            CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
        | init a =>
          rcases a with ⟨_ | _⟩ <;> dsimp [Scheme.Cover.functorOfLocallyDirected]
          · exact pullback.condition
          · rw [Category.assoc, pullback.condition, D.iso_hom_snd_assoc] }
  equifibered {i j} f := by
    cases f with
    | id =>
      rw [WidePushoutShape.hom_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
    | init a =>
      rcases a with ⟨_ | _⟩ <;> dsimp [Scheme.Cover.functorOfLocallyDirected]
      · exact IsPullback.of_hasPullback D.leftHom (S.homOfLE inf_le_left)
      · have hiso : IsPullback D.iso.hom (pullback.snd D.leftHom (S.homOfLE inf_le_left))
            (pullback.snd D.rightHom (S.homOfLE inf_le_right)) (𝟙 _) :=
          IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, D.iso_hom_snd]⟩
        simpa using hiso.paste_horiz (IsPullback.of_hasPullback D.rightHom (S.homOfLE inf_le_right))

/-- The scheme over `(U ⊔ W).toScheme` obtained by gluing `D.left` and `D.right` along `D.iso`. -/
abbrev glued : Scheme.{u} := D.toRelativeGluingData.glued

/-- The structure morphism from the glued scheme to `(U ⊔ W).toScheme`. -/
def toBase : D.glued ⟶ (U ⊔ W).toScheme := D.toRelativeGluingData.toBase

/-- The canonical open immersion `D.left ⟶ D.glued`. -/
def ιLeft : D.left ⟶ D.glued := colimit.ι D.toRelativeGluingData.functor (some ⟨.left⟩)

/-- The canonical open immersion `D.right ⟶ D.glued`. -/
def ιRight : D.right ⟶ D.glued := colimit.ι D.toRelativeGluingData.functor (some ⟨.right⟩)

/-- The inclusion of `D.left` into `D.glued` is the pullback of `D.toBase` over `U`. -/
theorem isPullback_left : IsPullback D.leftHom D.ιLeft (S.homOfLE le_sup_left) D.toBase :=
  D.toRelativeGluingData.isPullback_natTrans_ι_toBase (some ⟨.left⟩)

/-- The inclusion of `D.right` into `D.glued` is the pullback of `D.toBase` over `W`. -/
theorem isPullback_right : IsPullback D.rightHom D.ιRight (S.homOfLE le_sup_right) D.toBase :=
  D.toRelativeGluingData.isPullback_natTrans_ι_toBase (some ⟨.right⟩)

instance : IsOpenImmersion D.ιLeft :=
  MorphismProperty.of_isPullback D.isPullback_left inferInstance

instance : IsOpenImmersion D.ιRight :=
  MorphismProperty.of_isPullback D.isPullback_right inferInstance

@[reassoc (attr := simp)]
theorem ιLeft_toBase : D.ιLeft ≫ D.toBase = D.leftHom ≫ S.homOfLE le_sup_left :=
  D.toRelativeGluingData.ι_toBase (some ⟨.left⟩)

@[reassoc (attr := simp)]
theorem ιRight_toBase : D.ιRight ≫ D.toBase = D.rightHom ≫ S.homOfLE le_sup_right :=
  D.toRelativeGluingData.ι_toBase (some ⟨.right⟩)

@[reassoc]
theorem fst_ιLeft :
    pullback.fst D.leftHom (S.homOfLE (U := U ⊓ W) (V := U) inf_le_left) ≫ D.ιLeft =
      D.iso.hom ≫
        pullback.fst D.rightHom (S.homOfLE (U := U ⊓ W) (V := W) inf_le_right) ≫ D.ιRight := by
  rw [← Category.assoc]
  exact (colimit.w D.toRelativeGluingData.functor (WidePushoutShape.Hom.init ⟨.left⟩)).trans
    (colimit.w D.toRelativeGluingData.functor (WidePushoutShape.Hom.init ⟨.right⟩)).symm

/-- Universal morphism out of `D.glued` induced by morphisms from `D.left` and `D.right` that
agree along `D.iso` on `(U ⊓ W).toScheme`. -/
def desc {Z : Scheme.{u}} (fL : D.left ⟶ Z) (fR : D.right ⟶ Z)
    (h : pullback.fst D.leftHom (S.homOfLE (U := U ⊓ W) (V := U) inf_le_left) ≫ fL =
      D.iso.hom ≫ pullback.fst D.rightHom (S.homOfLE (U := U ⊓ W) (V := W) inf_le_right) ≫ fR) :
    D.glued ⟶ Z :=
  colimit.desc D.toRelativeGluingData.functor <|
    WidePushoutShape.mkCocone (F := D.toRelativeGluingData.functor)
      (pullback.fst D.leftHom (S.homOfLE (U := U ⊓ W) (V := U) inf_le_left) ≫ fL)
      (fun ⟨b⟩ ↦ match b with | .left => fL | .right => fR)
      (fun ⟨b⟩ ↦ match b with
        | .left => rfl
        | .right => (Category.assoc D.iso.hom _ fR).trans h.symm)

@[reassoc (attr := simp)]
theorem ιLeft_desc {Z : Scheme.{u}} (fL : D.left ⟶ Z) (fR : D.right ⟶ Z)
    (h : pullback.fst D.leftHom (S.homOfLE (U := U ⊓ W) (V := U) inf_le_left) ≫ fL =
      D.iso.hom ≫ pullback.fst D.rightHom (S.homOfLE (U := U ⊓ W) (V := W) inf_le_right) ≫ fR) :
    D.ιLeft ≫ D.desc fL fR h = fL :=
  colimit.ι_desc (F := D.toRelativeGluingData.functor) _ (some ⟨.left⟩)

@[reassoc (attr := simp)]
theorem ιRight_desc {Z : Scheme.{u}} (fL : D.left ⟶ Z) (fR : D.right ⟶ Z)
    (h : pullback.fst D.leftHom (S.homOfLE (U := U ⊓ W) (V := U) inf_le_left) ≫ fL =
      D.iso.hom ≫ pullback.fst D.rightHom (S.homOfLE (U := U ⊓ W) (V := W) inf_le_right) ≫ fR) :
    D.ιRight ≫ D.desc fL fR h = fR :=
  colimit.ι_desc (F := D.toRelativeGluingData.functor) _ (some ⟨.right⟩)

/-- Morphisms out of `D.glued` are uniquely determined by their restrictions to `D.left` and
`D.right`. -/
@[ext]
theorem hom_ext {Z : Scheme.{u}} {g₁ g₂ : D.glued ⟶ Z}
    (hL : D.ιLeft ≫ g₁ = D.ιLeft ≫ g₂) (hR : D.ιRight ≫ g₁ = D.ιRight ≫ g₂) :
    g₁ = g₂ := by
  apply colimit.hom_ext; rintro (_ | ⟨_ | _⟩)
  · rw [← colimit.w_assoc D.toRelativeGluingData.functor (WidePushoutShape.Hom.init ⟨.left⟩),
      ← colimit.w_assoc D.toRelativeGluingData.functor (WidePushoutShape.Hom.init ⟨.left⟩)]
    exact congrArg (D.toRelativeGluingData.functor.map (WidePushoutShape.Hom.init ⟨.left⟩) ≫ ·) hL
  · exact hL
  · exact hR

/-- The canonical isomorphism `pullback D.toBase (S.homOfLE le_sup_left) ≅ D.left` over `U`. -/
def pullbackLeftIso : pullback D.toBase (S.homOfLE le_sup_left) ≅ D.left :=
  (D.isPullback_left.flip.isoPullback).symm

@[reassoc (attr := simp)]
theorem pullbackLeftIso_hom_ιLeft :
    D.pullbackLeftIso.hom ≫ D.ιLeft = pullback.fst D.toBase (S.homOfLE le_sup_left) :=
  D.isPullback_left.flip.isoPullback_inv_fst

@[reassoc (attr := simp)]
theorem pullbackLeftIso_hom_leftHom :
    D.pullbackLeftIso.hom ≫ D.leftHom = pullback.snd D.toBase (S.homOfLE le_sup_left) :=
  D.isPullback_left.flip.isoPullback_inv_snd

@[reassoc (attr := simp)]
theorem pullbackLeftIso_inv_fst :
    D.pullbackLeftIso.inv ≫ pullback.fst D.toBase (S.homOfLE le_sup_left) = D.ιLeft :=
  D.isPullback_left.flip.isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem pullbackLeftIso_inv_snd :
    D.pullbackLeftIso.inv ≫ pullback.snd D.toBase (S.homOfLE le_sup_left) = D.leftHom :=
  D.isPullback_left.flip.isoPullback_hom_snd

/-- The canonical isomorphism `pullback D.toBase (S.homOfLE le_sup_right) ≅ D.right` over `W`. -/
def pullbackRightIso : pullback D.toBase (S.homOfLE le_sup_right) ≅ D.right :=
  (D.isPullback_right.flip.isoPullback).symm

@[reassoc (attr := simp)]
theorem pullbackRightIso_hom_ιRight :
    D.pullbackRightIso.hom ≫ D.ιRight = pullback.fst D.toBase (S.homOfLE le_sup_right) :=
  D.isPullback_right.flip.isoPullback_inv_fst

@[reassoc (attr := simp)]
theorem pullbackRightIso_hom_rightHom :
    D.pullbackRightIso.hom ≫ D.rightHom = pullback.snd D.toBase (S.homOfLE le_sup_right) :=
  D.isPullback_right.flip.isoPullback_inv_snd

@[reassoc (attr := simp)]
theorem pullbackRightIso_inv_fst :
    D.pullbackRightIso.inv ≫ pullback.fst D.toBase (S.homOfLE le_sup_right) = D.ιRight :=
  D.isPullback_right.flip.isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem pullbackRightIso_inv_snd :
    D.pullbackRightIso.inv ≫ pullback.snd D.toBase (S.homOfLE le_sup_right) = D.rightHom :=
  D.isPullback_right.flip.isoPullback_hom_snd

/-- Any Zariski-target-local morphism property satisfied by `D.leftHom` and `D.rightHom` holds for
the glued morphism `D.toBase`. -/
theorem morphismProperty_toBase (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (hL : P D.leftHom) (hR : P D.rightHom) : P D.toBase := by
  let iU : U.toScheme ⟶ (U ⊔ W).toScheme := S.homOfLE le_sup_left
  let iW : W.toScheme ⟶ (U ⊔ W).toScheme := S.homOfLE le_sup_right
  let V : WalkingPair → (U ⊔ W).toScheme.Opens
    | .left => iU.opensRange
    | .right => iW.opensRange
  refine IsZariskiLocalAtTarget.of_iSup_eq_top V ?_ fun b ↦ ?_
  · rw [eq_top_iff]
    rintro x -
    rw [TopologicalSpace.Opens.mem_iSup]
    rcases x.2 with hxU | hxW
    · exact ⟨.left, ⟨x.1, hxU⟩, Subtype.ext (Scheme.homOfLE_apply le_sup_left ⟨x.1, hxU⟩)⟩
    · exact ⟨.right, ⟨x.1, hxW⟩, Subtype.ext (Scheme.homOfLE_apply le_sup_right ⟨x.1, hxW⟩)⟩
  · cases b
    · have hiso : Arrow.mk (D.toBase ∣_ iU.opensRange) ≅ Arrow.mk D.leftHom :=
        morphismRestrictOpensRange D.toBase iU ≪≫
          Arrow.isoMk D.pullbackLeftIso (Iso.refl _)
            (by dsimp; rw [Category.comp_id, D.pullbackLeftIso_hom_leftHom])
      exact (P.arrow_mk_iso_iff hiso).mpr hL
    · have hiso : Arrow.mk (D.toBase ∣_ iW.opensRange) ≅ Arrow.mk D.rightHom :=
        morphismRestrictOpensRange D.toBase iW ≪≫
          Arrow.isoMk D.pullbackRightIso (Iso.refl _)
            (by dsimp; rw [Category.comp_id, D.pullbackRightIso_hom_rightHom])
      exact (P.arrow_mk_iso_iff hiso).mpr hR

end BinaryOpenGluingData

end TauCeti
