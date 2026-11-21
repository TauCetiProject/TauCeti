/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.AlgebraicGeometry.Stalk
public import TauCeti.AlgebraicGeometry.Limits.Affine.Transition

import Mathlib.CategoryTheory.Filtered.Final
import TauCeti.AlgebraicGeometry.Scheme.Opens

/-!
# The local scheme of a stalk as a cofiltered limit of affine open neighbourhoods

For `x : X`, the affine open neighbourhoods `X.AffineOpenNhds x` form a cofiltered poset.
`X.specStalkCone x` exhibits `Spec 𝒪_{X,x}` as the limit of `X.affineOpenNhdsDiagram x`
(`isLimitSpecStalkCone`), `directLimitRingEquivStalk` identifies `colim Γ(X, W)` with `𝒪_{X,x}`,
and `stalkOpensCone` expresses `(X.fromSpecStalk x ⁻¹ᵁ U).toScheme` as a cofiltered limit over
`Over W₀` (`isLimitStalkOpensCone`;
[Stacks Project, Lemma 32.20.3](https://stacks.math.columbia.edu/tag/0BQ5)).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

section Stalk

variable (X : Scheme.{u}) (x : X)

/-- The partially ordered set of affine open neighbourhoods of a point `x` in a scheme `X`. -/
def AffineOpenNhds : Type u := {W : X.affineOpens // x ∈ W.val}

namespace AffineOpenNhds

variable {X x}

instance : PartialOrder (X.AffineOpenNhds x) :=
  inferInstanceAs (PartialOrder {W : X.affineOpens // x ∈ W.val})

/-- Construct an affine open neighbourhood of `x` from `U : X.Opens`, `IsAffineOpen U`, `x ∈ U`. -/
def mk (U : X.Opens) (hU : IsAffineOpen U) (hx : x ∈ U) : X.AffineOpenNhds x := ⟨⟨U, hU⟩, hx⟩

/-- The underlying affine open of `X`. -/
def affineOpen (W : X.AffineOpenNhds x) : X.affineOpens := W.val

/-- The underlying open subset of `X`. -/
def opens (W : X.AffineOpenNhds x) : X.Opens := W.val.val

/-- The underlying affine open of `AffineOpenNhds.mk`. -/
@[simp] theorem mk_affineOpen (U : X.Opens) (hU : IsAffineOpen U) (hx : x ∈ U) :
    (mk U hU hx).affineOpen = ⟨U, hU⟩ := (rfl)

/-- The underlying open subset of `AffineOpenNhds.mk`. -/
@[simp] theorem mk_opens (U : X.Opens) (hU : IsAffineOpen U) (hx : x ∈ U) :
    (mk U hU hx).opens = U := (rfl)

/-- The base point `x` belongs to `W`. -/
theorem mem (W : X.AffineOpenNhds x) : x ∈ W.opens := W.property

/-- The underlying open subset of `W` is affine. -/
theorem isAffineOpen (W : X.AffineOpenNhds x) : IsAffineOpen W.opens := W.val.property

/-- Two affine open neighbourhoods of `x` are equal when their underlying open subsets agree. -/
@[ext] theorem ext {W₁ W₂ : X.AffineOpenNhds x} (h : W₁.opens = W₂.opens) : W₁ = W₂ :=
  Subtype.ext (Subtype.ext h)

/-- Ordering on `X.AffineOpenNhds x` is inclusion of underlying open subsets. -/
@[simp] theorem le_iff {W₁ W₂ : X.AffineOpenNhds x} : W₁ ≤ W₂ ↔ W₁.opens ≤ W₂.opens := Iff.rfl

instance : Nonempty (X.AffineOpenNhds x) :=
  let ⟨_, ⟨W, hW, rfl⟩, hxW, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  ⟨mk W hW hxW⟩
instance : IsCofilteredOrEmpty (X.AffineOpenNhds x) where
  cone_objs W₁ W₂ := by
    obtain ⟨_, ⟨W₃, hW₃, rfl⟩, hxW₃, hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_inter W₁.mem W₂.mem) (W₁.opens ⊓ W₂.opens).isOpen
    exact ⟨mk W₃ hW₃ hxW₃, homOfLE (le_iff.mpr (hle.trans inf_le_left)),
      homOfLE (le_iff.mpr (hle.trans inf_le_right)), trivial⟩
  cone_maps W₁ _ _ _ := ⟨W₁, 𝟙 W₁, Subsingleton.elim _ _⟩
instance : IsCofiltered (X.AffineOpenNhds x) := {}
instance : IsDirectedOrder (X.AffineOpenNhds x)ᵒᵈ where
  directed W₁ W₂ := let ⟨W₃, f₁, f₂, _⟩ :=
      IsCofilteredOrEmpty.cone_objs (OrderDual.ofDual W₁) (OrderDual.ofDual W₂)
    ⟨OrderDual.toDual W₃, leOfHom f₁, leOfHom f₂⟩

variable (X x) in
/-- Forgetful functor from affine open neighbourhoods of `x` to all open neighbourhoods of `x`. -/
@[expose, simps] def toOpenNhds : X.AffineOpenNhds x ⥤ OpenNhds x where
  obj W := ⟨W.opens, W.mem⟩
  map f := homOfLE (Subtype.mk_le_mk.mpr (le_iff.mp (leOfHom f)))

instance : (toOpenNhds X x).Initial := Functor.initial_of_exists_of_isCofiltered _
  (fun U ↦ let ⟨_, ⟨W, hW, rfl⟩, hxW, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open U.property U.val.isOpen
    ⟨mk W hW hxW, ⟨homOfLE (hle : (⟨W, hxW⟩ : OpenNhds x) ≤ U)⟩⟩)
  fun _ _ ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩

end AffineOpenNhds

/-- The diagram of affine open subschemes containing `x`, with open-inclusion transition maps. -/
@[expose, simps, implicit_reducible]
def affineOpenNhdsDiagram : X.AffineOpenNhds x ⥤ Scheme.{u} where
  obj W := W.opens.toScheme
  map f := X.homOfLE (AffineOpenNhds.le_iff.mp (leOfHom f))
  map_id W := X.homOfLE_rfl W.opens
  map_comp _ _ := (X.homOfLE_homOfLE _ _).symm

instance (W : X.AffineOpenNhds x) : IsAffine ((X.affineOpenNhdsDiagram x).obj W) := W.isAffineOpen
instance {W₁ W₂ : X.AffineOpenNhds x} (f : W₁ ⟶ W₂) :
    IsAffineHom ((X.affineOpenNhdsDiagram x).map f) := isAffineHom_of_isAffine _

/-- The natural isomorphism `W.opens.toScheme ≅ Spec Γ(X, W)` across `X.affineOpenNhdsDiagram x`. -/
def affineOpenNhdsDiagramIsoSpec :
    X.affineOpenNhdsDiagram x ≅
      (AffineOpenNhds.toOpenNhds X x ⋙ OpenNhds.inclusion x) ⋙ X.presheaf.rightOp ⋙ Scheme.Spec :=
  NatIso.ofComponents (fun W ↦ W.isAffineOpen.isoSpec) fun {_ _} f ↦
    (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map _ _ (AffineOpenNhds.le_iff.mp (leOfHom f))).symm

/-- Forward component of `affineOpenNhdsDiagramIsoSpec` at `W`. -/
@[simp] theorem affineOpenNhdsDiagramIsoSpec_hom_app (W : X.AffineOpenNhds x) :
    (X.affineOpenNhdsDiagramIsoSpec x).hom.app W = W.isAffineOpen.isoSpec.hom :=
  NatIso.ofComponents_hom_app _ _ W

/-- Inverse component of `affineOpenNhdsDiagramIsoSpec` at `W`. -/
@[simp] theorem affineOpenNhdsDiagramIsoSpec_inv_app (W : X.AffineOpenNhds x) :
    (X.affineOpenNhdsDiagramIsoSpec x).inv.app W = W.isAffineOpen.isoSpec.inv :=
  NatIso.ofComponents_inv_app _ _ W

/-- The cone with vertex `Spec 𝒪_{X,x}` over the diagram of affine open neighbourhoods of `x`. -/
@[expose, simps, implicit_reducible] def specStalkCone : Cone (X.affineOpenNhdsDiagram x) where
  pt := Spec (X.presheaf.stalk x)
  π := { app W := W.opens.fromSpecStalkOfMem x W.mem
         naturality _ W₂ _ := by
           dsimp [affineOpenNhdsDiagram]
           rw [Category.id_comp, ← cancel_mono W₂.opens.ι, Category.assoc, Scheme.homOfLE_ι,
             Opens.fromSpecStalkOfMem_ι, Opens.fromSpecStalkOfMem_ι] }

/-- `Spec 𝒪_{X,x}` is the cofiltered limit of the affine open neighbourhoods of `x`. -/
def isLimitSpecStalkCone : IsLimit (X.specStalkCone x) := by
  let hcW := (Functor.Final.isColimitWhiskerEquiv (AffineOpenNhds.toOpenNhds X x).op
    (colimit.cocone ((OpenNhds.inclusion x).op ⋙ X.presheaf))).symm (colimit.isColimit _)
  refine IsLimit.ofIsoLimit ((IsLimit.postcomposeInvEquiv (X.affineOpenNhdsDiagramIsoSpec x) _).symm
    (isLimitOfPreserves Scheme.Spec (isLimitConeRightOpOfCocone _ hcW)))
    -- Both cone vertices are definitionally `Spec (X.presheaf.stalk x)`.
    (Cone.ext (Iso.refl _) fun W ↦ ?_)
  simp only [Cone.postcompose_obj_π, Cone.postcompose_obj_pt, NatTrans.comp_app,
    Functor.mapCone_π_app, Functor.mapCone_pt, coneRightOpOfCocone_π, coneRightOpOfCocone_pt,
    NatTrans.rightOp_app, Cocone.whisker_ι, Cocone.whisker_pt, Functor.whiskerLeft_app,
    colimit.cocone_ι, colimit.cocone_x, Functor.rightOp_obj, Functor.comp_obj, Functor.op_obj,
    Scheme.Spec_map, Quiver.Hom.unop_op, unop_op, affineOpenNhdsDiagramIsoSpec_inv_app,
    specStalkCone_π_app, Iso.refl_hom]
  -- `TopCat.Presheaf.stalk` is definitionally `colimit ((OpenNhds.inclusion x).op ⋙ X.presheaf)`
  -- and `TopCat.Presheaf.germ` is definitionally `colimit.ι`.
  change Spec.map (X.presheaf.germ W.opens x W.mem) ≫ W.isAffineOpen.isoSpec.inv =
    𝟙 (Spec (X.presheaf.stalk x)) ≫ W.opens.fromSpecStalkOfMem x W.mem
  rw [Category.id_comp, ← Opens.fromSpecStalkOfMem_toSpecΓ_assoc W.opens x W.mem,
    ← IsAffineOpen.isoSpec_hom W.isAffineOpen, Iso.hom_inv_id, Category.comp_id]

/-- The directed system of section rings `Γ(X, W)` over `(X.AffineOpenNhds x)ᵒᵈ`. -/
abbrev stalkDirectSystemObj (W : (X.AffineOpenNhds x)ᵒᵈ) : Type u :=
  X.presheaf.obj (op (OrderDual.ofDual W).opens)

/-- The restriction maps in the directed system of section rings around `x`. -/
def stalkDirectSystemMap (W₁ W₂ : (X.AffineOpenNhds x)ᵒᵈ) (h : W₁ ≤ W₂) :
    X.stalkDirectSystemObj x W₁ →+* X.stalkDirectSystemObj x W₂ :=
  (X.presheaf.map (homOfLE (AffineOpenNhds.le_iff.mp (OrderDual.ofDual_le_ofDual.mpr h))).op).hom

/-- Evaluation of `stalkDirectSystemMap` as presheaf restriction. -/
@[simp] theorem stalkDirectSystemMap_apply (W₁ W₂ : (X.AffineOpenNhds x)ᵒᵈ) (h : W₁ ≤ W₂)
    (s : X.stalkDirectSystemObj x W₁) : X.stalkDirectSystemMap x W₁ W₂ h s =
      X.presheaf.map (homOfLE (AffineOpenNhds.le_iff.mp (OrderDual.ofDual_le_ofDual.mpr h))).op s :=
  (rfl)

instance : DirectedSystem (X.stalkDirectSystemObj x) (X.stalkDirectSystemMap x · · ·) where
  map_self _ _ := by simp
  map_map _ _ _ _ _ _ := by simp [← CommRingCat.comp_apply, ← X.presheaf.map_comp, ← op_comp]

/-- The canonical ring isomorphism from the concrete directed colimit of affine open section rings
around `x` to the stalk `𝒪_{X,x}`. -/
def directLimitRingEquivStalk :
    Ring.DirectLimit (X.stalkDirectSystemObj x) (X.stalkDirectSystemMap x · · ·) ≃+*
      X.presheaf.stalk x :=
  RingEquiv.ofBijective (Ring.DirectLimit.lift _ _ _
    (fun W ↦ (X.presheaf.germ (OrderDual.ofDual W).opens x (OrderDual.ofDual W).mem).hom)
    fun _ _ _ _ ↦ by simp) (by
      refine ⟨?_, fun t ↦ ?_⟩
      · rw [RingHom.injective_iff_ker_eq_bot, Submodule.eq_bot_iff]; intro z hz
        induction z using Ring.DirectLimit.induction_on with
        | ih W s =>
          rw [RingHom.mem_ker, Ring.DirectLimit.lift_of] at hz
          obtain ⟨V, hxV, hV, hVW, _, heq⟩ := TopCat.Presheaf.germ_eq_of_isBasis
            X.isBasis_affineOpens X.presheaf x (OrderDual.ofDual W).mem
            (OrderDual.ofDual W).mem (hz.trans (map_zero _).symm)
          have hWW' : W ≤ OrderDual.toDual (AffineOpenNhds.mk V hV hxV) :=
            OrderDual.le_toDual.mpr (AffineOpenNhds.le_iff.mpr hVW)
          have hzero : X.stalkDirectSystemMap x W _ hWW' s = 0 := by
            rw [stalkDirectSystemMap_apply]
            exact heq.trans (map_zero _)
          rw [← Ring.DirectLimit.of_f (hij := hWW'), hzero, map_zero]
      · obtain ⟨V, hxV, hV, s, rfl⟩ :=
          TopCat.Presheaf.exists_mem_germ_eq_of_isBasis X.isBasis_affineOpens X.presheaf x t
        let W : (X.AffineOpenNhds x)ᵒᵈ := OrderDual.toDual (AffineOpenNhds.mk V hV hxV)
        exact ⟨Ring.DirectLimit.of _ _ W (s : X.stalkDirectSystemObj x W),
          Ring.DirectLimit.lift_of ..⟩)

/-- Evaluation of `directLimitRingEquivStalk` on `Ring.DirectLimit.of` is the stalk germ. -/
@[simp] theorem directLimitRingEquivStalk_of (W : (X.AffineOpenNhds x)ᵒᵈ)
    (s : X.stalkDirectSystemObj x W) :
    X.directLimitRingEquivStalk x
        (Ring.DirectLimit.of (X.stalkDirectSystemObj x) (X.stalkDirectSystemMap x · · ·) W s) =
      X.presheaf.germ (OrderDual.ofDual W).opens x (OrderDual.ofDual W).mem s :=
  Ring.DirectLimit.lift_of (G := X.stalkDirectSystemObj x) (f := (X.stalkDirectSystemMap x · · ·))
    _ (fun W ↦ (X.presheaf.germ (OrderDual.ofDual W).opens x (OrderDual.ofDual W).mem).hom)
    (fun _ _ _ _ ↦ by simp) W s

end Stalk

section ExplicitNhds
variable (X : Scheme.{u}) (U : X.Opens) (x : X) (W₀ : X.AffineOpenNhds x)

/-- Diagram over `Over W₀` sending `j.left ≤ W₀` to the preimage of `U` in `j.left.opens`. -/
@[implicit_reducible] def stalkOpensDiagram : Over W₀ ⥤ Scheme.{u} :=
  opensDiagram (X.affineOpenNhdsDiagram x) W₀ (W₀.opens.ι ⁻¹ᵁ U)

/-- Cone over `X.stalkOpensDiagram U x W₀` induced by `X.specStalkCone x`. -/
@[implicit_reducible] def stalkOpensCone : Cone (X.stalkOpensDiagram U x W₀) :=
  opensCone (X.affineOpenNhdsDiagram x) (X.specStalkCone x) W₀ (W₀.opens.ι ⁻¹ᵁ U)

/-- `X.stalkOpensCone U x W₀` is a limit cone over `X.stalkOpensDiagram U x W₀`. -/
def isLimitStalkOpensCone : IsLimit (X.stalkOpensCone U x W₀) :=
  isLimitOpensCone (X.affineOpenNhdsDiagram x) (X.specStalkCone x) (X.isLimitSpecStalkCone x) W₀ _

/-- Identification of `(X.stalkOpensCone U x W₀).pt` with `(X.fromSpecStalk x ⁻¹ᵁ U).toScheme`. -/
def stalkOpensConePtIso : (X.stalkOpensCone U x W₀).pt ≅ (X.fromSpecStalk x ⁻¹ᵁ U).toScheme :=
  opensConePtIso (X.affineOpenNhdsDiagram x) (X.specStalkCone x) W₀ (W₀.opens.ι ⁻¹ᵁ U) ≪≫
    (Spec (X.presheaf.stalk x)).isoOfEq
      (by rw [← Scheme.Hom.comp_preimage, X.specStalkCone_π_app, Scheme.Opens.fromSpecStalkOfMem_ι])
end ExplicitNhds

section Instances
variable (X : Scheme.{u}) {U : X.Opens} {x : X} (W₀ : X.AffineOpenNhds x)
instance {j k : Over W₀} (f : j ⟶ k) : IsAffineHom ((X.stalkOpensDiagram U x W₀).map f) := by
  dsimp only [stalkOpensDiagram]; infer_instance
instance [QuasiCompact U.ι] (j : Over W₀) : CompactSpace ((X.stalkOpensDiagram U x W₀).obj j) :=
  isCompact_iff_compactSpace.mp <| (((X.affineOpenNhdsDiagram x).map j.hom).isCompact_preimage
    (W₀.opens.isCompact_ι_preimage_of_quasiCompact U W₀.isAffineOpen.isCompact))
instance (j : Over W₀) : QuasiSeparatedSpace ((X.stalkOpensDiagram U x W₀).obj j) :=
  (isQuasiSeparated_iff_quasiSeparatedSpace _
    ((X.affineOpenNhdsDiagram x).map j.hom ⁻¹ᵁ (W₀.opens.ι ⁻¹ᵁ U)).is_open').mp
      (.of_quasiSeparatedSpace _)
end Instances

variable (X : Scheme.{u}) (U : X.Opens) (x : X)

/-- Identification of stage `j` of `X.stalkOpensDiagram U x W₀` with `(j.left.opens.ι ⁻¹ᵁ U)`. -/
def stalkOpensObjIso {W₀ : X.AffineOpenNhds x} (j : Over W₀) :
    (X.stalkOpensDiagram U x W₀).obj j ≅ (j.left.opens.ι ⁻¹ᵁ U).toScheme :=
  opensDiagramObjIso (X.affineOpenNhdsDiagram x) W₀ (W₀.opens.ι ⁻¹ᵁ U) j ≪≫
    j.left.opens.toScheme.isoOfEq
      (by rw [← Scheme.Hom.comp_preimage, X.affineOpenNhdsDiagram_map, X.homOfLE_ι])

/-- Compatibility of `stalkOpensDiagram` transition maps with `stalkOpensObjIso` and inclusions. -/
theorem stalkOpensDiagram_map_comp_objIso_hom_ι {W₀ : X.AffineOpenNhds x} {j k : Over W₀}
    (f : j ⟶ k) :
    (X.stalkOpensDiagram U x W₀).map f ≫ (X.stalkOpensObjIso U x k).hom ≫ (k.left.opens.ι ⁻¹ᵁ U).ι =
      (X.stalkOpensObjIso U x j).hom ≫ (j.left.opens.ι ⁻¹ᵁ U).ι ≫
        X.homOfLE (AffineOpenNhds.le_iff.mp (leOfHom f.left)) := by
  simp only [stalkOpensDiagram, stalkOpensObjIso, Iso.trans_hom, Category.assoc,
    Scheme.isoOfEq_hom_ι, Scheme.isoOfEq_hom_ι_assoc, opensDiagram_map_comp_objIso_hom_assoc,
    Scheme.Hom.resLE_comp_ι, X.affineOpenNhdsDiagram_map x f.left]

/-- Compatibility of `stalkOpensCone` projections with `stalkOpensConePtIso` and inclusions. -/
theorem stalkOpensCone_π_app_comp_objIso_hom_ι {W₀ : X.AffineOpenNhds x} (j : Over W₀) :
    (X.stalkOpensCone U x W₀).π.app j ≫ (X.stalkOpensObjIso U x j).hom ≫ (j.left.opens.ι ⁻¹ᵁ U).ι =
      (X.stalkOpensConePtIso U x W₀).hom ≫ (X.fromSpecStalk x ⁻¹ᵁ U).ι ≫
        j.left.opens.fromSpecStalkOfMem x j.left.mem := by
  simp only [stalkOpensCone, stalkOpensObjIso, stalkOpensConePtIso, Iso.trans_hom, Category.assoc,
    Scheme.isoOfEq_hom_ι, Scheme.isoOfEq_hom_ι_assoc, opensCone_π_app_comp_objIso_hom_assoc,
    Scheme.Hom.resLE_comp_ι, X.specStalkCone_π_app x j.left]

/-- Canonical open immersion from the top stage `Over.mk (𝟙 W₀)` to `U.toScheme`. -/
def stalkOpensTopToOpen (W₀ : X.AffineOpenNhds x) :
    (X.stalkOpensDiagram U x W₀).obj (Over.mk (𝟙 W₀)) ⟶ U.toScheme :=
  (X.stalkOpensObjIso U x (Over.mk (𝟙 W₀))).hom ≫ W₀.opens.ι.resLE U (W₀.opens.ι ⁻¹ᵁ U) le_rfl

/-- Canonical open immersion from the top stage `Over.mk (𝟙 W₀)` to `W₀.opens.toScheme`. -/
def stalkOpensTopToNhds (W₀ : X.AffineOpenNhds x) :
    (X.stalkOpensDiagram U x W₀).obj (Over.mk (𝟙 W₀)) ⟶ W₀.opens.toScheme :=
  (X.stalkOpensObjIso U x (Over.mk (𝟙 W₀))).hom ≫ (W₀.opens.ι ⁻¹ᵁ U).ι

/-- Inclusions of the top stage of `X.stalkOpensDiagram U x W₀` into `U` and `W₀` agree in `X`. -/
theorem stalkOpensTopToOpen_ι (W₀ : X.AffineOpenNhds x) :
    X.stalkOpensTopToOpen U x W₀ ≫ U.ι = X.stalkOpensTopToNhds U x W₀ ≫ W₀.opens.ι := by
  simp [stalkOpensTopToOpen, stalkOpensTopToNhds]

/-- Top-stage projection of `stalkOpensCone` composed with `stalkOpensTopToNhds`. -/
theorem stalkOpensCone_π_top_toNhds (W₀ : X.AffineOpenNhds x) :
    (X.stalkOpensCone U x W₀).π.app (Over.mk (𝟙 W₀)) ≫ X.stalkOpensTopToNhds U x W₀ =
      ((X.stalkOpensConePtIso U x W₀).hom ≫ (X.fromSpecStalk x ⁻¹ᵁ U).ι) ≫
        W₀.opens.fromSpecStalkOfMem x W₀.mem := by
  simpa only [stalkOpensTopToNhds, Over.mk_left, Category.assoc] using
    X.stalkOpensCone_π_app_comp_objIso_hom_ι U x (W₀ := W₀) (Over.mk (𝟙 W₀))

/-- Top-stage projection of `stalkOpensCone` composed with `stalkOpensTopToOpen`. -/
theorem stalkOpensCone_π_top_toOpen (W₀ : X.AffineOpenNhds x) :
    (X.stalkOpensCone U x W₀).π.app (Over.mk (𝟙 W₀)) ≫ X.stalkOpensTopToOpen U x W₀ =
      (X.stalkOpensConePtIso U x W₀).hom ≫
        (X.fromSpecStalk x).resLE U (X.fromSpecStalk x ⁻¹ᵁ U) le_rfl := by
  rw [← cancel_mono U.ι, Category.assoc, X.stalkOpensTopToOpen_ι,
    ← Category.assoc ((X.stalkOpensCone U x W₀).π.app _), X.stalkOpensCone_π_top_toNhds]
  simp [Scheme.Opens.fromSpecStalkOfMem_ι]

/-- Identification of `(U ⊓ k.left.opens).toScheme` with stage `k` of `stalkOpensDiagram`. -/
def stalkOpensStageIso {W₀ : X.AffineOpenNhds x} (k : Over W₀) :
    (U ⊓ k.left.opens).toScheme ≅ (X.stalkOpensDiagram U x W₀).obj k :=
  (k.left.opens.ι.isoImage (k.left.opens.ι ⁻¹ᵁ U) ≪≫
    X.isoOfEq ((k.left.opens.ι_image_preimage_eq_inf U).trans (inf_comm _ _))).symm ≪≫
    (X.stalkOpensObjIso U x k).symm

/-- Compatibility of `stalkOpensStageIso` with the transition map to `W₀.opens.toScheme`. -/
theorem stalkOpensStageIso_hom_map_toNhds {W₀ : X.AffineOpenNhds x} {k : Over W₀}
    (fk : k ⟶ Over.mk (𝟙 W₀)) :
    (X.stalkOpensStageIso U x k).hom ≫ (X.stalkOpensDiagram U x W₀).map fk ≫
        X.stalkOpensTopToNhds U x W₀ =
      X.homOfLE (U := U ⊓ k.left.opens) (V := k.left.opens) inf_le_right ≫
        X.homOfLE (AffineOpenNhds.le_iff.mp (leOfHom k.hom)) := by
  have hmap := X.stalkOpensDiagram_map_comp_objIso_hom_ι U x fk
  have hfac : (k.left.opens.ι.isoImage (k.left.opens.ι ⁻¹ᵁ U) ≪≫
        X.isoOfEq ((k.left.opens.ι_image_preimage_eq_inf U).trans (inf_comm _ _))).inv ≫
      (k.left.opens.ι ⁻¹ᵁ U).ι = X.homOfLE inf_le_right := by
    rw [← cancel_mono k.left.opens.ι]; simp
  simp only [stalkOpensStageIso, stalkOpensTopToNhds, Iso.trans_hom, Iso.symm_hom, Over.mk_left,
    Category.assoc] at hmap ⊢
  have hfk : fk.left = k.hom := by simpa using Over.w fk
  rw [hmap, Iso.inv_hom_id_assoc, reassoc_of% hfac, hfk]

/-- Compatibility of `stalkOpensStageIso` with the transition map to `U.toScheme`. -/
theorem stalkOpensStageIso_hom_map_toOpen {W₀ : X.AffineOpenNhds x} {k : Over W₀}
    (fk : k ⟶ Over.mk (𝟙 W₀)) :
    (X.stalkOpensStageIso U x k).hom ≫ (X.stalkOpensDiagram U x W₀).map fk ≫
        X.stalkOpensTopToOpen U x W₀ = X.homOfLE (U := U ⊓ k.left.opens) (V := U) inf_le_left := by
  rw [← cancel_mono U.ι, Category.assoc, Category.assoc, X.stalkOpensTopToOpen_ι,
    reassoc_of% X.stalkOpensStageIso_hom_map_toNhds U x fk]; simp

/-- Compatibility of `stalkOpensConePtIso.inv`, `π.app k`, and `stalkOpensStageIso.inv` into `U`. -/
theorem stalkOpensConePtIso_inv_π_stageIso_inv {W₀ : X.AffineOpenNhds x} (k : Over W₀) :
    ((X.stalkOpensConePtIso U x W₀).inv ≫ (X.stalkOpensCone U x W₀).π.app k ≫
        (X.stalkOpensStageIso U x k).inv) ≫
      X.homOfLE (U := U ⊓ k.left.opens) (V := U) inf_le_left =
      (X.fromSpecStalk x).resLE U (X.fromSpecStalk x ⁻¹ᵁ U) le_rfl := by
  have hfac : (k.left.opens.ι ⁻¹ᵁ U).ι ≫ k.left.opens.ι = ((X.stalkOpensObjIso U x k).inv ≫
      (X.stalkOpensStageIso U x k).inv) ≫ X.homOfLE inf_le_left ≫ U.ι := by
    simp [stalkOpensStageIso]
  rw [← cancel_mono U.ι, Category.assoc, X.homOfLE_ι, Scheme.Hom.resLE_comp_ι]
  simpa only [← Category.assoc, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, hfac,
    X.homOfLE_ι, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc] using
    congrArg ((X.stalkOpensConePtIso U x W₀).inv ≫ · ≫ k.left.opens.ι)
      (X.stalkOpensCone_π_app_comp_objIso_hom_ι U x k)

/-- Compatibility of `stalkOpensConePtIso.inv`, `π.app k`, and `stalkOpensStageIso.inv` into `W`. -/
theorem stalkOpensConePtIso_inv_π_stageIso_inv_nhds {W₀ : X.AffineOpenNhds x} (k : Over W₀) :
    ((X.stalkOpensConePtIso U x W₀).inv ≫ (X.stalkOpensCone U x W₀).π.app k ≫
        (X.stalkOpensStageIso U x k).inv) ≫
      X.homOfLE (U := U ⊓ k.left.opens) (V := k.left.opens) inf_le_right =
      (X.fromSpecStalk x ⁻¹ᵁ U).ι ≫ k.left.opens.fromSpecStalkOfMem x k.left.mem := by
  rw [← cancel_mono k.left.opens.ι]
  have h := congrArg (· ≫ U.ι) (X.stalkOpensConePtIso_inv_π_stageIso_inv U x k)
  simpa only [Category.assoc, X.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι,
    Scheme.Hom.resLE_comp_ι] using h

end AlgebraicGeometry.Scheme
