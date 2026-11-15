/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.AlgebraicGeometry.Stalk
public import TauCeti.AlgebraicGeometry.Limits.AffineTransition

import Mathlib.CategoryTheory.Filtered.Final
import TauCeti.AlgebraicGeometry.Scheme.Opens

/-!
# The local scheme of a stalk as a cofiltered limit of affine open neighbourhoods

For a point `x` of a scheme `X`, the affine open neighbourhoods `W` of `x` form a cofiltered
partially ordered set `X.AffineOpenNhds x`. The functor sending `W` to `W.opens.toScheme` has
affine transition morphisms, and the morphisms `W.opens.fromSpecStalkOfMem x` assemble into a
limiting cone with vertex `Spec 𝒪_{X,x}`. Dually, the concrete directed colimit `Ring.DirectLimit`
of the section rings `Γ(X, W)` over `(X.AffineOpenNhds x)ᵒᵈ` is canonically isomorphic to the stalk
`𝒪_{X,x}` (`directLimitRingEquivStalk`).

Combining this limit presentation of `Spec 𝒪_{X,x}` with `opensDiagram` and `opensCone` presents
the preimage `(X.fromSpecStalk x) ⁻¹ᵁ U` of any open `U ⊆ X` as a cofiltered limit
(`stalkOpensDiagram`, `stalkOpensCone`, `isLimitStalkOpensCone`) of quasi-separated (and, when
`U.ι` is quasi-compact, quasi-compact) open subschemes `(U ⊓ W.opens).toScheme` of affine opens
with affine transition maps.

## Main definitions

* `AlgebraicGeometry.Scheme.AffineOpenNhds`: the partially ordered type of affine open
  neighbourhoods of `x` in `X`.
* `AlgebraicGeometry.Scheme.affineOpenNhdsDiagram`: the diagram `(X.AffineOpenNhds x) ⥤ Scheme`
  sending `W` to `W.opens.toScheme`.
* `AlgebraicGeometry.Scheme.specStalkCone` and `AlgebraicGeometry.Scheme.isLimitSpecStalkCone`:
  `Spec 𝒪_{X,x}` as the limit of `X.affineOpenNhdsDiagram x`.
* `AlgebraicGeometry.Scheme.directLimitRingEquivStalk`: the ring isomorphism from
  `Ring.DirectLimit` over `(X.AffineOpenNhds x)ᵒᵈ` to `𝒪_{X,x}`.
* `AlgebraicGeometry.Scheme.stalkOpensDiagram`, `AlgebraicGeometry.Scheme.stalkOpensCone`, and
  `AlgebraicGeometry.Scheme.isLimitStalkOpensCone`: `(X.fromSpecStalk x ⁻¹ᵁ U).toScheme` as a
  cofiltered limit over `Over W₀`, with stage/vertex identifications `stalkOpensObjIso`,
  `stalkOpensConePtIso`, and `stalkOpensStageIso`.

## References

* [Stacks Project, Lemma 32.20.3](https://stacks.math.columbia.edu/tag/0BQ5)
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (x : X)

/-- The partially ordered set of affine open neighbourhoods of a point `x` in a scheme `X`. -/
def AffineOpenNhds : Type u :=
  {W : X.affineOpens // x ∈ W.1}

namespace AffineOpenNhds

variable {X x}

instance : PartialOrder (X.AffineOpenNhds x) :=
  inferInstanceAs (PartialOrder {W : X.affineOpens // x ∈ W.1})

/-- Construct an affine open neighbourhood of `x` from an open subset `U : X.Opens`, a proof that
`U` is affine, and a proof that `x ∈ U`. -/
def mk (U : X.Opens) (hU : IsAffineOpen U) (hx : x ∈ U) : X.AffineOpenNhds x :=
  ⟨⟨U, hU⟩, hx⟩

/-- The underlying affine open of `X`. -/
def affineOpen (W : X.AffineOpenNhds x) : X.affineOpens := W.1

/-- The underlying open subset of `X`. -/
def opens (W : X.AffineOpenNhds x) : X.Opens := W.1.1

/-- The underlying affine open of `AffineOpenNhds.mk`. -/
@[simp]
theorem mk_affineOpen (U : X.Opens) (hU : IsAffineOpen U) (hx : x ∈ U) :
    (mk U hU hx).affineOpen = ⟨U, hU⟩ :=
  (rfl)

/-- The underlying open subset of `AffineOpenNhds.mk`. -/
@[simp]
theorem mk_opens (U : X.Opens) (hU : IsAffineOpen U) (hx : x ∈ U) :
    (mk U hU hx).opens = U :=
  (rfl)

/-- The base point `x` belongs to `W`. -/
theorem mem (W : X.AffineOpenNhds x) : x ∈ W.opens := W.2

/-- The underlying open subset of `W` is affine. -/
theorem isAffineOpen (W : X.AffineOpenNhds x) : IsAffineOpen W.opens := W.1.2

/-- Two affine open neighbourhoods of `x` are equal when their underlying open subsets agree. -/
@[ext]
theorem ext {W₁ W₂ : X.AffineOpenNhds x} (h : W₁.opens = W₂.opens) : W₁ = W₂ :=
  Subtype.ext (Subtype.ext h)

/-- Ordering on `X.AffineOpenNhds x` is inclusion of underlying open subsets. -/
@[simp]
theorem le_iff {W₁ W₂ : X.AffineOpenNhds x} : W₁ ≤ W₂ ↔ W₁.opens ≤ W₂.opens :=
  Iff.rfl

instance : Nonempty (X.AffineOpenNhds x) := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨mk W hW hxW⟩

instance : IsCofilteredOrEmpty (X.AffineOpenNhds x) where
  cone_objs W₁ W₂ := by
    have hx12 : x ∈ W₁.opens ⊓ W₂.opens := ⟨W₁.mem, W₂.mem⟩
    obtain ⟨_, ⟨W₃, hW₃, rfl⟩, hxW₃, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx12 (W₁.opens ⊓ W₂.opens).isOpen
    exact ⟨mk W₃ hW₃ hxW₃, homOfLE (le_iff.mpr (hle.trans inf_le_left)),
      homOfLE (le_iff.mpr (hle.trans inf_le_right)), trivial⟩
  cone_maps W₁ _ _ _ := ⟨W₁, 𝟙 W₁, Subsingleton.elim _ _⟩

instance : IsCofiltered (X.AffineOpenNhds x) where

instance : IsDirectedOrder (X.AffineOpenNhds x)ᵒᵈ where
  directed W₁ W₂ := by
    obtain ⟨W₃, f₁, f₂, -⟩ :=
      IsCofilteredOrEmpty.cone_objs (OrderDual.ofDual W₁) (OrderDual.ofDual W₂)
    exact ⟨OrderDual.toDual W₃, leOfHom f₁, leOfHom f₂⟩

variable (X x) in
/-- The forgetful functor from affine open neighbourhoods of `x` to all open neighbourhoods of
`x`. -/
@[expose, simps]
def toOpenNhds : X.AffineOpenNhds x ⥤ OpenNhds x where
  obj W := ⟨W.opens, W.mem⟩
  map f := homOfLE (Subtype.mk_le_mk.mpr (le_iff.mp (leOfHom f)))

instance : (toOpenNhds X x).Initial := by
  refine Functor.initial_of_exists_of_isCofiltered (toOpenNhds X x) (fun U ↦ ?_)
    (fun {_} {W} _ _ ↦ ⟨W, 𝟙 W, Subsingleton.elim _ _⟩)
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open U.2 U.1.isOpen
  have hle' : (⟨W, hxW⟩ : OpenNhds x) ≤ U := hle
  exact ⟨mk W hW hxW, ⟨homOfLE hle'⟩⟩

end AffineOpenNhds

/-- The diagram of affine open subschemes containing `x`, with open-inclusion transition maps. -/
@[expose, simps, implicit_reducible]
def affineOpenNhdsDiagram : X.AffineOpenNhds x ⥤ Scheme.{u} where
  obj W := W.opens.toScheme
  map f := X.homOfLE (AffineOpenNhds.le_iff.mp (leOfHom f))
  map_id W := X.homOfLE_rfl W.opens
  map_comp f g :=
    (X.homOfLE_homOfLE (AffineOpenNhds.le_iff.mp (leOfHom f))
      (AffineOpenNhds.le_iff.mp (leOfHom g))).symm

instance (W : X.AffineOpenNhds x) : IsAffine ((X.affineOpenNhdsDiagram x).obj W) := by
  rw [affineOpenNhdsDiagram_obj]
  exact W.isAffineOpen

instance {W₁ W₂ : X.AffineOpenNhds x} (f : W₁ ⟶ W₂) :
    IsAffineHom ((X.affineOpenNhdsDiagram x).map f) :=
  isAffineHom_of_isAffine _

/-- The natural isomorphism `W.opens.toScheme ≅ Spec Γ(X, W)` across `X.affineOpenNhdsDiagram x`. -/
def affineOpenNhdsDiagramIsoSpec :
    X.affineOpenNhdsDiagram x ≅
      (AffineOpenNhds.toOpenNhds X x ⋙ OpenNhds.inclusion x) ⋙
        X.presheaf.rightOp ⋙ Scheme.Spec :=
  NatIso.ofComponents
    (fun W ↦ W.isAffineOpen.isoSpec)
    (fun {_ _} f ↦
      (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map _ _ (AffineOpenNhds.le_iff.mp (leOfHom f))).symm)

/-- Forward component of `affineOpenNhdsDiagramIsoSpec` at `W`. -/
@[simp]
theorem affineOpenNhdsDiagramIsoSpec_hom_app (W : X.AffineOpenNhds x) :
    (X.affineOpenNhdsDiagramIsoSpec x).hom.app W = W.isAffineOpen.isoSpec.hom :=
  NatIso.ofComponents_hom_app _ _ W

/-- Inverse component of `affineOpenNhdsDiagramIsoSpec` at `W`. -/
@[simp]
theorem affineOpenNhdsDiagramIsoSpec_inv_app (W : X.AffineOpenNhds x) :
    (X.affineOpenNhdsDiagramIsoSpec x).inv.app W = W.isAffineOpen.isoSpec.inv :=
  NatIso.ofComponents_inv_app _ _ W

/-- The cone with vertex `Spec 𝒪_{X,x}` over the diagram of affine open neighbourhoods of `x`. -/
@[expose, implicit_reducible]
def specStalkCone : Cone (X.affineOpenNhdsDiagram x) where
  pt := Spec (X.presheaf.stalk x)
  π :=
    { app W := W.opens.fromSpecStalkOfMem x W.mem
      naturality {W₁ W₂} f := by
        dsimp [affineOpenNhdsDiagram]
        rw [Category.id_comp, ← cancel_mono W₂.opens.ι, Category.assoc, Scheme.homOfLE_ι,
          Opens.fromSpecStalkOfMem_ι, Opens.fromSpecStalkOfMem_ι] }

/-- Vertex of `X.specStalkCone x`. -/
@[simp]
theorem specStalkCone_pt : (X.specStalkCone x).pt = Spec (X.presheaf.stalk x) := rfl

/-- Projection of `X.specStalkCone x` to an affine open neighbourhood `W`. -/
@[simp]
theorem specStalkCone_π_app (W : X.AffineOpenNhds x) :
    (X.specStalkCone x).π.app W = W.opens.fromSpecStalkOfMem x W.mem := rfl

private def isColimitStalkWhisker (X : Scheme.{u}) (x : X) :
    IsColimit ((colimit.cocone ((OpenNhds.inclusion x).op ⋙ X.presheaf)).whisker
      (AffineOpenNhds.toOpenNhds X x).op) :=
  (Functor.Final.isColimitWhiskerEquiv (AffineOpenNhds.toOpenNhds X x).op
    (colimit.cocone ((OpenNhds.inclusion x).op ⋙ X.presheaf))).symm
    (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ X.presheaf))

/-- `Spec 𝒪_{X,x}` is the cofiltered limit of the affine open neighbourhoods of `x`. -/
def isLimitSpecStalkCone : IsLimit (X.specStalkCone x) := by
  let F : (X.AffineOpenNhds x)ᵒᵖ ⥤ CommRingCat.{u} :=
    (AffineOpenNhds.toOpenNhds X x).op ⋙ ((OpenNhds.inclusion x).op ⋙ X.presheaf)
  let hcSpec := isLimitOfPreserves Scheme.Spec
    (isLimitConeRightOpOfCocone F (isColimitStalkWhisker X x))
  let α : X.affineOpenNhdsDiagram x ≅ F.rightOp ⋙ Scheme.Spec :=
    X.affineOpenNhdsDiagramIsoSpec x
  -- `TopCat.Presheaf.stalk` is `colimit ((OpenNhds.inclusion x).op ⋙ X.presheaf)` and
  -- `TopCat.Presheaf.germ` is `colimit.ι ((OpenNhds.inclusion x).op ⋙ X.presheaf)`.
  have hpt : ((Cone.postcompose α.inv).obj
      (Scheme.Spec.mapCone (coneRightOpOfCocone
        ((colimit.cocone ((OpenNhds.inclusion x).op ⋙ X.presheaf)).whisker
          (AffineOpenNhds.toOpenNhds X x).op)))).pt = (X.specStalkCone x).pt := rfl
  refine IsLimit.ofIsoLimit ((IsLimit.postcomposeInvEquiv α _).symm hcSpec)
    (Cone.ext (eqToIso hpt) fun W ↦ ?_)
  have hlhs :
      ((Cone.postcompose α.inv).obj
          (Scheme.Spec.mapCone (coneRightOpOfCocone
            ((colimit.cocone ((OpenNhds.inclusion x).op ⋙ X.presheaf)).whisker
              (AffineOpenNhds.toOpenNhds X x).op)))).π.app W =
        Spec.map (X.presheaf.germ W.opens x W.mem) ≫ W.isAffineOpen.isoSpec.inv := rfl
  have hrhs :
      (eqToIso hpt).hom ≫ (X.specStalkCone x).π.app W =
        W.opens.fromSpecStalkOfMem x W.mem :=
    Category.id_comp (W.opens.fromSpecStalkOfMem x W.mem)
  rw [hlhs, hrhs, ← Opens.fromSpecStalkOfMem_toSpecΓ_assoc W.opens x W.mem,
    ← IsAffineOpen.isoSpec_hom W.isAffineOpen, Iso.hom_inv_id, Category.comp_id]

/-- The directed system of section rings `Γ(X, W)` over `(X.AffineOpenNhds x)ᵒᵈ`. -/
abbrev stalkDirectSystemObj (W : (X.AffineOpenNhds x)ᵒᵈ) : Type u :=
  X.presheaf.obj (op (OrderDual.ofDual W).opens)

/-- The restriction maps in the directed system of section rings around `x`. -/
def stalkDirectSystemMap (W₁ W₂ : (X.AffineOpenNhds x)ᵒᵈ) (h : W₁ ≤ W₂) :
    X.stalkDirectSystemObj x W₁ →+* X.stalkDirectSystemObj x W₂ :=
  (X.presheaf.map
    (homOfLE (AffineOpenNhds.le_iff.mp (OrderDual.ofDual_le_ofDual.mpr h))).op).hom

/-- Evaluation of `stalkDirectSystemMap` as presheaf restriction. -/
@[simp]
theorem stalkDirectSystemMap_apply (W₁ W₂ : (X.AffineOpenNhds x)ᵒᵈ) (h : W₁ ≤ W₂)
    (s : X.stalkDirectSystemObj x W₁) :
    X.stalkDirectSystemMap x W₁ W₂ h s =
      X.presheaf.map
        (homOfLE (AffineOpenNhds.le_iff.mp (OrderDual.ofDual_le_ofDual.mpr h))).op s := by
  rfl

instance : DirectedSystem (X.stalkDirectSystemObj x) (X.stalkDirectSystemMap x · · ·) where
  map_self _ _ := by simp
  map_map _ _ _ _ _ s := by
    simp only [stalkDirectSystemMap_apply, ← CommRingCat.comp_apply, ← X.presheaf.map_comp]
    rfl

/-- The canonical ring homomorphism from the concrete directed colimit of affine open section rings
around `x` to the stalk `𝒪_{X,x}`. -/
private def stalkRingHomFromDirectLimit :
    Ring.DirectLimit (X.stalkDirectSystemObj x) (X.stalkDirectSystemMap x · · ·) →+*
      X.presheaf.stalk x :=
  Ring.DirectLimit.lift (X.stalkDirectSystemObj x) (X.stalkDirectSystemMap x · · ·)
    (X.presheaf.stalk x)
    (fun W ↦ (X.presheaf.germ (OrderDual.ofDual W).opens x (OrderDual.ofDual W).mem).hom)
    (fun _ _ _ _ ↦ by simp)

@[simp]
private theorem stalkRingHomFromDirectLimit_of (W : (X.AffineOpenNhds x)ᵒᵈ)
    (s : X.stalkDirectSystemObj x W) :
    X.stalkRingHomFromDirectLimit x
        (Ring.DirectLimit.of (X.stalkDirectSystemObj x) (X.stalkDirectSystemMap x · · ·) W s) =
      X.presheaf.germ (OrderDual.ofDual W).opens x (OrderDual.ofDual W).mem s := by
  simp [stalkRingHomFromDirectLimit]

/-- The canonical ring isomorphism from the concrete directed colimit of affine open section rings
around `x` to the stalk `𝒪_{X,x}`. -/
def directLimitRingEquivStalk :
    Ring.DirectLimit (X.stalkDirectSystemObj x) (X.stalkDirectSystemMap x · · ·) ≃+*
      X.presheaf.stalk x := by
  refine RingEquiv.ofBijective (X.stalkRingHomFromDirectLimit x) ⟨?_, ?_⟩
  · rw [RingHom.injective_iff_ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    rw [RingHom.mem_ker] at hz
    induction z using Ring.DirectLimit.induction_on with
    | ih W s =>
      rw [stalkRingHomFromDirectLimit_of] at hz
      have hz0 :
          X.presheaf.germ (OrderDual.ofDual W).opens x (OrderDual.ofDual W).mem s =
            X.presheaf.germ (OrderDual.ofDual W).opens x (OrderDual.ofDual W).mem 0 :=
        hz.trans (map_zero _).symm
      obtain ⟨V, hxV, hV, hVW, _, heq⟩ :=
        TopCat.Presheaf.germ_eq_of_isBasis X.isBasis_affineOpens X.presheaf x
          (OrderDual.ofDual W).mem (OrderDual.ofDual W).mem hz0
      let W' : (X.AffineOpenNhds x)ᵒᵈ := OrderDual.toDual (AffineOpenNhds.mk V hV hxV)
      have hWW' : W ≤ W' :=
        OrderDual.le_toDual.mpr (AffineOpenNhds.le_iff.mpr
          ((AffineOpenNhds.mk_opens V hV hxV).le.trans hVW))
      have hmap0 : X.stalkDirectSystemMap x W W' hWW' s = 0 := heq.trans (map_zero _)
      rw [← Ring.DirectLimit.of_f (hij := hWW'), hmap0, map_zero]
  · intro t
    obtain ⟨V, hxV, hV, s, rfl⟩ :=
      TopCat.Presheaf.exists_mem_germ_eq_of_isBasis X.isBasis_affineOpens X.presheaf x t
    let W : (X.AffineOpenNhds x)ᵒᵈ := OrderDual.toDual (AffineOpenNhds.mk V hV hxV)
    let sW : X.stalkDirectSystemObj x W := s
    exact ⟨Ring.DirectLimit.of _ _ W sW, X.stalkRingHomFromDirectLimit_of x W sW⟩

/-- Evaluation of `directLimitRingEquivStalk` on `Ring.DirectLimit.of` is the stalk germ. -/
@[simp]
theorem directLimitRingEquivStalk_of (W : (X.AffineOpenNhds x)ᵒᵈ)
    (s : X.stalkDirectSystemObj x W) :
    X.directLimitRingEquivStalk x
        (Ring.DirectLimit.of (X.stalkDirectSystemObj x) (X.stalkDirectSystemMap x · · ·) W s) =
      X.presheaf.germ (OrderDual.ofDual W).opens x (OrderDual.ofDual W).mem s :=
  X.stalkRingHomFromDirectLimit_of x W s

section StalkOpens

/-- The diagram over `Over W₀` sending an affine open neighbourhood `j.left ≤ W₀` of `x` to the
preimage of `U` in `j.left.opens.toScheme`. -/
@[expose, implicit_reducible]
def stalkOpensDiagram (U : X.Opens) (x : X) (W₀ : X.AffineOpenNhds x) :
    Over W₀ ⥤ Scheme.{u} :=
  opensDiagram (X.affineOpenNhdsDiagram x) W₀ (W₀.opens.ι ⁻¹ᵁ U)

/-- The cone over `X.stalkOpensDiagram U x W₀` induced by `X.specStalkCone x`, with vertex
canonically isomorphic to `(X.fromSpecStalk x ⁻¹ᵁ U).toScheme`. -/
@[expose, implicit_reducible]
def stalkOpensCone (U : X.Opens) (x : X) (W₀ : X.AffineOpenNhds x) :
    Cone (X.stalkOpensDiagram U x W₀) :=
  opensCone (X.affineOpenNhdsDiagram x) (X.specStalkCone x) W₀ (W₀.opens.ι ⁻¹ᵁ U)

/-- `X.stalkOpensCone U x W₀` is a limit cone over `X.stalkOpensDiagram U x W₀`. -/
def isLimitStalkOpensCone (U : X.Opens) (x : X) (W₀ : X.AffineOpenNhds x) :
    IsLimit (X.stalkOpensCone U x W₀) :=
  isLimitOpensCone (X.affineOpenNhdsDiagram x) (X.specStalkCone x)
    (X.isLimitSpecStalkCone x) W₀ (W₀.opens.ι ⁻¹ᵁ U)

instance {U : X.Opens} {x : X} (W₀ : X.AffineOpenNhds x) {j k : Over W₀} (f : j ⟶ k) :
    IsAffineHom ((X.stalkOpensDiagram U x W₀).map f) := by
  dsimp only [stalkOpensDiagram]
  infer_instance

instance {U : X.Opens} [QuasiCompact U.ι] {x : X} (W₀ : X.AffineOpenNhds x) (j : Over W₀) :
    CompactSpace ((X.stalkOpensDiagram U x W₀).obj j) :=
  isCompact_iff_compactSpace.mp <|
    (((X.affineOpenNhdsDiagram x).map j.hom).isCompact_preimage
      (W₀.opens.isCompact_ι_preimage_of_quasiCompact U W₀.isAffineOpen.isCompact))

instance {U : X.Opens} {x : X} (W₀ : X.AffineOpenNhds x) (j : Over W₀) :
    QuasiSeparatedSpace ((X.stalkOpensDiagram U x W₀).obj j) :=
  (isQuasiSeparated_iff_quasiSeparatedSpace _
    ((X.affineOpenNhdsDiagram x).map j.hom ⁻¹ᵁ (W₀.opens.ι ⁻¹ᵁ U)).2).mp
    (.of_quasiSeparatedSpace _)

/-- Canonical identification of stage `j` of `X.stalkOpensDiagram U x W₀` with
`(j.left.opens.ι ⁻¹ᵁ U).toScheme`. -/
def stalkOpensObjIso (U : X.Opens) (x : X) {W₀ : X.AffineOpenNhds x} (j : Over W₀) :
    (X.stalkOpensDiagram U x W₀).obj j ≅ (j.left.opens.ι ⁻¹ᵁ U).toScheme :=
  opensDiagramObjIso (X.affineOpenNhdsDiagram x) W₀ (W₀.opens.ι ⁻¹ᵁ U) j ≪≫
    j.left.opens.toScheme.isoOfEq
      (by rw [← Scheme.Hom.comp_preimage, X.affineOpenNhdsDiagram_map, X.homOfLE_ι])

/-- Canonical identification of the vertex of `X.stalkOpensCone U x W₀` with
`(X.fromSpecStalk x ⁻¹ᵁ U).toScheme`. -/
def stalkOpensConePtIso (U : X.Opens) (x : X) (W₀ : X.AffineOpenNhds x) :
    (X.stalkOpensCone U x W₀).pt ≅ (X.fromSpecStalk x ⁻¹ᵁ U).toScheme :=
  opensConePtIso (X.affineOpenNhdsDiagram x) (X.specStalkCone x) W₀ (W₀.opens.ι ⁻¹ᵁ U) ≪≫
    (Spec (X.presheaf.stalk x)).isoOfEq
      (by rw [← Scheme.Hom.comp_preimage, X.specStalkCone_π_app,
        Scheme.Opens.fromSpecStalkOfMem_ι])

/-- Compatibility of `stalkOpensDiagram` transition maps with `stalkOpensObjIso` and open
inclusions. -/
theorem stalkOpensDiagram_map_comp_objIso_hom_ι (U : X.Opens) (x : X) {W₀ : X.AffineOpenNhds x}
    {j k : Over W₀} (f : j ⟶ k) :
    (X.stalkOpensDiagram U x W₀).map f ≫
        (X.stalkOpensObjIso U x k).hom ≫ (k.left.opens.ι ⁻¹ᵁ U).ι =
      (X.stalkOpensObjIso U x j).hom ≫ (j.left.opens.ι ⁻¹ᵁ U).ι ≫
        X.homOfLE (AffineOpenNhds.le_iff.mp (leOfHom f.left)) := by
  simp only [stalkOpensDiagram, stalkOpensObjIso, Iso.trans_hom, Category.assoc,
    Scheme.isoOfEq_hom_ι, Scheme.isoOfEq_hom_ι_assoc]
  rw [← Category.assoc, opensDiagram_map_comp_objIso_hom,
    Category.assoc, Scheme.Hom.resLE_comp_ι, X.affineOpenNhdsDiagram_map x f.left]

/-- Compatibility of `stalkOpensCone` projections with `stalkOpensConePtIso`, `stalkOpensObjIso`,
and `fromSpecStalkOfMem`. -/
theorem stalkOpensCone_π_app_comp_objIso_hom_ι (U : X.Opens) (x : X) {W₀ : X.AffineOpenNhds x}
    (j : Over W₀) :
    (X.stalkOpensCone U x W₀).π.app j ≫
        (X.stalkOpensObjIso U x j).hom ≫ (j.left.opens.ι ⁻¹ᵁ U).ι =
      (X.stalkOpensConePtIso U x W₀).hom ≫ (X.fromSpecStalk x ⁻¹ᵁ U).ι ≫
        j.left.opens.fromSpecStalkOfMem x j.left.mem := by
  simp only [stalkOpensCone, stalkOpensObjIso, stalkOpensConePtIso, Iso.trans_hom, Category.assoc,
    Scheme.isoOfEq_hom_ι, Scheme.isoOfEq_hom_ι_assoc]
  rw [← Category.assoc, opensCone_π_app_comp_objIso_hom,
    Category.assoc, Scheme.Hom.resLE_comp_ι, X.specStalkCone_π_app x j.left]

/-- Canonical open immersion from the top stage `Over.mk (𝟙 W₀)` of `X.stalkOpensDiagram U x W₀`
to `U.toScheme`. -/
def stalkOpensTopToOpen (U : X.Opens) (x : X) (W₀ : X.AffineOpenNhds x) :
    (X.stalkOpensDiagram U x W₀).obj (Over.mk (𝟙 W₀)) ⟶ U.toScheme :=
  (X.stalkOpensObjIso U x (Over.mk (𝟙 W₀))).hom ≫ W₀.opens.ι.resLE U (W₀.opens.ι ⁻¹ᵁ U) le_rfl

/-- Canonical open immersion from the top stage `Over.mk (𝟙 W₀)` of `X.stalkOpensDiagram U x W₀`
to `W₀.opens.toScheme`. -/
def stalkOpensTopToNhds (U : X.Opens) (x : X) (W₀ : X.AffineOpenNhds x) :
    (X.stalkOpensDiagram U x W₀).obj (Over.mk (𝟙 W₀)) ⟶ W₀.opens.toScheme :=
  (X.stalkOpensObjIso U x (Over.mk (𝟙 W₀))).hom ≫ (W₀.opens.ι ⁻¹ᵁ U).ι

/-- The inclusions of the top stage of `X.stalkOpensDiagram U x W₀` into `U` and `W₀` agree in `X`.
-/
theorem stalkOpensTopToOpen_ι (U : X.Opens) (x : X) (W₀ : X.AffineOpenNhds x) :
    X.stalkOpensTopToOpen U x W₀ ≫ U.ι = X.stalkOpensTopToNhds U x W₀ ≫ W₀.opens.ι := by
  simp [stalkOpensTopToOpen, stalkOpensTopToNhds]

/-- Composing the top-stage projection of `X.stalkOpensCone U x W₀` with `stalkOpensTopToNhds`
factors through `stalkOpensConePtIso` and `W₀.opens.fromSpecStalkOfMem x W₀.mem`. -/
theorem stalkOpensCone_π_top_toNhds (U : X.Opens) (x : X) (W₀ : X.AffineOpenNhds x) :
    (X.stalkOpensCone U x W₀).π.app (Over.mk (𝟙 W₀)) ≫ X.stalkOpensTopToNhds U x W₀ =
      ((X.stalkOpensConePtIso U x W₀).hom ≫ (X.fromSpecStalk x ⁻¹ᵁ U).ι) ≫
        W₀.opens.fromSpecStalkOfMem x W₀.mem := by
  simpa only [stalkOpensTopToNhds, Over.mk_left, Category.assoc] using
    X.stalkOpensCone_π_app_comp_objIso_hom_ι U x (W₀ := W₀) (Over.mk (𝟙 W₀))

/-- Composing the top-stage projection of `X.stalkOpensCone U x W₀` with `stalkOpensTopToOpen`
factors through `stalkOpensConePtIso` and `(X.fromSpecStalk x).resLE U (X.fromSpecStalk x ⁻¹ᵁ U)`.
-/
theorem stalkOpensCone_π_top_toOpen (U : X.Opens) (x : X) (W₀ : X.AffineOpenNhds x) :
    (X.stalkOpensCone U x W₀).π.app (Over.mk (𝟙 W₀)) ≫ X.stalkOpensTopToOpen U x W₀ =
      (X.stalkOpensConePtIso U x W₀).hom ≫
        (X.fromSpecStalk x).resLE U (X.fromSpecStalk x ⁻¹ᵁ U) le_rfl := by
  rw [← cancel_mono U.ι, Category.assoc, X.stalkOpensTopToOpen_ι,
    ← Category.assoc ((X.stalkOpensCone U x W₀).π.app _), X.stalkOpensCone_π_top_toNhds,
    Category.assoc, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
    Category.assoc, Scheme.Hom.resLE_comp_ι]

/-- Canonical isomorphism identifying `(U ⊓ k.left.opens).toScheme` with stage `k` of
`X.stalkOpensDiagram U x W₀`. -/
def stalkOpensStageIso (U : X.Opens) (x : X) {W₀ : X.AffineOpenNhds x} (k : Over W₀) :
    (U ⊓ k.left.opens).toScheme ≅ (X.stalkOpensDiagram U x W₀).obj k :=
  (k.left.opens.ι.isoImage (k.left.opens.ι ⁻¹ᵁ U) ≪≫
      X.isoOfEq ((k.left.opens.ι_image_preimage_eq_inf U).trans (inf_comm _ _))).symm ≪≫
    (X.stalkOpensObjIso U x k).symm

/-- Compatibility of `stalkOpensStageIso` with the transition map to `W₀.opens.toScheme`. -/
theorem stalkOpensStageIso_hom_map_toNhds (U : X.Opens) (x : X) {W₀ : X.AffineOpenNhds x}
    {k : Over W₀} (fk : k ⟶ Over.mk (𝟙 W₀)) :
    (X.stalkOpensStageIso U x k).hom ≫
        (X.stalkOpensDiagram U x W₀).map fk ≫ X.stalkOpensTopToNhds U x W₀ =
      X.homOfLE (U := U ⊓ k.left.opens) (V := k.left.opens) inf_le_right ≫
        X.homOfLE (AffineOpenNhds.le_iff.mp (leOfHom k.hom)) := by
  have hfk : fk.left = k.hom := by simpa using Over.w fk
  have hmap := X.stalkOpensDiagram_map_comp_objIso_hom_ι U x fk
  simp only [Over.mk_left] at hmap
  have hfac : (k.left.opens.ι.isoImage (k.left.opens.ι ⁻¹ᵁ U) ≪≫
        X.isoOfEq ((k.left.opens.ι_image_preimage_eq_inf U).trans (inf_comm _ _))).inv ≫
      (k.left.opens.ι ⁻¹ᵁ U).ι =
      X.homOfLE (U := U ⊓ k.left.opens) (V := k.left.opens) inf_le_right := by
    rw [← cancel_mono k.left.opens.ι]; simp
  simp only [stalkOpensStageIso, stalkOpensTopToNhds, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [hmap, Iso.inv_hom_id_assoc, reassoc_of% hfac, hfk]

/-- Compatibility of `stalkOpensStageIso` with the transition map to `U.toScheme`. -/
theorem stalkOpensStageIso_hom_map_toOpen (U : X.Opens) (x : X) {W₀ : X.AffineOpenNhds x}
    {k : Over W₀} (fk : k ⟶ Over.mk (𝟙 W₀)) :
    (X.stalkOpensStageIso U x k).hom ≫
        (X.stalkOpensDiagram U x W₀).map fk ≫ X.stalkOpensTopToOpen U x W₀ =
      X.homOfLE (U := U ⊓ k.left.opens) (V := U) inf_le_left := by
  rw [← cancel_mono U.ι, Category.assoc, Category.assoc, X.stalkOpensTopToOpen_ι,
    ← Category.assoc ((X.stalkOpensDiagram U x W₀).map fk),
    ← Category.assoc (X.stalkOpensStageIso U x k).hom, X.stalkOpensStageIso_hom_map_toNhds,
    Category.assoc, X.homOfLE_ι, X.homOfLE_ι, X.homOfLE_ι]

/-- Compatibility of `(stalkOpensConePtIso U x W₀).inv`, the cone leg `π.app k`, and
`(stalkOpensStageIso U x k).inv` with the restriction of `X.fromSpecStalk x` to `U ⊓ k.left.opens`.
-/
theorem stalkOpensConePtIso_inv_π_stageIso_inv (U : X.Opens) (x : X) {W₀ : X.AffineOpenNhds x}
    (k : Over W₀) :
    ((X.stalkOpensConePtIso U x W₀).inv ≫
        (X.stalkOpensCone U x W₀).π.app k ≫
        (X.stalkOpensStageIso U x k).inv) ≫
      X.homOfLE (U := U ⊓ k.left.opens) (V := U) inf_le_left =
      (X.fromSpecStalk x).resLE U (X.fromSpecStalk x ⁻¹ᵁ U) le_rfl := by
  have hfac : (k.left.opens.ι ⁻¹ᵁ U).ι ≫ k.left.opens.ι =
      ((X.stalkOpensObjIso U x k).inv ≫ (X.stalkOpensStageIso U x k).inv) ≫
        X.homOfLE (U := U ⊓ k.left.opens) (V := U) inf_le_left ≫ U.ι := by
    simp [stalkOpensStageIso]
  rw [← cancel_mono U.ι]
  simp only [Category.assoc, X.homOfLE_ι, Scheme.Hom.resLE_comp_ι]
  have hπ := congrArg (· ≫ k.left.opens.ι) (X.stalkOpensCone_π_app_comp_objIso_hom_ι U x k)
  simp only [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι] at hπ
  rw [hfac] at hπ
  simp only [← Category.assoc] at hπ ⊢
  have hπ' := congrArg ((X.stalkOpensConePtIso U x W₀).inv ≫ ·) hπ
  simpa only [Category.assoc, X.homOfLE_ι, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc] using hπ'

/-- Compatibility of `(stalkOpensConePtIso U x W₀).inv`, the cone leg `π.app k`, and
`(stalkOpensStageIso U x k).inv` with `k.left.opens.fromSpecStalkOfMem x k.left.mem`. -/
theorem stalkOpensConePtIso_inv_π_stageIso_inv_nhds (U : X.Opens) (x : X) {W₀ : X.AffineOpenNhds x}
    (k : Over W₀) :
    ((X.stalkOpensConePtIso U x W₀).inv ≫
        (X.stalkOpensCone U x W₀).π.app k ≫
        (X.stalkOpensStageIso U x k).inv) ≫
      X.homOfLE (U := U ⊓ k.left.opens) (V := k.left.opens) inf_le_right =
      (X.fromSpecStalk x ⁻¹ᵁ U).ι ≫ k.left.opens.fromSpecStalkOfMem x k.left.mem := by
  rw [← cancel_mono k.left.opens.ι]
  simp only [Category.assoc, X.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
  have h := congrArg (· ≫ U.ι) (X.stalkOpensConePtIso_inv_π_stageIso_inv U x k)
  simpa only [Category.assoc, X.homOfLE_ι, Scheme.Hom.resLE_comp_ι] using h

end StalkOpens

end AlgebraicGeometry.Scheme
