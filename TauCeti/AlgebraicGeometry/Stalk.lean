/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Stalk
public import TauCeti.AlgebraicGeometry.PuncturedSpectrum

import Mathlib.CategoryTheory.Filtered.Final
import TauCeti.Topology.Sober

/-!
# The local scheme of a stalk as a cofiltered limit of affine open neighbourhoods

For a point `x` of a scheme `X`, the affine open neighbourhoods `W` of `x` form a cofiltered
partially ordered set `X.AffineOpenNhds x`. The functor sending `W` to `W.opens.toScheme` has
affine transition morphisms, and the morphisms `W.opens.fromSpecStalkOfMem x` assemble into a
limiting cone with vertex `Spec 𝒪_{X,x}`. Dually, the stalk `𝒪_{X,x}` is canonically isomorphic to
the concrete directed colimit `Ring.DirectLimit` of the section rings `Γ(X, W)` over
`(X.AffineOpenNhds x)ᵒᵈ`.

Together with Mathlib's `AlgebraicGeometry.AffineTransitionLimit`, this presents both `Spec 𝒪_{X,x}`
and the preimage `(X.fromSpecStalk x) ⁻¹ᵁ U` of any open `U ⊆ X` as cofiltered limits of
quasi-separated (and, when `U.ι` is quasi-compact, quasi-compact) open subschemes of affine opens
with affine transition maps.

We also show that for any proper open `U ≠ ⊤` of a scheme `X`, the closed complement `X \ U`
contains the generic point `s` of one of its irreducible components, and for such `s` the preimage
`(X.fromSpecStalk s) ⁻¹ᵁ U` is the punctured spectrum of `𝒪_{X,s}`.

## Main definitions

* `AlgebraicGeometry.Scheme.AffineOpenNhds`: the partially ordered type of affine open
  neighbourhoods of `x` in `X`.
* `AlgebraicGeometry.Scheme.affineOpenNhdsDiagram`: the diagram `(X.AffineOpenNhds x) ⥤ Scheme`
  sending `W` to `W.opens.toScheme`.
* `AlgebraicGeometry.Scheme.specStalkCone` and `AlgebraicGeometry.Scheme.isLimitSpecStalkCone`:
  `Spec 𝒪_{X,x}` as the limit of `X.affineOpenNhdsDiagram x`.
* `AlgebraicGeometry.Scheme.stalkRingEquivDirectLimit`: the ring isomorphism between
  `Ring.DirectLimit` over `(X.AffineOpenNhds x)ᵒᵈ` and `𝒪_{X,x}`.

## Main results

* `AlgebraicGeometry.Scheme.Opens.exists_notMem_specializes_imp_mem`: every proper open `U ≠ ⊤`
  misses a point `s` whose strict generizations all lie in `U`.
* `TauCeti.fromSpecStalk_preimage_eq_puncturedSpectrum_of_specializes` and
  `AlgebraicGeometry.Scheme.Opens.exists_notMem_fromSpecStalk_preimage_eq_puncturedSpectrum`: for
  such a point `s`, the preimage of `U` in `Spec 𝒪_{X,s}` is
  `IsLocalRing.puncturedSpectrum 𝒪_{X,s}`.

## References

* [Stacks Project, Section 32.20](https://stacks.math.columbia.edu/tag/0BQ5)
* [Stacks Project, Lemma 58.21.6](https://stacks.math.columbia.edu/tag/0EY7)
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (x : X)

/-- The partially ordered set of affine open neighbourhoods of a point `x` in a scheme `X`. -/
@[expose]
def AffineOpenNhds : Type u :=
  {W : X.affineOpens // x ∈ W.1}

namespace AffineOpenNhds

variable {X x}

instance : PartialOrder (X.AffineOpenNhds x) :=
  inferInstanceAs (PartialOrder {W : X.affineOpens // x ∈ W.1})

/-- The underlying affine open of `X`. -/
abbrev affineOpen (W : X.AffineOpenNhds x) : X.affineOpens := W.1

/-- The underlying open subset of `X`. -/
abbrev opens (W : X.AffineOpenNhds x) : X.Opens := W.1.1

/-- The base point `x` belongs to `W`. -/
theorem mem (W : X.AffineOpenNhds x) : x ∈ W.opens := W.2

/-- The underlying open subset of `W` is affine. -/
theorem isAffineOpen (W : X.AffineOpenNhds x) : IsAffineOpen W.opens := W.1.2

@[ext]
theorem ext {W₁ W₂ : X.AffineOpenNhds x} (h : W₁.opens = W₂.opens) : W₁ = W₂ :=
  Subtype.ext (Subtype.ext h)

@[simp]
theorem le_iff {W₁ W₂ : X.AffineOpenNhds x} : W₁ ≤ W₂ ↔ W₁.opens ≤ W₂.opens :=
  Iff.rfl

instance : Nonempty (X.AffineOpenNhds x) := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨⟨⟨W, hW⟩, hxW⟩⟩

instance : IsCofilteredOrEmpty (X.AffineOpenNhds x) where
  cone_objs W₁ W₂ := by
    have hx12 : x ∈ W₁.opens ⊓ W₂.opens := ⟨W₁.mem, W₂.mem⟩
    obtain ⟨_, ⟨W₃, hW₃, rfl⟩, hxW₃, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx12 (W₁.opens ⊓ W₂.opens).isOpen
    exact ⟨⟨⟨W₃, hW₃⟩, hxW₃⟩, homOfLE (hle.trans inf_le_left),
      homOfLE (hle.trans inf_le_right), trivial⟩
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
  exact ⟨⟨⟨W, hW⟩, hxW⟩, ⟨homOfLE hle'⟩⟩

end AffineOpenNhds

/-- The diagram of affine open subschemes containing `x`, with open-inclusion transition maps. -/
@[expose, simps, implicit_reducible]
def affineOpenNhdsDiagram : X.AffineOpenNhds x ⥤ Scheme.{u} where
  obj W := W.opens.toScheme
  map f := X.homOfLE (AffineOpenNhds.le_iff.mp (leOfHom f))
  map_id W := X.homOfLE_rfl W.opens
  map_comp f g := (X.homOfLE_homOfLE (leOfHom f) (leOfHom g)).symm

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
    (fun {_ _} f ↦ (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map _ _ (leOfHom f)).symm)

@[simp]
theorem affineOpenNhdsDiagramIsoSpec_hom_app (W : X.AffineOpenNhds x) :
    (X.affineOpenNhdsDiagramIsoSpec x).hom.app W = W.isAffineOpen.isoSpec.hom :=
  NatIso.ofComponents_hom_app _ _ W

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

@[simp]
theorem specStalkCone_pt : (X.specStalkCone x).pt = Spec (X.presheaf.stalk x) := rfl

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
def stalkRingEquivDirectLimit :
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
      let W' : (X.AffineOpenNhds x)ᵒᵈ := OrderDual.toDual ⟨⟨V, hV⟩, hxV⟩
      have hWW' : W ≤ W' := hVW
      have hmap0 : X.stalkDirectSystemMap x W W' hWW' s = 0 := heq.trans (map_zero _)
      rw [← Ring.DirectLimit.of_f (hij := hWW'), hmap0, map_zero]
  · intro t
    obtain ⟨V, hxV, hV, s, rfl⟩ :=
      TopCat.Presheaf.exists_mem_germ_eq_of_isBasis X.isBasis_affineOpens X.presheaf x t
    let W : (X.AffineOpenNhds x)ᵒᵈ := OrderDual.toDual ⟨⟨V, hV⟩, hxV⟩
    let sW : X.stalkDirectSystemObj x W := s
    exact ⟨Ring.DirectLimit.of _ _ W sW, X.stalkRingHomFromDirectLimit_of x W sW⟩

@[simp]
theorem stalkRingEquivDirectLimit_of (W : (X.AffineOpenNhds x)ᵒᵈ)
    (s : X.stalkDirectSystemObj x W) :
    X.stalkRingEquivDirectLimit x
        (Ring.DirectLimit.of (X.stalkDirectSystemObj x) (X.stalkDirectSystemMap x · · ·) W s) =
      X.presheaf.germ (OrderDual.ofDual W).opens x (OrderDual.ofDual W).mem s :=
  X.stalkRingHomFromDirectLimit_of x W s

/-- Every proper open `U ≠ ⊤` of a scheme `X` misses the generic point `s` of an irreducible
component of `X \ U`; every strict generization of `s` lies in `U`. -/
theorem Opens.exists_notMem_specializes_imp_mem {X : Scheme.{u}} (U : X.Opens) (hU : U ≠ ⊤) :
    ∃ s : X, s ∉ U ∧ ∀ ⦃t : X⦄, t ⤳ s → t ≠ s → t ∈ U := by
  obtain ⟨z₀, hz₀⟩ : ((U : Set X)ᶜ).Nonempty :=
    Set.nonempty_compl.mpr fun h ↦ hU (SetLike.ext' (h.trans Opens.coe_top.symm))
  let : QuasiSober ((U : Set X)ᶜ : Set X) :=
    U.isOpen.isClosed_compl.isClosedEmbedding_subtypeVal.quasiSober
  obtain ⟨s, hs, -⟩ := U.isOpen.isClosed_compl.exists_genericPoint_specializes hz₀
  refine ⟨s.1, s.2, fun t hts hne ↦ ?_⟩
  by_contra htU
  have hts' : (⟨t, htU⟩ : ((U : Set X)ᶜ : Set X)) ⤳ s :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp hts
  exact hne (congrArg Subtype.val ((TauCeti.mem_genericPoints_iff.mp hs) ⟨t, htU⟩ hts'))

end AlgebraicGeometry.Scheme

namespace TauCeti

open AlgebraicGeometry

/-- If `s ∉ U` and every strict generization of `s` lies in `U`, then the preimage of `U` along
`Spec 𝒪_{X,s} ⟶ X` is the punctured spectrum of `𝒪_{X,s}`. -/
theorem fromSpecStalk_preimage_eq_puncturedSpectrum_of_specializes
    {X : Scheme.{u}} {U : X.Opens} {s : X} (hs : s ∉ U)
    (hgen : ∀ ⦃t : X⦄, t ⤳ s → t ≠ s → t ∈ U) :
    (X.fromSpecStalk s) ⁻¹ᵁ U = IsLocalRing.puncturedSpectrum (X.presheaf.stalk s) := by
  ext p
  rw [SetLike.mem_coe, SetLike.mem_coe, Scheme.Hom.mem_preimage]
  refine Iff.trans ?_ (IsLocalRing.mem_puncturedSpectrum_iff (X.presheaf.stalk s) p).symm
  constructor
  · intro hpU hpc
    subst hpc
    exact hs (Scheme.fromSpecStalk_closedPoint (X := X) (x := s) ▸ hpU)
  · intro hne
    have hspec : X.fromSpecStalk s p ⤳ s :=
      ((IsLocalRing.specializes_closedPoint p).map (X.fromSpecStalk s).continuous).trans
        (specializes_of_eq Scheme.fromSpecStalk_closedPoint)
    have hinj : X.fromSpecStalk s p ≠ s := by
      intro heq
      apply hne
      exact (X.fromSpecStalk s).isEmbedding.injective
        (heq.trans Scheme.fromSpecStalk_closedPoint.symm)
    exact hgen hspec hinj

end TauCeti

namespace AlgebraicGeometry.Scheme.Opens

/-- For any proper open `U ≠ ⊤` of a scheme `X`, there exists a point `s ∉ U` such that the
preimage of `U` in `Spec 𝒪_{X,s}` is the punctured spectrum of `𝒪_{X,s}`. -/
theorem exists_notMem_fromSpecStalk_preimage_eq_puncturedSpectrum
    {X : Scheme.{u}} (U : X.Opens) (hU : U ≠ ⊤) :
    ∃ s : X, s ∉ U ∧
      (X.fromSpecStalk s) ⁻¹ᵁ U = TauCeti.IsLocalRing.puncturedSpectrum (X.presheaf.stalk s) := by
  obtain ⟨s, hs, hgen⟩ := U.exists_notMem_specializes_imp_mem hU
  exact ⟨s, hs, TauCeti.fromSpecStalk_preimage_eq_puncturedSpectrum_of_specializes hs hgen⟩

end AlgebraicGeometry.Scheme.Opens
