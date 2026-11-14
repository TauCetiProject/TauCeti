/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.Topology.Convenient.HomSpace
public import TauCeti.Topology.Convenient.GeneratedBy

/-!
# Cartesian closed structure on categories of generated spaces

Given a family of topological spaces `G : ι → Type u`, Mathlib defines the full subcategory
`GeneratedByTopCat G` of `G`-generated spaces in `TopCat` and the equivalent Escardó–Lawson–Simpson
category `ContinuousGeneratedByCat G` of all spaces and `G`-continuous maps
(`ContinuousMapGeneratedBy G Y Z`).

This file equips both categories with chosen finite products (`CartesianMonoidalCategory` and
`BraidedCategory`) and, when each `G i` is locally compact and each `G i × G j` is `G`-generated,
with the `MonoidalClosed` structure induced by `Topology.ContinuousMapGeneratedBy.curryEquiv`:

* In `ContinuousGeneratedByCat G`, the product is `Y × Z` and `(ihom Y).obj Z` is
  `ContinuousMapGeneratedBy G Y Z`.
* In `GeneratedByTopCat G`, the product is `WithGeneratedByTopology G (Y × Z)` and `(ihom Y).obj Z`
  is `WithGeneratedByTopology G (ContinuousMapGeneratedBy G Y Z)`.
* When `Y` is `G`-generated, `ContinuousMapGeneratedBy G Y Z` has the same underlying maps as
  `C(Y, Z)`, `ContinuousMap.continuous_toContinuousMapGeneratedBy` gives continuity from the
  compact-open topology, and `Topology.ContinuousMapGeneratedBy.homeomorphContinuousMap` upgrades
  this to a homeomorphism when compact subsets of `Y` are images of compact subsets of generators.

## References

* M. Escardó, J. Lawson, and A. Simpson, *Comparing Cartesian closed categories of (core)
  compactly generated spaces*, Topology Appl. 143 (2004), 105–145.
* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Math. Z. 119
  (1971), 11–28.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Topology

universe v v' t u

section MappingSpaceComparison

variable {ι : Type t} {G : ι → Type u} [∀ i, TopologicalSpace (G i)]
  {Y : Type v} [TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]

namespace ContinuousMap

/-- Every continuous map `Y → Z` is `G`-continuous. -/
@[expose]
def toContinuousMapGeneratedBy (G : ι → Type u) [∀ i, TopologicalSpace (G i)] (f : C(Y, Z)) :
    ContinuousMapGeneratedBy G Y Z :=
  ⟨f, f.continuous.continuousGeneratedBy⟩

@[simp]
theorem toContinuousMapGeneratedBy_apply (f : C(Y, Z)) (y : Y) :
    f.toContinuousMapGeneratedBy G y = f y := rfl

/-- The canonical inclusion from the compact-open mapping space `C(Y, Z)` to
`ContinuousMapGeneratedBy G Y Z` is continuous. -/
@[continuity, fun_prop]
theorem continuous_toContinuousMapGeneratedBy :
    Continuous (toContinuousMapGeneratedBy G : C(Y, Z) → ContinuousMapGeneratedBy G Y Z) :=
  ContinuousMapGeneratedBy.continuous_iff.2 fun _ p ↦ p.continuous_precomp

end ContinuousMap

namespace Topology.ContinuousMapGeneratedBy

/-- When the source `Y` is `G`-generated, every `G`-continuous map `Y → Z` is continuous. -/
@[expose]
def toContinuousMap [IsGeneratedBy G Y] (f : ContinuousMapGeneratedBy G Y Z) : C(Y, Z) :=
  ⟨f, (IsGeneratedBy.continuous_iff G f).2 f.prop⟩

@[simp]
theorem toContinuousMap_apply [IsGeneratedBy G Y] (f : ContinuousMapGeneratedBy G Y Z) (y : Y) :
    f.toContinuousMap y = f y := rfl

@[simp]
theorem coe_toContinuousMap [IsGeneratedBy G Y] (f : ContinuousMapGeneratedBy G Y Z) :
    (f.toContinuousMap : Y → Z) = f := rfl

/-- When `Y` is `G`-generated, `G`-continuous maps `Y → Z` coincide with continuous maps `Y → Z`. -/
@[expose]
def equivContinuousMap [IsGeneratedBy G Y] : ContinuousMapGeneratedBy G Y Z ≃ C(Y, Z) where
  toFun := toContinuousMap
  invFun := ContinuousMap.toContinuousMapGeneratedBy G
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

@[simp]
theorem equivContinuousMap_apply [IsGeneratedBy G Y] (f : ContinuousMapGeneratedBy G Y Z) :
    equivContinuousMap f = f.toContinuousMap := (rfl)

@[simp]
theorem equivContinuousMap_symm_apply [IsGeneratedBy G Y] (f : C(Y, Z)) :
    (equivContinuousMap (G := G)).symm f = f.toContinuousMapGeneratedBy G := (rfl)

/-- If every compact subset of `Y` is the image of a compact subset of some generator `G i` along a
continuous map `G i → Y`, then `toContinuousMap` is continuous into the compact-open topology on
`C(Y, Z)`. -/
theorem continuous_toContinuousMap [IsGeneratedBy G Y]
    (hG : ∀ ⦃K : Set Y⦄, IsCompact K →
      ∃ (i : ι) (L : Set (G i)) (p : C(G i, Y)), IsCompact L ∧ p '' L = K) :
    Continuous (toContinuousMap : ContinuousMapGeneratedBy G Y Z → C(Y, Z)) := by
  refine ContinuousMap.continuous_compactOpen.2 fun K hK U hU ↦ ?_
  obtain ⟨i, L, p, hL, rfl⟩ := hG hK
  rw [show {f : ContinuousMapGeneratedBy G Y Z | Set.MapsTo f.toContinuousMap (p '' L) U} =
      precomp p ⁻¹' {g : C(G i, Z) | Set.MapsTo g L U} by ext; exact Set.mapsTo_image_iff]
  exact (ContinuousMap.isOpen_setOfPred_mapsTo hL hU).preimage (continuous_precomp p)

/-- When `Y` is `G`-generated and every compact subset of `Y` is the continuous image of a compact
subset of some generator `G i`, the `G`-probed mapping space `ContinuousMapGeneratedBy G Y Z` is
homeomorphic to `C(Y, Z)` with the compact-open topology. -/
@[expose]
def homeomorphContinuousMap [IsGeneratedBy G Y]
    (hG : ∀ ⦃K : Set Y⦄, IsCompact K →
      ∃ (i : ι) (L : Set (G i)) (p : C(G i, Y)), IsCompact L ∧ p '' L = K) :
    ContinuousMapGeneratedBy G Y Z ≃ₜ C(Y, Z) where
  toEquiv := equivContinuousMap
  continuous_toFun := continuous_toContinuousMap hG
  continuous_invFun := ContinuousMap.continuous_toContinuousMapGeneratedBy

@[simp]
theorem homeomorphContinuousMap_apply [IsGeneratedBy G Y]
    (hG : ∀ ⦃K : Set Y⦄, IsCompact K →
      ∃ (i : ι) (L : Set (G i)) (p : C(G i, Y)), IsCompact L ∧ p '' L = K)
    (f : ContinuousMapGeneratedBy G Y Z) :
    homeomorphContinuousMap hG f = f.toContinuousMap := (rfl)

@[simp]
theorem homeomorphContinuousMap_symm_apply [IsGeneratedBy G Y]
    (hG : ∀ ⦃K : Set Y⦄, IsCompact K →
      ∃ (i : ι) (L : Set (G i)) (p : C(G i, Y)), IsCompact L ∧ p '' L = K) (f : C(Y, Z)) :
    (homeomorphContinuousMap (Z := Z) hG).symm f = f.toContinuousMapGeneratedBy G := (rfl)

end Topology.ContinuousMapGeneratedBy

end MappingSpaceComparison

namespace ContinuousGeneratedByCat

variable {ι : Type t} {G : ι → Type u} [∀ i, TopologicalSpace (G i)]

/-- `PUnit` is terminal in `ContinuousGeneratedByCat G`. -/
@[expose]
def isTerminalPUnit : IsTerminal (of (X := G) PUnit.{v + 1}) :=
  have : ∀ Y : ContinuousGeneratedByCat.{v} G, Unique (Y ⟶ of (X := G) PUnit.{v + 1}) := fun _ ↦
    ⟨⟨homMk (fun _ ↦ PUnit.unit) continuous_const.continuousGeneratedBy⟩, fun _ ↦ by ext⟩
  IsTerminal.ofUnique _

/-- First projection from the binary product in `ContinuousGeneratedByCat G`. -/
@[expose]
def prodFst (Y Z : ContinuousGeneratedByCat.{v} G) : of (X := G) (Y × Z) ⟶ Y :=
  homMk Prod.fst continuous_fst.continuousGeneratedBy

/-- Second projection from the binary product in `ContinuousGeneratedByCat G`. -/
@[expose]
def prodSnd (Y Z : ContinuousGeneratedByCat.{v} G) : of (X := G) (Y × Z) ⟶ Z :=
  homMk Prod.snd continuous_snd.continuousGeneratedBy

/-- The explicit binary product fan in `ContinuousGeneratedByCat G`, whose point is `Y × Z` with
the ordinary product topology. -/
@[expose]
def prodBinaryFan (Y Z : ContinuousGeneratedByCat.{v} G) : BinaryFan Y Z :=
  BinaryFan.mk (prodFst Y Z) (prodSnd Y Z)

/-- The ordinary product `Y × Z` is a categorical binary product in `ContinuousGeneratedByCat G`. -/
@[expose]
def prodBinaryFanIsLimit (Y Z : ContinuousGeneratedByCat.{v} G) :
    IsLimit (prodBinaryFan Y Z) where
  lift := fun S : BinaryFan Y Z ↦ homMk (fun s ↦ (S.fst s, S.snd s))
    fun _ p ↦ (S.fst.hom.prop p).prodMk (S.snd.hom.prop p)
  fac := by rintro S (_ | _) <;> rfl
  uniq S m hm := by
    ext s
    exact Prod.ext (ConcreteCategory.congr_hom (hm ⟨WalkingPair.left⟩) s)
      (ConcreteCategory.congr_hom (hm ⟨WalkingPair.right⟩) s)

instance instCartesianMonoidalCategory :
    CartesianMonoidalCategory (ContinuousGeneratedByCat.{v} G) :=
  .ofChosenFiniteProducts ⟨_, isTerminalPUnit⟩
    fun Y Z ↦ ⟨prodBinaryFan Y Z, prodBinaryFanIsLimit Y Z⟩

instance instBraidedCategory : BraidedCategory (ContinuousGeneratedByCat.{v} G) :=
  .ofCartesianMonoidalCategory

@[simp]
theorem tensor_apply {W X Y Z : ContinuousGeneratedByCat.{v} G} (f : W ⟶ X) (g : Y ⟶ Z)
    (p : ↑(W ⊗ Y)) : (f ⊗ₘ g) p = (f p.1, g p.2) := rfl

@[simp]
theorem whiskerLeft_apply (X : ContinuousGeneratedByCat.{v} G)
    {Y Z : ContinuousGeneratedByCat.{v} G} (f : Y ⟶ Z) (p : ↑(X ⊗ Y)) :
    (X ◁ f) p = (p.1, f p.2) := rfl

@[simp]
theorem whiskerRight_apply {Y Z : ContinuousGeneratedByCat.{v} G} (f : Y ⟶ Z)
    (X : ContinuousGeneratedByCat.{v} G) (p : ↑(Y ⊗ X)) : (f ▷ X) p = (f p.1, p.2) := rfl

@[simp]
theorem fst_apply (X Y : ContinuousGeneratedByCat.{v} G) (p : ↑(X ⊗ Y)) :
    CartesianMonoidalCategory.fst X Y p = p.1 := rfl

@[simp]
theorem snd_apply (X Y : ContinuousGeneratedByCat.{v} G) (p : ↑(X ⊗ Y)) :
    CartesianMonoidalCategory.snd X Y p = p.2 := rfl

@[simp]
protected theorem lift_apply {X Y Z : ContinuousGeneratedByCat.{v} G} (f : X ⟶ Y) (g : X ⟶ Z)
    (x : X) : CartesianMonoidalCategory.lift f g x = (f x, g x) := rfl

section Closed

variable [∀ i, LocallyCompactSpace (G i)] [∀ i j, IsGeneratedBy G (G i × G j)]

/-- The internal hom functor on `ContinuousGeneratedByCat G`, sending `Z` to the `G`-probed
mapping space `ContinuousMapGeneratedBy G Y Z`. -/
@[expose, simps]
def ihomFunctor (Y : ContinuousGeneratedByCat.{v} G) :
    ContinuousGeneratedByCat.{v} G ⥤ ContinuousGeneratedByCat.{v} G where
  obj Z := of (ContinuousMapGeneratedBy G Y Z)
  map p := ConcreteCategory.ofHom p.hom.postcomp

/-- Currying equivalence `(Y ⊗ Z ⟶ T) ≃ (Z ⟶ (ihomFunctor Y).obj T)` in
`ContinuousGeneratedByCat G`. -/
@[expose]
def curryEquiv (Y Z T : ContinuousGeneratedByCat.{v} G) :
    (Y ⊗ Z ⟶ T) ≃ (Z ⟶ (ihomFunctor Y).obj T) where
  toFun f := ConcreteCategory.ofHom (ContinuousMapGeneratedBy.curryEquiv f.hom)
  invFun g := ConcreteCategory.ofHom (ContinuousMapGeneratedBy.curryEquiv.symm g.hom)
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

/-- `Y ⊗ -` is left adjoint to `ihomFunctor Y` in `ContinuousGeneratedByCat G`. -/
@[expose]
def tensorLeftAdjunction (Y : ContinuousGeneratedByCat.{v} G) : tensorLeft Y ⊣ ihomFunctor Y :=
  Adjunction.mkOfHomEquiv
    { homEquiv := curryEquiv Y
      homEquiv_naturality_left_symm _ _ := by ext ⟨_, _⟩; rfl
      homEquiv_naturality_right _ _ := by ext; rfl }

instance instMonoidalClosed : MonoidalClosed (ContinuousGeneratedByCat.{v} G) where
  closed Y := { rightAdj := ihomFunctor Y, adj := tensorLeftAdjunction Y }

end Closed

end ContinuousGeneratedByCat

namespace GeneratedByTopCat

variable {ι : Type t} {G : ι → Type u} [∀ i, TopologicalSpace (G i)]

/-- `PUnit` is terminal in `GeneratedByTopCat G`. -/
@[expose]
def isTerminalPUnit : IsTerminal (of (X := G) PUnit.{v + 1}) :=
  have : ∀ Y : GeneratedByTopCat.{v} G, Unique (Y ⟶ of (X := G) PUnit.{v + 1}) := fun _ ↦
    ⟨⟨ObjectProperty.homMk (TopCat.ofHom ⟨fun _ ↦ PUnit.unit, continuous_const⟩)⟩, fun _ ↦ by ext⟩
  IsTerminal.ofUnique _

/-- First projection from the convenient product `WithGeneratedByTopology G (Y × Z)`. -/
@[expose]
def prodFst (Y Z : GeneratedByTopCat.{v} G) :
    of (X := G) (WithGeneratedByTopology G (Y × Z)) ⟶ Y :=
  ObjectProperty.homMk (TopCat.ofHom ⟨fun p ↦ (WithGeneratedByTopology.equiv p).1,
    continuous_fst.comp WithGeneratedByTopology.continuous_equiv⟩)

/-- Second projection from the convenient product `WithGeneratedByTopology G (Y × Z)`. -/
@[expose]
def prodSnd (Y Z : GeneratedByTopCat.{v} G) :
    of (X := G) (WithGeneratedByTopology G (Y × Z)) ⟶ Z :=
  ObjectProperty.homMk (TopCat.ofHom ⟨fun p ↦ (WithGeneratedByTopology.equiv p).2,
    continuous_snd.comp WithGeneratedByTopology.continuous_equiv⟩)

@[simp]
theorem prodFst_apply (Y Z : GeneratedByTopCat.{v} G) (p : WithGeneratedByTopology G (Y × Z)) :
    prodFst Y Z p = (WithGeneratedByTopology.equiv p).1 := rfl

@[simp]
theorem prodSnd_apply (Y Z : GeneratedByTopCat.{v} G) (p : WithGeneratedByTopology G (Y × Z)) :
    prodSnd Y Z p = (WithGeneratedByTopology.equiv p).2 := rfl

/-- The explicit binary product fan in `GeneratedByTopCat G`, whose point is the generated
refinement `WithGeneratedByTopology G (Y × Z)` of the ordinary topological product. -/
@[expose]
def prodBinaryFan (Y Z : GeneratedByTopCat.{v} G) : BinaryFan Y Z :=
  BinaryFan.mk (prodFst Y Z) (prodSnd Y Z)

/-- The generated refinement `WithGeneratedByTopology G (Y × Z)` is a categorical binary product in
`GeneratedByTopCat G`. -/
@[expose]
def prodBinaryFanIsLimit (Y Z : GeneratedByTopCat.{v} G) : IsLimit (prodBinaryFan Y Z) where
  lift := fun S : BinaryFan Y Z ↦ ObjectProperty.homMk (TopCat.ofHom
    ⟨fun s ↦ WithGeneratedByTopology.equiv.symm (S.fst.hom.hom s, S.snd.hom.hom s),
      (IsGeneratedBy.equiv_symm_comp_continuous_iff (X := G)
        (fun s : S.pt ↦ (S.fst.hom.hom s, S.snd.hom.hom s))).2
        (S.fst.hom.hom.continuous.prodMk S.snd.hom.hom.continuous)⟩)
  fac := by rintro S (_ | _) <;> rfl
  uniq S m hm := by
    ext x
    apply (WithGeneratedByTopology.equiv (X := G)).injective
    exact Prod.ext
      (ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom (hm ⟨WalkingPair.left⟩)) x)
      (ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom (hm ⟨WalkingPair.right⟩)) x)

instance instCartesianMonoidalCategory : CartesianMonoidalCategory (GeneratedByTopCat.{v} G) :=
  .ofChosenFiniteProducts ⟨_, isTerminalPUnit⟩
    fun Y Z ↦ ⟨prodBinaryFan Y Z, prodBinaryFanIsLimit Y Z⟩

instance instBraidedCategory : BraidedCategory (GeneratedByTopCat.{v} G) :=
  .ofCartesianMonoidalCategory

@[simp]
theorem fst_apply (Y Z : GeneratedByTopCat.{v} G) (p : ↑(Y ⊗ Z)) :
    CartesianMonoidalCategory.fst Y Z p =
      (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z) p).1 := rfl

@[simp]
theorem snd_apply (Y Z : GeneratedByTopCat.{v} G) (p : ↑(Y ⊗ Z)) :
    CartesianMonoidalCategory.snd Y Z p =
      (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z) p).2 := rfl

@[simp]
protected theorem lift_apply {X Y Z : GeneratedByTopCat.{v} G} (f : X ⟶ Y) (g : X ⟶ Z) (x : X) :
    CartesianMonoidalCategory.lift f g x =
      (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z)).symm (f x, g x) := rfl

section Closed

variable [∀ i, LocallyCompactSpace (G i)] [∀ i j, IsGeneratedBy G (G i × G j)]

/-- The internal hom functor on `GeneratedByTopCat G`, sending `Z` to the `G`-generated refinement
of `ContinuousMapGeneratedBy G Y Z`. -/
@[expose, simps! obj]
def ihomFunctor (Y : GeneratedByTopCat.{v} G) :
    GeneratedByTopCat.{v} G ⥤ GeneratedByTopCat.{v} G where
  obj Z := of (WithGeneratedByTopology G (ContinuousMapGeneratedBy G Y Z))
  map p := ObjectProperty.homMk (TopCat.ofHom
    ((p.hom.hom.toContinuousMapGeneratedBy G).postcomp (Y := Y)).prop.continuousMap)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

@[simp]
theorem ihomFunctor_map_apply {Y Z T : GeneratedByTopCat.{v} G} (p : Z ⟶ T)
    (g : ↑((ihomFunctor Y).obj Z)) (y : Y) :
    (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T)
      ((ihomFunctor Y).map p g)) y =
      p ((WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y Z) g) y) := rfl

/-- Currying a morphism `Y ⊗ Z ⟶ T` in `GeneratedByTopCat G`. -/
@[expose]
def curryHom {Y Z T : GeneratedByTopCat.{v} G} (f : Y ⊗ Z ⟶ T) : Z ⟶ (ihomFunctor Y).obj T :=
  let c := (ContinuousMapGeneratedBy.curryEquiv (X := G)
    { toFun p := f.hom.hom ((WithGeneratedByTopology.equiv (X := G) (Y := Y × Z)).symm p)
      prop := fun _ q ↦ f.hom.hom.continuous.comp
        ((IsGeneratedBy.equiv_symm_comp_continuous_iff (X := G) q).2 q.continuous) })
    |>.toContinuousMap
  ObjectProperty.homMk <| TopCat.ofHom
    ⟨(WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T)).symm ∘ c,
      (IsGeneratedBy.equiv_symm_comp_continuous_iff (X := G) c).2 c.continuous⟩

/-- Uncurrying a morphism `Z ⟶ (ihomFunctor Y).obj T` in `GeneratedByTopCat G`. -/
@[expose]
def uncurryHom {Y Z T : GeneratedByTopCat.{v} G} (g : Z ⟶ (ihomFunctor Y).obj T) : Y ⊗ Z ⟶ T :=
  let g₀ : C(Z, ContinuousMapGeneratedBy G Y T) :=
    ⟨WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T) ∘ g.hom.hom,
      WithGeneratedByTopology.continuous_equiv.comp g.hom.hom.continuous⟩
  let u := ContinuousMapGeneratedBy.curryEquiv.symm (g₀.toContinuousMapGeneratedBy G)
  ObjectProperty.homMk <| TopCat.ofHom
    ⟨WithGeneratedByTopology.equiv (X := G) (Y := T) ∘ u.prop.continuousMap,
      WithGeneratedByTopology.continuous_equiv.comp u.prop.continuousMap.continuous⟩

@[simp]
theorem equiv_curryHom_apply {Y Z T : GeneratedByTopCat.{v} G} (f : Y ⊗ Z ⟶ T) (z : Z) (y : Y) :
    (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T)
      (curryHom f z)) y =
      f ((WithGeneratedByTopology.equiv (X := G) (Y := Y × Z)).symm (y, z)) := rfl

@[simp]
theorem uncurryHom_apply {Y Z T : GeneratedByTopCat.{v} G} (g : Z ⟶ (ihomFunctor Y).obj T)
    (p : ↑(Y ⊗ Z)) :
    uncurryHom g p =
      (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T)
        (g (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z) p).2))
        (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z) p).1 := rfl

/-- Currying equivalence `(Y ⊗ Z ⟶ T) ≃ (Z ⟶ (ihomFunctor Y).obj T)` in `GeneratedByTopCat G`. -/
@[expose, simps]
def curryEquiv (Y Z T : GeneratedByTopCat.{v} G) :
    (Y ⊗ Z ⟶ T) ≃ (Z ⟶ (ihomFunctor Y).obj T) where
  toFun := curryHom
  invFun := uncurryHom
  left_inv _ := by ext; rfl
  right_inv g := by
    ext z
    apply (WithGeneratedByTopology.equiv (X := G)
      (Y := ContinuousMapGeneratedBy G Y T)).injective
    ext y
    exact equiv_curryHom_apply (uncurryHom g) z y

/-- `Y ⊗ -` is left adjoint to `ihomFunctor Y` in `GeneratedByTopCat G`. -/
@[expose]
def tensorLeftAdjunction (Y : GeneratedByTopCat.{v} G) : tensorLeft Y ⊣ ihomFunctor Y :=
  Adjunction.mkOfHomEquiv
    { homEquiv := curryEquiv Y
      homEquiv_naturality_left_symm f g := by
        ext p
        change uncurryHom (f ≫ g) p = uncurryHom g ((tensorLeft Y).map f p)
        simp only [uncurryHom_apply]; rfl
      homEquiv_naturality_right {Z T T'} f g := by
        ext z
        apply (WithGeneratedByTopology.equiv (X := G)
          (Y := ContinuousMapGeneratedBy G Y T')).injective
        ext y
        change (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T')
          (curryHom (f ≫ g) z)) y =
          (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T')
            ((ihomFunctor Y).map g (curryHom f z))) y
        rw [equiv_curryHom_apply, ihomFunctor_map_apply, equiv_curryHom_apply]; rfl }

instance instMonoidalClosed : MonoidalClosed (GeneratedByTopCat.{v} G) where
  closed Y := { rightAdj := ihomFunctor Y, adj := tensorLeftAdjunction Y }

end Closed

end GeneratedByTopCat

end
