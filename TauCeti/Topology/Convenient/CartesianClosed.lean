/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
public import Mathlib.Topology.Category.TopCat.Monoidal
public import TauCeti.Topology.Convenient.Category
public import TauCeti.Topology.Convenient.GeneratedBy
public import TauCeti.Topology.Convenient.HomSpace

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
* The canonical product comparison `CartesianMonoidalCategory.prodComparison toTopCat Y Z` in
  `TopCat` is the generated-topology counit on `Y × Z`
  (`GeneratedByTopCat.prodComparison_toTopCat`), so `Y ⊗ Z ≃ₜ Y × Z` whenever `Y × Z` is
  `G`-generated (in particular whenever either factor is locally compact).
* When every compact subset of `Y` is a finite union of continuous images of compact subsets of
  generators `G i`, `(ihom Y).obj Z` is canonically isomorphic to the `G`-generated refinement of
  the compact-open mapping space `C(Y, Z)`
  (`GeneratedByTopCat.ihomIsoCompactOpenOfExistsIUnionIsCompactImageEq`).

## References

* M. Escardó, J. Lawson, and A. Simpson, *Comparing Cartesian closed categories of (core)
  compactly generated spaces*, Topology Appl. 143 (2004), 105–145.
* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Arch. Math.
  (Basel) 22 (1971), 545–555.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Topology

universe w v t u

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

instance instFunLikeIhomFunctor (Y Z : ContinuousGeneratedByCat.{v} G) :
    FunLike ↑((ihomFunctor Y).obj Z) Y Z :=
  inferInstanceAs (FunLike (ContinuousMapGeneratedBy G Y Z) Y Z)

/-- Currying equivalence `(Y ⊗ Z ⟶ T) ≃ (Z ⟶ (ihomFunctor Y).obj T)` in
`ContinuousGeneratedByCat G`. -/
def curryEquiv (Y Z T : ContinuousGeneratedByCat.{v} G) :
    (Y ⊗ Z ⟶ T) ≃ (Z ⟶ (ihomFunctor Y).obj T) where
  toFun f := ConcreteCategory.ofHom (ContinuousMapGeneratedBy.curryEquiv f.hom)
  invFun g := ConcreteCategory.ofHom (ContinuousMapGeneratedBy.curryEquiv.symm g.hom)
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

@[simp]
theorem curryEquiv_apply_apply {Y Z T : ContinuousGeneratedByCat.{v} G} (f : Y ⊗ Z ⟶ T)
    (z : Z) (y : Y) : (curryEquiv Y Z T f z) y = f (y, z) := (rfl)

@[simp]
theorem curryEquiv_symm_apply {Y Z T : ContinuousGeneratedByCat.{v} G}
    (g : Z ⟶ (ihomFunctor Y).obj T) (p : ↑(Y ⊗ Z)) :
    (curryEquiv Y Z T).symm g p = g p.2 p.1 := (rfl)

/-- `Y ⊗ -` is left adjoint to `ihomFunctor Y` in `ContinuousGeneratedByCat G`. -/
def tensorLeftAdjunction (Y : ContinuousGeneratedByCat.{v} G) : tensorLeft Y ⊣ ihomFunctor Y :=
  Adjunction.mkOfHomEquiv
    { homEquiv := curryEquiv Y
      homEquiv_naturality_left_symm _ _ := by ext ⟨_, _⟩; rfl
      homEquiv_naturality_right _ _ := by ext; rfl }

instance instMonoidalClosed : MonoidalClosed (ContinuousGeneratedByCat.{v} G) where
  closed Y := { rightAdj := ihomFunctor Y, adj := tensorLeftAdjunction Y }

instance instFunLikeIhom (Y Z : ContinuousGeneratedByCat.{v} G) :
    FunLike ↑((ihom Y).obj Z) Y Z :=
  inferInstanceAs (FunLike (ContinuousMapGeneratedBy G Y Z) Y Z)

/-- The hom-set bijection of the internal-hom adjunction on `ContinuousGeneratedByCat G` is
`curryEquiv`. -/
theorem ihom_adjunction_homEquiv (Y Z T : ContinuousGeneratedByCat.{v} G) :
    (ihom.adjunction Y).homEquiv Z T = curryEquiv Y Z T :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _

@[simp]
theorem curry_apply {Y Z T : ContinuousGeneratedByCat.{v} G} (f : Y ⊗ Z ⟶ T) (z : Z) (y : Y) :
    (MonoidalClosed.curry f z) y = f (y, z) := by
  rw [← MonoidalClosed.homEquiv_apply_eq, ihom_adjunction_homEquiv]
  exact curryEquiv_apply_apply f z y

@[simp]
theorem uncurry_apply {Y Z T : ContinuousGeneratedByCat.{v} G} (g : Z ⟶ (ihom Y).obj T)
    (p : ↑(Y ⊗ Z)) : MonoidalClosed.uncurry g p = g p.2 p.1 := by
  rw [← MonoidalClosed.homEquiv_symm_apply_eq, ihom_adjunction_homEquiv]
  exact curryEquiv_symm_apply g p

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

instance : Subsingleton ↑(𝟙_ (GeneratedByTopCat.{v} G)) :=
  inferInstanceAs (Subsingleton PUnit.{v + 1})

instance (Y Z : GeneratedByTopCat.{v} G) [T2Space Y] [T2Space Z] : T2Space ↑(Y ⊗ Z) :=
  inferInstanceAs (T2Space (WithGeneratedByTopology G (Y × Z)))

instance (Y Z : GeneratedByTopCat.{v} G) [Small.{w} Y] [Small.{w} Z] : Small.{w} ↑(Y ⊗ Z) :=
  inferInstanceAs (Small.{w} (WithGeneratedByTopology G (Y × Z)))

@[simp]
theorem whiskerLeft_apply (X : GeneratedByTopCat.{v} G) {Y Z : GeneratedByTopCat.{v} G}
    (f : Y ⟶ Z) (p : ↑(X ⊗ Y)) :
    (X ◁ f) p = (WithGeneratedByTopology.equiv (X := G) (Y := X × Z)).symm
      ((WithGeneratedByTopology.equiv (X := G) (Y := X × Y) p).1,
        f (WithGeneratedByTopology.equiv (X := G) (Y := X × Y) p).2) := rfl

@[simp]
theorem whiskerRight_apply {Y Z : GeneratedByTopCat.{v} G} (f : Y ⟶ Z)
    (X : GeneratedByTopCat.{v} G) (p : ↑(Y ⊗ X)) :
    (f ▷ X) p = (WithGeneratedByTopology.equiv (X := G) (Y := Z × X)).symm
      (f (WithGeneratedByTopology.equiv (X := G) (Y := Y × X) p).1,
        (WithGeneratedByTopology.equiv (X := G) (Y := Y × X) p).2) := rfl

@[simp]
theorem tensorHom_apply {W₁ W₂ Y₁ Y₂ : GeneratedByTopCat.{v} G}
    (f : W₁ ⟶ W₂) (g : Y₁ ⟶ Y₂) (p : ↑(W₁ ⊗ Y₁)) :
    (f ⊗ₘ g) p = (WithGeneratedByTopology.equiv (X := G) (Y := W₂ × Y₂)).symm
      (f (WithGeneratedByTopology.equiv (X := G) (Y := W₁ × Y₁) p).1,
        g (WithGeneratedByTopology.equiv (X := G) (Y := W₁ × Y₁) p).2) := rfl

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

@[simp]
theorem braiding_hom_apply (Y Z : GeneratedByTopCat.{v} G) (p : ↑(Y ⊗ Z)) :
    (β_ Y Z).hom p = (WithGeneratedByTopology.equiv (X := G) (Y := Z × Y)).symm
      ((WithGeneratedByTopology.equiv (X := G) (Y := Y × Z) p).2,
        (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z) p).1) := rfl

@[simp]
theorem braiding_inv_apply (Y Z : GeneratedByTopCat.{v} G) (p : ↑(Z ⊗ Y)) :
    (β_ Y Z).inv p = (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z)).symm
      ((WithGeneratedByTopology.equiv (X := G) (Y := Z × Y) p).2,
        (WithGeneratedByTopology.equiv (X := G) (Y := Z × Y) p).1) := rfl

@[simp]
theorem leftUnitor_hom_apply (Y : GeneratedByTopCat.{v} G)
    (p : ↑(𝟙_ (GeneratedByTopCat.{v} G) ⊗ Y)) :
    (λ_ Y).hom p = (WithGeneratedByTopology.equiv (X := G) (Y := PUnit × Y) p).2 := rfl

@[simp]
theorem leftUnitor_inv_apply (Y : GeneratedByTopCat.{v} G) (y : Y) :
    (λ_ Y).inv y =
      (WithGeneratedByTopology.equiv (X := G) (Y := PUnit × Y)).symm (PUnit.unit, y) := rfl

@[simp]
theorem rightUnitor_hom_apply (Y : GeneratedByTopCat.{v} G)
    (p : ↑(Y ⊗ 𝟙_ (GeneratedByTopCat.{v} G))) :
    (ρ_ Y).hom p = (WithGeneratedByTopology.equiv (X := G) (Y := Y × PUnit) p).1 := rfl

@[simp]
theorem rightUnitor_inv_apply (Y : GeneratedByTopCat.{v} G) (y : Y) :
    (ρ_ Y).inv y =
      (WithGeneratedByTopology.equiv (X := G) (Y := Y × PUnit)).symm (y, PUnit.unit) := rfl

section ProdComparison

variable (Y Z : GeneratedByTopCat.{v} G)

/-- The canonical product comparison `toTopCat.obj (Y ⊗ Z) ⟶ toTopCat.obj Y ⊗ toTopCat.obj Z` in
`TopCat` is the generated-topology counit on `Y × Z`. -/
theorem prodComparison_toTopCat :
    CartesianMonoidalCategory.prodComparison toTopCat Y Z =
      (adjCounit (X := G)).app (Y.obj ⊗ Z.obj) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [CartesianMonoidalCategory.prodComparison_fst]; ext p; rfl
  · rw [CartesianMonoidalCategory.prodComparison_snd]; ext p; rfl

@[simp]
theorem prodComparison_toTopCat_apply (p : ↑(Y ⊗ Z)) :
    ConcreteCategory.hom (X := (Y ⊗ Z).obj) (Y := Y.obj ⊗ Z.obj)
      (CartesianMonoidalCategory.prodComparison toTopCat Y Z) p =
      WithGeneratedByTopology.equiv (X := G) (Y := Y × Z) p := by
  rw [prodComparison_toTopCat]; rfl

/-- The convenient product `Y ⊗ Z` has the ordinary product topology if and only if `Y × Z` is
`G`-generated. -/
theorem isIso_prodComparison_toTopCat_iff :
    IsIso (CartesianMonoidalCategory.prodComparison toTopCat Y Z) ↔ IsGeneratedBy G (Y × Z) := by
  rw [prodComparison_toTopCat]; exact isIso_adjCounit_app_iff G (Y.obj ⊗ Z.obj)

/-- When `Y × Z` is `G`-generated, the product comparison in `TopCat` is an isomorphism. -/
instance instIsIsoProdComparisonToTopCat [IsGeneratedBy G (Y × Z)] :
    IsIso (CartesianMonoidalCategory.prodComparison toTopCat Y Z) :=
  (isIso_prodComparison_toTopCat_iff Y Z).2 inferInstance

/-- When `Y × Z` is `G`-generated, the convenient product `Y ⊗ Z` is homeomorphic to the ordinary
product `Y × Z` via `WithGeneratedByTopology.equiv`. -/
@[expose]
def tensorHomeomorphProd [IsGeneratedBy G (Y × Z)] : ↑(Y ⊗ Z) ≃ₜ Y × Z :=
  IsGeneratedBy.homeomorph (X := G) (Y := Y × Z)

@[simp]
theorem coe_tensorHomeomorphProd [IsGeneratedBy G (Y × Z)] :
    ⇑(tensorHomeomorphProd Y Z) = WithGeneratedByTopology.equiv (X := G) (Y := Y × Z) := rfl

@[simp]
theorem coe_tensorHomeomorphProd_symm [IsGeneratedBy G (Y × Z)] :
    ⇑(tensorHomeomorphProd Y Z).symm =
      (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z)).symm := rfl

end ProdComparison

section Closed

variable [∀ i, LocallyCompactSpace (G i)] [∀ i j, IsGeneratedBy G (G i × G j)]

section LocallyCompact

variable (Y Z : GeneratedByTopCat.{v} G)

/-- When all test spaces `G i` are locally compact, their pairwise products are `G`-generated, and
`Z` is locally compact, the product comparison in `TopCat` is an isomorphism. -/
instance instIsIsoProdComparisonToTopCatOfLocallyCompactRight [LocallyCompactSpace Z] :
    IsIso (CartesianMonoidalCategory.prodComparison toTopCat Y Z) := by
  have := IsGeneratedBy.prod_of_locallyCompactSpace_right (G := G) Y Z; infer_instance

/-- When all test spaces `G i` are locally compact, their pairwise products are `G`-generated, and
`Y` is locally compact, the product comparison in `TopCat` is an isomorphism. -/
instance instIsIsoProdComparisonToTopCatOfLocallyCompactLeft [LocallyCompactSpace Y] :
    IsIso (CartesianMonoidalCategory.prodComparison toTopCat Y Z) := by
  have := IsGeneratedBy.prod_of_locallyCompactSpace_left (G := G) Y Z; infer_instance

/-- When all test spaces `G i` are locally compact, their pairwise products are `G`-generated, and
`Z` is locally compact, the convenient product `Y ⊗ Z` is homeomorphic to the ordinary product
`Y × Z` via `WithGeneratedByTopology.equiv`. -/
@[expose]
def tensorHomeomorphProdOfLocallyCompactRight [LocallyCompactSpace Z] : ↑(Y ⊗ Z) ≃ₜ Y × Z :=
  have := IsGeneratedBy.prod_of_locallyCompactSpace_right (G := G) Y Z
  tensorHomeomorphProd Y Z

@[simp]
theorem coe_tensorHomeomorphProdOfLocallyCompactRight [LocallyCompactSpace Z] :
    ⇑(tensorHomeomorphProdOfLocallyCompactRight Y Z) =
      WithGeneratedByTopology.equiv (X := G) (Y := Y × Z) := rfl

@[simp]
theorem coe_tensorHomeomorphProdOfLocallyCompactRight_symm [LocallyCompactSpace Z] :
    ⇑(tensorHomeomorphProdOfLocallyCompactRight Y Z).symm =
      (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z)).symm := rfl

/-- When all test spaces `G i` are locally compact, their pairwise products are `G`-generated, and
`Y` is locally compact, the convenient product `Y ⊗ Z` is homeomorphic to the ordinary product
`Y × Z` via `WithGeneratedByTopology.equiv`. -/
@[expose]
def tensorHomeomorphProdOfLocallyCompactLeft [LocallyCompactSpace Y] : ↑(Y ⊗ Z) ≃ₜ Y × Z :=
  have := IsGeneratedBy.prod_of_locallyCompactSpace_left (G := G) Y Z
  tensorHomeomorphProd Y Z

@[simp]
theorem coe_tensorHomeomorphProdOfLocallyCompactLeft [LocallyCompactSpace Y] :
    ⇑(tensorHomeomorphProdOfLocallyCompactLeft Y Z) =
      WithGeneratedByTopology.equiv (X := G) (Y := Y × Z) := rfl

@[simp]
theorem coe_tensorHomeomorphProdOfLocallyCompactLeft_symm [LocallyCompactSpace Y] :
    ⇑(tensorHomeomorphProdOfLocallyCompactLeft Y Z).symm =
      (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z)).symm := rfl

end LocallyCompact

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
      f ((WithGeneratedByTopology.equiv (X := G) (Y := Y × Z)).symm (y, z)) := (rfl)

@[simp]
theorem uncurryHom_apply {Y Z T : GeneratedByTopCat.{v} G} (g : Z ⟶ (ihomFunctor Y).obj T)
    (p : ↑(Y ⊗ Z)) :
    uncurryHom g p =
      (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T)
        (g (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z) p).2))
        (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z) p).1 := (rfl)

/-- Currying equivalence `(Y ⊗ Z ⟶ T) ≃ (Z ⟶ (ihomFunctor Y).obj T)` in `GeneratedByTopCat G`. -/
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

@[simp]
theorem curryEquiv_apply {Y Z T : GeneratedByTopCat.{v} G} (f : Y ⊗ Z ⟶ T) :
    curryEquiv Y Z T f = curryHom f := (rfl)

@[simp]
theorem curryEquiv_symm_apply {Y Z T : GeneratedByTopCat.{v} G}
    (g : Z ⟶ (ihomFunctor Y).obj T) :
    (curryEquiv Y Z T).symm g = uncurryHom g := (rfl)

/-- Naturality of `curryEquiv.symm` in the source: precomposing with `f` corresponds to
precomposing with `Y ◁ f`. -/
theorem curryEquiv_symm_comp {Y Z' Z T : GeneratedByTopCat.{v} G} (f : Z' ⟶ Z)
    (g : Z ⟶ (ihomFunctor Y).obj T) :
    (curryEquiv Y Z' T).symm (f ≫ g) = Y ◁ f ≫ (curryEquiv Y Z T).symm g := by
  refine ConcreteCategory.hom_ext _ _ fun p ↦ ?_
  let q : ↑(Y ⊗ Z) := (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z)).symm
    ((WithGeneratedByTopology.equiv (X := G) (Y := Y × Z') p).1,
      f (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z') p).2)
  calc
    (curryEquiv Y Z' T).symm (f ≫ g) p
      = (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T)
          (g (f (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z') p).2)))
          (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z') p).1 := by
        rw [curryEquiv_symm_apply, uncurryHom_apply, CategoryTheory.comp_apply]
    _ = (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T)
          (g (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z) q).2))
          (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z) q).1 := by
        rw [Equiv.apply_symm_apply]
    _ = uncurryHom g q := (uncurryHom_apply g q).symm
    _ = (Y ◁ f ≫ (curryEquiv Y Z T).symm g) p := by
        rw [CategoryTheory.comp_apply, curryEquiv_symm_apply, whiskerLeft_apply]

/-- Naturality of `curryEquiv` in the target: postcomposing with `g` corresponds to postcomposing
with `(ihomFunctor Y).map g`. -/
theorem curryEquiv_comp {Y Z T T' : GeneratedByTopCat.{v} G} (f : Y ⊗ Z ⟶ T) (g : T ⟶ T') :
    curryEquiv Y Z T' (f ≫ g) = curryEquiv Y Z T f ≫ (ihomFunctor Y).map g := by
  refine ConcreteCategory.hom_ext _ _ fun z ↦ ?_
  apply (WithGeneratedByTopology.equiv (X := G)
    (Y := ContinuousMapGeneratedBy G Y T')).injective
  refine DFunLike.ext _ _ fun y ↦ ?_
  let p : ↑(Y ⊗ Z) := (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z)).symm (y, z)
  calc
    (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T')
        (curryEquiv Y Z T' (f ≫ g) z)) y
      = (f ≫ g) p := by rw [curryEquiv_apply, equiv_curryHom_apply]
    _ = g (f p) := CategoryTheory.comp_apply f g p
    _ = (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T')
          ((curryEquiv Y Z T f ≫ (ihomFunctor Y).map g) z)) y := by
        rw [CategoryTheory.comp_apply, ihomFunctor_map_apply, curryEquiv_apply,
          equiv_curryHom_apply]

/-- `Y ⊗ -` is left adjoint to `ihomFunctor Y` in `GeneratedByTopCat G`. -/
def tensorLeftAdjunction (Y : GeneratedByTopCat.{v} G) : tensorLeft Y ⊣ ihomFunctor Y :=
  Adjunction.mkOfHomEquiv
    { homEquiv := curryEquiv Y
      homEquiv_naturality_left_symm := curryEquiv_symm_comp
      homEquiv_naturality_right := curryEquiv_comp }

instance instMonoidalClosed : MonoidalClosed (GeneratedByTopCat.{v} G) where
  closed Y := { rightAdj := ihomFunctor Y, adj := tensorLeftAdjunction Y }

/-- The hom-set bijection of the internal-hom adjunction on `GeneratedByTopCat G` is
`curryEquiv`. -/
theorem ihom_adjunction_homEquiv (Y Z T : GeneratedByTopCat.{v} G) :
    (ihom.adjunction Y).homEquiv Z T = curryEquiv Y Z T :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _

@[simp]
theorem equiv_curry_apply {Y Z T : GeneratedByTopCat.{v} G} (f : Y ⊗ Z ⟶ T) (z : Z) (y : Y) :
    (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T)
      (MonoidalClosed.curry f z)) y =
      f ((WithGeneratedByTopology.equiv (X := G) (Y := Y × Z)).symm (y, z)) := by
  rw [← MonoidalClosed.homEquiv_apply_eq, ihom_adjunction_homEquiv]
  exact equiv_curryHom_apply f z y

@[simp]
theorem uncurry_apply {Y Z T : GeneratedByTopCat.{v} G} (g : Z ⟶ (ihom Y).obj T)
    (p : ↑(Y ⊗ Z)) :
    MonoidalClosed.uncurry g p =
      (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T)
        (g (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z) p).2))
        (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z) p).1 := by
  rw [← MonoidalClosed.homEquiv_symm_apply_eq, ihom_adjunction_homEquiv]
  exact uncurryHom_apply g p

/-- Evaluation in `GeneratedByTopCat G` applies the underlying `G`-continuous map to a point. -/
@[simp]
theorem ihom_ev_app_apply (Y Z : GeneratedByTopCat.{v} G) (p : ↑(Y ⊗ (ihom Y).obj Z)) :
    ConcreteCategory.hom (X := Y ⊗ (ihom Y).obj Z) (Y := Z) ((ihom.ev Y).app Z) p =
      (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y Z)
        (WithGeneratedByTopology.equiv (X := G) (Y := Y × _) p).2)
        (WithGeneratedByTopology.equiv (X := G) (Y := Y × _) p).1 := by
  rw [← MonoidalClosed.uncurry_id_eq_ev, uncurry_apply]; rfl

/-- Coevaluation in `GeneratedByTopCat G` sends `z` to the slice map `y ↦ (y, z)`. -/
@[simp]
theorem equiv_ihom_coev_app_apply (Y Z : GeneratedByTopCat.{v} G) (z : Z) (y : Y) :
    (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y ↑(Y ⊗ Z))
      (ConcreteCategory.hom (X := Z) (Y := (ihom Y).obj (Y ⊗ Z))
        ((ihom.coev Y).app Z) z)) y =
      (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z)).symm (y, z) := by
  rw [← MonoidalClosed.curry_id_eq_coev, equiv_curry_apply]; rfl

@[simp]
theorem equiv_pre_app_apply {W Y : GeneratedByTopCat.{v} G} (f : W ⟶ Y)
    (Z : GeneratedByTopCat.{v} G) (g : ↑((ihom Y).obj Z)) (w : W) :
    (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G W Z)
      (((MonoidalClosed.pre f).app Z) g)) w =
      (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y Z) g) (f w) := by
  let wg : ↑(W ⊗ (ihom Y).obj Z) :=
    (WithGeneratedByTopology.equiv (X := G) (Y := W × _)).symm (w, g)
  let fwg : ↑(Y ⊗ (ihom Y).obj Z) :=
    (WithGeneratedByTopology.equiv (X := G) (Y := Y × _)).symm (f w, g)
  have h := congrArg (fun φ : W ⊗ (ihom Y).obj Z ⟶ Z ↦ φ wg)
    (MonoidalClosed.uncurry_pre f Z)
  rw [uncurry_apply, CategoryTheory.comp_apply, whiskerRight_apply] at h
  have hev := ihom_ev_app_apply Y Z fwg
  simp only [wg, fwg, Equiv.apply_symm_apply] at h hev
  exact h.trans hev

/-- Canonical morphism from the `G`-generated refinement of the compact-open mapping space
`C(Y, Z)` into the internal hom `(ihom Y).obj Z`. -/
@[expose]
def compactOpenToIhom (Y Z : GeneratedByTopCat.{v} G) :
    of (X := G) (WithGeneratedByTopology G C(Y, Z)) ⟶ (ihom Y).obj Z :=
  (TopCat.toGeneratedByTopCat (X := G)).map <| TopCat.ofHom
    ⟨ContinuousMap.toContinuousMapGeneratedBy G,
      ContinuousMap.continuous_toContinuousMapGeneratedBy⟩

@[simp]
theorem equiv_compactOpenToIhom_apply (Y Z : GeneratedByTopCat.{v} G)
    (f : WithGeneratedByTopology G C(Y, Z)) (y : Y) :
    (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y Z)
      (compactOpenToIhom Y Z f)) y =
      WithGeneratedByTopology.equiv (X := G) (Y := C(Y, Z)) f y := by
  have h := congrArg (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y Z))
    (TopCat.toGeneratedByTopCat_map_apply (G := G)
      (TopCat.ofHom ⟨ContinuousMap.toContinuousMapGeneratedBy G,
        ContinuousMap.continuous_toContinuousMapGeneratedBy⟩) f)
  rw [Equiv.apply_symm_apply] at h
  exact congrArg (fun k : ContinuousMapGeneratedBy G Y Z ↦ k y) h

section CompactOpen

variable {Y : GeneratedByTopCat.{v} G}
  (hK : ∀ ⦃K : Set Y⦄, IsCompact K →
    ∃ (m : ℕ) (i : Fin m → ι) (L : ∀ j, Set (G (i j))) (p : ∀ j, C(G (i j), Y)),
      (∀ j, IsCompact (L j)) ∧ ⋃ j, p j '' L j = K)

include hK

/-- When every compact subset of `Y` is a finite union of images of compact subsets of generators
`G i` under continuous maps, the internal hom `(ihom Y).obj Z` is canonically isomorphic to the
`G`-generated refinement of the compact-open mapping space `C(Y, Z)`. -/
@[expose]
def ihomIsoCompactOpenOfExistsIUnionIsCompactImageEq (Z : GeneratedByTopCat.{v} G) :
    (ihom Y).obj Z ≅ of (X := G) (WithGeneratedByTopology G C(Y, Z)) :=
  (TopCat.toGeneratedByTopCat (X := G)).mapIso <|
    TopCat.isoOfHomeo
      (X := TopCat.of (ContinuousMapGeneratedBy G Y Z)) (Y := TopCat.of C(Y, Z)) <|
      ContinuousMapGeneratedBy.homeomorphContinuousMapOfExistsIUnionIsCompactImageEq
        (G := G) (Z := Z) hK

@[simp]
theorem ihomIsoCompactOpenOfExistsIUnionIsCompactImageEq_inv (Z : GeneratedByTopCat.{v} G) :
    (ihomIsoCompactOpenOfExistsIUnionIsCompactImageEq hK Z).inv = compactOpenToIhom Y Z := by
  refine GeneratedByTopCat.hom_ext fun f ↦ ?_
  apply (WithGeneratedByTopology.equiv (X := G)
    (Y := ContinuousMapGeneratedBy G Y Z)).injective
  refine DFunLike.ext _ _ fun y ↦ ?_
  rw [equiv_compactOpenToIhom_apply]
  exact congrArg (fun k : ContinuousMapGeneratedBy G Y Z ↦ k y)
    (Equiv.apply_symm_apply (WithGeneratedByTopology.equiv (X := G)
      (Y := ContinuousMapGeneratedBy G Y Z)) _)

@[simp]
theorem equiv_ihomIsoCompactOpenOfExistsIUnionIsCompactImageEq_hom_apply
    (Z : GeneratedByTopCat.{v} G) (f : ↑((ihom Y).obj Z)) (y : Y) :
    WithGeneratedByTopology.equiv (X := G) (Y := C(Y, Z))
      ((ihomIsoCompactOpenOfExistsIUnionIsCompactImageEq hK Z).hom f) y =
      (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y Z) f) y := by
  let g₀ : WithGeneratedByTopology G C(Y, Z) :=
    (WithGeneratedByTopology.equiv (X := G) (Y := C(Y, Z))).symm
      (WithGeneratedByTopology.equiv (X := G)
        (Y := ContinuousMapGeneratedBy G Y Z) f).toContinuousMap
  have hinv : (ihomIsoCompactOpenOfExistsIUnionIsCompactImageEq hK Z).inv g₀ = f := by
    rw [ihomIsoCompactOpenOfExistsIUnionIsCompactImageEq_inv]
    apply (WithGeneratedByTopology.equiv (X := G)
      (Y := ContinuousMapGeneratedBy G Y Z)).injective
    refine DFunLike.ext _ _ fun y' ↦ ?_
    rw [equiv_compactOpenToIhom_apply]
    simp [g₀]
  have hhom := (ihomIsoCompactOpenOfExistsIUnionIsCompactImageEq hK Z).inv_hom_id_apply g₀
  rw [hinv] at hhom
  simp only [hhom, g₀, Equiv.apply_symm_apply,
    Topology.ContinuousMapGeneratedBy.toContinuousMap_apply]

end CompactOpen

end Closed

end GeneratedByTopCat

end
