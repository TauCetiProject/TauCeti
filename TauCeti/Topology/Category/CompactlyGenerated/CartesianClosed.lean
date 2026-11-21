/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
public import Mathlib.Topology.Category.TopCat.Monoidal
public import TauCeti.Topology.Category.CompactlyGenerated.Coreflection
public import TauCeti.Topology.Category.TopCat.MappingSpace
import TauCeti.CategoryTheory.Monoidal.Closed.Unit

/-!
# Convenient products and Cartesian closed structure on `CompactlyGenerated`

Passing from `TopCat` to `CompactlyGenerated.{u, w}` and forming binary products via
`TopCat.toCompactlyGenerated` yields a Cartesian closed category for every test universe `u` and
object universe `w`.

## Main declarations

* `CompactlyGenerated.isInitialPEmpty`, `CompactlyGenerated.isTerminalPUnit`,
  `CompactlyGenerated.prodBinaryFanIsLimit`: initial object (`PEmpty`) and chosen finite products
  giving `CartesianMonoidalCategory` and `BraidedCategory` with binary product carrier `k(X × Y)`.
* `CompactlyGenerated.prodComparison_compactlyGeneratedToTop`,
  `CompactlyGenerated.isIso_prodComparison_compactlyGeneratedToTop_iff`,
  `CompactlyGenerated.tensorHomeomorphProd`,
  `CompactlyGenerated.tensorHomeomorphProdOfLocallyCompactRight`,
  `CompactlyGenerated.tensorHomeomorphProdOfLocallyCompactLeft`,
  `CompactlyGenerated.tensorRightLocallyCompactHomeomorph`,
  `CompactlyGenerated.tensorLeftLocallyCompactHomeomorph`,
  `CompactlyGenerated.toCompactlyGeneratedProdRightIso`,
  `CompactlyGenerated.toCompactlyGeneratedProdLeftIso`: the product comparison in `TopCat` is the
  coreflection counit on `X × Y`, so `X ⊗ Y ≃ₜ X × Y` whenever `X × Y` is `u`-compactly generated
  (in particular whenever either factor is locally compact, with no separation or smallness needed
  on the factors; for `u`-small locally compact Hausdorff `L`, `Y ⊗ of L ≃ₜ Y × L` and
  `k(X × L) ≅ kX ⊗ of L`).
* `CompactlyGenerated.ihomFunctor`, `CompactlyGenerated.curryEquiv`,
  `CompactlyGenerated.tensorLeftAdjunction`: the `MonoidalClosed` structure on
  `CompactlyGenerated.{u, w}` with internal hom `k(ContinuousMapGeneratedBy CompHaus.{u} Y Z)`.
* `CompactlyGenerated.compactOpenToIhom`,
  `CompactlyGenerated.ihomHomeomorphToCompactlyGeneratedContinuousMap`,
  `CompactlyGenerated.ihomIsoToCompactlyGeneratedMappingSpace`,
  `CompactlyGenerated.toCompactlyGeneratedMappingSpaceCurryIso`,
  `CompactlyGenerated.toCompactlyGeneratedMappingSpaceCurryHomeomorph`,
  `CompactlyGenerated.ihomULiftBoolIso`, `CompactlyGenerated.ihomULiftBoolHomeomorph`: compact-open
  comparisons, exponential law `k(C(X ⊗ Y, Z)) ≃ₜ k(C(X, k(C(Y, Z))))`, and
  `(ihom S⁰).obj Z ≅ Z ⊗ Z`.

## References

* N. E. Steenrod, *A convenient category of topological spaces*, Michigan Math. J. 14 (1967),
  133–152.
* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Arch. Math.
  (Basel) 22 (1971), 545–555.
* M. Escardó, J. Lawson, and A. Simpson, *Comparing Cartesian closed categories of (core)
  compactly generated spaces*, Topology Appl. 143 (2004), 105–145.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Appendix
  (compactly generated spaces and the compact-open topology).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Topology

universe u w v₁

namespace CompactlyGenerated

/-! ### Chosen finite products and Cartesian monoidal structure -/

/-- `PEmpty` is initial in `CompactlyGenerated.{u, w}`. -/
@[expose]
def isInitialPEmpty : IsInitial (of PEmpty.{w + 1} : CompactlyGenerated.{u, w}) :=
  have : ∀ X : CompactlyGenerated.{u, w},
      Unique ((of PEmpty.{w + 1} : CompactlyGenerated.{u, w}) ⟶ X) :=
    fun _ ↦ ⟨⟨ofHom ⟨PEmpty.elim, continuous_of_discreteTopology⟩⟩, fun _ ↦ by ext ⟨⟩⟩
  IsInitial.ofUnique _

/-- `PUnit` is terminal in `CompactlyGenerated.{u, w}`. -/
@[expose]
def isTerminalPUnit : IsTerminal (of PUnit.{w + 1} : CompactlyGenerated.{u, w}) :=
  have : ∀ X : CompactlyGenerated.{u, w},
      Unique (X ⟶ (of PUnit.{w + 1} : CompactlyGenerated.{u, w})) :=
    fun _ ↦ ⟨⟨InducedCategory.homMk (TopCat.ofHom ⟨fun _ ↦ PUnit.unit, continuous_const⟩)⟩,
      fun _ ↦ by ext⟩
  IsTerminal.ofUnique _

/-- First projection from the convenient product `k(X × Y)`. -/
@[expose]
def prodFst (X Y : CompactlyGenerated.{u, w}) :
    TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of (X × Y)) ⟶ X :=
  InducedCategory.homMk (adj.{u, w}.counit.app (TopCat.of (X × Y)) ≫ TopCat.ofHom ContinuousMap.fst)

/-- Second projection from the convenient product `k(X × Y)`. -/
@[expose]
def prodSnd (X Y : CompactlyGenerated.{u, w}) :
    TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of (X × Y)) ⟶ Y :=
  InducedCategory.homMk (adj.{u, w}.counit.app (TopCat.of (X × Y)) ≫ TopCat.ofHom ContinuousMap.snd)

@[simp]
theorem prodFst_apply (X Y : CompactlyGenerated.{u, w})
    (p : TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of (X × Y))) : prodFst X Y p = p.1 := rfl

@[simp]
theorem prodSnd_apply (X Y : CompactlyGenerated.{u, w})
    (p : TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of (X × Y))) : prodSnd X Y p = p.2 := rfl

/-- Explicit binary product fan in `CompactlyGenerated.{u, w}`, with carrier `k(X × Y)`. -/
@[expose]
def prodBinaryFan (X Y : CompactlyGenerated.{u, w}) : BinaryFan X Y :=
  BinaryFan.mk (prodFst X Y) (prodSnd X Y)

/-- `k(X × Y)` is a categorical binary product in `CompactlyGenerated.{u, w}`. -/
@[expose]
def prodBinaryFanIsLimit (X Y : CompactlyGenerated.{u, w}) : IsLimit (prodBinaryFan X Y) where
  lift := fun S : BinaryFan X Y ↦ adj.{u, w}.homEquiv S.pt (TopCat.of (X × Y))
    (TopCat.ofHom (S.fst.hom.hom.prodMk S.snd.hom.hom))
  fac := by rintro S (_ | _) <;> rfl
  uniq S m hm := ConcreteCategory.hom_ext _ _ fun s ↦ Prod.ext
    (ConcreteCategory.congr_hom (hm ⟨WalkingPair.left⟩) s)
    (ConcreteCategory.congr_hom (hm ⟨WalkingPair.right⟩) s)

instance instCartesianMonoidalCategory : CartesianMonoidalCategory CompactlyGenerated.{u, w} :=
  .ofChosenFiniteProducts ⟨_, isTerminalPUnit⟩
    fun X Y ↦ ⟨prodBinaryFan X Y, prodBinaryFanIsLimit X Y⟩

instance instBraidedCategory : BraidedCategory CompactlyGenerated.{u, w} :=
  .ofCartesianMonoidalCategory

instance : Subsingleton ↑(𝟙_ CompactlyGenerated.{u, w}) :=
  inferInstanceAs (Subsingleton PUnit.{w + 1})
instance (X Y : CompactlyGenerated.{u, w}) [T2Space X] [T2Space Y] : T2Space ↑(X ⊗ Y) :=
  inferInstanceAs (T2Space (TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of (X × Y))))

instance (X Y : CompactlyGenerated.{u, w}) [Small.{v₁} X] [Small.{v₁} Y] : Small.{v₁} ↑(X ⊗ Y) :=
  inferInstanceAs (Small.{v₁} (TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of (X × Y))))

@[simp]
theorem tensor_apply {W X Y Z : CompactlyGenerated.{u, w}} (f : W ⟶ X) (g : Y ⟶ Z)
    (p : ↑(W ⊗ Y)) : (f ⊗ₘ g) p = (f p.1, g p.2) := rfl

@[simp]
theorem whiskerLeft_apply (X : CompactlyGenerated.{u, w}) {Y Z : CompactlyGenerated.{u, w}}
    (f : Y ⟶ Z) (p : ↑(X ⊗ Y)) : (X ◁ f) p = (p.1, f p.2) := rfl

@[simp]
theorem whiskerRight_apply {Y Z : CompactlyGenerated.{u, w}} (f : Y ⟶ Z)
    (X : CompactlyGenerated.{u, w}) (p : ↑(Y ⊗ X)) : (f ▷ X) p = (f p.1, p.2) := rfl

@[simp]
theorem fst_apply (X Y : CompactlyGenerated.{u, w}) (p : ↑(X ⊗ Y)) :
    CartesianMonoidalCategory.fst X Y p = p.1 := rfl

@[simp]
theorem snd_apply (X Y : CompactlyGenerated.{u, w}) (p : ↑(X ⊗ Y)) :
    CartesianMonoidalCategory.snd X Y p = p.2 := rfl

@[simp]
protected theorem lift_apply {X Y Z : CompactlyGenerated.{u, w}} (f : X ⟶ Y) (g : X ⟶ Z) (x : X) :
    CartesianMonoidalCategory.lift f g x = (f x, g x) := rfl

@[simp]
theorem leftUnitor_hom_apply {X : CompactlyGenerated.{u, w}} (p : PUnit.{w + 1}) (x : X) :
    (λ_ X).hom (p, x) = x := rfl

@[simp]
theorem leftUnitor_inv_apply {X : CompactlyGenerated.{u, w}} (x : X) :
    (λ_ X).inv x = (PUnit.unit, x) := rfl

@[simp]
theorem rightUnitor_hom_apply {X : CompactlyGenerated.{u, w}} (x : X) (p : PUnit.{w + 1}) :
    (ρ_ X).hom (x, p) = x := rfl

@[simp]
theorem rightUnitor_inv_apply {X : CompactlyGenerated.{u, w}} (x : X) :
    (ρ_ X).inv x = (x, PUnit.unit) := rfl

@[simp]
theorem associator_hom_apply {X Y Z : CompactlyGenerated.{u, w}} (x : X) (y : Y) (z : Z) :
    (α_ X Y Z).hom ((x, y), z) = (x, (y, z)) := rfl

@[simp]
theorem associator_inv_apply {X Y Z : CompactlyGenerated.{u, w}} (x : X) (y : Y) (z : Z) :
    (α_ X Y Z).inv (x, (y, z)) = ((x, y), z) := rfl

@[simp]
theorem braiding_hom_apply {X Y : CompactlyGenerated.{u, w}} (x : X) (y : Y) :
    (β_ X Y).hom (x, y) = (y, x) := rfl

@[simp]
theorem braiding_inv_apply {X Y : CompactlyGenerated.{u, w}} (x : X) (y : Y) :
    (β_ X Y).inv (y, x) = (x, y) := rfl

/-- When `L` is `u`-small, locally compact, and Hausdorff, the convenient product `Y ⊗ of L` in
`CompactlyGenerated.{u, w}` is homeomorphic to the ordinary product `Y × L` by the identity on
points. -/
@[expose]
def tensorRightLocallyCompactHomeomorph (Y : CompactlyGenerated.{u, w}) (L : Type w)
    [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L] [Small.{u} L] :
    ↑(Y ⊗ (of L : CompactlyGenerated.{u, w})) ≃ₜ Y × L :=
  have : UCompactlyGeneratedSpace.{u} (Y × L) := UCompactlyGeneratedSpace.prod_right
  counitHomeomorph.{u, w} (TopCat.of (Y × L))

@[simp]
theorem tensorRightLocallyCompactHomeomorph_apply (Y : CompactlyGenerated.{u, w}) (L : Type w)
    [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L] [Small.{u} L]
    (p : ↑(Y ⊗ (of L : CompactlyGenerated.{u, w}))) :
    tensorRightLocallyCompactHomeomorph Y L p = p := rfl

@[simp]
theorem tensorRightLocallyCompactHomeomorph_symm_apply (Y : CompactlyGenerated.{u, w}) (L : Type w)
    [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L] [Small.{u} L] (p : Y × L) :
    (tensorRightLocallyCompactHomeomorph Y L).symm p = p := rfl

/-- Symmetric version of `tensorRightLocallyCompactHomeomorph`: `of L ⊗ Y ≃ₜ L × Y`. -/
@[expose]
def tensorLeftLocallyCompactHomeomorph (L : Type w) (Y : CompactlyGenerated.{u, w})
    [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L] [Small.{u} L] :
    ↑((of L : CompactlyGenerated.{u, w}) ⊗ Y) ≃ₜ L × Y :=
  have : UCompactlyGeneratedSpace.{u} (L × Y) := UCompactlyGeneratedSpace.prod_left
  counitHomeomorph.{u, w} (TopCat.of (L × Y))

@[simp]
theorem tensorLeftLocallyCompactHomeomorph_apply (L : Type w) (Y : CompactlyGenerated.{u, w})
    [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L] [Small.{u} L]
    (p : ↑((of L : CompactlyGenerated.{u, w}) ⊗ Y)) :
    tensorLeftLocallyCompactHomeomorph L Y p = p := rfl

@[simp]
theorem tensorLeftLocallyCompactHomeomorph_symm_apply (L : Type w) (Y : CompactlyGenerated.{u, w})
    [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L] [Small.{u} L] (p : L × Y) :
    (tensorLeftLocallyCompactHomeomorph L Y).symm p = p := rfl

/-- Isomorphism `k(X × L) ≅ kX ⊗ of L` in `CompactlyGenerated.{u, w}` for any `X : TopCat.{w}` and
any `u`-small locally compact Hausdorff space `L`. -/
@[expose]
def toCompactlyGeneratedProdRightIso (X : TopCat.{w}) (L : Type w)
    [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L] [Small.{u} L] :
    TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of (X × L)) ≅
      TopCat.toCompactlyGenerated.{u, w}.obj X ⊗ (of L : CompactlyGenerated.{u, w}) :=
  isoOfHomeo <| (TopCat.toCompactlyGeneratedProdRightHomeomorph.{u} X L).trans
    (tensorRightLocallyCompactHomeomorph (TopCat.toCompactlyGenerated.{u, w}.obj X) L).symm

@[simp]
theorem toCompactlyGeneratedProdRightIso_hom_apply (X : TopCat.{w}) (L : Type w)
    [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L] [Small.{u} L]
    (p : TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of (X × L))) :
    (toCompactlyGeneratedProdRightIso X L).hom p = p := rfl

@[simp]
theorem toCompactlyGeneratedProdRightIso_inv_apply (X : TopCat.{w}) (L : Type w)
    [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L] [Small.{u} L]
    (p : ↑(TopCat.toCompactlyGenerated.{u, w}.obj X ⊗ (of L : CompactlyGenerated.{u, w}))) :
    (toCompactlyGeneratedProdRightIso X L).inv p = p := rfl

/-- Symmetric isomorphism `k(L × X) ≅ of L ⊗ kX` in `CompactlyGenerated.{u, w}`. -/
@[expose]
def toCompactlyGeneratedProdLeftIso (L : Type w) (X : TopCat.{w})
    [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L] [Small.{u} L] :
    TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of (L × X)) ≅
      (of L : CompactlyGenerated.{u, w}) ⊗ TopCat.toCompactlyGenerated.{u, w}.obj X :=
  isoOfHomeo <| (TopCat.toCompactlyGeneratedProdLeftHomeomorph.{u} L X).trans
    (tensorLeftLocallyCompactHomeomorph L (TopCat.toCompactlyGenerated.{u, w}.obj X)).symm

@[simp]
theorem toCompactlyGeneratedProdLeftIso_hom_apply (L : Type w) (X : TopCat.{w})
    [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L] [Small.{u} L]
    (p : TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of (L × X))) :
    (toCompactlyGeneratedProdLeftIso L X).hom p = p := rfl

@[simp]
theorem toCompactlyGeneratedProdLeftIso_inv_apply (L : Type w) (X : TopCat.{w})
    [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L] [Small.{u} L]
    (p : ↑((of L : CompactlyGenerated.{u, w}) ⊗ TopCat.toCompactlyGenerated.{u, w}.obj X)) :
    (toCompactlyGeneratedProdLeftIso L X).inv p = p := rfl

section ProdComparison

variable (X Y : CompactlyGenerated.{u, w})

/-- The canonical product comparison `(X ⊗ Y).toTop ⟶ X.toTop ⊗ Y.toTop` in `TopCat` is the
compact-generation counit on `X × Y`. -/
theorem prodComparison_compactlyGeneratedToTop :
    CartesianMonoidalCategory.prodComparison compactlyGeneratedToTop.{u, w} X Y =
      adj.{u, w}.counit.app (X.toTop ⊗ Y.toTop) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [CartesianMonoidalCategory.prodComparison_fst]; rfl
  · rw [CartesianMonoidalCategory.prodComparison_snd]; rfl

@[simp]
theorem prodComparison_compactlyGeneratedToTop_apply (p : ↑(X ⊗ Y)) :
    CartesianMonoidalCategory.prodComparison compactlyGeneratedToTop.{u, w} X Y p =
      (p : X × Y) := by
  rw [prodComparison_compactlyGeneratedToTop]; rfl

/-- The convenient product `X ⊗ Y` has the ordinary product topology if and only if `X × Y` is
`u`-compactly generated. -/
theorem isIso_prodComparison_compactlyGeneratedToTop_iff :
    IsIso (CartesianMonoidalCategory.prodComparison compactlyGeneratedToTop.{u, w} X Y) ↔
      UCompactlyGeneratedSpace.{u} (X × Y) := by
  rw [prodComparison_compactlyGeneratedToTop]; exact isIso_counit_app_iff (X.toTop ⊗ Y.toTop)

/-- When `X × Y` is `u`-compactly generated, the product comparison in `TopCat` is an
isomorphism. -/
instance instIsIsoProdComparisonCompactlyGeneratedToTop [UCompactlyGeneratedSpace.{u} (X × Y)] :
    IsIso (CartesianMonoidalCategory.prodComparison compactlyGeneratedToTop.{u, w} X Y) :=
  (isIso_prodComparison_compactlyGeneratedToTop_iff X Y).2 inferInstance

/-- When `X × Y` is `u`-compactly generated, the convenient product `X ⊗ Y` is homeomorphic to the
ordinary product `X × Y` by the identity on points. -/
@[expose]
def tensorHomeomorphProd [UCompactlyGeneratedSpace.{u} (X × Y)] : ↑(X ⊗ Y) ≃ₜ X × Y :=
  counitHomeomorph.{u, w} (TopCat.of (X × Y))

@[simp]
theorem tensorHomeomorphProd_apply [UCompactlyGeneratedSpace.{u} (X × Y)] (p : ↑(X ⊗ Y)) :
    tensorHomeomorphProd X Y p = p := rfl

@[simp]
theorem tensorHomeomorphProd_symm_apply [UCompactlyGeneratedSpace.{u} (X × Y)] (p : X × Y) :
    (tensorHomeomorphProd X Y).symm p = p := rfl

/-- When `Y` is locally compact, the product comparison in `TopCat` is an isomorphism, without
requiring separation or `u`-smallness on `Y`. -/
instance instIsIsoProdComparisonCompactlyGeneratedToTopOfLocallyCompactRight
    [LocallyCompactSpace Y] :
    IsIso (CartesianMonoidalCategory.prodComparison compactlyGeneratedToTop.{u, w} X Y) := by
  have := TauCeti.uCompactlyGeneratedSpace_prod_of_locallyCompactSpace_right.{u} X Y; infer_instance

/-- When `X` is locally compact, the product comparison in `TopCat` is an isomorphism, without
requiring separation or `u`-smallness on `X`. -/
instance instIsIsoProdComparisonCompactlyGeneratedToTopOfLocallyCompactLeft
    [LocallyCompactSpace X] :
    IsIso (CartesianMonoidalCategory.prodComparison compactlyGeneratedToTop.{u, w} X Y) := by
  have := TauCeti.uCompactlyGeneratedSpace_prod_of_locallyCompactSpace_left.{u} X Y; infer_instance

/-- When `Y` is locally compact, the convenient product `X ⊗ Y` is homeomorphic to the ordinary
product `X × Y` by the identity on points, without separation or `u`-smallness hypotheses. -/
@[expose]
def tensorHomeomorphProdOfLocallyCompactRight [LocallyCompactSpace Y] : ↑(X ⊗ Y) ≃ₜ X × Y :=
  have := TauCeti.uCompactlyGeneratedSpace_prod_of_locallyCompactSpace_right.{u} X Y
  tensorHomeomorphProd X Y

@[simp]
theorem tensorHomeomorphProdOfLocallyCompactRight_apply [LocallyCompactSpace Y]
    (p : ↑(X ⊗ Y)) : tensorHomeomorphProdOfLocallyCompactRight X Y p = p := rfl

@[simp]
theorem tensorHomeomorphProdOfLocallyCompactRight_symm_apply [LocallyCompactSpace Y]
    (p : X × Y) : (tensorHomeomorphProdOfLocallyCompactRight X Y).symm p = p := rfl

/-- When `X` is locally compact, the convenient product `X ⊗ Y` is homeomorphic to the ordinary
product `X × Y` by the identity on points, without separation or `u`-smallness hypotheses. -/
@[expose]
def tensorHomeomorphProdOfLocallyCompactLeft [LocallyCompactSpace X] : ↑(X ⊗ Y) ≃ₜ X × Y :=
  have := TauCeti.uCompactlyGeneratedSpace_prod_of_locallyCompactSpace_left.{u} X Y
  tensorHomeomorphProd X Y

@[simp]
theorem tensorHomeomorphProdOfLocallyCompactLeft_apply [LocallyCompactSpace X]
    (p : ↑(X ⊗ Y)) : tensorHomeomorphProdOfLocallyCompactLeft X Y p = p := rfl

@[simp]
theorem tensorHomeomorphProdOfLocallyCompactLeft_symm_apply [LocallyCompactSpace X]
    (p : X × Y) : (tensorHomeomorphProdOfLocallyCompactLeft X Y).symm p = p := rfl

end ProdComparison

/-- Any map into `↑(X ⊗ Y)` from a `u`-compactly generated space that is continuous into the
ordinary product `X × Y` is continuous into the convenient product `X ⊗ Y`. -/
theorem continuous_toCompactlyGeneratedProd {A : Type*} [TopologicalSpace A]
    [UCompactlyGeneratedSpace.{u} A] {X Y : CompactlyGenerated.{u, w}}
    {g : A → ↑(X ⊗ Y)} (hg : Continuous fun a ↦ ((g a).1, (g a).2)) :
    Continuous g :=
  ((⟨fun a ↦ ((g a).1, (g a).2), hg⟩ : C(A, X × Y)).toCompactlyGenerated.{u}.continuous.comp
    (counitHomeomorph.{u} (TopCat.of A)).symm.continuous).congr fun _ ↦ rfl

/-! ### Cartesian closed structure -/

/-- The internal hom functor on `CompactlyGenerated.{u, w}`, sending `Z` to `k` of the
`CompHaus.{u}`-probed mapping space `ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) Y Z`. -/
@[expose, simps! obj]
def ihomFunctor (Y : CompactlyGenerated.{u, w}) :
    CompactlyGenerated.{u, w} ⥤ CompactlyGenerated.{u, w} where
  obj Z := TopCat.toCompactlyGenerated.{u, w}.obj
    (TopCat.of (ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) Y Z))
  map p := TopCat.toCompactlyGeneratedOfContinuousGeneratedBy.{u}
    ((p.hom.hom.toContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K)).postcomp (Y := Y))
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

instance (Y Z : CompactlyGenerated.{u, w}) : FunLike ↑((ihomFunctor Y).obj Z) Y Z :=
  inferInstanceAs (FunLike (ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) Y Z) Y Z)

/-- Currying a morphism `Y ⊗ Z ⟶ T` in `CompactlyGenerated.{u, w}`. -/
@[expose]
def curryHom {Y Z T : CompactlyGenerated.{u, w}} (f : Y ⊗ Z ⟶ T) : Z ⟶ (ihomFunctor Y).obj T :=
  let f₀ : ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) (Y × Z) T :=
    { toFun := f
      prop := fun S q ↦ f.hom.hom.continuous.comp <|
        (q.toCompactlyGenerated.{u}.comp
          ((counitHomeomorph.{u, u} (TopCat.of S)).symm : C(S, _))).continuous.congr fun _ ↦ rfl }
  adj.{u, w}.homEquiv Z (TopCat.of (ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) Y T))
    (TopCat.ofHom (ContinuousMapGeneratedBy.curryEquiv f₀).toContinuousMap)

/-- Uncurrying a morphism `Z ⟶ (ihomFunctor Y).obj T` in `CompactlyGenerated.{u, w}`. -/
@[expose]
def uncurryHom {Y Z T : CompactlyGenerated.{u, w}} (g : Z ⟶ (ihomFunctor Y).obj T) : Y ⊗ Z ⟶ T :=
  let g₀ : C(Z, ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) Y T) :=
    ((adj.{u, w}.homEquiv Z _).symm g).hom
  TopCat.toCompactlyGeneratedOfContinuousGeneratedBy.{u}
      (ContinuousMapGeneratedBy.curryEquiv.symm
        (g₀.toContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K))) ≫
    adjUnitIso.{u, w}.inv.app T

/-- Currying equivalence `(Y ⊗ Z ⟶ T) ≃ (Z ⟶ (ihomFunctor Y).obj T)` in
`CompactlyGenerated.{u, w}`. -/
@[expose]
def curryEquiv (Y Z T : CompactlyGenerated.{u, w}) :
    (Y ⊗ Z ⟶ T) ≃ (Z ⟶ (ihomFunctor Y).obj T) where
  toFun := curryHom
  invFun := uncurryHom
  left_inv _ := ConcreteCategory.hom_ext _ _ fun ⟨_, _⟩ ↦ rfl
  right_inv _ := ConcreteCategory.hom_ext _ _ fun _ ↦ DFunLike.ext _ _ fun _ ↦ rfl

@[simp]
theorem curryEquiv_apply {Y Z T : CompactlyGenerated.{u, w}} (f : Y ⊗ Z ⟶ T) :
    curryEquiv Y Z T f = curryHom f := rfl

@[simp]
theorem curryEquiv_symm_apply {Y Z T : CompactlyGenerated.{u, w}} (g : Z ⟶ (ihomFunctor Y).obj T) :
    (curryEquiv Y Z T).symm g = uncurryHom g := rfl

/-- `Y ⊗ -` is left adjoint to `ihomFunctor Y` in `CompactlyGenerated.{u, w}`. -/
@[expose]
def tensorLeftAdjunction (Y : CompactlyGenerated.{u, w}) : tensorLeft Y ⊣ ihomFunctor Y :=
  Adjunction.mkOfHomEquiv
    { homEquiv := curryEquiv Y
      homEquiv_naturality_left_symm _ _ := ConcreteCategory.hom_ext _ _ fun ⟨_, _⟩ ↦ rfl
      homEquiv_naturality_right _ _ :=
        ConcreteCategory.hom_ext _ _ fun _ ↦ DFunLike.ext _ _ fun _ ↦ rfl }

instance instMonoidalClosed : MonoidalClosed CompactlyGenerated.{u, w} where
  closed Y := { rightAdj := ihomFunctor Y, adj := tensorLeftAdjunction Y }

instance instFunLikeIhom (Y Z : CompactlyGenerated.{u, w}) : FunLike ↑((ihom Y).obj Z) Y Z :=
  inferInstanceAs (FunLike (ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) Y Z) Y Z)

instance instFunLikeTensorLeftCompIhom (Y Z : CompactlyGenerated.{u, w}) :
    FunLike ↑((tensorLeft Y ⋙ ihom Y).obj Z) Y ↑(Y ⊗ Z) :=
  inferInstanceAs (FunLike ↑((ihom Y).obj (Y ⊗ Z)) Y ↑(Y ⊗ Z))

@[simp]
theorem ihom_map_apply {Y Z T : CompactlyGenerated.{u, w}} (p : Z ⟶ T) (g : ↑((ihom Y).obj Z))
    (y : Y) : ((ihom Y).map p g) y = p (g y) := rfl

@[simp]
theorem curryHom_apply {Y Z T : CompactlyGenerated.{u, w}} (f : Y ⊗ Z ⟶ T) (z : Z) (y : Y) :
    (curryHom f z) y = f (y, z) := (rfl)

@[simp]
theorem uncurryHom_apply {Y Z T : CompactlyGenerated.{u, w}} (g : Z ⟶ (ihomFunctor Y).obj T)
    (p : ↑(Y ⊗ Z)) : uncurryHom g p = g p.2 p.1 := (rfl)

/-- The hom-set equivalence of `ihom.adjunction Y` in `CompactlyGenerated.{u, w}` is
`curryEquiv Y`. -/
theorem ihom_adjunction_homEquiv (Y Z T : CompactlyGenerated.{u, w}) :
    (ihom.adjunction Y).homEquiv Z T = curryEquiv Y Z T :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _

@[simp]
theorem curry_apply {Y Z T : CompactlyGenerated.{u, w}} (f : Y ⊗ Z ⟶ T) (z : Z) (y : Y) :
    (MonoidalClosed.curry f z) y = f (y, z) := by
  rw [← MonoidalClosed.homEquiv_apply_eq, ihom_adjunction_homEquiv]
  exact curryHom_apply f z y

@[simp]
theorem uncurry_apply {Y Z T : CompactlyGenerated.{u, w}} (g : Z ⟶ (ihom Y).obj T) (p : ↑(Y ⊗ Z)) :
    MonoidalClosed.uncurry g p = g p.2 p.1 := by
  rw [← MonoidalClosed.homEquiv_symm_apply_eq, ihom_adjunction_homEquiv]
  exact uncurryHom_apply g p

@[simp]
theorem ihom_ev_app_apply (Y Z : CompactlyGenerated.{u, w}) (p : ↑(Y ⊗ (ihom Y).obj Z)) :
    dsimp% only [Functor.comp_obj, MonoidalCategory.curriedTensor_obj_obj, Functor.id_obj]
      ((ihom.ev Y).app Z p) = p.2 p.1 := by
  rw [← MonoidalClosed.uncurry_id_eq_ev, uncurry_apply]; rfl

@[simp]
theorem ihom_coev_app_apply (Y Z : CompactlyGenerated.{u, w}) (z : Z) (y : Y) :
    dsimp% only [Functor.comp_obj, MonoidalCategory.curriedTensor_obj_obj, Functor.id_obj]
      (((ihom.coev Y).app Z z) y) = (y, z) := by
  rw [← MonoidalClosed.curry_id_eq_coev]; exact curry_apply (𝟙 _) z y

/-- Pointwise formula for precomposition `(MonoidalClosed.pre f).app Z` in
`CompactlyGenerated.{u, w}`. -/
@[simp]
theorem pre_app_apply {A B : CompactlyGenerated.{u, w}} (f : B ⟶ A)
    (Z : CompactlyGenerated.{u, w}) (g : ↑((ihom A).obj Z)) (b : B) :
    ((MonoidalClosed.pre f).app Z g) b = g (f b) := by
  let bg : ↑(B ⊗ (ihom A).obj Z) := (b, g); let fbg : ↑(A ⊗ (ihom A).obj Z) := (f b, g)
  have h := uncurry_apply ((MonoidalClosed.pre f).app Z) bg
  rw [MonoidalClosed.uncurry_pre, CategoryTheory.comp_apply, whiskerRight_apply] at h
  exact h.symm.trans (ihom_ev_app_apply A Z fbg)

/-- Pointwise formula for internal currying `MonoidalClosed.ihomCurry` in
`CompactlyGenerated.{u, w}`. -/
@[simp]
theorem ihomCurry_apply (Y X Z : CompactlyGenerated.{u, w})
    (g : ↑((ihom (Y ⊗ X)).obj Z)) (x : X) (y : Y) :
    ((MonoidalClosed.ihomCurry Y X Z g) x) y = g (y, x) := by
  let xg : ↑(X ⊗ (ihom (Y ⊗ X)).obj Z) := (x, g)
  let yxg : ↑(Y ⊗ (X ⊗ (ihom (Y ⊗ X)).obj Z)) := (y, xg)
  let yx_g : ↑((Y ⊗ X) ⊗ (ihom (Y ⊗ X)).obj Z) := ((y, x), g)
  calc
    ((MonoidalClosed.ihomCurry Y X Z g) x) y
      = MonoidalClosed.uncurry (MonoidalClosed.uncurry (MonoidalClosed.ihomCurry Y X Z)) yxg := by
        rw [uncurry_apply, uncurry_apply]
    _ = ((α_ Y X _).inv ≫ (ihom.ev (Y ⊗ X)).app Z) yxg := by
        rw [MonoidalClosed.uncurry_uncurry_ihomCurry]
    _ = (ihom.ev (Y ⊗ X)).app Z ((α_ Y X _).inv yxg) := CategoryTheory.comp_apply _ _ yxg
    _ = (ihom.ev (Y ⊗ X)).app Z yx_g := congrArg _ (associator_inv_apply y x g)
    _ = g (y, x) := ihom_ev_app_apply (Y ⊗ X) Z yx_g

@[ext]
theorem ihom_obj_ext {Y Z : CompactlyGenerated.{u, w}} {f g : ↑((ihom Y).obj Z)}
    (h : ∀ y, f y = g y) : f = g :=
  DFunLike.ext f g h

/-- Pointwise formula for internal uncurrying `MonoidalClosed.ihomUncurry` in
`CompactlyGenerated.{u, w}`. -/
@[simp]
theorem ihomUncurry_apply (Y X Z : CompactlyGenerated.{u, w})
    (g : ↑((ihom X).obj ((ihom Y).obj Z))) (p : ↑(Y ⊗ X)) :
    (MonoidalClosed.ihomUncurry Y X Z g) p = (g p.2) p.1 := by
  let p2g : ↑(X ⊗ (ihom X).obj ((ihom Y).obj Z)) := (p.2, g)
  let p1_p2g : ↑(Y ⊗ (X ⊗ (ihom X).obj ((ihom Y).obj Z))) := (p.1, p2g)
  let pg : ↑((Y ⊗ X) ⊗ (ihom X).obj ((ihom Y).obj Z)) := ((p.1, p.2), g)
  calc
    (MonoidalClosed.ihomUncurry Y X Z g) p
      = MonoidalClosed.uncurry (MonoidalClosed.ihomUncurry Y X Z) (p, g) :=
        (uncurry_apply _ (p, g)).symm
    _ = ((α_ Y X _).hom ≫ Y ◁ (ihom.ev X).app ((ihom Y).obj Z) ≫ (ihom.ev Y).app Z) pg := by
        rw [MonoidalClosed.uncurry_ihomUncurry]; rfl
    _ = (ihom.ev Y).app Z ((Y ◁ (ihom.ev X).app ((ihom Y).obj Z)) ((α_ Y X _).hom pg)) := rfl
    _ = (ihom.ev Y).app Z ((Y ◁ (ihom.ev X).app ((ihom Y).obj Z)) p1_p2g) :=
        congrArg (fun q ↦ (ihom.ev Y).app Z ((Y ◁ (ihom.ev X).app ((ihom Y).obj Z)) q))
          (associator_hom_apply p.1 p.2 g)
    _ = (ihom.ev Y).app Z (p.1, (ihom.ev X).app ((ihom Y).obj Z) p2g) := by
        rw [whiskerLeft_apply]
    _ = (g p.2) p.1 := by
        rw [ihom_ev_app_apply X ((ihom Y).obj Z) p2g]
        exact ihom_ev_app_apply Y Z (p.1, g p.2)

/-- Evaluation at a point `y : Y` as a morphism `(ihom Y).obj Z ⟶ Z` in
`CompactlyGenerated.{u, w}`. -/
@[expose]
def evalAt (Y Z : CompactlyGenerated.{u, w}) (y : Y) : (ihom Y).obj Z ⟶ Z :=
  TopCat.toCompactlyGeneratedOfContinuousGeneratedBy.{u}
    ((ContinuousMapGeneratedBy.ev (X := fun K : CompHaus.{u} ↦ K)).comp
      ⟨fun f ↦ (y, f), (continuous_const.prodMk continuous_id).continuousGeneratedBy⟩) ≫
    adjUnitIso.{u, w}.inv.app Z

@[simp]
theorem evalAt_apply (Y Z : CompactlyGenerated.{u, w}) (y : Y) (f : ↑((ihom Y).obj Z)) :
    evalAt Y Z y f = f y := rfl

/-! ### Compact-open mapping space comparisons and exponential homeomorphism -/

/-- Canonical morphism `k(C(Y, Z)) ⟶ (ihom Y).obj Z` in `CompactlyGenerated.{u, w}` induced by
viewing continuous maps as `CompHaus.{u}`-continuous maps. -/
@[expose]
def compactOpenToIhom (Y Z : CompactlyGenerated.{u, w}) :
    TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(Y, Z)) ⟶ (ihom Y).obj Z :=
  TopCat.toCompactlyGeneratedOfContinuousGeneratedBy.{u}
    ⟨ContinuousMap.toContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K),
      ContinuousMap.continuous_toContinuousMapGeneratedBy.continuousGeneratedBy⟩

@[simp]
theorem compactOpenToIhom_apply (Y Z : CompactlyGenerated.{u, w})
    (f : TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(Y, Z))) (y : Y) :
    (compactOpenToIhom Y Z f) y = f y := rfl

instance (Y Z : CompactlyGenerated.{u, w}) :
    FunLike ↑((compactlyGeneratedToTop.{u, w} ⋙ TopCat.mappingSpace Y.toTop ⋙
      TopCat.toCompactlyGenerated.{u, w}).obj Z) Y Z :=
  inferInstanceAs (FunLike C(Y, Z) Y Z)

/-- When `Y : CompactlyGenerated.{u, w}` is `u`-small and Hausdorff, the internal hom
`(ihom Y).obj Z` is homeomorphic to `k(C(Y, Z))`, the compact-generation coreflection of the
compact-open mapping space `C(Y, Z)`. -/
@[expose]
def ihomHomeomorphToCompactlyGeneratedContinuousMap (Y Z : CompactlyGenerated.{u, w})
    [T2Space Y] [Small.{u} Y] :
    ↑((ihom Y).obj Z) ≃ₜ TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(Y, Z)) :=
  let e := Topology.ContinuousMapGeneratedBy.homeomorphContinuousMapCompHaus.{u} Y Z
  { toEquiv := e.toEquiv
    continuous_toFun := (ContinuousMap.toCompactlyGenerated.{u} ⟨e, e.continuous⟩).continuous
    continuous_invFun :=
      (ContinuousMap.toCompactlyGenerated.{u} ⟨e.symm, e.symm.continuous⟩).continuous }

@[simp]
theorem ihomHomeomorphToCompactlyGeneratedContinuousMap_apply (Y Z : CompactlyGenerated.{u, w})
    [T2Space Y] [Small.{u} Y] (f : ↑((ihom Y).obj Z)) (y : Y) :
    (ihomHomeomorphToCompactlyGeneratedContinuousMap Y Z f) y = f y := (rfl)

@[simp]
theorem ihomHomeomorphToCompactlyGeneratedContinuousMap_symm_apply
    (Y Z : CompactlyGenerated.{u, w}) [T2Space Y] [Small.{u} Y]
    (f : TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(Y, Z))) (y : Y) :
    ((ihomHomeomorphToCompactlyGeneratedContinuousMap Y Z).symm f) y = f y := (rfl)

/-- For a `u`-small Hausdorff space `Y : CompactlyGenerated.{u, w}`, the internal hom functor
`ihom Y` is naturally isomorphic to forming the compact-open mapping space `TopCat.mappingSpace Y`
followed by `TopCat.toCompactlyGenerated`. -/
@[expose]
def ihomIsoToCompactlyGeneratedMappingSpace (Y : CompactlyGenerated.{u, w})
    [T2Space Y] [Small.{u} Y] :
    ihom Y ≅
      compactlyGeneratedToTop.{u, w} ⋙ TopCat.mappingSpace Y.toTop ⋙
        TopCat.toCompactlyGenerated.{u, w} :=
  NatIso.ofComponents
    (fun Z ↦ isoOfHomeo (ihomHomeomorphToCompactlyGeneratedContinuousMap Y Z))
    (fun _ ↦ ConcreteCategory.hom_ext _ _ fun _ ↦ DFunLike.ext _ _ fun _ ↦ rfl)

theorem ihomIsoToCompactlyGeneratedMappingSpace_inv_app
    (Y Z : CompactlyGenerated.{u, w}) [T2Space Y] [Small.{u} Y] :
    (ihomIsoToCompactlyGeneratedMappingSpace Y).inv.app Z = compactOpenToIhom Y Z :=
  ConcreteCategory.hom_ext _ _ fun _ ↦ DFunLike.ext _ _ fun _ ↦ rfl

@[simp]
theorem ihomIsoToCompactlyGeneratedMappingSpace_hom_app_apply
    (Y Z : CompactlyGenerated.{u, w}) [T2Space Y] [Small.{u} Y]
    (f : ↑((ihom Y).obj Z)) (y : Y) :
    dsimp% only [Functor.comp_obj]
      (((ihomIsoToCompactlyGeneratedMappingSpace Y).hom.app Z f) y) = f y :=
  ihomHomeomorphToCompactlyGeneratedContinuousMap_apply Y Z f y

@[simp]
theorem ihomIsoToCompactlyGeneratedMappingSpace_inv_app_apply
    (Y Z : CompactlyGenerated.{u, w}) [T2Space Y] [Small.{u} Y]
    (f : TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(Y, Z))) (y : Y) :
    dsimp% only [Functor.comp_obj]
      (((ihomIsoToCompactlyGeneratedMappingSpace Y).inv.app Z f) y) = f y :=
  ihomHomeomorphToCompactlyGeneratedContinuousMap_symm_apply Y Z f y

/-- When `Y` is locally compact, `u`-small, and Hausdorff, currying `Y ⊗ X ⟶ Z` into `k(C(Y, Z))`
agrees with currying on the ordinary product `Y × X` in `TopCat` (`TopCat.curryEquiv`) followed by
`CompactlyGenerated.adj.homEquiv`. -/
theorem curry_comp_ihomIsoToCompactlyGeneratedMappingSpace
    {Y X Z : CompactlyGenerated.{u, w}} [LocallyCompactSpace Y] [T2Space Y] [Small.{u} Y]
    (f : Y ⊗ X ⟶ Z) :
    MonoidalClosed.curry f ≫ (ihomIsoToCompactlyGeneratedMappingSpace Y).hom.app Z =
      adj.{u, w}.homEquiv X (TopCat.of C(Y, Z))
        (TopCat.curryEquiv Y.toTop X.toTop Z.toTop
          ((TopCat.isoOfHomeo (tensorLeftLocallyCompactHomeomorph Y X)).inv ≫ f.hom)) := by
  refine ConcreteCategory.hom_ext _ _ fun x ↦ DFunLike.ext _ _ fun y ↦ ?_
  let g : X.toTop ⟶ TopCat.of C(Y, Z) := TopCat.curryEquiv Y.toTop X.toTop Z.toTop
    ((TopCat.isoOfHomeo (tensorLeftLocallyCompactHomeomorph Y X)).inv ≫ f.hom)
  calc
    ((MonoidalClosed.curry f ≫ (ihomIsoToCompactlyGeneratedMappingSpace Y).hom.app Z) x) y
      = ((ihomIsoToCompactlyGeneratedMappingSpace Y).hom.app Z (MonoidalClosed.curry f x)) y := by
        rw [CategoryTheory.comp_apply]
    _ = (MonoidalClosed.curry f x) y :=
        ihomIsoToCompactlyGeneratedMappingSpace_hom_app_apply Y Z _ y
    _ = f (y, x) := curry_apply f x y
    _ = g.hom x y := by rw [TopCat.curryEquiv_apply_hom_apply_apply]; rfl
    _ = (adj.{u, w}.homEquiv X (TopCat.of C(Y, Z)) g x) y :=
        congrArg (fun h : C(Y, Z) ↦ h y) (adj_homEquiv_apply g x).symm

/-- Exponential isomorphism on `k`-ified compact-open mapping spaces: when both source factors `X`
and `Y` are `u`-small and Hausdorff (and `Z : CompactlyGenerated.{u, w}` is arbitrary), currying
identifies `k(C(X ⊗ Y, Z))` with `k(C(X, k(C(Y, Z))))` in `CompactlyGenerated.{u, w}`. -/
@[expose]
def toCompactlyGeneratedMappingSpaceCurryIso (X Y Z : CompactlyGenerated.{u, w})
    [T2Space X] [Small.{u} X] [T2Space Y] [Small.{u} Y] :
    TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(↑(X ⊗ Y), Z)) ≅
      TopCat.toCompactlyGenerated.{u, w}.obj
        (TopCat.of C(X, TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(Y, Z)))) :=
  (isoOfHomeo (ihomHomeomorphToCompactlyGeneratedContinuousMap (X ⊗ Y) Z)).symm ≪≫
    (MonoidalClosed.internalHom.mapIso (β_ Y X).op).app Z ≪≫ MonoidalClosed.ihomCurryIso Y X Z ≪≫
    (ihom X).mapIso (isoOfHomeo (ihomHomeomorphToCompactlyGeneratedContinuousMap Y Z)) ≪≫
    isoOfHomeo (ihomHomeomorphToCompactlyGeneratedContinuousMap X
      (TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(Y, Z))))

/-- Homeomorphism underlying `toCompactlyGeneratedMappingSpaceCurryIso`: for `u`-small Hausdorff
`u`-compactly generated `X` and `Y` and arbitrary `u`-compactly generated `Z`, currying gives a
homeomorphism `k(C(X ⊗ Y, Z)) ≃ₜ k(C(X, k(C(Y, Z))))` sending `f` to `x ↦ (y ↦ f (x, y))`. -/
@[expose]
def toCompactlyGeneratedMappingSpaceCurryHomeomorph (X Y Z : CompactlyGenerated.{u, w})
    [T2Space X] [Small.{u} X] [T2Space Y] [Small.{u} Y] :
    TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(↑(X ⊗ Y), Z)) ≃ₜ
      TopCat.toCompactlyGenerated.{u, w}.obj
        (TopCat.of C(X, TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(Y, Z)))) :=
  homeoOfIso (toCompactlyGeneratedMappingSpaceCurryIso X Y Z)

/-- Pointwise evaluation formula for `toCompactlyGeneratedMappingSpaceCurryIso`. -/
@[simp]
theorem toCompactlyGeneratedMappingSpaceCurryIso_hom_apply
    (X Y Z : CompactlyGenerated.{u, w}) [T2Space X] [Small.{u} X] [T2Space Y] [Small.{u} Y]
    (f : TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(↑(X ⊗ Y), Z))) (x : X) (y : Y) :
    (((toCompactlyGeneratedMappingSpaceCurryIso X Y Z).hom f) x) y = f (x, y) := by
  let g4 : ↑((ihom (X ⊗ Y)).obj Z) :=
    (ihomHomeomorphToCompactlyGeneratedContinuousMap (X ⊗ Y) Z).symm f
  let g3 : ↑((ihom (Y ⊗ X)).obj Z) := (MonoidalClosed.pre (β_ Y X).hom).app Z g4
  let yx : ↑(Y ⊗ X) := (y, x)
  let xy : ↑(X ⊗ Y) := (x, y)
  have hhom : (toCompactlyGeneratedMappingSpaceCurryIso X Y Z).hom =
      (isoOfHomeo (ihomHomeomorphToCompactlyGeneratedContinuousMap (X ⊗ Y) Z)).inv ≫
        (MonoidalClosed.pre (β_ Y X).hom).app Z ≫ MonoidalClosed.ihomCurry Y X Z ≫
        (ihom X).map (isoOfHomeo (ihomHomeomorphToCompactlyGeneratedContinuousMap Y Z)).hom ≫
        (isoOfHomeo (ihomHomeomorphToCompactlyGeneratedContinuousMap X
          (TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(Y, Z))))).hom := rfl
  rw [hhom]
  simp only [CategoryTheory.comp_apply, isoOfHomeo_hom_apply, isoOfHomeo_inv_apply,
    ihomHomeomorphToCompactlyGeneratedContinuousMap_apply, ihom_map_apply, ihomCurry_apply]
  calc
    g3 yx = g4 ((β_ Y X).hom yx) := pre_app_apply (β_ Y X).hom Z g4 yx
    _ = g4 xy := congrArg g4 (braiding_hom_apply y x)
    _ = f xy := ihomHomeomorphToCompactlyGeneratedContinuousMap_symm_apply (X ⊗ Y) Z f xy

/-- Pointwise evaluation formula for `toCompactlyGeneratedMappingSpaceCurryHomeomorph`. -/
@[simp]
theorem toCompactlyGeneratedMappingSpaceCurryHomeomorph_apply
    (X Y Z : CompactlyGenerated.{u, w}) [T2Space X] [Small.{u} X] [T2Space Y] [Small.{u} Y]
    (f : TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(↑(X ⊗ Y), Z))) (x : X) (y : Y) :
    (((toCompactlyGeneratedMappingSpaceCurryHomeomorph X Y Z f) x) y) = f (x, y) :=
  toCompactlyGeneratedMappingSpaceCurryIso_hom_apply X Y Z f x y

/-! ### Concrete exponential identifications -/

/-- Pointwise formula for `(MonoidalClosed.unitIsoSelf Z).hom` in `CompactlyGenerated.{u, w}`. -/
@[simp]
theorem unitIsoSelf_hom_apply (Z : CompactlyGenerated.{u, w})
    (f : ↑((ihom (𝟙_ CompactlyGenerated.{u, w})).obj Z)) :
    (MonoidalClosed.unitIsoSelf (X := Z)).hom f = f PUnit.unit := by
  let pf : ↑(𝟙_ CompactlyGenerated.{u, w} ⊗ (ihom (𝟙_ CompactlyGenerated.{u, w})).obj Z) :=
    (PUnit.unit, f)
  calc
    (MonoidalClosed.unitIsoSelf (X := Z)).hom f
      = ((λ_ ((ihom (𝟙_ CompactlyGenerated.{u, w})).obj Z)).inv ≫
          (ihom.ev (𝟙_ CompactlyGenerated.{u, w})).app Z) f := by
        rw [MonoidalClosed.unitIsoSelf_hom]
    _ = (ihom.ev (𝟙_ CompactlyGenerated.{u, w})).app Z
          ((λ_ ((ihom (𝟙_ CompactlyGenerated.{u, w})).obj Z)).inv f) :=
        CategoryTheory.comp_apply _ _ f
    _ = (ihom.ev (𝟙_ CompactlyGenerated.{u, w})).app Z pf :=
        congrArg _ (leftUnitor_inv_apply f)
    _ = f PUnit.unit := ihom_ev_app_apply _ Z pf

/-- Pointwise formula for `(MonoidalClosed.unitIsoSelf Z).inv` in `CompactlyGenerated.{u, w}`. -/
@[simp]
theorem unitIsoSelf_inv_apply (Z : CompactlyGenerated.{u, w}) (z : Z) (p : PUnit.{w + 1}) :
    ((MonoidalClosed.unitIsoSelf Z).inv z) p = z := by
  rw [MonoidalClosed.unitIsoSelf_inv, curry_apply, leftUnitor_hom_apply]

/-- Auxiliary evaluation morphism `S⁰ ⊗ (Z ⊗ Z) ⟶ Z` sending `(⟨false⟩, z₀, z₁)` to `z₀` and
`(⟨true⟩, z₀, z₁)` to `z₁`. -/
@[expose]
def uliftBoolEval (Z : CompactlyGenerated.{u, w}) :
    (of.{u, w} (ULift.{w} Bool)) ⊗ (Z ⊗ Z) ⟶ Z :=
  haveI : UCompactlyGeneratedSpace.{u} (ULift.{w} Bool × ↑(Z ⊗ Z)) :=
    UCompactlyGeneratedSpace.prod_left
  let condHom : of.{u, w} (ULift.{w} Bool × ↑(Z ⊗ Z)) ⟶ Z :=
    InducedCategory.homMk <| TopCat.ofHom
      ⟨fun q : ULift.{w} Bool × ↑(Z ⊗ Z) ↦
          cond q.1.down (CartesianMonoidalCategory.snd Z Z q.2)
            (CartesianMonoidalCategory.fst Z Z q.2),
        continuous_prod_of_discrete_left.2 <| by
          rintro ⟨_ | _⟩
          · exact (CartesianMonoidalCategory.fst Z Z).hom.hom.continuous
          · exact (CartesianMonoidalCategory.snd Z Z).hom.hom.continuous⟩
  (isoOfHomeo (tensorLeftLocallyCompactHomeomorph (ULift.{w} Bool) (Z ⊗ Z))).hom ≫ condHom

@[simp]
theorem uliftBoolEval_apply_false (Z : CompactlyGenerated.{u, w}) (p : ↑(Z ⊗ Z)) :
    uliftBoolEval Z (ULift.up false, p) = p.1 := rfl

@[simp]
theorem uliftBoolEval_apply_true (Z : CompactlyGenerated.{u, w}) (p : ↑(Z ⊗ Z)) :
    uliftBoolEval Z (ULift.up true, p) = p.2 := rfl

/-- The exponential `(ihom S⁰).obj Z` out of the discrete two-point space `ULift Bool` is
canonically isomorphic to the convenient square `Z ⊗ Z`, sending `f` to `(f ⟨false⟩, f ⟨true⟩)`. -/
@[expose]
def ihomULiftBoolIso (Z : CompactlyGenerated.{u, w}) :
    (ihom (of.{u, w} (ULift.{w} Bool))).obj Z ≅ Z ⊗ Z where
  hom := CartesianMonoidalCategory.lift
    (evalAt (of.{u, w} (ULift.{w} Bool)) Z (ULift.up false))
    (evalAt (of.{u, w} (ULift.{w} Bool)) Z (ULift.up true))
  inv := MonoidalClosed.curry (uliftBoolEval Z)
  hom_inv_id := ConcreteCategory.hom_ext _ _ fun f ↦ DFunLike.ext _ _ fun ⟨b⟩ ↦ by
    cases b <;> (rw [CategoryTheory.comp_apply, CategoryTheory.id_apply, curry_apply]; rfl)
  inv_hom_id := by
    refine ConcreteCategory.hom_ext _ _ fun p ↦ Prod.ext ?_ ?_
    · rw [CategoryTheory.comp_apply, CategoryTheory.id_apply, CompactlyGenerated.lift_apply]
      dsimp only; rw [evalAt_apply, curry_apply]; rfl
    · rw [CategoryTheory.comp_apply, CategoryTheory.id_apply, CompactlyGenerated.lift_apply]
      dsimp only; rw [evalAt_apply, curry_apply]; rfl

@[simp]
theorem ihomULiftBoolIso_hom_apply (Z : CompactlyGenerated.{u, w})
    (f : ↑((ihom (of.{u, w} (ULift.{w} Bool))).obj Z)) :
    (ihomULiftBoolIso Z).hom f = (f (ULift.up false), f (ULift.up true)) := rfl

@[simp]
theorem ihomULiftBoolIso_inv_apply_false (Z : CompactlyGenerated.{u, w}) (p : ↑(Z ⊗ Z)) :
    ((ihomULiftBoolIso Z).inv p) (ULift.up false) = p.1 :=
  curry_apply (uliftBoolEval Z) p (ULift.up false)

@[simp]
theorem ihomULiftBoolIso_inv_apply_true (Z : CompactlyGenerated.{u, w}) (p : ↑(Z ⊗ Z)) :
    ((ihomULiftBoolIso Z).inv p) (ULift.up true) = p.2 :=
  curry_apply (uliftBoolEval Z) p (ULift.up true)

/-- For any `u`-small locally compact Hausdorff space `L`, the exponential `(ihom S⁰).obj (of L)`
in `CompactlyGenerated.{u, w}` is homeomorphic to the ordinary product `L × L`, sending `f` to
`(f ⟨false⟩, f ⟨true⟩)`. -/
@[expose]
def ihomULiftBoolHomeomorph (L : Type w) [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L]
    [Small.{u} L] :
    ↑((ihom (of.{u, w} (ULift.{w} Bool))).obj (of.{u, w} L)) ≃ₜ L × L :=
  (homeoOfIso (ihomULiftBoolIso (of.{u, w} L))).trans
    (tensorRightLocallyCompactHomeomorph (of.{u, w} L) L)

@[simp]
theorem ihomULiftBoolHomeomorph_apply (L : Type w) [TopologicalSpace L] [LocallyCompactSpace L]
    [T2Space L] [Small.{u} L]
    (f : ↑((ihom (of.{u, w} (ULift.{w} Bool))).obj (of.{u, w} L))) :
    ihomULiftBoolHomeomorph.{u, w} L f = (f (ULift.up false), f (ULift.up true)) := rfl

@[simp]
theorem ihomULiftBoolHomeomorph_symm_apply_false (L : Type w) [TopologicalSpace L]
    [LocallyCompactSpace L] [T2Space L] [Small.{u} L] (p : L × L) :
    ((ihomULiftBoolHomeomorph.{u, w} L).symm p) (ULift.up false) = p.1 :=
  ihomULiftBoolIso_inv_apply_false (of.{u, w} L) p

@[simp]
theorem ihomULiftBoolHomeomorph_symm_apply_true (L : Type w) [TopologicalSpace L]
    [LocallyCompactSpace L] [T2Space L] [Small.{u} L] (p : L × L) :
    ((ihomULiftBoolHomeomorph.{u, w} L).symm p) (ULift.up true) = p.2 :=
  ihomULiftBoolIso_inv_apply_true (of.{u, w} L) p

end CompactlyGenerated

end
