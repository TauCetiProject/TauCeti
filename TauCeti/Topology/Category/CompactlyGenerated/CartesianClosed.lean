/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Topology.Category.CompactlyGenerated.Coreflection
public import TauCeti.Topology.Category.TopCat.MappingSpace
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Convenient products, homotopies, and Cartesian closed structure on `CompactlyGenerated`

Passing from `TopCat` to `CompactlyGenerated.{u, w}` and forming binary products via
`TopCat.toCompactlyGenerated` yields a Cartesian closed category for every test universe `u` and
object universe `w`.

## Main declarations

* `CompactlyGenerated.isInitialPEmpty`, `CompactlyGenerated.isTerminalPUnit`,
  `CompactlyGenerated.prodBinaryFanIsLimit`: chosen finite products giving
  `CartesianMonoidalCategory` and `BraidedCategory` with binary product carrier `k(X × Y)`.
* `TopCat.toCompactlyGeneratedProdRightHomeomorph`,
  `TopCat.toCompactlyGeneratedProdLeftHomeomorph`,
  `CompactlyGenerated.tensorRightLocallyCompactHomeomorph`,
  `CompactlyGenerated.toCompactlyGeneratedProdRightIso`: for `u`-small locally compact Hausdorff
  `L`, `k(X × L)` agrees with `k(X) × L` by the identity on points.
* `ContinuousMap.toCompactlyGenerated`, `ContinuousMap.Homotopy.toCompactlyGenerated`,
  `ContinuousMap.HomotopyRel.toCompactlyGenerated`,
  `ContinuousMap.HomotopyEquiv.toCompactlyGenerated`: `k` preserves continuous maps, (relative)
  homotopies, and homotopy equivalences across arbitrary universes without separation hypotheses.
* `CompactlyGenerated.ihomFunctor`, `CompactlyGenerated.curryEquiv`,
  `CompactlyGenerated.tensorLeftAdjunction`: the `MonoidalClosed` structure on
  `CompactlyGenerated.{u, w}` with internal hom `k(ContinuousMapGeneratedBy CompHaus.{u} Y Z)`.
* `CompactlyGenerated.ihomHomeomorphToCompactlyGeneratedContinuousMap`,
  `CompactlyGenerated.ihomIsoToCompactlyGeneratedMappingSpace`,
  `CompactlyGenerated.continuous_eval_toCompactlyGeneratedContinuousMap`,
  `CompactlyGenerated.toCompactlyGeneratedMappingSpaceCurryIso`,
  `CompactlyGenerated.toCompactlyGeneratedMappingSpaceCurryHomeomorph`,
  `CompactlyGenerated.ihomULiftBoolIso`: compact-open comparisons, evaluation continuity,
  Hatcher's exponential law `k(C(X ⊗ Y, Z)) ≃ₜ k(C(X, k(C(Y, Z))))`, and `(ihom S⁰).obj Z ≅ Z ⊗ Z`.

## References

* N. E. Steenrod, *A convenient category of topological spaces*, Michigan Math. J. 14 (1967),
  133–152.
* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Math. Z. 119
  (1971), 11–28.
* M. Escardó, J. Lawson, and A. Simpson, *Comparing Cartesian closed categories of (core)
  compactly generated spaces*, Topology Appl. 143 (2004), 105–145.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Appendix A,
  Propositions A.14–A.16, pp. 530–531.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Topology

universe u w v₁ v₂ v₃

/-! ### Functoriality of `k` on maps, locally compact products, and homotopies -/

namespace TopCat

/-- When `L` is a `u`-small locally compact Hausdorff space, refining `X × L` by
`TopCat.toCompactlyGenerated` agrees with refining `X` alone and taking the ordinary topological
product with `L`. -/
@[expose]
def toCompactlyGeneratedProdRightHomeomorph (X : Type v₁) (L : Type v₂)
    [TopologicalSpace X] [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L] [Small.{u} L] :
    TopCat.toCompactlyGenerated.{u, max v₁ v₂}.obj (TopCat.of (X × L)) ≃ₜ
      TopCat.toCompactlyGenerated.{u, v₁}.obj (TopCat.of X) × L :=
  let e := (CompactlyGenerated.toCompactlyGeneratedHomeomorphGeneratedBy.{u, max v₁ v₂}
      (TopCat.of (X × L))).trans <|
    (Topology.WithGeneratedByTopology.prodRightHomeomorph (fun K : CompHaus.{u} ↦ K) X L).trans <|
      (CompactlyGenerated.toCompactlyGeneratedHomeomorphGeneratedBy.{u, v₁}
        (TopCat.of X)).symm.prodCongr (Homeomorph.refl L)
  let eqvXL := Topology.WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := X × L)
  let eqvX := Topology.WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := X)
  { toEquiv := Equiv.refl (X × L)
    continuous_toFun := e.continuous.congr fun p ↦ Prod.ext
      ((eqvX.apply_symm_apply _).trans (congrArg Prod.fst (eqvXL.apply_symm_apply p)))
      (congrArg Prod.snd (eqvXL.apply_symm_apply p))
    continuous_invFun := e.symm.continuous.congr fun p ↦
      (eqvXL.apply_symm_apply _).trans (Prod.ext (eqvX.apply_symm_apply p.1) rfl) }

@[simp]
theorem toCompactlyGeneratedProdRightHomeomorph_apply {X : Type v₁} {L : Type v₂}
    [TopologicalSpace X] [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L] [Small.{u} L]
    (p : TopCat.toCompactlyGenerated.{u, max v₁ v₂}.obj (TopCat.of (X × L))) :
    toCompactlyGeneratedProdRightHomeomorph.{u} X L p = p := rfl

@[simp]
theorem toCompactlyGeneratedProdRightHomeomorph_symm_apply {X : Type v₁} {L : Type v₂}
    [TopologicalSpace X] [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L] [Small.{u} L]
    (p : TopCat.toCompactlyGenerated.{u, v₁}.obj (TopCat.of X) × L) :
    (toCompactlyGeneratedProdRightHomeomorph.{u} X L).symm p = p := rfl

/-- When `L` is a `u`-small locally compact Hausdorff space, refining `L × X` by
`TopCat.toCompactlyGenerated` agrees with taking the ordinary topological product of `L` with the
refinement of `X`. -/
@[expose]
def toCompactlyGeneratedProdLeftHomeomorph (L : Type v₁) (X : Type v₂)
    [TopologicalSpace L] [TopologicalSpace X] [LocallyCompactSpace L] [T2Space L] [Small.{u} L] :
    TopCat.toCompactlyGenerated.{u, max v₁ v₂}.obj (TopCat.of (L × X)) ≃ₜ
      L × TopCat.toCompactlyGenerated.{u, v₂}.obj (TopCat.of X) :=
  let e := (CompactlyGenerated.toCompactlyGeneratedHomeomorphGeneratedBy.{u, max v₁ v₂}
      (TopCat.of (L × X))).trans <|
    (Topology.WithGeneratedByTopology.prodLeftHomeomorph (fun K : CompHaus.{u} ↦ K) L X).trans <|
      (Homeomorph.refl L).prodCongr
        (CompactlyGenerated.toCompactlyGeneratedHomeomorphGeneratedBy.{u, v₂} (TopCat.of X)).symm
  let eqvLX := Topology.WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := L × X)
  let eqvX := Topology.WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := X)
  { toEquiv := Equiv.refl (L × X)
    continuous_toFun := e.continuous.congr fun p ↦ Prod.ext
      (congrArg Prod.fst (eqvLX.apply_symm_apply p))
      ((eqvX.apply_symm_apply _).trans (congrArg Prod.snd (eqvLX.apply_symm_apply p)))
    continuous_invFun := e.symm.continuous.congr fun p ↦
      (eqvLX.apply_symm_apply _).trans (Prod.ext rfl (eqvX.apply_symm_apply p.2)) }

@[simp]
theorem toCompactlyGeneratedProdLeftHomeomorph_apply {L : Type v₁} {X : Type v₂}
    [TopologicalSpace L] [TopologicalSpace X] [LocallyCompactSpace L] [T2Space L] [Small.{u} L]
    (p : TopCat.toCompactlyGenerated.{u, max v₁ v₂}.obj (TopCat.of (L × X))) :
    toCompactlyGeneratedProdLeftHomeomorph.{u} L X p = p := rfl

@[simp]
theorem toCompactlyGeneratedProdLeftHomeomorph_symm_apply {L : Type v₁} {X : Type v₂}
    [TopologicalSpace L] [TopologicalSpace X] [LocallyCompactSpace L] [T2Space L] [Small.{u} L]
    (p : L × TopCat.toCompactlyGenerated.{u, v₂}.obj (TopCat.of X)) :
    (toCompactlyGeneratedProdLeftHomeomorph.{u} L X).symm p = p := rfl

/-- Any `CompHaus.{u}`-continuous map `A → B` induces a morphism `kA ⟶ kB` in
`CompactlyGenerated.{u, w}` acting identically on underlying points. -/
@[expose]
def toCompactlyGeneratedOfContinuousGeneratedBy {A B : Type w}
    [TopologicalSpace A] [TopologicalSpace B]
    (φ : ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) A B) :
    TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of A) ⟶
      TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of B) :=
  InducedCategory.homMk <| @TopCat.ofHom A B (TopologicalSpace.compactlyGenerated.{u} A)
    (TopologicalSpace.compactlyGenerated.{u} B) <|
    @ContinuousMap.mk A B (TopologicalSpace.compactlyGenerated.{u} A)
      (TopologicalSpace.compactlyGenerated.{u} B) φ
      (continuous_from_compactlyGenerated.{u} (t := TopologicalSpace.compactlyGenerated.{u} B) φ
        fun _ g ↦ TopologicalSpace.continuous_to_compactlyGenerated.{u} ⟨φ ∘ g, φ.prop g⟩)

@[simp]
theorem toCompactlyGeneratedOfContinuousGeneratedBy_apply {A B : Type w}
    [TopologicalSpace A] [TopologicalSpace B]
    (φ : ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) A B)
    (a : TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of A)) :
    toCompactlyGeneratedOfContinuousGeneratedBy.{u} φ a = φ a := rfl

end TopCat

namespace ContinuousMap

section ToCompactlyGenerated

variable {X : Type v₁} {Y : Type v₂} {Z : Type v₃}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Apply the compact-generation coreflector `k` to a continuous map `C(X, Y)`, with `X` and `Y` in
possibly distinct universes. -/
@[expose]
def toCompactlyGenerated (f : C(X, Y)) :
    C(TopCat.toCompactlyGenerated.{u, v₁}.obj (TopCat.of X),
      TopCat.toCompactlyGenerated.{u, v₂}.obj (TopCat.of Y)) where
  toFun := f
  continuous_toFun :=
    continuous_from_compactlyGenerated.{u} (t := TopologicalSpace.compactlyGenerated.{u} Y) f
      fun _ g ↦ TopologicalSpace.continuous_to_compactlyGenerated.{u} (f.comp g)

@[simp]
theorem toCompactlyGenerated_apply (f : C(X, Y))
    (x : TopCat.toCompactlyGenerated.{u, v₁}.obj (TopCat.of X)) :
    f.toCompactlyGenerated.{u} x = f x := rfl

@[simp]
theorem toCompactlyGenerated_id :
    (ContinuousMap.id X).toCompactlyGenerated.{u} =
      ContinuousMap.id (TopCat.toCompactlyGenerated.{u, v₁}.obj (TopCat.of X)) := rfl

@[simp]
theorem toCompactlyGenerated_comp (g : C(Y, Z)) (f : C(X, Y)) :
    (g.comp f).toCompactlyGenerated.{u} =
      g.toCompactlyGenerated.{u}.comp f.toCompactlyGenerated.{u} := rfl

/-- Because `unitInterval` is locally compact, Hausdorff, and `0`-small, `k` commutes with the
cylinder `unitInterval × -` and therefore carries homotopies `f₀ ≃ f₁` to homotopies
`k(f₀) ≃ k(f₁)`. -/
@[expose]
def Homotopy.toCompactlyGenerated {f₀ f₁ : C(X, Y)} (F : f₀.Homotopy f₁) :
    f₀.toCompactlyGenerated.{u}.Homotopy f₁.toCompactlyGenerated.{u} where
  toContinuousMap := F.toContinuousMap.toCompactlyGenerated.{u}.comp
    (TopCat.toCompactlyGeneratedProdLeftHomeomorph.{u} unitInterval X).symm
  map_zero_left := F.map_zero_left
  map_one_left := F.map_one_left

@[simp]
theorem Homotopy.toCompactlyGenerated_apply {f₀ f₁ : C(X, Y)} (F : f₀.Homotopy f₁)
    (p : unitInterval × TopCat.toCompactlyGenerated.{u, v₁}.obj (TopCat.of X)) :
    F.toCompactlyGenerated.{u} p = F p := rfl

/-- `k` carries homotopies relative to a subset `S : Set X` to homotopies relative to `S`. -/
@[expose]
def HomotopyRel.toCompactlyGenerated {f₀ f₁ : C(X, Y)} {S : Set X} (F : f₀.HomotopyRel f₁ S) :
    f₀.toCompactlyGenerated.{u}.HomotopyRel f₁.toCompactlyGenerated.{u} S :=
  ⟨F.toHomotopy.toCompactlyGenerated.{u}, F.prop⟩

@[simp]
theorem HomotopyRel.toCompactlyGenerated_apply {f₀ f₁ : C(X, Y)} {S : Set X}
    (F : f₀.HomotopyRel f₁ S)
    (p : unitInterval × TopCat.toCompactlyGenerated.{u, v₁}.obj (TopCat.of X)) :
    F.toCompactlyGenerated.{u} p = F p := rfl

/-- `k` preserves the homotopy relation between continuous maps. -/
theorem Homotopic.toCompactlyGenerated {f₀ f₁ : C(X, Y)} (h : f₀.Homotopic f₁) :
    f₀.toCompactlyGenerated.{u}.Homotopic f₁.toCompactlyGenerated.{u} :=
  h.map Homotopy.toCompactlyGenerated.{u}

/-- `k` preserves homotopy relative to a subset `S : Set X`. -/
theorem HomotopicRel.toCompactlyGenerated {f₀ f₁ : C(X, Y)} {S : Set X}
    (h : f₀.HomotopicRel f₁ S) :
    f₀.toCompactlyGenerated.{u}.HomotopicRel f₁.toCompactlyGenerated.{u} S :=
  h.map HomotopyRel.toCompactlyGenerated.{u}

/-- `k` preserves homotopy equivalences across arbitrary universes without separation hypotheses. -/
@[expose]
def HomotopyEquiv.toCompactlyGenerated (e : X ≃ₕ Y) :
    TopCat.toCompactlyGenerated.{u, v₁}.obj (TopCat.of X) ≃ₕ
      TopCat.toCompactlyGenerated.{u, v₂}.obj (TopCat.of Y) where
  toFun := e.toFun.toCompactlyGenerated.{u}
  invFun := e.invFun.toCompactlyGenerated.{u}
  left_inv := e.left_inv.toCompactlyGenerated.{u}
  right_inv := e.right_inv.toCompactlyGenerated.{u}

@[simp]
theorem HomotopyEquiv.toCompactlyGenerated_apply (e : X ≃ₕ Y)
    (x : TopCat.toCompactlyGenerated.{u, v₁}.obj (TopCat.of X)) :
    e.toCompactlyGenerated.{u} x = e x := rfl

@[simp]
theorem HomotopyEquiv.toCompactlyGenerated_symm_apply (e : X ≃ₕ Y)
    (y : TopCat.toCompactlyGenerated.{u, v₂}.obj (TopCat.of Y)) :
    (e.toCompactlyGenerated.{u}).symm y = e.symm y := rfl

end ToCompactlyGenerated

end ContinuousMap

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

@[simp]
theorem curry_apply {Y Z T : CompactlyGenerated.{u, w}} (f : Y ⊗ Z ⟶ T) (z : Z) (y : Y) :
    (MonoidalClosed.curry f z) y = f (y, z) := by
  change ((tensorLeftAdjunction Y).homEquiv Z T f z) y = f (y, z)
  rw [tensorLeftAdjunction, Adjunction.mkOfHomEquiv_homEquiv]; rfl

@[simp]
theorem uncurry_apply {Y Z T : CompactlyGenerated.{u, w}} (g : Z ⟶ (ihom Y).obj T) (p : ↑(Y ⊗ Z)) :
    MonoidalClosed.uncurry g p = g p.2 p.1 := by
  change ((tensorLeftAdjunction Y).homEquiv Z T).symm g p = g p.2 p.1
  rw [tensorLeftAdjunction, Adjunction.mkOfHomEquiv_homEquiv]; rfl

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
theorem pre_app_apply {A B : CompactlyGenerated.{u, w}} (f : B ⟶ A)
    (Z : CompactlyGenerated.{u, w}) (g : ↑((ihom A).obj Z)) (b : B) :
    ((MonoidalClosed.pre f).app Z g) b = g (f b) := by
  let bg : ↑(B ⊗ (ihom A).obj Z) := (b, g); let fbg : ↑(A ⊗ (ihom A).obj Z) := (f b, g)
  have h := uncurry_apply ((MonoidalClosed.pre f).app Z) bg
  rw [MonoidalClosed.uncurry_pre, CategoryTheory.comp_apply, whiskerRight_apply] at h
  exact h.symm.trans (ihom_ev_app_apply A Z fbg)

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

/-- Ordinary product evaluation `k(C(Y, Z)) × Y → Z` is continuous whenever the evaluation source
`Y` is locally compact (Hatcher, Proposition A.14). -/
theorem continuous_eval_toCompactlyGeneratedContinuousMap (Y Z : Type w)
    [TopologicalSpace Y] [TopologicalSpace Z] [LocallyCompactSpace Y] :
    Continuous fun p : TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(Y, Z)) × Y ↦ p.1 p.2 :=
  (continuous_eval (F := C(Y, Z))).comp <|
    (adj.{u, w}.counit.app (TopCat.of C(Y, Z))).hom.continuous.prodMap continuous_id

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
  simp only [Functor.comp_obj, CategoryTheory.comp_apply,
    ihomIsoToCompactlyGeneratedMappingSpace_hom_app_apply, curry_apply]
  change f (y, x) =
    (TopCat.curryEquiv Y.toTop X.toTop Z.toTop
      ((TopCat.isoOfHomeo (tensorLeftLocallyCompactHomeomorph Y X)).inv ≫ f.hom)).hom x y
  rw [TopCat.curryEquiv_apply_hom_apply_apply]; rfl

@[simp]
theorem isoOfHomeo_hom_apply {X Y : CompactlyGenerated.{u, w}} (e : X ≃ₜ Y) (x : X) :
    (isoOfHomeo e).hom x = e x := rfl

@[simp]
theorem isoOfHomeo_inv_apply {X Y : CompactlyGenerated.{u, w}} (e : X ≃ₜ Y) (y : Y) :
    (isoOfHomeo e).inv y = e.symm y := rfl

/-- Precomposition by an isomorphism `e : B ≅ A` induces a natural isomorphism `ihom A ≅ ihom B`. -/
@[expose, simps]
def preIso {A B : CompactlyGenerated.{u, w}} (e : B ≅ A) : ihom A ≅ ihom B where
  hom := MonoidalClosed.pre e.hom
  inv := MonoidalClosed.pre e.inv
  hom_inv_id := by rw [← MonoidalClosed.pre_map, e.inv_hom_id, MonoidalClosed.pre_id]
  inv_hom_id := by rw [← MonoidalClosed.pre_map, e.hom_inv_id, MonoidalClosed.pre_id]

/-- Hatcher's exponential isomorphism (Proposition A.16) on `k`-ified compact-open mapping spaces:
when both source factors `X` and `Y` are `u`-small and Hausdorff (and `Z` is arbitrary), currying
identifies `k(C(X ⊗ Y, Z))` with `k(C(X, k(C(Y, Z))))` in `CompactlyGenerated.{u, w}`. -/
@[expose]
def toCompactlyGeneratedMappingSpaceCurryIso (X Y Z : CompactlyGenerated.{u, w})
    [T2Space X] [Small.{u} X] [T2Space Y] [Small.{u} Y] :
    TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(↑(X ⊗ Y), Z)) ≅
      TopCat.toCompactlyGenerated.{u, w}.obj
        (TopCat.of C(X, TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(Y, Z)))) :=
  (isoOfHomeo (ihomHomeomorphToCompactlyGeneratedContinuousMap (X ⊗ Y) Z)).symm ≪≫
    (preIso (β_ Y X)).app Z ≪≫ MonoidalClosed.ihomCurryIso Y X Z ≪≫
    (ihom X).mapIso (isoOfHomeo (ihomHomeomorphToCompactlyGeneratedContinuousMap Y Z)) ≪≫
    isoOfHomeo (ihomHomeomorphToCompactlyGeneratedContinuousMap X
      (TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(Y, Z))))

/-- Homeomorphism underlying `toCompactlyGeneratedMappingSpaceCurryIso`: for `u`-small Hausdorff
`u`-compactly generated `X` and `Y` and arbitrary `Z`, currying gives a homeomorphism
`k(C(X ⊗ Y, Z)) ≃ₜ k(C(X, k(C(Y, Z))))` sending `f` to `x ↦ (y ↦ f (x, y))`. -/
@[expose]
def toCompactlyGeneratedMappingSpaceCurryHomeomorph (X Y Z : CompactlyGenerated.{u, w})
    [T2Space X] [Small.{u} X] [T2Space Y] [Small.{u} Y] :
    TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(↑(X ⊗ Y), Z)) ≃ₜ
      TopCat.toCompactlyGenerated.{u, w}.obj
        (TopCat.of C(X, TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(Y, Z)))) :=
  homeoOfIso (toCompactlyGeneratedMappingSpaceCurryIso X Y Z)

/-- Pointwise evaluation formula for `toCompactlyGeneratedMappingSpaceCurryIso`. -/
theorem toCompactlyGeneratedMappingSpaceCurryIso_hom_apply
    (X Y Z : CompactlyGenerated.{u, w}) [T2Space X] [Small.{u} X] [T2Space Y] [Small.{u} Y]
    (f : TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(↑(X ⊗ Y), Z))) (x : X) (y : Y) :
    (((toCompactlyGeneratedMappingSpaceCurryIso X Y Z).hom f) x) y = f (x, y) := by
  simp only [toCompactlyGeneratedMappingSpaceCurryIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    preIso_hom, MonoidalClosed.ihomCurryIso_hom, Functor.mapIso_hom, CategoryTheory.comp_apply,
    isoOfHomeo_hom_apply, isoOfHomeo_inv_apply,
    ihomHomeomorphToCompactlyGeneratedContinuousMap_apply, ihom_map_apply]
  let g4 : ↑((ihom (X ⊗ Y)).obj Z) :=
    (ihomHomeomorphToCompactlyGeneratedContinuousMap (X ⊗ Y) Z).symm f
  let g3 : ↑((ihom (Y ⊗ X)).obj Z) := (MonoidalClosed.pre (β_ Y X).hom).app Z g4
  let xg3 : ↑(X ⊗ (ihom (Y ⊗ X)).obj Z) := (x, g3)
  let yxg3 : ↑(Y ⊗ (X ⊗ (ihom (Y ⊗ X)).obj Z)) := (y, xg3)
  let yx : ↑(Y ⊗ X) := (y, x); let xy : ↑(X ⊗ Y) := (x, y)
  let yx_g3 : ↑((Y ⊗ X) ⊗ (ihom (Y ⊗ X)).obj Z) := (yx, g3)
  have h3 : ((α_ Y X _).inv ≫ (ihom.ev (Y ⊗ X)).app Z) yxg3 = (ihom.ev (Y ⊗ X)).app Z yx_g3 := by
    rw [CategoryTheory.comp_apply]; exact congrArg _ (associator_inv_apply y x g3)
  change (((MonoidalClosed.ihomCurry Y X Z) g3) x) y = f xy
  exact (DFunLike.congr_fun (curry_apply _ g3 x) y).trans <| (curry_apply _ xg3 y).trans <|
    h3.trans <| (ihom_ev_app_apply (Y ⊗ X) Z yx_g3).trans <|
      (pre_app_apply (β_ Y X).hom Z g4 yx).trans <|
        (congrArg g4 (braiding_hom_apply y x)).trans <|
          ihomHomeomorphToCompactlyGeneratedContinuousMap_symm_apply (X ⊗ Y) Z f xy

/-- Pointwise evaluation formula for `toCompactlyGeneratedMappingSpaceCurryHomeomorph`. -/
theorem toCompactlyGeneratedMappingSpaceCurryHomeomorph_apply
    (X Y Z : CompactlyGenerated.{u, w}) [T2Space X] [Small.{u} X] [T2Space Y] [Small.{u} Y]
    (f : TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(↑(X ⊗ Y), Z))) (x : X) (y : Y) :
    (((toCompactlyGeneratedMappingSpaceCurryHomeomorph X Y Z f) x) y) = f (x, y) :=
  toCompactlyGeneratedMappingSpaceCurryIso_hom_apply X Y Z f x y

/-! ### Standard objects and concrete product and exponential identifications -/

/-- The unit interval as an object of `CompactlyGenerated.{u, w}`, matching `TopCat.I.{w}`. -/
@[expose, implicit_reducible]
def I : CompactlyGenerated.{u, w} := of (ULift.{w} unitInterval)

/-- The convenient square `I ⊗ I` in `CompactlyGenerated.{u, w}` is homeomorphic to the ordinary
square `I × I` via the identity on points, retaining both coordinates. -/
@[expose]
def tensorIHomeomorph :
    ↑(I.{u, w} ⊗ I.{u, w}) ≃ₜ ULift.{w} unitInterval × ULift.{w} unitInterval :=
  tensorRightLocallyCompactHomeomorph I.{u, w} (ULift.{w} unitInterval)

@[simp]
theorem tensorIHomeomorph_apply (p : ↑(I.{u, w} ⊗ I.{u, w})) : tensorIHomeomorph.{u, w} p = p := rfl

@[simp]
theorem tensorIHomeomorph_symm_apply (p : ULift.{w} unitInterval × ULift.{w} unitInterval) :
    (tensorIHomeomorph.{u, w}).symm p = p := rfl

@[simp]
theorem unitIsoSelf_hom_apply (Z : CompactlyGenerated.{u, w})
    (f : ↑((ihom (𝟙_ CompactlyGenerated.{u, w})).obj Z)) :
    (MonoidalClosed.unitIsoSelf (X := Z)).hom f = f PUnit.unit := by
  simpa [MonoidalClosed.unitIsoSelf, MonoidalClosed.unitNatIso, conjugateIsoEquiv, conjugateEquiv]
    using ihom_ev_app_apply _ _ (PUnit.unit, f)

/-- Pointwise formula for `(MonoidalClosed.unitIsoSelf Z).inv` in `CompactlyGenerated.{u, w}`. -/
theorem unitIsoSelf_inv_apply (Z : CompactlyGenerated.{u, w}) (z : Z) (p : PUnit.{w + 1}) :
    ((MonoidalClosed.unitIsoSelf Z).inv z) p = z := by
  cases p
  rw [← unitIsoSelf_hom_apply Z ((MonoidalClosed.unitIsoSelf Z).inv z)]
  exact (homeoOfIso (MonoidalClosed.unitIsoSelf Z)).apply_symm_apply z

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

/-- Specialization of `ihomULiftBoolIso` to the unit interval: `C(S⁰, I)` in
`CompactlyGenerated.{u, w}` is homeomorphic to `I × I`, and under evaluation the pair `(0, 1)`
sends the two vertices `⟨false⟩` and `⟨true⟩` to `0` and `1`. -/
@[expose]
def ihomULiftBoolIHomeomorph :
    ↑((ihom (of (ULift.{w} Bool) : CompactlyGenerated.{u, w})).obj I.{u, w}) ≃ₜ
      ULift.{w} unitInterval × ULift.{w} unitInterval :=
  (homeoOfIso (ihomULiftBoolIso I.{u, w})).trans tensorIHomeomorph.{u, w}

@[simp]
theorem ihomULiftBoolIHomeomorph_symm_zero_one_false :
    ((ihomULiftBoolIHomeomorph.{u, w}).symm (ULift.up 0, ULift.up 1)) (ULift.up false) =
      ULift.up (0 : unitInterval) := by
  simp only [ihomULiftBoolIHomeomorph, Homeomorph.symm_trans_apply, tensorIHomeomorph_symm_apply]
  exact ihomULiftBoolIso_inv_apply_false I.{u, w} (ULift.up 0, ULift.up 1)

@[simp]
theorem ihomULiftBoolIHomeomorph_symm_zero_one_true :
    ((ihomULiftBoolIHomeomorph.{u, w}).symm (ULift.up 0, ULift.up 1)) (ULift.up true) =
      ULift.up (1 : unitInterval) := by
  simp only [ihomULiftBoolIHomeomorph, Homeomorph.symm_trans_apply, tensorIHomeomorph_symm_apply]
  exact ihomULiftBoolIso_inv_apply_true I.{u, w} (ULift.up 0, ULift.up 1)

end CompactlyGenerated

end
