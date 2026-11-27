/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.Cohomology.Forget
public import TauCeti.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Data.ZMod.Basic

/-!
# Native derived restriction on proper disconnected opens and endpoint coefficients

These examples retain arbitrary degree, a proper nested pair of opens, a genuinely nonidentity
coefficient map, empty and zero coefficients, and a point over ℤ/2. They use the native
restriction maps and composition comparison; no forgetting-injectives instance is supplied.
-/

public section
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TopologicalSpace.Opens TauCeti.Topology
universe u
namespace TauCeti.Examples.DerivedRestriction


namespace Disconnected
/-- A discrete three-point space for proper open restrictions. -/
abbrev threePointSpace : TopCat := @TopCat.of (Fin 3) ⊥
instance : DiscreteTopology threePointSpace := ⟨rfl⟩
/-- The proper open consisting of the first two points. -/
def firstTwo : Opens threePointSpace := ⟨{x | x.val < 2}, isOpen_discrete _⟩
/-- The single-point open inside the first two points. -/
def firstOne : Opens threePointSpace := ⟨{x | x.val < 1}, isOpen_discrete _⟩
/-- The chosen nested opens form an inclusion. -/
lemma firstOne_le_firstTwo : firstOne ≤ firstTwo := by
  intro x h
  exact lt_trans h (by decide : (1 : ℕ) < 2)
/-- The two-point open is a proper open of the three-point space. -/
lemma firstTwo_proper : firstTwo ≠ ⊤ := by
  intro h
  have hx : (2 : Fin 3) ∈ firstTwo := h ▸ trivial
  exact (by decide : ¬((2 : Fin 3).val < 2)) hx
/-- The inner open is proper in the two-point subspace. -/
lemma firstOne_proper_in_firstTwo : firstOne ≠ firstTwo := by
  intro h
  have hx : (1 : Fin 3) ∈ firstOne := h ▸ (by simp [firstTwo])
  exact (by decide : ¬((1 : Fin 3).val < 1)) hx
/-- Decidable equality identifies the coefficient stalk in the skyscraper example. -/
def pointDecisions : (U : Opens threePointSpace) → Decidable ((0 : Fin 3) ∈ U) :=
  fun _ ↦ Classical.propDecidable _
/-- The skyscraper sheaf with a specified module stalk. -/
abbrev skyscraperF := @skyscraperSheafFunctor threePointSpace (0 : Fin 3) pointDecisions
  (ModuleCat ℤ) inferInstance inferInstance
/-- The integer module used as the nonzero coefficient stalk. -/
abbrev integerModule := ModuleCat.of ℤ ℤ
/-- The integer skyscraper sheaf on the three-point space. -/
def integerSheaf : threePointSpace.Sheaf (ModuleCat ℤ) := skyscraperF.obj integerModule
/-- The skyscraper coefficient map induced by multiplication by two. -/
def coefficientTwo : integerSheaf ⟶ integerSheaf :=
  skyscraperF.map (2 • 𝟙 integerModule)
/-- Multiplication by two gives a nonidentity coefficient morphism. -/
lemma coefficientTwo_ne_id : coefficientTwo ≠ 𝟙 integerSheaf := by
  intro h
  have hmem : (0 : Fin 3) ∈ (⊤ : Opens threePointSpace) := trivial
  have ht := congrArg (fun f : integerSheaf ⟶ integerSheaf ↦ f.hom.app (op ⊤)) h
  let he : (@skyscraperPresheaf threePointSpace (0 : Fin 3) pointDecisions (ModuleCat ℤ)
    inferInstance inferInstance integerModule).obj (op ⊤) =
      integerModule := ite_eq_left (show (0 : Fin 3) ∈ (⊤ : Opens threePointSpace) from trivial)
  let e := eqToIso he
  have hf : coefficientTwo.hom.app (op ⊤) = e.hom ≫ (2 • 𝟙 integerModule) ≫ e.inv := by
    dsimp only [coefficientTwo, skyscraperF, skyscraperSheafFunctor, skyscraperPresheafFunctor,
      ObjectProperty.homMk]
    simp only [SkyscraperPresheafFunctor.map'_app, e, eqToIso.hom, eqToIso.inv]
    -- The top open contains the skyscraper point, so the `dite` takes its first branch. Its
    -- condition is stated for `unop (op ⊤)`, which `exact` unifies with `⊤`.
    exact dite_eq_left hmem
  have hc := congrArg (fun f ↦ e.inv ≫ f ≫ e.hom) ht
  -- The evaluated identity sheaf map is the identity on the skyscraper's top carrier.
  have hid : (𝟙 integerSheaf : integerSheaf ⟶ integerSheaf).hom.app (op ⊤) =
      e.hom ≫ e.inv := by
    exact e.hom_inv_id.symm
  rw [hf, hid] at hc
  have hm : (2 • 𝟙 integerModule) = 𝟙 integerModule := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.id_comp, Category.comp_id] using hc
  have hh := ConcreteCategory.congr_hom hm (1 : ℤ)
  norm_num at hh
example (n : ℕ) :
    ((Sheaf.Γ (Opens.grothendieckTopology threePointSpace) (ModuleCat ℤ)).rightDerived n).map
        coefficientTwo ≫ (rightDerivedΓRestriction firstTwo n).app integerSheaf =
    (rightDerivedΓRestriction firstTwo n).app integerSheaf ≫
      ((Sheaf.Γ (Opens.grothendieckTopology firstTwo) (ModuleCat ℤ)).rightDerived n).map
        (firstTwo.sheafRestrict.map coefficientTwo) :=
  (rightDerivedΓRestriction firstTwo n).naturality coefficientTwo
/-- Direct restriction agrees with restriction through the relative open subspace. -/
example (n : ℕ) :
    (firstOne.rightDerivedΓRestriction n).app integerSheaf =
    (firstTwo.rightDerivedΓRestriction n).app integerSheaf ≫
      (rightDerivedΓRestriction (X := TopCat.of firstTwo)
        ((Opens.map firstTwo.inclusion').obj firstOne) n).app
          (firstTwo.sheafRestrict.obj integerSheaf) ≫
      (relativeDerivedΓIso firstOne_le_firstTwo n).hom.app
        (((Opens.map firstTwo.inclusion').obj firstOne).sheafRestrict.obj
          (firstTwo.sheafRestrict.obj integerSheaf)) ≫
      ((Sheaf.Γ (Opens.grothendieckTopology firstOne) (ModuleCat ℤ)).rightDerived n).map
        ((nestedRestrictionIso firstOne_le_firstTwo).hom.app integerSheaf) :=
  rightDerivedΓRestriction_nested firstOne_le_firstTwo integerSheaf n
end Disconnected
namespace Empty
open scoped ZeroObject
variable {X : TopCat.{u}} {R : Type u} [CommRing R]
example (F : X.Sheaf (ModuleCat.{u} R)) (n : ℕ) :
    (rightDerivedΓRestriction (R := R) (⊥ : Opens X) n).app F = 0 := by
  have h := Functor.map_isZero
    ((Sheaf.Γ (Opens.grothendieckTopology (⊥ : Opens X)) (ModuleCat.{u} R)).rightDerived n)
    (isZero_sheaf_bot ((⊥ : Opens X).sheafRestrict.obj F))
  exact h.eq_of_tgt _ _
example (U : Opens X) (n : ℕ) :
    (rightDerivedΓRestriction (R := R) U n).app (0 : X.Sheaf (ModuleCat.{u} R)) = 0 :=
  (Functor.map_isZero _ (isZero_zero _)).eq_of_src _ _

example [Subsingleton R] (U : Opens X) (F : X.Sheaf (ModuleCat.{u} R)) (n : ℕ) :
    (rightDerivedΓRestriction (R := R) U n).app F = 0 :=
  (ModuleCat.isZero_iff_subsingleton.mpr (Module.subsingleton R _)).eq_of_src _ _

end Empty
namespace ModTwo
open TopologicalSpace.Opens
/-- The one-point space for the characteristic-two endpoint. -/
def pointSpace : TopCat := TopCat.of PUnit
/-- The constant sheaf with the native module over ZMod 2. -/
def modTwoSheaf : pointSpace.Sheaf (ModuleCat (ZMod 2)) :=
  (constantSheaf (Opens.grothendieckTopology pointSpace) (ModuleCat (ZMod 2))).obj
    (ModuleCat.of (ZMod 2) (ZMod 2))
example (n : ℕ) :
    (forget₂ (ModuleCat (ZMod 2)) AddCommGrpCat).map
        ((rightDerivedΓRestriction (⊤ : Opens pointSpace) n).app modTwoSheaf) ≫
      ((moduleCohomologyForgetComparison (TopCat.of (⊤ : Opens pointSpace)) (ZMod 2) n).app
        ((⊤ : Opens pointSpace).sheafRestrict.obj modTwoSheaf)).hom =
    ((moduleCohomologyForgetComparison pointSpace (ZMod 2) n).app modTwoSheaf).hom ≫
      (Sheaf.cohomologyPresheafEvaluationIsoFunctorH
        (Opens.grothendieckTopology pointSpace) n isTerminalTop).inv.app
          ((sheafCompose (Opens.grothendieckTopology pointSpace)
            (forget₂ (ModuleCat (ZMod 2)) AddCommGrpCat)).obj modTwoSheaf) ≫
      (((sheafCompose (Opens.grothendieckTopology pointSpace)
          (forget₂ (ModuleCat (ZMod 2)) AddCommGrpCat)).obj modTwoSheaf).cohomologyPresheaf n).map
        (homOfLE (show (⊤ : Opens pointSpace) ≤ ⊤ from le_top)).op ≫
      ((⊤ : Opens pointSpace).cohomologyPresheafObjIsoSheafRestrictH
        ((sheafCompose (Opens.grothendieckTopology pointSpace)
          (forget₂ (ModuleCat (ZMod 2)) AddCommGrpCat)).obj modTwoSheaf) n).hom := by
  exact moduleCohomologyForgetComparison_restriction (⊤ : Opens pointSpace) modTwoSheaf n
end ModTwo
variable {X : TopCat.{u}} {R : Type u} [CommRing R]
example (n : ℕ) :
    rightDerivedΓRestriction (R := R) (⊤ : Opens X) n ≫
      (rightDerivedΓRestrictionTopIso (X := X) (R := R) n).inv = 𝟙 _ := by
  rw [rightDerivedΓRestriction_top]
  exact Iso.hom_inv_id _
end TauCeti.Examples.DerivedRestriction
