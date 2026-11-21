/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Basic
public import TauCeti.Combinatorics.PlanarMatching.Duality
public import TauCeti.Combinatorics.PlanarMatching.Monoidal

/-!
# Rigid and pivotal structure of the Temperley–Lieb diagram category

Every object `TLDiagCat.of n` of the Temperley–Lieb diagram category is self-dual, with
coevaluation the nested cup `TauCeti.TLDiagCat.nestedCup n : 𝟙_ TLDiagCat ⟶ of n ⊗ of n` and
evaluation the nested cap `TauCeti.TLDiagCat.nestedCap n : of n ⊗ of n ⟶ 𝟙_ TLDiagCat`. This
makes `TauCeti.TLDiagCat` a rigid monoidal category (`RigidCategory TLDiagCat`) in which every
object equals its own left and right dual (`Xᘁ = X`, `ᘁX = X`).

Both the right and left adjoint mates of a morphism `f : X ⟶ Y` coincide with its 180-degree
rotation `TLDiagram.verticalReflect X.as Y.as (TLDiagram.reflect X.as Y.as f.diagram)`
(`TauCeti.TLDiagCat.diagram_rightAdjointMate`,
`TauCeti.TLDiagCat.leftAdjointMate_eq_rightAdjointMate`),
so the double right dual functor is strictly the identity on objects and morphisms. The dual
tensor comparison `rightDualTensorIso X Y` is the equality-induced isomorphism from
`Nat.add_comm X.as Y.as`, so the double dual tensor and unit comparisons are identities, and the
identity natural isomorphism makes `TLDiagCat` a pivotal category (`PivotalCategory TLDiagCat`).

## Main definitions

* `TauCeti.TLDiagCat.nestedCup`, `TauCeti.TLDiagCat.nestedCap`: the nested cup and cap morphisms
  in `TLDiagCat`.
* `TauCeti.TLDiagCat.exactPairingSelf`, `RightRigidCategory TauCeti.TLDiagCat`,
  `LeftRigidCategory TauCeti.TLDiagCat`, `RigidCategory TauCeti.TLDiagCat`: self-duality and
  rigidity of `TLDiagCat`.
* `PivotalCategory TauCeti.TLDiagCat`: the trivial pivotal structure on `TLDiagCat`.

## Main results

* `TauCeti.TLDiagCat.nestedCup_comp_nestedCap`: composing the nested cup and cap yields
  `(End.of TLDiagCat.circle ^ n).asHom`.
* `TauCeti.TLDiagCat.diagram_rightAdjointMate`,
  `TauCeti.TLDiagCat.leftAdjointMate_eq_rightAdjointMate`,
  `TauCeti.TLDiagCat.rightAdjointMate_rightAdjointMate`: both mates are 180-degree rotation.
* `TauCeti.TLDiagCat.rightDualTensorIso_eq`, `TauCeti.TLDiagCat.rightDualUnitIso_eq`: the dual
  monoidal comparisons are equality-induced.
* `TauCeti.TLDiagCat.pivotalIsoApp_eq_refl`: the pivotal isomorphism at every object is `Iso.refl`.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
-/

public section

open CategoryTheory MonoidalCategory ExactPairing

namespace TauCeti

namespace TLDiagCat

/-! ### Nested cups and caps in `TLDiagCat` -/

/-- The **nested cup** `𝟙_ TLDiagCat ⟶ of n ⊗ of n` on `n` strands. -/
def nestedCup (n : ℕ) : 𝟙_ TLDiagCat ⟶ of n ⊗ of n :=
  Hom.mk (TLDiagram.nestedCup n)

/-- The **nested cap** `of n ⊗ of n ⟶ 𝟙_ TLDiagCat` on `n` strands. -/
def nestedCap (n : ℕ) : of n ⊗ of n ⟶ 𝟙_ TLDiagCat :=
  Hom.mk (TLDiagram.nestedCap n)

@[simp]
theorem diagram_nestedCup (n : ℕ) : (nestedCup n).diagram = TLDiagram.nestedCup n := (rfl)

@[simp]
theorem diagram_nestedCap (n : ℕ) : (nestedCap n).diagram = TLDiagram.nestedCap n := (rfl)

/-- On one strand, the nested cup is `TLDiagCat.cup`. -/
@[simp]
theorem nestedCup_one : nestedCup 1 = cup :=
  hom_ext (by rw [diagram_nestedCup, diagram_cup, TLDiagram.nestedCup_one])

/-- On one strand, the nested cap is `TLDiagCat.cap`. -/
@[simp]
theorem nestedCap_one : nestedCap 1 = cap :=
  hom_ext (by rw [diagram_nestedCap, diagram_cap, TLDiagram.nestedCap_one])

/-- On zero strands, the nested cup is the identity of `𝟙_ TLDiagCat`. -/
@[simp]
theorem nestedCup_zero : nestedCup 0 = 𝟙 (𝟙_ TLDiagCat) :=
  hom_ext (by rw [diagram_nestedCup, diagram_id]; exact TLDiagram.nestedCup_zero)

/-- On zero strands, the nested cap is the identity of `𝟙_ TLDiagCat`. -/
@[simp]
theorem nestedCap_zero : nestedCap 0 = 𝟙 (𝟙_ TLDiagCat) :=
  hom_ext (by rw [diagram_nestedCap, diagram_id]; exact TLDiagram.nestedCap_zero)

/-- Composing the nested cup and nested cap on `n` strands produces `n` closed circles. -/
@[simp]
theorem nestedCup_comp_nestedCap (n : ℕ) :
    nestedCup n ≫ nestedCap n = ((End.of circle) ^ n).asHom :=
  hom_ext (by rw [diagram_comp, diagram_nestedCup, diagram_nestedCap,
    TLDiagram.nestedCup_comp_nestedCap, diagram_circle_pow])

/-! ### Self-duality and rigidity -/

/-- Every object `X` of `TLDiagCat` is self-dual, via the nested cup and nested cap on `X.as`
strands. -/
instance exactPairingSelf (X : TLDiagCat) : ExactPairing X X where
  coevaluation' := nestedCup X.as
  evaluation' := nestedCap X.as
  coevaluation_evaluation' := by
    refine hom_ext ?_
    rw [associator_inv, rightUnitor_hom, leftUnitor_inv, eqToHom_trans, diagram_eqToHom,
      diagram_comp, diagram_eqToHom_comp, diagram_whiskerLeft, diagram_whiskerRight,
      diagram_nestedCup, diagram_nestedCap]
    have hcast : TLDiagram.cast (Nat.add_zero X.as).symm (Nat.zero_add X.as).symm
        (TLDiagram.id X.as) =
        TLDiagram.cast rfl (by omega : X.as + 0 = 0 + X.as) (TLDiagram.id (X.as + 0)) := by
      rw [← TLDiagram.cast_id (Nat.add_zero X.as).symm, TLDiagram.cast_cast]
    exact (TLDiagram.zigzag_right X.as).trans hcast
  evaluation_coevaluation' := by
    refine hom_ext ?_
    rw [associator_hom, leftUnitor_hom, rightUnitor_inv, eqToHom_trans, diagram_eqToHom,
      diagram_comp, diagram_eqToHom_comp, diagram_whiskerRight, diagram_whiskerLeft,
      diagram_nestedCup, diagram_nestedCap]
    have hcast : TLDiagram.cast (Nat.zero_add X.as).symm (Nat.add_zero X.as).symm
        (TLDiagram.id X.as) =
        TLDiagram.cast rfl (by omega : 0 + X.as = X.as + 0) (TLDiagram.id (0 + X.as)) := by
      rw [← TLDiagram.cast_id (Nat.zero_add X.as).symm, TLDiagram.cast_cast]
    exact (TLDiagram.zigzag_left X.as).trans hcast

/-- `TLDiagCat` is right rigid, with every object as its own right dual. -/
instance : RightRigidCategory TLDiagCat where
  rightDual X := { rightDual := X, exact := exactPairingSelf X }

/-- `TLDiagCat` is left rigid, with every object as its own left dual. -/
instance : LeftRigidCategory TLDiagCat where
  leftDual X := { leftDual := X, exact := exactPairingSelf X }

/-- `TLDiagCat` is a rigid monoidal category. -/
instance : RigidCategory TLDiagCat where

@[simp]
theorem rightDual_eq (X : TLDiagCat) : Xᘁ = X := (rfl)

@[simp]
theorem leftDual_eq (X : TLDiagCat) : (ᘁX : TLDiagCat) = X := (rfl)

@[simp]
theorem coevaluation_eq_nestedCup (X : TLDiagCat) : η_ X X = nestedCup X.as := (rfl)

@[simp]
theorem evaluation_eq_nestedCap (X : TLDiagCat) : ε_ X X = nestedCap X.as := (rfl)

/-- The coevaluation of the generating object `of 1` is `cup`. -/
theorem coevaluation_of_one : η_ (of 1) (of 1) = cup :=
  nestedCup_one

/-- The evaluation of the generating object `of 1` is `cap`. -/
theorem evaluation_of_one : ε_ (of 1) (of 1) = cap :=
  nestedCap_one

/-! ### Adjoint mates and dual comparisons -/

/-- The right adjoint mate `fᘁ` of `f : X ⟶ Y` has underlying diagram the 180-degree rotation
`TLDiagram.verticalReflect X.as Y.as (TLDiagram.reflect X.as Y.as f.diagram)`. -/
theorem diagram_rightAdjointMate {X Y : TLDiagCat} (f : X ⟶ Y) :
    (fᘁ).diagram = TLDiagram.verticalReflect X.as Y.as (TLDiagram.reflect X.as Y.as f.diagram) := by
  have h : fᘁ = (ρ_ Y).inv ≫
      (Y ◁ (η_ X X ≫ f ▷ X) ≫ (α_ Y Y X).inv ≫ ε_ Y Y ▷ X) ≫ (λ_ X).hom := by
    simp only [rightAdjointMate, MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rfl
  rw [h, rightUnitor_inv, associator_inv, leftUnitor_hom, diagram_eqToHom_comp,
    diagram_comp_eqToHom, TLDiagram.cast_cast, diagram_comp, diagram_eqToHom_comp,
    diagram_whiskerLeft, diagram_comp, diagram_whiskerRight, diagram_whiskerRight,
    coevaluation_eq_nestedCup, evaluation_eq_nestedCap, diagram_nestedCup, diagram_nestedCap]
  exact TLDiagram.rightMate_eq f.diagram

/-- Taking the right adjoint mate twice is the identity on morphisms of `TLDiagCat`. -/
@[simp]
theorem rightAdjointMate_rightAdjointMate {X Y : TLDiagCat} (f : X ⟶ Y) : (fᘁ)ᘁ = f := by
  refine hom_ext ?_
  rw [diagram_rightAdjointMate, diagram_rightAdjointMate]
  -- `Xᘁ = X` and `Yᘁ = Y` definitionally.
  change TLDiagram.verticalReflect Y.as X.as (TLDiagram.reflect Y.as X.as
    (TLDiagram.verticalReflect X.as Y.as (TLDiagram.reflect X.as Y.as f.diagram))) = f.diagram
  rw [← TLDiagram.reflect_verticalReflect, TLDiagram.verticalReflect_verticalReflect,
    TLDiagram.reflect_reflect]

/-- In `TLDiagCat`, the left and right adjoint mates of every morphism coincide. -/
@[simp]
theorem leftAdjointMate_eq_rightAdjointMate {X Y : TLDiagCat} (f : X ⟶ Y) : (ᘁf) = fᘁ := by
  calc (ᘁf) = (ᘁ((fᘁ)ᘁ)) := by rw [rightAdjointMate_rightAdjointMate]
    _ = fᘁ := leftAdjointMate_rightAdjointMate (fᘁ)

/-- The left adjoint mate `ᘁf` of `f : X ⟶ Y` is also the 180-degree rotation of `f`. -/
theorem diagram_leftAdjointMate {X Y : TLDiagCat} (f : X ⟶ Y) :
    (ᘁf).diagram = TLDiagram.verticalReflect X.as Y.as (TLDiagram.reflect X.as Y.as f.diagram) := by
  rw [leftAdjointMate_eq_rightAdjointMate, diagram_rightAdjointMate]

private theorem rightAdjointMate_eqToHom {X Y : TLDiagCat} (h : X = Y) :
    (eqToHom h)ᘁ = eqToHom h.symm := by
  subst h; exact rightAdjointMate_id

/-- The dual tensor comparison `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ` is the equality-induced isomorphism from
`Nat.add_comm X.as Y.as`. -/
theorem rightDualTensorIso_eq (X Y : TLDiagCat) :
    rightDualTensorIso X Y = eqToIso (congrArg of (Nat.add_comm X.as Y.as)) := by
  refine Iso.ext (rightHom_ext (X := X ⊗ Y) ?_)
  rw [rightDualTensorIso_hom_whiskerRight_evaluation]
  refine hom_ext ?_
  symm
  -- Unfold `Xᘁ = X`, `Yᘁ = Y`, `eqToIso.hom`, and `ε_ (X ⊗ Y) (X ⊗ Y) = nestedCap`.
  change (eqToHom (congrArg of (Nat.add_comm X.as Y.as)) ▷ (X ⊗ Y) ≫
    @ExactPairing.evaluation TLDiagCat _ _ (X ⊗ Y) (Y ⊗ X) ExactPairing.tensor).diagram =
    (nestedCap (X.as + Y.as)).diagram
  have hev : @ExactPairing.evaluation TLDiagCat _ _ (X ⊗ Y) (Y ⊗ X) ExactPairing.tensor =
      eqToHom (congrArg of (by omega : Y.as + X.as + (X.as + Y.as) =
        Y.as + (X.as + X.as + Y.as))) ≫
        Y ◁ (nestedCap X.as ▷ Y) ≫
        eqToHom (congrArg of (by omega : Y.as + (0 + Y.as) = Y.as + Y.as)) ≫
        nestedCap Y.as := by
    simp [ExactPairing.tensor_evaluation, monoidalComp, associator_hom, associator_inv,
      leftUnitor_hom, whiskerLeft_eqToHom, eqToHom_trans, evaluation_eq_nestedCap]
  rw [hev, ← Category.assoc (eqToHom _ ▷ _), eqToHom_whiskerRight,
    eqToHom_trans, diagram_eqToHom_comp, diagram_comp, diagram_eqToHom_comp, diagram_whiskerLeft,
    diagram_whiskerRight, diagram_nestedCap, diagram_nestedCap,
    TLDiagram.id_tensor_nestedCap_comp_nestedCap, TLDiagram.cast_cast]
  have hcap : ∀ {a b : ℕ} (h : a = b),
      TLDiagram.cast (by omega : a + a = b + b) rfl (TLDiagram.nestedCap a) =
        TLDiagram.nestedCap b := fun h => by subst h; simp
  exact hcap (Nat.add_comm Y.as X.as)

/-- The canonical identification `(𝟙_ TLDiagCat)ᘁ ≅ 𝟙_ TLDiagCat` is the identity isomorphism. -/
theorem rightDualUnitIso_eq :
    rightDualUnitIso TLDiagCat = Iso.refl (𝟙_ TLDiagCat) := by
  refine Iso.ext
    (@rightHom_ext TLDiagCat _ _ (𝟙_ TLDiagCat) (𝟙_ TLDiagCat) (𝟙_ TLDiagCat) exactPairingUnit _ _
      ?_)
  rw [rightDualUnitIso_hom,
    rightDualIso_hom_whiskerRight_evaluation (RightRigidCategory.rightDual (𝟙_ TLDiagCat)).exact
      exactPairingUnit]
  -- Unfold `(𝟙_ TLDiagCat)ᘁ = 𝟙_ TLDiagCat` and the unit pairing evaluation `(ρ_ _).hom`.
  change nestedCap 0 = (Iso.refl (𝟙_ TLDiagCat)).hom ▷ 𝟙_ TLDiagCat ≫ (ρ_ (𝟙_ TLDiagCat)).hom
  rw [nestedCap_zero, Iso.refl_hom, id_whiskerRight, Category.id_comp, rightUnitor_hom]
  simp; rfl

/-! ### Pivotal and spherical structure -/

open Functor.LaxMonoidal Functor.OplaxMonoidal in
/-- `TLDiagCat` is a **pivotal category**, with trivial pivotal isomorphism `φ_X = 𝟙 X`. -/
noncomputable instance : PivotalCategory TLDiagCat where
  pivotalIso := NatIso.ofComponents (fun X => Iso.refl X) fun f => by
    dsimp only [Functor.id_map, Iso.refl_hom]
    rw [doubleRightDualFunctor_map, rightAdjointMate_rightAdjointMate]
    -- `Xᘁᘁ = X` and `Yᘁᘁ = Y` definitionally.
    change f ≫ 𝟙 _ = 𝟙 _ ≫ f
    rw [Category.comp_id, Category.id_comp]
  pivotalIso_isMonoidal :=
    { unit := by
        rw [doubleRightDualFunctor_ε_eq_rightAdjointMate, ← rightDualUnitIso_inv,
          ← rightDualUnitIso_hom, rightDualUnitIso_eq]
        -- Unfold the identity functor's unit comparison `ε (𝟭 _) = 𝟙 _` and `Iso.refl`.
        change 𝟙 (𝟙_ TLDiagCat) ≫ 𝟙 (𝟙_ TLDiagCat) =
          𝟙 (𝟙_ TLDiagCat) ≫ @rightAdjointMate TLDiagCat _ _ _ _ (RightRigidCategory.rightDual _)
            (RightRigidCategory.rightDual (𝟙_ TLDiagCat)) (𝟙 (𝟙_ TLDiagCat))
        rw [Category.id_comp, Category.id_comp]
        exact (@rightAdjointMate_id TLDiagCat _ _ (𝟙_ TLDiagCat)
          (RightRigidCategory.rightDual (𝟙_ TLDiagCat))).symm
      tensor := fun X Y => by
        rw [doubleRightDualFunctor_μ]
        -- Unfold the identity functor's tensor comparison `μ (𝟭 _) = 𝟙 _` and `Iso.refl`.
        change 𝟙 (X ⊗ Y) ≫ 𝟙 (X ⊗ Y) = (𝟙 X ⊗ₘ 𝟙 Y) ≫
          (rightDualTensorIso Y X).inv ≫ ((rightDualTensorIso X Y).hom)ᘁ
        rw [id_tensorHom_id, Category.id_comp, Category.id_comp,
          rightDualTensorIso_eq, rightDualTensorIso_eq, eqToIso.inv, eqToIso.hom,
          rightAdjointMate_eqToHom, eqToHom_trans, eqToHom_refl] }

@[simp]
theorem pivotalIsoApp_eq_refl (X : TLDiagCat) : pivotalIsoApp X = Iso.refl X :=
  Iso.ext (by rw [← pivotalIso_hom_app]; rfl)

end TLDiagCat

end TauCeti
