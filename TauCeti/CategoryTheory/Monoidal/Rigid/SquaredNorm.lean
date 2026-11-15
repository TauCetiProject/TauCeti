/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Rigid.DualFunctor
public import TauCeti.CategoryTheory.Monoidal.Rigid.Simple
public import TauCeti.CategoryTheory.Monoidal.Scalar
public import TauCeti.CategoryTheory.Semisimple.Basic

/-!
# Bidual traces and squared norms in a rigid category

In a right rigid monoidal category `C`, an object `X` need not come with a pivotal identification
`X ≅ Xᘁᘁ`, so an endomorphism `X ⟶ X` has no canonical trace. A morphism `a : X ⟶ Xᘁᘁ` into the
double right dual *can* be closed into a scalar loop without any pivotal structure:

`doubleDualTrace a = η_ X Xᘁ ≫ a ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ : 𝟙_ C ⟶ 𝟙_ C`.

For an isomorphism `a : X ≅ Xᘁᘁ`, Etingof–Nikshych–Ostrik define the **squared norm** of `X` with
respect to `a` as the composite scalar

`squaredNorm a = doubleDualTrace a.hom ≫ doubleDualTrace (a.inv)ᘁ : 𝟙_ C ⟶ 𝟙_ C`.

On a general object, `squaredNorm a` depends on `a`: in finite-dimensional vector spaces, `X = k²`
with `a = 𝟙` has squared norm `4`, while `a = diag(1, 2)` has squared norm `(1 + 2)(1 + 1/2) = 9/2`.
However, when `X` has scalar endomorphisms over a commutative semiring `R`, any two isomorphisms
`a, b : X ≅ Xᘁᘁ` differ by a mutually inverse pair of scalar automorphisms of `X`, whose scalars
scale `doubleDualTrace a.hom` and `doubleDualTrace (a.inv)ᘁ` by inverse factors and cancel in
`squaredNorm` (`TauCeti.squaredNorm_congr`). Thus the squared norm of an object with scalar
endomorphisms—and in particular of a split simple object—is an intrinsic invariant of the rigid
category, requiring no pivotal structure.

We also establish the basic calculus of `doubleDualTrace` and `squaredNorm`:
* twisted cyclicity `doubleDualTrace (c ≫ fᘁᘁ) = doubleDualTrace (f ≫ c)`, giving invariance under
  conjugation by an isomorphism (`TauCeti.doubleDualTrace_conj`, `TauCeti.squaredNorm_conj`);
* invariance under the double right dual functor
  (`TauCeti.doubleDualTrace_rightAdjointMate_rightAdjointMate`),
  so the dual isomorphism `(a.inv)ᘁ : Xᘁ ≅ Xᘁᘁᘁ` has the same squared norm as `a`
  (`TauCeti.squaredNorm_symm_rightAdjointMate`);
* normalization on the tensor unit (`TauCeti.doubleDualTrace_doubleRightDualFunctor_ε`,
  `TauCeti.squaredNorm_εIso_doubleRightDualFunctor`) and vanishing on zero objects;
* additivity and `R`-linearity of `doubleDualTrace`;
* invertibility (and hence nonvanishing) of `doubleDualTrace a.hom` and `squaredNorm a` for a split
  simple object `X` in a finite semisimple category with simple tensor unit
  (`TauCeti.isIso_doubleDualTrace_of_simple`, `TauCeti.isIso_squaredNorm_of_simple`).

## Main declarations

* `TauCeti.doubleDualTrace`: the scalar trace `𝟙_ C ⟶ 𝟙_ C` of a morphism `X ⟶ Xᘁᘁ`;
* `TauCeti.squaredNorm`: the squared norm `doubleDualTrace a.hom ≫ doubleDualTrace (a.inv)ᘁ` of
  an isomorphism `a : X ≅ Xᘁᘁ`;
* `TauCeti.doubleDualTrace_comp_rightAdjointMate_rightAdjointMate`, `TauCeti.doubleDualTrace_conj`
  and `TauCeti.squaredNorm_conj`: twisted cyclicity and isomorphism invariance;
* `TauCeti.doubleDualTrace_rightAdjointMate_rightAdjointMate` and
  `TauCeti.squaredNorm_symm_rightAdjointMate`: invariance under taking double duals and right duals;
* `TauCeti.doubleDualTrace_doubleRightDualFunctor_ε` and
  `TauCeti.squaredNorm_εIso_doubleRightDualFunctor`: unit values;
* `TauCeti.squaredNorm_congr`: independence of `a : X ≅ Xᘁᘁ` when `X` has scalar endomorphisms;
* `TauCeti.isIso_doubleDualTrace_of_simple`, `TauCeti.doubleDualTrace_ne_zero_of_simple`,
  `TauCeti.isIso_squaredNorm_of_simple` and `TauCeti.squaredNorm_ne_zero_of_simple`:
  invertibility and nonvanishing on split simple objects when `𝟙_ C` is simple.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005), §2.1,
  Proposition 2.1 and Definition 2.2
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.21
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory ExactPairing
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped ZeroObject

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section RightRigid

variable [RightRigidCategory C]

/-- The trace `η_ X Xᘁ ≫ a ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ` of a morphism `a : X ⟶ Xᘁᘁ`, closed with the
evaluation of `(Xᘁ, Xᘁᘁ)` without choosing a pivotal structure. -/
noncomputable def doubleDualTrace {X : C} (a : X ⟶ (Xᘁ : C)ᘁ) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ X (Xᘁ : C) ≫ a ▷ (Xᘁ : C) ≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C)

/-- **The squared norm** of `X` with respect to an isomorphism `a : X ≅ Xᘁᘁ`
(Etingof–Nikshych–Ostrik, *On fusion categories*, §2.1): `Tr(a) ≫ Tr((a⁻¹)ᘁ)`. -/
noncomputable def squaredNorm {X : C} (a : X ≅ (Xᘁ : C)ᘁ) : 𝟙_ C ⟶ 𝟙_ C :=
  doubleDualTrace a.hom ≫ doubleDualTrace (rightAdjointMate a.inv)

/-- The defining formula of `TauCeti.doubleDualTrace`. -/
theorem doubleDualTrace_def {X : C} (a : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace a = η_ X (Xᘁ : C) ≫ a ▷ (Xᘁ : C) ≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) :=
  (rfl)

/-- The defining formula of `TauCeti.squaredNorm`. -/
theorem squaredNorm_def {X : C} (a : X ≅ (Xᘁ : C)ᘁ) :
    squaredNorm a = doubleDualTrace a.hom ≫ doubleDualTrace (rightAdjointMate a.inv) :=
  (rfl)

/-- For an isomorphism `a : X ≅ Xᘁᘁ`, `doubleDualTrace a.hom` is the coevaluation of `(X, Xᘁ)`
followed by the evaluation of `exactPairingCongrRight a : ExactPairing Xᘁ X`. -/
theorem doubleDualTrace_hom_eq_exactPairingCongrRight_evaluation {X : C} (a : X ≅ (Xᘁ : C)ᘁ) :
    doubleDualTrace a.hom =
      η_ X (Xᘁ : C) ≫ @evaluation C _ _ (Xᘁ : C) X (exactPairingCongrRight a) := by
  rw [doubleDualTrace_def, exactPairingCongrRight_evaluation]

/-- A scalar acting on `X` from the left factors out of `doubleDualTrace`. -/
theorem doubleDualTrace_scalar_whiskerRight_comp {X : C} (d : 𝟙_ C ⟶ 𝟙_ C)
    (a : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace ((λ_ X).inv ≫ d ▷ X ≫ (λ_ X).hom ≫ a) = d ≫ doubleDualTrace a := by
  have h : η_ X (Xᘁ : C) ≫ ((λ_ X).inv ≫ d ▷ X ≫ (λ_ X).hom ≫ a) ▷ (Xᘁ : C) =
      d ≫ η_ X (Xᘁ : C) ≫ a ▷ (Xᘁ : C) := by
    calc
      _ = (η_ X (Xᘁ : C) ≫ (λ_ (X ⊗ (Xᘁ : C))).inv) ≫ d ▷ (X ⊗ (Xᘁ : C)) ≫
            (λ_ (X ⊗ (Xᘁ : C))).hom ≫ a ▷ (Xᘁ : C) := by monoidal
      _ = _ := by rw [comp_scalar_whiskerRight_assoc]; simp
  rw [doubleDualTrace_def, doubleDualTrace_def, reassoc_of% h]

/-- **Twisted cyclicity** of `doubleDualTrace`: for `f : X ⟶ Y` and `c : Y ⟶ Xᘁᘁ`,
`doubleDualTrace (c ≫ fᘁᘁ) = doubleDualTrace (f ≫ c)`. -/
theorem doubleDualTrace_comp_rightAdjointMate_rightAdjointMate {X Y : C} (f : X ⟶ Y)
    (c : Y ⟶ (Xᘁ : C)ᘁ) : doubleDualTrace (c ≫ fᘁᘁ) = doubleDualTrace (f ≫ c) := by
  rw [doubleDualTrace_def, doubleDualTrace_def, comp_whiskerRight_assoc,
    rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc,
    coevaluation_comp_rightAdjointMate_assoc, ← comp_whiskerRight_assoc]

/-- `doubleDualTrace` is invariant under conjugation by an isomorphism `e : X ≅ Y`. -/
theorem doubleDualTrace_conj {X Y : C} (e : X ≅ Y) (a : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace (e.inv ≫ a ≫ e.homᘁᘁ) = doubleDualTrace a := by
  rw [← Category.assoc, doubleDualTrace_comp_rightAdjointMate_rightAdjointMate,
    Iso.hom_inv_id_assoc]

/-- Transporting `a : X ≅ Xᘁᘁ` along an isomorphism `e : X ≅ Y` preserves `squaredNorm`. -/
theorem squaredNorm_conj {X Y : C} (e : X ≅ Y) (a : X ≅ (Xᘁ : C)ᘁ) :
    squaredNorm (e.symm ≪≫ a ≪≫ (doubleRightDualFunctor C).mapIso e) = squaredNorm a := by
  -- Name the transported isomorphism with explicit target `Yᘁᘁ` so `rw` can unfold `squaredNorm`
  -- without traversing `(doubleRightDualFunctor C).obj Y` at implicit transparency.
  let b : Y ≅ ((Yᘁ : C)ᘁ : C) := e.symm ≪≫ a ≪≫ (doubleRightDualFunctor C).mapIso e
  have hb_hom : b.hom = e.inv ≫ a.hom ≫ e.homᘁᘁ := rfl
  have hb_inv_raw : b.inv = (e.invᘁᘁ ≫ a.inv) ≫ e.hom := rfl
  have hb_inv : rightAdjointMate b.inv =
      (e.rightAdjointMate).symm.inv ≫ rightAdjointMate a.inv ≫
        ((e.rightAdjointMate).symm.hom)ᘁᘁ := by
    rw [hb_inv_raw]
    simp only [comp_rightAdjointMate, Category.assoc, Iso.symm_inv, Iso.symm_hom,
      Iso.rightAdjointMate_hom, Iso.rightAdjointMate_inv]
  have key : squaredNorm b = squaredNorm a := by
    rw [squaredNorm_def, squaredNorm_def, hb_hom, hb_inv, doubleDualTrace_conj,
      doubleDualTrace_conj]
  exact key

/-- Taking the double right mate preserves `doubleDualTrace`. -/
@[simp]
theorem doubleDualTrace_rightAdjointMate_rightAdjointMate {X : C} (a : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace (aᘁᘁ) = doubleDualTrace a := by
  -- Chain `Eq.trans` steps so expressions typed via `(doubleRightDualFunctor C).obj` are not
  -- rewritten alongside `Xᘁᘁ` at implicit transparency.
  have hμ : μ (doubleRightDualFunctor C) X (Xᘁ : C) ≫
      (doubleRightDualFunctor C).map (a ▷ (Xᘁ : C)) ≫
      δ (doubleRightDualFunctor C) ((Xᘁ : C)ᘁ : C) (Xᘁ : C) =
      aᘁᘁ ▷ (((Xᘁ : C)ᘁ : C)ᘁ : C) := by
    rw [← Functor.LaxMonoidal.μ_natural_left_assoc, Functor.Monoidal.μ_δ, Category.comp_id]
    rfl
  have hmap : (doubleRightDualFunctor C).map (doubleDualTrace a) =
      η (doubleRightDualFunctor C) ≫ doubleDualTrace (aᘁᘁ) ≫ ε (doubleRightDualFunctor C) := by
    rw [doubleDualTrace_def a, doubleDualTrace_def (aᘁᘁ), Category.assoc, Category.assoc,
      Functor.map_comp, Functor.map_comp]
    refine (congrArg₂ (· ≫ ·) (doubleRightDualFunctor_map_coevaluation X)
      (congrArg₂ (· ≫ ·) rfl (doubleRightDualFunctor_map_evaluation (Xᘁ : C)))).trans ?_
    refine (Category.assoc _ _ _).trans (congrArg (η (doubleRightDualFunctor C) ≫ ·) ?_)
    refine (Category.assoc _ _ _).trans
      (congrArg (η_ ((Xᘁ : C)ᘁ : C) (((Xᘁ : C)ᘁ : C)ᘁ : C) ≫ ·) ?_)
    let m₁ := μ (doubleRightDualFunctor C) X (Xᘁ : C)
    let m₂ := (doubleRightDualFunctor C).map (a ▷ (Xᘁ : C))
    let m₃ := δ (doubleRightDualFunctor C) ((Xᘁ : C)ᘁ : C) (Xᘁ : C)
    let r := ε_ (((Xᘁ : C)ᘁ : C)ᘁ : C) ((((Xᘁ : C)ᘁ : C)ᘁ : C)ᘁ : C) ≫ ε (doubleRightDualFunctor C)
    exact (congrArg (m₁ ≫ ·) (Category.assoc m₂ m₃ r).symm).trans
      ((Category.assoc m₁ (m₂ ≫ m₃) r).symm.trans (congrArg (· ≫ r) hμ))
  symm
  rw [← doubleRightDualFunctor_ε_comp_map_scalar_comp_η (doubleDualTrace a), hmap]
  simp only [Category.assoc]
  rw [Functor.Monoidal.ε_η_assoc, Functor.Monoidal.ε_η, Category.comp_id]

/-- **Duality invariance of the squared norm**: the dual isomorphism
`a.symm.rightAdjointMate : Xᘁ ≅ Xᘁᘁᘁ` has the same squared norm as `a : X ≅ Xᘁᘁ`. -/
@[simp]
theorem squaredNorm_symm_rightAdjointMate {X : C} (a : X ≅ (Xᘁ : C)ᘁ) :
    squaredNorm a.symm.rightAdjointMate = squaredNorm a := by
  rw [squaredNorm_def, squaredNorm_def, Iso.rightAdjointMate_hom, Iso.rightAdjointMate_inv,
    Iso.symm_hom, Iso.symm_inv, doubleDualTrace_rightAdjointMate_rightAdjointMate, scalar_comm]

/-- The `doubleDualTrace` of the unit comparison `ε (doubleRightDualFunctor C) : 𝟙_ C ⟶ (𝟙_ C)ᘁᘁ`
is the identity of `𝟙_ C`. -/
@[simp]
theorem doubleDualTrace_doubleRightDualFunctor_ε :
    doubleDualTrace (ε (doubleRightDualFunctor C)) = 𝟙 (𝟙_ C) := by
  -- Type `ε (doubleRightDualFunctor C)` with explicit iterated right duals so `rw` matches
  -- `doubleDualTrace_def` without unfolding `(doubleRightDualFunctor C).obj (𝟙_ C)`.
  let e : 𝟙_ C ⟶ (@HasRightDual.rightDual C _ _
      (@HasRightDual.rightDual C _ _ (𝟙_ C) (RightRigidCategory.rightDual (𝟙_ C)))
      (RightRigidCategory.rightDual _)) := ε (doubleRightDualFunctor C)
  have he : e =
      (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).inv ≫
        rightMate HasRightDual.exact (RightRigidCategory.rightDual (𝟙_ C)).exact
          (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).hom :=
    doubleRightDualFunctor_ε C
  have key : doubleDualTrace e = 𝟙 (𝟙_ C) := by
    rw [doubleDualTrace_def, he, comp_whiskerRight_assoc, rightMate_comp_evaluation,
      ← whisker_exchange_assoc, rightDualIso_hom, coevaluation_comp_rightMate_assoc,
      rightDualIso_inv_whiskerRight_evaluation]
    simp
  exact key

/-- For any scalar `s : 𝟙_ C ⟶ 𝟙_ C`, the `doubleDualTrace` of
`s ≫ ε (doubleRightDualFunctor C)` is `s`. -/
@[simp]
theorem doubleDualTrace_comp_doubleRightDualFunctor_ε (s : 𝟙_ C ⟶ 𝟙_ C) :
    doubleDualTrace (s ≫ ε (doubleRightDualFunctor C)) = s := by
  let e : 𝟙_ C ⟶ (@HasRightDual.rightDual C _ _
      (@HasRightDual.rightDual C _ _ (𝟙_ C) (RightRigidCategory.rightDual (𝟙_ C)))
      (RightRigidCategory.rightDual _)) := ε (doubleRightDualFunctor C)
  have key : doubleDualTrace (s ≫ e) = s := by
    rw [doubleDualTrace_def, comp_whiskerRight_assoc, comp_scalar_whiskerRight_assoc,
      ← doubleDualTrace_def]
    exact (congrArg (s ≫ ·) doubleDualTrace_doubleRightDualFunctor_ε).trans (Category.comp_id s)
  exact key

/-- The `doubleDualTrace` of `(η (doubleRightDualFunctor C))ᘁ` is the identity of `𝟙_ C`. -/
@[simp]
theorem doubleDualTrace_rightAdjointMate_doubleRightDualFunctor_η :
    doubleDualTrace (@rightAdjointMate C _ _ _ _ (RightRigidCategory.rightDual _)
      (RightRigidCategory.rightDual (𝟙_ C)) (η (doubleRightDualFunctor C))) = 𝟙 (𝟙_ C) := by
  let u := rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit
  let e : 𝟙_ C ⟶ (@HasRightDual.rightDual C _ _
      (@HasRightDual.rightDual C _ _ (𝟙_ C) (RightRigidCategory.rightDual (𝟙_ C)))
      (RightRigidCategory.rightDual _)) := ε (doubleRightDualFunctor C)
  let n : (@HasRightDual.rightDual C _ _
      (@HasRightDual.rightDual C _ _ (𝟙_ C) (RightRigidCategory.rightDual (𝟙_ C)))
      (RightRigidCategory.rightDual _)) ⟶ 𝟙_ C := η (doubleRightDualFunctor C)
  have hε : e = u.inv ≫ @rightAdjointMate C _ _ _ _ (RightRigidCategory.rightDual _)
      (RightRigidCategory.rightDual (𝟙_ C)) u.hom :=
    doubleRightDualFunctor_ε_eq_rightAdjointMate C
  have hη : n =
      @rightAdjointMate C _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C))
        (RightRigidCategory.rightDual _) u.inv ≫ u.hom :=
    (doubleRightDualFunctor_η C).trans (congrArg (· ≫ u.hom)
      (@rightAdjointMate_eq_rightMate C _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C))
        (RightRigidCategory.rightDual _) u.inv).symm)
  have hconj : @rightAdjointMate C _ _ _ _ (RightRigidCategory.rightDual _)
      (RightRigidCategory.rightDual (𝟙_ C)) n =
      u.symm.inv ≫ e ≫ rightAdjointMate (@rightAdjointMate C _ _ _ _
        (RightRigidCategory.rightDual (𝟙_ C)) (RightRigidCategory.rightDual _) u.symm.hom) := by
    rw [hη, @comp_rightAdjointMate C _ _ _ _ _ (RightRigidCategory.rightDual _)
      (RightRigidCategory.rightDual _) (RightRigidCategory.rightDual (𝟙_ C))]
    simp only [Iso.symm_inv, Iso.symm_hom, hε, Category.assoc, u.hom_inv_id_assoc]
  have key : doubleDualTrace (@rightAdjointMate C _ _ _ _ (RightRigidCategory.rightDual _)
      (RightRigidCategory.rightDual (𝟙_ C)) n) = 𝟙 (𝟙_ C) := by
    rw [hconj, @doubleDualTrace_conj C _ _ _ _ _ u.symm e]
    exact doubleDualTrace_doubleRightDualFunctor_ε
  exact key

/-- The squared norm of the unit isomorphism `Functor.Monoidal.εIso (doubleRightDualFunctor C)`
is `𝟙 (𝟙_ C)`. -/
@[simp]
theorem squaredNorm_εIso_doubleRightDualFunctor :
    squaredNorm (Functor.Monoidal.εIso (doubleRightDualFunctor C)) = 𝟙 (𝟙_ C) :=
  (squaredNorm_def _).trans (by
    refine (congrArg₂ (· ≫ ·) doubleDualTrace_doubleRightDualFunctor_ε
      doubleDualTrace_rightAdjointMate_doubleRightDualFunctor_η).trans ?_
    exact Category.id_comp _)

section Zero

variable [HasZeroMorphisms C]

/-- The `doubleDualTrace` of the zero morphism is zero. -/
@[simp]
theorem doubleDualTrace_zero (X : C) : doubleDualTrace (0 : X ⟶ (Xᘁ : C)ᘁ) = 0 := by
  simp [doubleDualTrace_def]

/-- A zero object has squared norm zero. -/
theorem squaredNorm_of_isZero {X : C} (hX : IsZero X) (a : X ≅ (Xᘁ : C)ᘁ) :
    squaredNorm a = 0 := by
  rw [squaredNorm_def, hX.eq_of_src a.hom 0, doubleDualTrace_zero, zero_comp]

/-- The zero object `0` has squared norm zero. -/
@[simp]
theorem squaredNorm_zero [HasZeroObject C] (a : (0 : C) ≅ ((0 : C)ᘁ : C)ᘁ) :
    squaredNorm a = 0 :=
  squaredNorm_of_isZero (Limits.isZero_zero C) a

end Zero

section Linear

variable [Preadditive C] [MonoidalPreadditive C]

/-- `doubleDualTrace` is additive. -/
@[simp]
theorem doubleDualTrace_add {X : C} (a b : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace (a + b) = doubleDualTrace a + doubleDualTrace b := by
  simp [doubleDualTrace_def]

/-- `doubleDualTrace` commutes with finite sums. -/
@[simp]
theorem doubleDualTrace_sum {ι : Type*} {X : C} (s : Finset ι) (f : ι → (X ⟶ (Xᘁ : C)ᘁ)) :
    doubleDualTrace (∑ i ∈ s, f i) = ∑ i ∈ s, doubleDualTrace (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih]

/-- `doubleDualTrace` commutes with negation. -/
@[simp]
theorem doubleDualTrace_neg {X : C} (a : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace (-a) = -doubleDualTrace a :=
  eq_neg_of_add_eq_zero_left (by rw [← doubleDualTrace_add, neg_add_cancel, doubleDualTrace_zero])

/-- `doubleDualTrace` commutes with subtraction. -/
@[simp]
theorem doubleDualTrace_sub {X : C} (a b : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace (a - b) = doubleDualTrace a - doubleDualTrace b := by
  rw [sub_eq_add_neg, doubleDualTrace_add, doubleDualTrace_neg, sub_eq_add_neg]

/-- `doubleDualTrace` is `R`-linear in an `R`-linear monoidal category. -/
@[simp]
theorem doubleDualTrace_smul {R : Type*} [Semiring R] [Linear R C] [MonoidalLinear R C]
    {X : C} (r : R) (a : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace (r • a) = r • doubleDualTrace a := by
  simp [doubleDualTrace_def]

end Linear

section ScalarEnd

variable (R : Type w) [CommSemiring R] [Preadditive C] [Linear R C] [MonoidalPreadditive C]
  [MonoidalLinear R C] {X : C}

/-- When `X` has scalar endomorphisms over `R`, changing `a : X ≅ Xᘁᘁ` to `b : X ≅ Xᘁᘁ` scales
`doubleDualTrace a.hom` by the scalar of `b.hom ≫ a.inv`. -/
theorem doubleDualTrace_hom_eq_smul (hX : Function.Bijective (algebraMap R (End X)))
    (a b : X ≅ (Xᘁ : C)ᘁ) :
    doubleDualTrace b.hom =
      endAlgEquivOfBijective R hX (End.of (b.hom ≫ a.inv)) • doubleDualTrace a.hom := by
  have hf : b.hom ≫ a.inv =
      endAlgEquivOfBijective R hX (End.of (b.hom ≫ a.inv)) • 𝟙 X :=
    (endAlgEquivOfBijective_smul_id hX (End.of (b.hom ≫ a.inv))).symm
  have hb : b.hom = endAlgEquivOfBijective R hX (End.of (b.hom ≫ a.inv)) • a.hom := by
    calc
      b.hom = (b.hom ≫ a.inv) ≫ a.hom := by simp
      _ = (endAlgEquivOfBijective R hX (End.of (b.hom ≫ a.inv)) • 𝟙 X) ≫ a.hom :=
        congrArg (· ≫ a.hom) hf
      _ = _ := by rw [Linear.smul_comp, Category.id_comp]
  conv_lhs => rw [hb, doubleDualTrace_smul]

/-- When `X` has scalar endomorphisms over `R`, changing `a : X ≅ Xᘁᘁ` to `b : X ≅ Xᘁᘁ` scales
`doubleDualTrace (a.inv)ᘁ` by the scalar of `a.hom ≫ b.inv`. -/
theorem doubleDualTrace_rightAdjointMate_inv_eq_smul
    (hX : Function.Bijective (algebraMap R (End X))) (a b : X ≅ (Xᘁ : C)ᘁ) :
    doubleDualTrace (rightAdjointMate b.inv) =
      endAlgEquivOfBijective R hX (End.of (a.hom ≫ b.inv)) •
        doubleDualTrace (rightAdjointMate a.inv) := by
  have hf : a.hom ≫ b.inv =
      endAlgEquivOfBijective R hX (End.of (a.hom ≫ b.inv)) • 𝟙 X :=
    (endAlgEquivOfBijective_smul_id hX (End.of (a.hom ≫ b.inv))).symm
  have hb : rightAdjointMate b.inv =
      endAlgEquivOfBijective R hX (End.of (a.hom ≫ b.inv)) • rightAdjointMate a.inv := by
    calc
      rightAdjointMate b.inv = rightAdjointMate (a.inv ≫ (a.hom ≫ b.inv)) := by simp
      _ = rightAdjointMate (a.hom ≫ b.inv) ≫ rightAdjointMate a.inv := by
        rw [comp_rightAdjointMate]
      _ = rightAdjointMate (endAlgEquivOfBijective R hX (End.of (a.hom ≫ b.inv)) • 𝟙 X) ≫
            rightAdjointMate a.inv :=
        congrArg (fun g ↦ rightAdjointMate g ≫ rightAdjointMate a.inv) hf
      _ = _ := by
        rw [rightAdjointMate_smul, rightAdjointMate_id, Linear.smul_comp, Category.id_comp]
  conv_lhs => rw [hb, doubleDualTrace_smul]

/-- **Independence of the isomorphism**: for an object `X` with scalar endomorphisms over a
commutative semiring `R`, `squaredNorm a` does not depend on the chosen isomorphism
`a : X ≅ Xᘁᘁ`. -/
theorem squaredNorm_congr (hX : Function.Bijective (algebraMap R (End X)))
    (a b : X ≅ (Xᘁ : C)ᘁ) : squaredNorm a = squaredNorm b := by
  have hmul :
      endAlgEquivOfBijective R hX (End.of (a.hom ≫ b.inv)) *
        endAlgEquivOfBijective R hX (End.of (b.hom ≫ a.inv)) = 1 := by
    rw [← map_mul, ← End.of_comp]
    simp
  rw [squaredNorm_def b, doubleDualTrace_hom_eq_smul R hX a b,
    doubleDualTrace_rightAdjointMate_inv_eq_smul R hX a b]
  simp [squaredNorm_def, smul_smul, hmul]

end ScalarEnd

end RightRigid

section Simple

variable (k : Type w) [Field k] [IsAlgClosed k]

/-- Over an algebraically closed field, the squared norm of a simple object with finite-dimensional
endomorphisms does not depend on the chosen isomorphism to its double dual. -/
theorem squaredNorm_congr_of_simple [RightRigidCategory C] [Preadditive C] [HasKernels C]
    [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C] {X : C} [Simple X]
    [FiniteDimensional k (X ⟶ X)] (a b : X ≅ (Xᘁ : C)ᘁ) :
    squaredNorm a = squaredNorm b :=
  squaredNorm_congr k (bijective_algebraMap_end_of_simple k X) a b

section FiniteSemisimple

variable [Abelian C] [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)]

include k in
/-- In a finite semisimple right rigid category with simple tensor unit, `doubleDualTrace a.hom`
is an isomorphism (an invertible scalar of `𝟙_ C`) for every split simple object `X` and every
isomorphism `a : X ≅ Xᘁᘁ`. -/
theorem isIso_doubleDualTrace_of_simple [RightRigidCategory C] {X : C} [Simple X]
    [FiniteDimensional k (X ⟶ X)] (a : X ≅ (Xᘁ : C)ᘁ) :
    IsIso (doubleDualTrace a.hom) := by
  have : IsSplitMono (η_ X (Xᘁ : C)) :=
    isSplitMono_of_nonzero_from_simple (coevaluation_ne_zero (Simple.not_isZero X))
  let := exactPairingCongrRight (X := (Xᘁ : C)) a
  obtain ⟨c, hc⟩ := hom_tensorUnit_eq_smul_evaluation_of_simple_right k
    (retraction (η_ X (Xᘁ : C)))
  have h : (c • 𝟙 (𝟙_ C)) ≫ doubleDualTrace a.hom = 𝟙 (𝟙_ C) := by
    rw [Linear.smul_comp, Category.id_comp,
      doubleDualTrace_hom_eq_exactPairingCongrRight_evaluation, ← Linear.comp_smul, ← hc]
    exact IsSplitMono.id _
  exact ⟨⟨c • 𝟙 (𝟙_ C), by rw [scalar_comm, h], h⟩⟩

include k in
/-- In a finite semisimple right rigid category with simple tensor unit, `doubleDualTrace a.hom`
is a unit in `End (𝟙_ C)` for every split simple object `X` and `a : X ≅ Xᘁᘁ`. -/
theorem isUnit_of_doubleDualTrace_of_simple [RightRigidCategory C] {X : C} [Simple X]
    [FiniteDimensional k (X ⟶ X)] (a : X ≅ (Xᘁ : C)ᘁ) :
    IsUnit (End.of (doubleDualTrace a.hom)) :=
  have := isIso_doubleDualTrace_of_simple k a
  (isUnit_iff_isIso (End.of (doubleDualTrace a.hom))).2 inferInstance

include k in
/-- In a finite semisimple right rigid category with simple tensor unit, `doubleDualTrace a.hom`
is nonzero for every split simple object `X` and `a : X ≅ Xᘁᘁ`. -/
theorem doubleDualTrace_ne_zero_of_simple [RightRigidCategory C] {X : C} [Simple X]
    [FiniteDimensional k (X ⟶ X)] (a : X ≅ (Xᘁ : C)ᘁ) :
    doubleDualTrace a.hom ≠ 0 := by
  have := isIso_doubleDualTrace_of_simple k a
  intro h
  have hid : 𝟙 (𝟙_ C) = 0 :=
    (IsIso.hom_inv_id _).symm.trans ((congrArg (· ≫ inv (doubleDualTrace a.hom)) h).trans
      zero_comp)
  exact CategoryTheory.id_ne_zero (𝟙_ C) hid

include k in
/-- In a finite semisimple rigid category with simple tensor unit,
`doubleDualTrace (a.inv)ᘁ` is an isomorphism for every split simple object `X` and
`a : X ≅ Xᘁᘁ`. -/
theorem isIso_doubleDualTrace_rightAdjointMate_of_simple [RigidCategory C] {X : C} [Simple X]
    [FiniteDimensional k (X ⟶ X)] (a : X ≅ (Xᘁ : C)ᘁ) :
    IsIso (doubleDualTrace (rightAdjointMate a.inv)) := by
  have : FiniteDimensional k ((Xᘁ : C) ⟶ (Xᘁ : C)) :=
    (rightAdjointMateLinearEquiv k X X).finiteDimensional
  simpa using isIso_doubleDualTrace_of_simple k a.symm.rightAdjointMate

include k in
/-- In a finite semisimple rigid category with simple tensor unit,
`doubleDualTrace (a.inv)ᘁ` is nonzero for every split simple object `X` and `a : X ≅ Xᘁᘁ`. -/
theorem doubleDualTrace_rightAdjointMate_ne_zero_of_simple [RigidCategory C] {X : C} [Simple X]
    [FiniteDimensional k (X ⟶ X)] (a : X ≅ (Xᘁ : C)ᘁ) :
    doubleDualTrace (rightAdjointMate a.inv) ≠ 0 := by
  have : FiniteDimensional k ((Xᘁ : C) ⟶ (Xᘁ : C)) :=
    (rightAdjointMateLinearEquiv k X X).finiteDimensional
  simpa using doubleDualTrace_ne_zero_of_simple k a.symm.rightAdjointMate

include k in
/-- In a finite semisimple rigid category with simple tensor unit, `squaredNorm a` is an
isomorphism for every split simple object `X` and `a : X ≅ Xᘁᘁ`. -/
theorem isIso_squaredNorm_of_simple [RigidCategory C] {X : C} [Simple X]
    [FiniteDimensional k (X ⟶ X)] (a : X ≅ (Xᘁ : C)ᘁ) :
    IsIso (squaredNorm a) := by
  have := isIso_doubleDualTrace_of_simple k a
  have := isIso_doubleDualTrace_rightAdjointMate_of_simple k a
  rw [squaredNorm_def]
  infer_instance

include k in
/-- In a finite semisimple rigid category with simple tensor unit, `squaredNorm a` is a unit in
`End (𝟙_ C)` for every split simple object `X` and `a : X ≅ Xᘁᘁ`. -/
theorem isUnit_of_squaredNorm_of_simple [RigidCategory C] {X : C} [Simple X]
    [FiniteDimensional k (X ⟶ X)] (a : X ≅ (Xᘁ : C)ᘁ) :
    IsUnit (End.of (squaredNorm a)) :=
  have := isIso_squaredNorm_of_simple k a
  (isUnit_iff_isIso (End.of (squaredNorm a))).2 inferInstance

include k in
/-- In a finite semisimple rigid category with simple tensor unit, `squaredNorm a` is nonzero for
every split simple object `X` and `a : X ≅ Xᘁᘁ`. -/
theorem squaredNorm_ne_zero_of_simple [RigidCategory C] {X : C} [Simple X]
    [FiniteDimensional k (X ⟶ X)] (a : X ≅ (Xᘁ : C)ᘁ) :
    squaredNorm a ≠ 0 := by
  have := isIso_squaredNorm_of_simple k a
  intro h
  have hid : 𝟙 (𝟙_ C) = 0 :=
    (IsIso.hom_inv_id _).symm.trans ((congrArg (· ≫ inv (squaredNorm a)) h).trans zero_comp)
  exact CategoryTheory.id_ne_zero (𝟙_ C) hid

end FiniteSemisimple

end Simple

end TauCeti
