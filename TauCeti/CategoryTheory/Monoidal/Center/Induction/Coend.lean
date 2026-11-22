/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.End
public import Mathlib.CategoryTheory.Monoidal.Rigid.Functor
public import TauCeti.CategoryTheory.Monoidal.Center.Induction.End
import TauCeti.CategoryTheory.Semisimple.Multiplicity

/-!
# The universal coend property of `Center.inductionObj`

Let `C` be a finite semisimple right rigid `k`-linear monoidal category over an algebraically closed
field `k`, with finitely many isomorphism classes of simple objects and finite-dimensional simple
endomorphism spaces. Dual to the end structure in
`TauCeti.CategoryTheory.Monoidal.Center.Induction.End`, the finite biproduct

```text
inductionObj X = ⨁ (S : SimpleClasses C), S.repr ⊗ X ⊗ S.reprᘁ
```

also realizes the categorical coend `∫^{Y ∈ C} Y ⊗ X ⊗ Yᘁ`: choosing a decomposition of `Y : C` as
a finite biproduct of simple objects yields a canonical coprojection
`inductionCoendι X Y : Y ⊗ X ⊗ Yᘁ ⟶ inductionObj X` which is dinatural in `Y`
(`g ▷ (X ⊗ Y'ᘁ)` against `Y ◁ X ◁ gᘁ`), independent of the chosen decomposition, and universal
among dinatural cowedges.

On any simple object `S`, composing the coend coprojection `inductionCoendι X S` with the end
projection `inductionEndπ X S` gives the identity of `S ⊗ X ⊗ Sᘁ`
(`CategoryTheory.Center.inductionCoendι_comp_inductionEndπ_of_simple`). Applied to a simple tensor
unit `𝟙_ C`, this exhibits `X` as a canonical retract of `inductionObj X` and underpins the left
adjunction `Center.forget C ⊣ Center.induction k C` (its dual left adjunction
`Center.induction k C ⊣ Center.forget C`).

## Main declarations

* `CategoryTheory.Center.inductionCoendι`: the canonical dinatural coend coprojection
  `Y ⊗ X ⊗ Yᘁ ⟶ inductionObj X`, with dinaturality
  `CategoryTheory.Center.inductionCoendι_dinatural`, evaluation
  `CategoryTheory.Center.inductionCoendι_repr` on simple representatives, dual-basis expansion
  `CategoryTheory.Center.inductionCoendι_comp_π` against summand projections, naturality
  `CategoryTheory.Center.inductionCoendι_comp_inductionMap` in `X`, and splitting
  `CategoryTheory.Center.inductionCoendι_comp_inductionEndπ_of_simple` on simple objects;
* `CategoryTheory.Center.inductionMapDesc`,
  `CategoryTheory.Center.map_ι_comp_inductionMapDesc`,
  `CategoryTheory.Center.map_coendι_comp_inductionMapDesc`,
  `CategoryTheory.Center.inductionObj_map_hom_ext_ι`, and
  `CategoryTheory.Center.inductionObj_map_hom_ext_coendι`: the universal coend descent and
  uniqueness principles under a functor `F : C ⥤ D`;
* `CategoryTheory.Center.coendι_comp_biproduct_desc` and
  `CategoryTheory.Center.inductionObj_hom_ext_coendι`: the universal coend descent through
  `biproduct.desc` and uniqueness principle in `C`;
* `CategoryTheory.Center.inductionBifunctor`, `CategoryTheory.Center.inductionCowedge`,
  `CategoryTheory.Center.isColimitInductionCowedge`,
  `CategoryTheory.Center.hasCoend_inductionBifunctor`, and
  `CategoryTheory.Center.inductionObjIsoCoend`: the bundled bifunctor `(Y', Y) ↦ Y ⊗ X ⊗ Y'ᘁ`,
  its cowedge on `inductionObj X`, its `IsColimit` and `HasCoend` witnesses, and its canonical
  comparison isomorphism with Mathlib's `Limits.coend`.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005), §§2, 8
* M. Müger, *From subfactors to categories and topology II: The quantum double of tensor
  categories and subfactors*, J. Pure Appl. Algebra **180** (2003), 159–219
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§7.13, 9.3
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory TauCeti

universe w v u

namespace CategoryTheory.Center

attribute [local instance] Abelian.hasFiniteBiproducts

section CoendCowedge

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [Linear k C] [MonoidalLinear k C] [RightRigidCategory C]
  [∀ S : SimpleClasses C, FiniteDimensional k (S.repr ⟶ S.repr)]

include k in
/-- On representatives of simple classes, the biproduct inclusions of `inductionSummand X` satisfy
the coend dinaturality condition by Schur's lemma. -/
private theorem repr_codinatural [Finite (SimpleClasses C)] (X : C) {S T : SimpleClasses C}
    (m : S.repr ⟶ T.repr) :
    m ▷ (X ⊗ T.reprᘁ) ≫ biproduct.ι (inductionSummand X) T =
      S.repr ◁ X ◁ mᘁ ≫ biproduct.ι (inductionSummand X) S := by
  by_cases h : S = T
  · subst h
    obtain ⟨c, rfl⟩ := endomorphism_simple_eq_smul_id k m
    simp [rightAdjointMate]
  · rw [(SimpleClasses.homOrthogonal_repr h).elim m 0]
    simp

variable [Fintype (SimpleClasses C)]

/-- Auxiliary coprojection from `Y ⊗ X ⊗ Yᘁ` into `inductionObj X` associated to a chosen simple
biproduct decomposition of `Y`. -/
private def coendιAux {Y : C} {ι : Type*} [Fintype ι] (a : ι → C) [∀ i, Simple (a i)]
    [HasBiproduct a] (e : Y ≅ ⨁ a) (X : C) : Y ⊗ X ⊗ Yᘁ ⟶ inductionObj X :=
  ∑ i : ι,
    SimpleClasses.decompProj a e i ▷ (X ⊗ Yᘁ) ≫
      (SimpleClasses.classOf (a i)).repr ◁ X ◁ (SimpleClasses.decompIncl a e i)ᘁ ≫
      biproduct.ι (inductionSummand X) (SimpleClasses.classOf (a i))

omit [MonoidalPreadditive C] in
private theorem coendιAux_def {Y : C} {ι : Type*} [Fintype ι] (a : ι → C) [∀ i, Simple (a i)]
    [HasBiproduct a] (e : Y ≅ ⨁ a) (X : C) :
    coendιAux a e X = ∑ i : ι,
      SimpleClasses.decompProj a e i ▷ (X ⊗ Yᘁ) ≫
        (SimpleClasses.classOf (a i)).repr ◁ X ◁ (SimpleClasses.decompIncl a e i)ᘁ ≫
        biproduct.ι (inductionSummand X) (SimpleClasses.classOf (a i)) :=
  rfl

include k in
/-- `coendιAux` is dinatural with respect to any morphism `g : Y ⟶ Y'`, regardless of which simple
decompositions of `Y` and `Y'` are used. -/
private theorem coendιAux_dinatural {Y Y' : C} {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (a : ι → C) [∀ i, Simple (a i)] [HasBiproduct a] (e : Y ≅ ⨁ a)
    (b : ι' → C) [∀ j, Simple (b j)] [HasBiproduct b] (e' : Y' ≅ ⨁ b)
    (X : C) (g : Y ⟶ Y') :
    g ▷ (X ⊗ Y'ᘁ) ≫ coendιAux b e' X = Y ◁ X ◁ gᘁ ≫ coendιAux a e X := by
  have hY : ∑ i : ι, SimpleClasses.decompProj a e i ≫ SimpleClasses.decompIncl a e i = 𝟙 Y :=
    SimpleClasses.sum_comp_classOfReprIso_eq_id a e
  have hY' : ∑ j : ι', SimpleClasses.decompProj b e' j ≫ SimpleClasses.decompIncl b e' j = 𝟙 Y' :=
    SimpleClasses.sum_comp_classOfReprIso_eq_id b e'
  have hgL (i : ι) : SimpleClasses.decompIncl a e i ≫ g =
      ∑ j, (SimpleClasses.decompIncl a e i ≫ g ≫ SimpleClasses.decompProj b e' j) ≫
        SimpleClasses.decompIncl b e' j := by
    simp only [Category.assoc, ← Preadditive.comp_sum, hY', Category.comp_id]
  have hgR (j : ι') : g ≫ SimpleClasses.decompProj b e' j =
      ∑ i, SimpleClasses.decompProj a e i ≫
        (SimpleClasses.decompIncl a e i ≫ g ≫ SimpleClasses.decompProj b e' j) := by
    simp only [← Category.assoc, ← Preadditive.sum_comp, hY, Category.id_comp]
  rw [coendιAux_def, coendιAux_def]
  calc g ▷ (X ⊗ Y'ᘁ) ≫ (∑ j, SimpleClasses.decompProj b e' j ▷ (X ⊗ Y'ᘁ) ≫
          _ ◁ X ◁ (SimpleClasses.decompIncl b e' j)ᘁ ≫
          biproduct.ι (inductionSummand X) (SimpleClasses.classOf (b j)))
      = ∑ j, (g ≫ SimpleClasses.decompProj b e' j) ▷ (X ⊗ Y'ᘁ) ≫
          _ ◁ X ◁ (SimpleClasses.decompIncl b e' j)ᘁ ≫
          biproduct.ι (inductionSummand X) (SimpleClasses.classOf (b j)) := by
          simp only [Preadditive.comp_sum, ← comp_whiskerRight_assoc]
    _ = ∑ j, ∑ i, SimpleClasses.decompProj a e i ▷ (X ⊗ Y'ᘁ) ≫
          _ ◁ X ◁ (SimpleClasses.decompIncl b e' j)ᘁ ≫
          ((SimpleClasses.decompIncl a e i ≫ g ≫ SimpleClasses.decompProj b e' j) ▷ (X ⊗ _) ≫
            biproduct.ι (inductionSummand X) (SimpleClasses.classOf (b j))) := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          conv_lhs => rw [hgR j]
          simp only [sum_whiskerRight, Preadditive.sum_comp]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [comp_whiskerRight_assoc (SimpleClasses.decompProj a e i)
              (SimpleClasses.decompIncl a e i ≫ g ≫ SimpleClasses.decompProj b e' j),
            whisker_exchange_assoc]
    _ = ∑ j, ∑ i, SimpleClasses.decompProj a e i ▷ (X ⊗ Y'ᘁ) ≫
          _ ◁ X ◁ ((SimpleClasses.decompIncl b e' j)ᘁ ≫
            (SimpleClasses.decompIncl a e i ≫ g ≫ SimpleClasses.decompProj b e' j)ᘁ) ≫
          biproduct.ι (inductionSummand X) (SimpleClasses.classOf (a i)) := by
          refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
          rw [repr_codinatural k X
              (SimpleClasses.decompIncl a e i ≫ g ≫ SimpleClasses.decompProj b e' j),
            ← whiskerLeft_comp_assoc, ← whiskerLeft_comp]
    _ = ∑ i, SimpleClasses.decompProj a e i ▷ (X ⊗ Y'ᘁ) ≫
          _ ◁ X ◁ (SimpleClasses.decompIncl a e i ≫ g)ᘁ ≫
          biproduct.ι (inductionSummand X) (SimpleClasses.classOf (a i)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          conv_rhs => rw [hgL i, rightAdjointMate_sum]
          simp only [comp_rightAdjointMate, whiskerLeft_sum, Preadditive.comp_sum,
            Preadditive.sum_comp, Category.assoc]
    _ = Y ◁ X ◁ gᘁ ≫ (∑ i, SimpleClasses.decompProj a e i ▷ (X ⊗ Yᘁ) ≫
          _ ◁ X ◁ (SimpleClasses.decompIncl a e i)ᘁ ≫
          biproduct.ι (inductionSummand X) (SimpleClasses.classOf (a i))) := by
          simp only [Preadditive.comp_sum, comp_rightAdjointMate, whiskerLeft_comp,
            ← whisker_exchange_assoc, Category.assoc]

end CoendCowedge

section Coendι

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [Linear k C] [MonoidalLinear k C] [RightRigidCategory C] [IsFiniteSemisimpleCategory C]
  [Fintype (SimpleClasses C)] [∀ S : SimpleClasses C, FiniteDimensional k (S.repr ⟶ S.repr)]

/-- The canonical dinatural coend coprojection `Y ⊗ X ⊗ Yᘁ ⟶ inductionObj X`. -/
def inductionCoendι (X Y : C) : Y ⊗ X ⊗ Yᘁ ⟶ inductionObj X :=
  coendιAux (IsFiniteSemisimpleCategory.chosenSimpleFamily Y)
    (IsFiniteSemisimpleCategory.chosenSimpleIso Y) X

omit [MonoidalPreadditive C] in
private theorem inductionCoendι_eq_coendιAux (X Y : C) :
    inductionCoendι X Y =
      coendιAux (IsFiniteSemisimpleCategory.chosenSimpleFamily Y)
        (IsFiniteSemisimpleCategory.chosenSimpleIso Y) X :=
  rfl

omit [MonoidalPreadditive C] in
private theorem inductionCoendι_def (X Y : C) :
    inductionCoendι X Y = ∑ i : IsFiniteSemisimpleCategory.chosenSimpleIndex Y,
      SimpleClasses.decompProj (IsFiniteSemisimpleCategory.chosenSimpleFamily Y)
          (IsFiniteSemisimpleCategory.chosenSimpleIso Y) i ▷ (X ⊗ Yᘁ) ≫
        (SimpleClasses.classOf (IsFiniteSemisimpleCategory.chosenSimpleFamily Y i)).repr ◁ X ◁
          (SimpleClasses.decompIncl (IsFiniteSemisimpleCategory.chosenSimpleFamily Y)
            (IsFiniteSemisimpleCategory.chosenSimpleIso Y) i)ᘁ ≫
        biproduct.ι (inductionSummand X)
          (SimpleClasses.classOf (IsFiniteSemisimpleCategory.chosenSimpleFamily Y i)) :=
  rfl

include k in
/-- Dinaturality of `inductionCoendι`: precomposing with `g ▷ (X ⊗ Y'ᘁ)` on the first factor agrees
with precomposing with `Y ◁ X ◁ gᘁ` on the third factor. -/
@[reassoc]
theorem inductionCoendι_dinatural (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    g ▷ (X ⊗ Y'ᘁ) ≫ inductionCoendι X Y' = Y ◁ X ◁ gᘁ ≫ inductionCoendι X Y := by
  rw [inductionCoendι_eq_coendιAux, inductionCoendι_eq_coendιAux]
  exact coendιAux_dinatural k _ _ _ _ X g

include k in
/-- On the chosen representative `S.repr` of a simple class `S`, `inductionCoendι` is the biproduct
inclusion of the `S`-summand. -/
@[reassoc] -- Not `@[simp]` because `k` cannot be inferred from the LHS.
theorem inductionCoendι_repr (X : C) (S : SimpleClasses C) :
    inductionCoendι X S.repr = biproduct.ι (inductionSummand X) S := by
  rw [inductionCoendι_def]
  symm
  calc biproduct.ι (inductionSummand X) S
      = (∑ i, SimpleClasses.decompProj (IsFiniteSemisimpleCategory.chosenSimpleFamily S.repr)
              (IsFiniteSemisimpleCategory.chosenSimpleIso S.repr) i ≫
            SimpleClasses.decompIncl (IsFiniteSemisimpleCategory.chosenSimpleFamily S.repr)
              (IsFiniteSemisimpleCategory.chosenSimpleIso S.repr) i) ▷
          (X ⊗ S.reprᘁ) ≫ biproduct.ι (inductionSummand X) S := by
          rw [SimpleClasses.sum_comp_classOfReprIso_eq_id, id_whiskerRight, Category.id_comp]
    _ = ∑ i, SimpleClasses.decompProj (IsFiniteSemisimpleCategory.chosenSimpleFamily S.repr)
            (IsFiniteSemisimpleCategory.chosenSimpleIso S.repr) i ▷ (X ⊗ S.reprᘁ) ≫
          (SimpleClasses.decompIncl (IsFiniteSemisimpleCategory.chosenSimpleFamily S.repr)
              (IsFiniteSemisimpleCategory.chosenSimpleIso S.repr) i ▷ (X ⊗ S.reprᘁ) ≫
            biproduct.ι (inductionSummand X) S) := by
          simp only [sum_whiskerRight, Preadditive.sum_comp, comp_whiskerRight_assoc]
    _ = ∑ i, SimpleClasses.decompProj (IsFiniteSemisimpleCategory.chosenSimpleFamily S.repr)
            (IsFiniteSemisimpleCategory.chosenSimpleIso S.repr) i ▷ (X ⊗ S.reprᘁ) ≫
          _ ◁ X ◁ (SimpleClasses.decompIncl (IsFiniteSemisimpleCategory.chosenSimpleFamily S.repr)
            (IsFiniteSemisimpleCategory.chosenSimpleIso S.repr) i)ᘁ ≫
          biproduct.ι (inductionSummand X)
            (SimpleClasses.classOf (IsFiniteSemisimpleCategory.chosenSimpleFamily S.repr i)) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [repr_codinatural k X
            (SimpleClasses.decompIncl (IsFiniteSemisimpleCategory.chosenSimpleFamily S.repr)
              (IsFiniteSemisimpleCategory.chosenSimpleIso S.repr) i)]

omit [MonoidalPreadditive C] in
/-- Naturality of `inductionCoendι` in `X` with respect to `inductionMap f`. -/
@[reassoc]
theorem inductionCoendι_comp_inductionMap {X X' : C} (f : X ⟶ X') (Y : C) :
    inductionCoendι X Y ≫ inductionMap f = Y ◁ f ▷ Yᘁ ≫ inductionCoendι X' Y := by
  rw [inductionCoendι_def, inductionCoendι_def]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc, biproduct.ι_map]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← whiskerLeft_comp_assoc, whisker_exchange, whiskerLeft_comp_assoc,
    ← whisker_exchange_assoc]

include k in
/-- For any simple object `S`, the coend coprojection `inductionCoendι X S` is a section of the end
projection `inductionEndπ X S`. -/
@[reassoc]
theorem inductionCoendι_comp_inductionEndπ_of_simple (X S : C) [Simple S] :
    inductionCoendι X S ≫ inductionEndπ X S = 𝟙 (S ⊗ X ⊗ Sᘁ) := by
  let e : S ≅ (SimpleClasses.classOf S).repr := (SimpleClasses.classOfReprIso S).symm
  have hcoend : inductionCoendι X S =
      S ◁ X ◁ (e.inv)ᘁ ≫ e.hom ▷ (X ⊗ (SimpleClasses.classOf S).reprᘁ) ≫
        biproduct.ι (inductionSummand X) (SimpleClasses.classOf S) := by
    rw [← inductionCoendι_repr k X (SimpleClasses.classOf S),
      inductionCoendι_dinatural k X e.hom, ← whiskerLeft_comp_assoc, ← whiskerLeft_comp,
      ← comp_rightAdjointMate, Iso.hom_inv_id, rightAdjointMate_id, whiskerLeft_id,
      whiskerLeft_id, Category.id_comp]
  have hend : inductionEndπ X S =
      inductionEndπ X (SimpleClasses.classOf S).repr ≫ e.inv ▷ (X ⊗ _) ≫ S ◁ X ◁ (e.hom)ᘁ := by
    rw [inductionEndπ_dinatural_assoc k X e.inv, ← whiskerLeft_comp, ← whiskerLeft_comp,
      ← comp_rightAdjointMate, Iso.hom_inv_id, rightAdjointMate_id, whiskerLeft_id,
      whiskerLeft_id, Category.comp_id]
  rw [hcoend, hend, inductionEndπ_repr k X (SimpleClasses.classOf S)]
  simp only [Category.assoc, biproduct.ι_π_self_assoc, ← comp_whiskerRight_assoc, Iso.hom_inv_id,
    id_whiskerRight, Category.id_comp, ← whiskerLeft_comp, ← comp_rightAdjointMate,
    rightAdjointMate_id, whiskerLeft_id]

end Coendι

section DualBasis

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [Linear k C] [MonoidalLinear k C] [RightRigidCategory C] [IsFiniteSemisimpleCategory C]
  [Fintype (SimpleClasses C)] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

/-- Composing `inductionCoendι X Y` with the `S`-summand projection expands over any `k`-basis `b`
of `S.repr ⟶ Y` and its composition-dual basis `b.homDual`. -/
@[reassoc]
theorem inductionCoendι_comp_π (X Y : C)
    (S : SimpleClasses C) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k (S.repr ⟶ Y)) :
    inductionCoendι X Y ≫ biproduct.π (inductionSummand X) S =
      ∑ i, b.homDual i ▷ (X ⊗ Yᘁ) ≫ S.repr ◁ X ◁ (b i)ᘁ := by
  classical
  let c (R : SimpleClasses C) := Module.finBasis k (R.repr ⟶ Y)
  have hbasis : ∑ j, (c S).homDual j ▷ (X ⊗ Yᘁ) ≫ S.repr ◁ X ◁ (c S j)ᘁ =
      ∑ i, b.homDual i ▷ (X ⊗ Yᘁ) ≫ S.repr ◁ X ◁ (b i)ᘁ :=
    (c S).sum_homDual_eq b (LinearMap.mk₂ k
      (fun u v ↦ u ▷ (X ⊗ Yᘁ) ≫ S.repr ◁ X ◁ vᘁ)
      (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)
      (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp [rightAdjointMate]))
  rw [← hbasis]
  calc inductionCoendι X Y ≫ biproduct.π (inductionSummand X) S
      = (∑ R : SimpleClasses C, ∑ j, (c R).homDual j ≫ c R j) ▷ (X ⊗ Yᘁ) ≫
          inductionCoendι X Y ≫ biproduct.π (inductionSummand X) S := by
          rw [sum_sum_homDual_comp_eq_id Y c, id_whiskerRight, Category.id_comp]
    _ = ∑ R : SimpleClasses C, ∑ j, (c R).homDual j ▷ (X ⊗ Yᘁ) ≫
          (c R j ▷ (X ⊗ Yᘁ) ≫ inductionCoendι X Y) ≫ biproduct.π (inductionSummand X) S := by
          simp only [sum_whiskerRight, Preadditive.sum_comp, comp_whiskerRight_assoc,
            Category.assoc]
    _ = ∑ R : SimpleClasses C, ∑ j, (c R).homDual j ▷ (X ⊗ Yᘁ) ≫ R.repr ◁ X ◁ (c R j)ᘁ ≫
          (biproduct.ι (inductionSummand X) R ≫ biproduct.π (inductionSummand X) S) := by
          refine Finset.sum_congr rfl fun R _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
          rw [inductionCoendι_dinatural k X (c R j), inductionCoendι_repr k X R, Category.assoc]
    _ = ∑ j, (c S).homDual j ▷ (X ⊗ Yᘁ) ≫ S.repr ◁ X ◁ (c S j)ᘁ := by
          rw [Finset.sum_eq_single S]
          · simp
          · intro R _ hRS
            simp [biproduct.ι_π_ne _ hRS]
          · simp

end DualBasis

section UniversalCoend

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [RightRigidCategory C]
  [Fintype (SimpleClasses C)]

/-- Morphisms out of `F.obj (inductionObj X)` for a functor `F : C ⥤ D` preserving the biproduct
of `inductionSummand X` agree once they agree after every summand inclusion
`F.map (biproduct.ι (inductionSummand X) S)`. -/
theorem inductionObj_map_hom_ext_ι {D : Type*} [Category* D] [HasZeroMorphisms D]
    {F : C ⥤ D} [F.PreservesZeroMorphisms] {X : C}
    [PreservesBiproduct (inductionSummand X) F] {W : D}
    {f₁ f₂ : F.obj (inductionObj X) ⟶ W}
    (h : ∀ S : SimpleClasses C,
      F.map (biproduct.ι (inductionSummand X) S) ≫ f₁ =
        F.map (biproduct.ι (inductionSummand X) S) ≫ f₂) :
    f₁ = f₂ :=
  Cofan.IsColimit.hom_ext (isBilimitOfPreserves F (biproduct.isBilimit _)).isColimit _ _ h

/-- Universal coend descent out of `F.obj (inductionObj X)` associated to a family
`w : ∀ Y : C, F.obj (Y ⊗ X ⊗ Yᘁ) ⟶ W` under a biproduct-preserving functor `F : C ⥤ D`. -/
def inductionMapDesc {D : Type*} [Category* D] [HasZeroMorphisms D]
    {F : C ⥤ D} [F.PreservesZeroMorphisms] {X : C}
    [PreservesBiproduct (inductionSummand X) F] {W : D}
    (w : ∀ Y : C, F.obj (Y ⊗ X ⊗ Yᘁ) ⟶ W) :
    F.obj (inductionObj X) ⟶ W :=
  (isBilimitOfPreserves F (biproduct.isBilimit _)).isColimit.desc
    (Cofan.mk W fun S : SimpleClasses C ↦ w S.repr)

/-- Evaluating `inductionMapDesc w` on the `S`-summand inclusion recovers `w S.repr`. -/
@[reassoc (attr := simp)]
theorem map_ι_comp_inductionMapDesc {D : Type*} [Category* D] [HasZeroMorphisms D]
    {F : C ⥤ D} [F.PreservesZeroMorphisms] {X : C}
    [PreservesBiproduct (inductionSummand X) F] {W : D}
    (w : ∀ Y : C, F.obj (Y ⊗ X ⊗ Yᘁ) ⟶ W) (S : SimpleClasses C) :
    F.map (biproduct.ι (inductionSummand X) S) ≫ inductionMapDesc w = w S.repr :=
  (isBilimitOfPreserves F (biproduct.isBilimit _)).isColimit.fac
    (Cofan.mk W fun T : SimpleClasses C ↦ w T.repr) ⟨S⟩

variable [IsFiniteSemisimpleCategory C]

/-- Morphisms out of `F.obj (inductionObj X)` for a functor `F : C ⥤ D` preserving the biproduct
of `inductionSummand X` agree once they agree after every coend coprojection
`F.map (inductionCoendι X Y)`. -/
theorem inductionObj_map_hom_ext_coendι {D : Type*} [Category* D] [HasZeroMorphisms D]
    {F : C ⥤ D} [F.PreservesZeroMorphisms] {X : C}
    [PreservesBiproduct (inductionSummand X) F] {W : D}
    {f₁ f₂ : F.obj (inductionObj X) ⟶ W}
    (h : ∀ Y : C, F.map (inductionCoendι X Y) ≫ f₁ = F.map (inductionCoendι X Y) ≫ f₂) :
    f₁ = f₂ := by
  refine inductionObj_map_hom_ext_ι fun S ↦ ?_
  let a := IsFiniteSemisimpleCategory.chosenSimpleFamily S.repr
  let e := IsFiniteSemisimpleCategory.chosenSimpleIso S.repr
  obtain ⟨e', he'⟩ := exists_equiv_of_iso_biproduct_simples a (fun _ : Unit ↦ S.repr)
    (e.symm ≪≫ (biproductUniqueIso (fun _ : Unit ↦ S.repr)).symm)
  let : Unique (IsFiniteSemisimpleCategory.chosenSimpleIndex S.repr) := e'.unique
  have hcls : SimpleClasses.classOf (a default) = S :=
    ((SimpleClasses.classOf_eq_iff_nonempty_iso _ _).2 (he' default)).trans
      (SimpleClasses.classOf_repr S)
  have hS := h S.repr
  rw [inductionCoendι_def, Fintype.sum_unique] at hS
  have hcancel :
      ((SimpleClasses.classOf (a default)).repr ◁ X ◁
          (SimpleClasses.decompProj a e default)ᘁ ≫
          SimpleClasses.decompIncl a e default ▷ (X ⊗ S.reprᘁ)) ≫
        SimpleClasses.decompProj a e default ▷ (X ⊗ S.reprᘁ) ≫
          (SimpleClasses.classOf (a default)).repr ◁ X ◁
            (SimpleClasses.decompIncl a e default)ᘁ ≫
          biproduct.ι (inductionSummand X) (SimpleClasses.classOf (a default)) =
      biproduct.ι (inductionSummand X) (SimpleClasses.classOf (a default)) := by
    simp only [Category.assoc, ← comp_whiskerRight_assoc,
      SimpleClasses.decompIncl_comp_decompProj_self, id_whiskerRight, Category.id_comp,
      ← whiskerLeft_comp_assoc, ← whiskerLeft_comp, ← comp_rightAdjointMate, rightAdjointMate_id,
      whiskerLeft_id]
  have hR := congrArg
    (F.map ((SimpleClasses.classOf (a default)).repr ◁ X ◁
        (SimpleClasses.decompProj a e default)ᘁ ≫
      SimpleClasses.decompIncl a e default ▷ (X ⊗ S.reprᘁ)) ≫ ·) hS
  rw [← F.map_comp_assoc, ← F.map_comp_assoc, hcancel] at hR
  exact hcls ▸ hR

/-- Two morphisms out of `inductionObj X` agree once they agree after every coend coprojection
`inductionCoendι X Y`. -/
theorem inductionObj_hom_ext_coendι {X W : C}
    {f₁ f₂ : inductionObj X ⟶ W}
    (h : ∀ Y : C, inductionCoendι X Y ≫ f₁ = inductionCoendι X Y ≫ f₂) :
    f₁ = f₂ :=
  inductionObj_map_hom_ext_coendι (F := 𝟭 C) h

variable [MonoidalPreadditive C]

/-- Universal property of `inductionCoendι` under an additive functor `F : C ⥤ D`: any dinatural
cowedge `w : ∀ Y : C, F.obj (Y ⊗ X ⊗ Yᘁ) ⟶ W` factors through `inductionMapDesc w`. -/
@[reassoc]
theorem map_coendι_comp_inductionMapDesc {D : Type*} [Category* D] [Preadditive D]
    {F : C ⥤ D} [F.Additive] {X : C} {W : D}
    (w : ∀ Y : C, F.obj (Y ⊗ X ⊗ Yᘁ) ⟶ W)
    (hw : ∀ {Y Y' : C} (g : Y ⟶ Y'),
      F.map (g ▷ (X ⊗ Y'ᘁ)) ≫ w Y' = F.map (Y ◁ X ◁ gᘁ) ≫ w Y)
    (Y : C) :
    F.map (inductionCoendι X Y) ≫ inductionMapDesc w = w Y := by
  let a := IsFiniteSemisimpleCategory.chosenSimpleFamily Y
  let e := IsFiniteSemisimpleCategory.chosenSimpleIso Y
  rw [inductionCoendι_def, F.map_sum, Preadditive.sum_comp]
  calc ∑ i, F.map (SimpleClasses.decompProj a e i ▷ (X ⊗ Yᘁ) ≫
          _ ◁ X ◁ (SimpleClasses.decompIncl a e i)ᘁ ≫
          biproduct.ι (inductionSummand X) (SimpleClasses.classOf (a i))) ≫ inductionMapDesc w
      = ∑ i, F.map (SimpleClasses.decompProj a e i ▷ (X ⊗ Yᘁ)) ≫
          F.map (_ ◁ X ◁ (SimpleClasses.decompIncl a e i)ᘁ) ≫
          (F.map (biproduct.ι (inductionSummand X) (SimpleClasses.classOf (a i))) ≫
            inductionMapDesc w) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [F.map_comp, F.map_comp, Category.assoc, Category.assoc]
    _ = ∑ i, F.map ((SimpleClasses.decompProj a e i ≫
            SimpleClasses.decompIncl a e i) ▷ (X ⊗ Yᘁ)) ≫ w Y := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [map_ι_comp_inductionMapDesc, ← hw (SimpleClasses.decompIncl a e i),
            ← Category.assoc, ← F.map_comp, ← comp_whiskerRight]
    _ = w Y := by
          rw [← Preadditive.sum_comp, ← F.map_sum, ← sum_whiskerRight,
            SimpleClasses.sum_comp_classOfReprIso_eq_id a e, id_whiskerRight, F.map_id,
            Category.id_comp]

/-- Precomposing `biproduct.desc fun S ↦ w S.repr` with `inductionCoendι X Y` recovers `w Y`
whenever `w` is dinatural. -/
@[reassoc]
theorem coendι_comp_biproduct_desc {X W : C} (w : ∀ Y : C, Y ⊗ X ⊗ Yᘁ ⟶ W)
    (hw : ∀ {Y Y' : C} (g : Y ⟶ Y'),
      g ▷ (X ⊗ Y'ᘁ) ≫ w Y' = Y ◁ X ◁ gᘁ ≫ w Y)
    (Y : C) :
    inductionCoendι X Y ≫ biproduct.desc (fun S : SimpleClasses C ↦ w S.repr) = w Y := by
  have hdesc : biproduct.desc (fun S : SimpleClasses C ↦ w S.repr) =
      inductionMapDesc (F := 𝟭 C) w :=
    inductionObj_map_hom_ext_ι (F := 𝟭 C) fun S ↦ by
      rw [Functor.id_map, biproduct.ι_desc]
      exact (map_ι_comp_inductionMapDesc (F := 𝟭 C) w S).symm
  rw [hdesc]
  exact map_coendι_comp_inductionMapDesc (F := 𝟭 C) w hw Y

end UniversalCoend

section Coend

section Bifunctor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The bifunctor `Cᵒᵖ ⥤ C ⥤ C` sending `(Y', Y)` to `Y ⊗ X ⊗ Y'ᘁ`, whose coend is
`inductionObj X`. -/
@[expose] def inductionBifunctor (X : C) : Cᵒᵖ ⥤ C ⥤ C :=
  (rightDualFunctor C ⋙ unmopFunctor Cᵒᵖ).leftOp ⋙
    tensorLeft X ⋙ (curriedTensor C).flip

/-- The bifunctor `inductionBifunctor X` evaluates on `(op Y', Y)` to `Y ⊗ X ⊗ Y'ᘁ`. -/
@[simp]
theorem inductionBifunctor_obj_obj (X : C) (Y' : Cᵒᵖ) (Y : C) :
    ((inductionBifunctor X).obj Y').obj Y = Y ⊗ X ⊗ Y'.unopᘁ :=
  rfl

/-- On covariant morphisms `f : Y₁ ⟶ Y₂`, `inductionBifunctor X` acts by `f ▷ (X ⊗ Y'ᘁ)`. -/
@[simp]
theorem inductionBifunctor_obj_map (X : C) (Y' : Cᵒᵖ) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) :
    ((inductionBifunctor X).obj Y').map f = f ▷ (X ⊗ Y'.unopᘁ) :=
  rfl

/-- On contravariant morphisms `g : Y₁' ⟶ Y₂'`, `inductionBifunctor X` acts by
`Y ◁ X ◁ g.unopᘁ`. -/
@[simp]
theorem inductionBifunctor_map_app (X : C) {Y₁' Y₂' : Cᵒᵖ} (g : Y₁' ⟶ Y₂') (Y : C) :
    ((inductionBifunctor X).map g).app Y = Y ◁ X ◁ g.unopᘁ :=
  rfl

end Bifunctor

section Cowedge

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [Linear k C] [MonoidalLinear k C] [RightRigidCategory C] [IsFiniteSemisimpleCategory C]
  [Fintype (SimpleClasses C)] [∀ S : SimpleClasses C, FiniteDimensional k (S.repr ⟶ S.repr)]

include k

/-- The cowedge for `inductionBifunctor X` with point `inductionObj X` and coprojections
`inductionCoendι X`. -/
@[expose] def inductionCowedge (X : C) : Limits.Cowedge (inductionBifunctor X) :=
  Limits.Cowedge.mk (inductionObj X) (inductionCoendι X) fun _ _ g ↦
    (inductionCoendι_dinatural k X g).symm

/-- The cocone point of `inductionCowedge k X` is `inductionObj X`. -/
@[simp]
theorem inductionCowedge_pt (X : C) : (inductionCowedge k X).pt = inductionObj X :=
  rfl

/-- The `Y`-coprojection of `inductionCowedge k X` is `inductionCoendι X Y`. -/
@[simp]
theorem inductionCowedge_π (X Y : C) : (inductionCowedge k X).π Y = inductionCoendι X Y :=
  rfl

/-- `inductionCowedge k X` is a colimit cowedge, realizing `inductionObj X` as the categorical
coend `∫^{Y ∈ C} Y ⊗ X ⊗ Yᘁ`. -/
def isColimitInductionCowedge (X : C) : Limits.IsColimit (inductionCowedge k X) :=
  Limits.Multicofork.IsColimit.mk (inductionCowedge k X)
    (fun s ↦ biproduct.desc fun S : SimpleClasses C ↦ s.π S.repr)
    (fun s Y ↦ coendι_comp_biproduct_desc (fun Y' : C ↦ s.π Y')
      (fun {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) ↦ (Limits.Cowedge.condition s g).symm) Y)
    (fun s m hm ↦ inductionObj_map_hom_ext_ι (F := 𝟭 C) fun S ↦ by
      have hmS : biproduct.ι (inductionSummand X) S ≫ m = s.π S.repr := by
        rw [← inductionCoendι_repr k X S]
        exact hm S.repr
      have hdesc : biproduct.ι (inductionSummand X) S ≫
          biproduct.desc (fun T : SimpleClasses C ↦ s.π T.repr) = s.π S.repr :=
        biproduct.ι_desc (fun T : SimpleClasses C ↦ (s.π T.repr : inductionSummand X T ⟶ s.pt)) S
      exact hmS.trans hdesc.symm)

omit [Fintype (SimpleClasses C)] in
/-- `inductionBifunctor X` admits a categorical coend. -/
theorem hasCoend_inductionBifunctor [Finite (SimpleClasses C)] (X : C) :
    Limits.HasCoend (inductionBifunctor X) := by
  let := Fintype.ofFinite (SimpleClasses C)
  exact Limits.HasColimit.mk ⟨inductionCowedge k X, isColimitInductionCowedge k X⟩

/-- Canonical comparison isomorphism between `inductionObj X` and Mathlib's chosen coend
`Limits.coend (inductionBifunctor X)`. -/
def inductionObjIsoCoend (X : C) [Limits.HasCoend (inductionBifunctor X)] :
    inductionObj X ≅ Limits.coend (inductionBifunctor X) :=
  (isColimitInductionCowedge k X).coconePointUniqueUpToIso (Limits.colimit.isColimit _)

/-- Composing `inductionCoendι X Y` with the forward comparison isomorphism recovers Mathlib's
chosen coend coprojection `Limits.coend.ι (inductionBifunctor X) Y`. -/
@[reassoc (attr := simp)]
theorem inductionCoendι_comp_inductionObjIsoCoend_hom (X Y : C)
    [Limits.HasCoend (inductionBifunctor X)] :
    inductionCoendι X Y ≫ (inductionObjIsoCoend k X).hom =
      Limits.coend.ι (inductionBifunctor X) Y :=
  (isColimitInductionCowedge k X).comp_coconePointUniqueUpToIso_hom
    (Limits.colimit.isColimit _) (Limits.WalkingMultispan.right Y)

/-- Composing Mathlib's chosen coend coprojection `Limits.coend.ι (inductionBifunctor X) Y` with
the inverse comparison isomorphism recovers `inductionCoendι X Y`. -/
@[reassoc (attr := simp)]
theorem coend_ι_comp_inductionObjIsoCoend_inv (X Y : C)
    [Limits.HasCoend (inductionBifunctor X)] :
    Limits.coend.ι (inductionBifunctor X) Y ≫ (inductionObjIsoCoend k X).inv =
      inductionCoendι X Y :=
  Limits.colimit.comp_coconePointUniqueUpToIso_inv
    (isColimitInductionCowedge k X) (Limits.WalkingMultispan.right Y)

end Cowedge

end Coend

end CategoryTheory.Center
