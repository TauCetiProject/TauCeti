/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Center.Induction.End

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
adjunction `Center.induction k C ⊣ Center.forget C`.

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
  `CategoryTheory.Center.map_coendι_comp_inductionMapDesc`, and
  `CategoryTheory.Center.inductionObj_map_hom_ext_ι`: the universal coend descent and uniqueness
  principle under a functor `F : C ⥤ D`;
* `CategoryTheory.Center.inductionDesc`, `CategoryTheory.Center.ι_comp_inductionDesc`,
  `CategoryTheory.Center.coendι_comp_inductionDesc`, and
  `CategoryTheory.Center.inductionObj_hom_ext_coendι`: the universal coend descent and uniqueness
  principle in `C`.

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

section SimpleDecomposition

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Projection from `Y` to the representative of the simple class of `a i` in a simple biproduct
decomposition `e : Y ≅ ⨁ a`. -/
private def decompProj {Y : C} {ι : Type*} (a : ι → C) [∀ i, Simple (a i)]
    [HasBiproduct a] (e : Y ≅ ⨁ a) (i : ι) : Y ⟶ (SimpleClasses.classOf (a i)).repr :=
  e.hom ≫ biproduct.π a i ≫ (SimpleClasses.classOfReprIso (a i)).inv

/-- Inclusion from the representative of the simple class of `a i` into `Y` in a simple biproduct
decomposition `e : Y ≅ ⨁ a`. -/
private def decompIncl {Y : C} {ι : Type*} (a : ι → C) [∀ i, Simple (a i)]
    [HasBiproduct a] (e : Y ≅ ⨁ a) (i : ι) : (SimpleClasses.classOf (a i)).repr ⟶ Y :=
  (SimpleClasses.classOfReprIso (a i)).hom ≫ biproduct.ι a i ≫ e.inv

private theorem sum_decompProj_comp_decompIncl {Y : C} {ι : Type*} [Fintype ι] (a : ι → C)
    [∀ i, Simple (a i)] [HasBiproduct a] (e : Y ≅ ⨁ a) :
    ∑ i : ι, decompProj a e i ≫ decompIncl a e i = 𝟙 Y :=
  SimpleClasses.sum_comp_classOfReprIso_eq_id a e

variable [IsFiniteSemisimpleCategory C]

/-- Index type of the chosen simple biproduct decomposition of `Y`. -/
private def chosenSimpleIndex (Y : C) : Type :=
  (IsFiniteSemisimpleCategory.exists_biproduct_simples Y).choose

private instance (Y : C) : Fintype (chosenSimpleIndex Y) :=
  (IsFiniteSemisimpleCategory.exists_biproduct_simples Y).choose_spec.choose

/-- Family of simple objects in the chosen biproduct decomposition of `Y`. -/
private def chosenSimpleFamily (Y : C) : chosenSimpleIndex Y → C :=
  (IsFiniteSemisimpleCategory.exists_biproduct_simples Y).choose_spec.choose_spec.choose

private instance (Y : C) (i : chosenSimpleIndex Y) : Simple (chosenSimpleFamily Y i) :=
  (IsFiniteSemisimpleCategory.exists_biproduct_simples Y).choose_spec.choose_spec.choose_spec.choose
    i

private instance (Y : C) : HasBiproduct (chosenSimpleFamily Y) :=
  (IsFiniteSemisimpleCategory.exists_biproduct_simples
    Y).choose_spec.choose_spec.choose_spec.choose_spec.choose

/-- Isomorphism `Y ≅ ⨁ chosenSimpleFamily Y` of the chosen simple biproduct decomposition of `Y`. -/
private def chosenSimpleIso (Y : C) : Y ≅ ⨁ chosenSimpleFamily Y :=
  (IsFiniteSemisimpleCategory.exists_biproduct_simples
    Y).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.some

end SimpleDecomposition

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
    decompProj a e i ▷ (X ⊗ Yᘁ) ≫
      (SimpleClasses.classOf (a i)).repr ◁ X ◁ (decompIncl a e i)ᘁ ≫
      biproduct.ι (inductionSummand X) (SimpleClasses.classOf (a i))

omit [MonoidalPreadditive C] in
private theorem coendιAux_def {Y : C} {ι : Type*} [Fintype ι] (a : ι → C) [∀ i, Simple (a i)]
    [HasBiproduct a] (e : Y ≅ ⨁ a) (X : C) :
    coendιAux a e X = ∑ i : ι,
      decompProj a e i ▷ (X ⊗ Yᘁ) ≫
        (SimpleClasses.classOf (a i)).repr ◁ X ◁ (decompIncl a e i)ᘁ ≫
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
  have hgL (i : ι) : decompIncl a e i ≫ g =
      ∑ j, (decompIncl a e i ≫ g ≫ decompProj b e' j) ≫ decompIncl b e' j := by
    simp only [Category.assoc, ← Preadditive.comp_sum, sum_decompProj_comp_decompIncl b e',
      Category.comp_id]
  have hgR (j : ι') : g ≫ decompProj b e' j =
      ∑ i, decompProj a e i ≫ (decompIncl a e i ≫ g ≫ decompProj b e' j) := by
    simp only [← Category.assoc, ← Preadditive.sum_comp, sum_decompProj_comp_decompIncl a e,
      Category.id_comp]
  rw [coendιAux_def, coendιAux_def]
  calc g ▷ (X ⊗ Y'ᘁ) ≫ (∑ j, decompProj b e' j ▷ (X ⊗ Y'ᘁ) ≫ _ ◁ X ◁ (decompIncl b e' j)ᘁ ≫
          biproduct.ι (inductionSummand X) (SimpleClasses.classOf (b j)))
      = ∑ j, (g ≫ decompProj b e' j) ▷ (X ⊗ Y'ᘁ) ≫ _ ◁ X ◁ (decompIncl b e' j)ᘁ ≫
          biproduct.ι (inductionSummand X) (SimpleClasses.classOf (b j)) := by
          simp only [Preadditive.comp_sum, ← comp_whiskerRight_assoc]
    _ = ∑ j, ∑ i, decompProj a e i ▷ (X ⊗ Y'ᘁ) ≫ _ ◁ X ◁ (decompIncl b e' j)ᘁ ≫
          ((decompIncl a e i ≫ g ≫ decompProj b e' j) ▷ (X ⊗ _) ≫
            biproduct.ι (inductionSummand X) (SimpleClasses.classOf (b j))) := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          conv_lhs => rw [hgR j]
          simp only [sum_whiskerRight, Preadditive.sum_comp]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [comp_whiskerRight_assoc (decompProj a e i)
              (decompIncl a e i ≫ g ≫ decompProj b e' j),
            whisker_exchange_assoc]
    _ = ∑ j, ∑ i, decompProj a e i ▷ (X ⊗ Y'ᘁ) ≫
          _ ◁ X ◁ ((decompIncl b e' j)ᘁ ≫ (decompIncl a e i ≫ g ≫ decompProj b e' j)ᘁ) ≫
          biproduct.ι (inductionSummand X) (SimpleClasses.classOf (a i)) := by
          refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
          rw [repr_codinatural k X (decompIncl a e i ≫ g ≫ decompProj b e' j),
            ← whiskerLeft_comp_assoc, ← whiskerLeft_comp]
    _ = ∑ i, decompProj a e i ▷ (X ⊗ Y'ᘁ) ≫ _ ◁ X ◁ (decompIncl a e i ≫ g)ᘁ ≫
          biproduct.ι (inductionSummand X) (SimpleClasses.classOf (a i)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          conv_rhs => rw [hgL i, rightAdjointMate_sum]
          simp only [comp_rightAdjointMate, whiskerLeft_sum, Preadditive.comp_sum,
            Preadditive.sum_comp, Category.assoc]
    _ = Y ◁ X ◁ gᘁ ≫ (∑ i, decompProj a e i ▷ (X ⊗ Yᘁ) ≫ _ ◁ X ◁ (decompIncl a e i)ᘁ ≫
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
  coendιAux (chosenSimpleFamily Y) (chosenSimpleIso Y) X

omit [MonoidalPreadditive C] in
private theorem inductionCoendι_eq_coendιAux (X Y : C) :
    inductionCoendι X Y = coendιAux (chosenSimpleFamily Y) (chosenSimpleIso Y) X :=
  rfl

omit [MonoidalPreadditive C] in
private theorem inductionCoendι_def (X Y : C) :
    inductionCoendι X Y = ∑ i : chosenSimpleIndex Y,
      decompProj (chosenSimpleFamily Y) (chosenSimpleIso Y) i ▷ (X ⊗ Yᘁ) ≫
        (SimpleClasses.classOf (chosenSimpleFamily Y i)).repr ◁ X ◁
          (decompIncl (chosenSimpleFamily Y) (chosenSimpleIso Y) i)ᘁ ≫
        biproduct.ι (inductionSummand X) (SimpleClasses.classOf (chosenSimpleFamily Y i)) :=
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
      = (∑ i, decompProj (chosenSimpleFamily S.repr) (chosenSimpleIso S.repr) i ≫
            decompIncl (chosenSimpleFamily S.repr) (chosenSimpleIso S.repr) i) ▷
          (X ⊗ S.reprᘁ) ≫ biproduct.ι (inductionSummand X) S := by
          rw [sum_decompProj_comp_decompIncl, id_whiskerRight, Category.id_comp]
    _ = ∑ i, decompProj (chosenSimpleFamily S.repr) (chosenSimpleIso S.repr) i ▷ (X ⊗ S.reprᘁ) ≫
          (decompIncl (chosenSimpleFamily S.repr) (chosenSimpleIso S.repr) i ▷ (X ⊗ S.reprᘁ) ≫
            biproduct.ι (inductionSummand X) S) := by
          simp only [sum_whiskerRight, Preadditive.sum_comp, comp_whiskerRight_assoc]
    _ = ∑ i, decompProj (chosenSimpleFamily S.repr) (chosenSimpleIso S.repr) i ▷ (X ⊗ S.reprᘁ) ≫
          _ ◁ X ◁ (decompIncl (chosenSimpleFamily S.repr) (chosenSimpleIso S.repr) i)ᘁ ≫
          biproduct.ι (inductionSummand X)
            (SimpleClasses.classOf (chosenSimpleFamily S.repr i)) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [repr_codinatural k X
            (decompIncl (chosenSimpleFamily S.repr) (chosenSimpleIso S.repr) i)]

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
`w : ∀ Y : C, F.obj (Y ⊗ X ⊗ Yᘁ) ⟶ W` under a functor `F : C ⥤ D`. -/
def inductionMapDesc {D : Type*} [Category* D] [Preadditive D]
    {F : C ⥤ D} {X : C} {W : D}
    (w : ∀ Y : C, F.obj (Y ⊗ X ⊗ Yᘁ) ⟶ W) :
    F.obj (inductionObj X) ⟶ W :=
  ∑ S : SimpleClasses C, F.map (biproduct.π (inductionSummand X) S) ≫ w S.repr

/-- Evaluating `inductionMapDesc w` on the `S`-summand inclusion recovers `w S.repr`. -/
@[reassoc (attr := simp)]
theorem map_ι_comp_inductionMapDesc {D : Type*} [Category* D] [Preadditive D]
    {F : C ⥤ D} [F.PreservesZeroMorphisms] {X : C} {W : D}
    (w : ∀ Y : C, F.obj (Y ⊗ X ⊗ Yᘁ) ⟶ W) (S : SimpleClasses C) :
    F.map (biproduct.ι (inductionSummand X) S) ≫ inductionMapDesc w = w S.repr := by
  classical
  dsimp only [inductionMapDesc]
  simp only [Preadditive.comp_sum, ← Category.assoc, ← F.map_comp]
  rw [Finset.sum_eq_single S]
  · rw [biproduct.ι_π_self, F.map_id, Category.id_comp]
  · intro T _ hTS
    rw [biproduct.ι_π_ne _ (Ne.symm hTS), F.map_zero, zero_comp]
  · intro hS
    exact absurd (Finset.mem_univ S) hS

/-- Universal coend descent out of `inductionObj X` associated to a cowedge
`w : ∀ Y : C, Y ⊗ X ⊗ Yᘁ ⟶ W`. -/
def inductionDesc {X W : C} (w : ∀ Y : C, Y ⊗ X ⊗ Yᘁ ⟶ W) : inductionObj X ⟶ W :=
  inductionMapDesc (F := 𝟭 C) w

/-- Evaluating `inductionDesc w` on the `S`-summand inclusion recovers `w S.repr`. -/
@[reassoc (attr := simp)]
theorem ι_comp_inductionDesc {X W : C} (w : ∀ Y : C, Y ⊗ X ⊗ Yᘁ ⟶ W) (S : SimpleClasses C) :
    biproduct.ι (inductionSummand X) S ≫ inductionDesc w = w S.repr :=
  map_ι_comp_inductionMapDesc (F := 𝟭 C) w S

variable [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C]

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
  rw [inductionCoendι_def, F.map_sum, Preadditive.sum_comp]
  calc ∑ i, F.map (decompProj (chosenSimpleFamily Y) (chosenSimpleIso Y) i ▷ (X ⊗ Yᘁ) ≫
          _ ◁ X ◁ (decompIncl (chosenSimpleFamily Y) (chosenSimpleIso Y) i)ᘁ ≫
          biproduct.ι (inductionSummand X)
            (SimpleClasses.classOf (chosenSimpleFamily Y i))) ≫ inductionMapDesc w
      = ∑ i, F.map (decompProj (chosenSimpleFamily Y) (chosenSimpleIso Y) i ▷ (X ⊗ Yᘁ)) ≫
          F.map (_ ◁ X ◁ (decompIncl (chosenSimpleFamily Y) (chosenSimpleIso Y) i)ᘁ) ≫
          (F.map (biproduct.ι (inductionSummand X)
              (SimpleClasses.classOf (chosenSimpleFamily Y i))) ≫
            inductionMapDesc w) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [F.map_comp, F.map_comp, Category.assoc, Category.assoc]
    _ = ∑ i, F.map ((decompProj (chosenSimpleFamily Y) (chosenSimpleIso Y) i ≫
            decompIncl (chosenSimpleFamily Y) (chosenSimpleIso Y) i) ▷ (X ⊗ Yᘁ)) ≫ w Y := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [map_ι_comp_inductionMapDesc,
            ← hw (decompIncl (chosenSimpleFamily Y) (chosenSimpleIso Y) i), ← Category.assoc,
            ← F.map_comp, ← comp_whiskerRight]
    _ = w Y := by
          rw [← Preadditive.sum_comp, ← F.map_sum, ← sum_whiskerRight,
            sum_decompProj_comp_decompIncl, id_whiskerRight, F.map_id, Category.id_comp]

/-- Precomposing `inductionDesc w` with `inductionCoendι X Y` recovers `w Y` whenever `w` is
dinatural. -/
@[reassoc]
theorem coendι_comp_inductionDesc {X W : C} (w : ∀ Y : C, Y ⊗ X ⊗ Yᘁ ⟶ W)
    (hw : ∀ {Y Y' : C} (g : Y ⟶ Y'),
      g ▷ (X ⊗ Y'ᘁ) ≫ w Y' = Y ◁ X ◁ gᘁ ≫ w Y)
    (Y : C) :
    inductionCoendι X Y ≫ inductionDesc w = w Y :=
  map_coendι_comp_inductionMapDesc (F := 𝟭 C) w hw Y

variable (k : Type w) [Field k] [IsAlgClosed k] [Linear k C] [MonoidalLinear k C]
  [∀ S : SimpleClasses C, FiniteDimensional k (S.repr ⟶ S.repr)]

include k in
/-- Two morphisms out of `inductionObj X` agree once they agree after every coend coprojection
`inductionCoendι X Y`. -/
theorem inductionObj_hom_ext_coendι {X W : C}
    {f₁ f₂ : inductionObj X ⟶ W}
    (h : ∀ Y : C, inductionCoendι X Y ≫ f₁ = inductionCoendι X Y ≫ f₂) :
    f₁ = f₂ :=
  inductionObj_map_hom_ext_ι (F := 𝟭 C) fun S ↦ by
    simpa [inductionCoendι_repr k X S] using h S.repr

end UniversalCoend

end CategoryTheory.Center
