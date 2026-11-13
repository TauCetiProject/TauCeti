/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Center.Induction.Basic

/-!
# The universal end property of `Center.inductionObj`

Let `C` be a finite semisimple right rigid `k`-linear monoidal category over an algebraically closed
field `k`, with finitely many isomorphism classes of simple objects and finite-dimensional simple
endomorphism spaces. For each `X : C`, the finite biproduct

```text
inductionObj X = ⨁ (S : SimpleClasses C), S.repr ⊗ X ⊗ S.reprᘁ
```

realizes the categorical end `∫_{Y ∈ C} Y ⊗ X ⊗ Yᘁ`: choosing a decomposition of any `Y : C` as a
finite biproduct of simple objects produces a canonical projection
`inductionEndπ X Y : inductionObj X ⟶ Y ⊗ X ⊗ Yᘁ` which is dinatural in `Y`
(`g ▷ (X ⊗ Yᘁ)` against `Y' ◁ X ◁ gᘁ`) by Schur's lemma, independent of the chosen decomposition,
and universal among dinatural wedges. Moreover, since every additive functor `F : C ⥤ D` preserves
finite biproducts, `F` preserves this universal end property.

In `TauCeti.CategoryTheory.Monoidal.Center.Induction.Adjunction`, this universal property
characterizes `Center.inductionβHom` on the dinatural end projections and constructs the right
adjunction `Center.forget C ⊣ Center.induction k C`.

## Main declarations

* `CategoryTheory.Center.inductionEndπ`: the canonical dinatural end projection
  `inductionObj X ⟶ Y ⊗ X ⊗ Yᘁ`, with dinaturality
  `CategoryTheory.Center.inductionEndπ_dinatural`, evaluation
  `CategoryTheory.Center.inductionEndπ_repr` on simple representatives, dual-basis expansion
  `CategoryTheory.Center.ι_comp_inductionEndπ` on summand inclusions, and naturality
  `CategoryTheory.Center.inductionMap_comp_inductionEndπ` in `X`;
* `CategoryTheory.Center.inductionMapLift`,
  `CategoryTheory.Center.inductionMapLift_comp_map_π`,
  `CategoryTheory.Center.inductionMapLift_comp_map_endπ`, and
  `CategoryTheory.Center.inductionObj_map_hom_ext`: the universal end lift and uniqueness principle
  under an additive functor `F : C ⥤ D`;
* `CategoryTheory.Center.inductionLift`, `CategoryTheory.Center.inductionLift_comp_endπ`, and
  `CategoryTheory.Center.inductionObj_hom_ext_endπ`: the universal end lift and uniqueness
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

section EndWedge

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [Linear k C] [MonoidalLinear k C] [RightRigidCategory C]
  [∀ S : SimpleClasses C, FiniteDimensional k (S.repr ⟶ S.repr)]

include k in
/-- On representatives of simple classes, the biproduct projections of `inductionSummand X` satisfy
the end dinaturality condition by Schur's lemma. -/
private theorem repr_dinatural [Finite (SimpleClasses C)] (X : C) {S T : SimpleClasses C}
    (m : S.repr ⟶ T.repr) :
    biproduct.π (inductionSummand X) S ≫ m ▷ (X ⊗ S.reprᘁ) =
      biproduct.π (inductionSummand X) T ≫ T.repr ◁ X ◁ mᘁ := by
  by_cases h : S = T
  · subst h
    obtain ⟨c, rfl⟩ := endomorphism_simple_eq_smul_id k m
    simp [rightAdjointMate]
  · rw [(SimpleClasses.homOrthogonal_repr h).elim m 0]
    simp

variable [Fintype (SimpleClasses C)]

/-- Auxiliary projection from `inductionObj X` to `Y ⊗ X ⊗ Yᘁ` associated to a chosen simple
biproduct decomposition of `Y`. -/
private def endπAux {Y : C} {ι : Type*} [Fintype ι] (a : ι → C) [∀ i, Simple (a i)]
    [HasBiproduct a] (e : Y ≅ ⨁ a) (X : C) : inductionObj X ⟶ Y ⊗ X ⊗ Yᘁ :=
  ∑ i : ι,
    biproduct.π (inductionSummand X) (SimpleClasses.classOf (a i)) ≫
      ((SimpleClasses.classOfReprIso (a i)).hom ≫ biproduct.ι a i ≫ e.inv) ▷
        (X ⊗ (SimpleClasses.classOf (a i)).reprᘁ) ≫
      Y ◁ X ◁ (e.hom ≫ biproduct.π a i ≫ (SimpleClasses.classOfReprIso (a i)).inv)ᘁ

include k in
/-- `endπAux` is dinatural with respect to any morphism `g : Y ⟶ Y'`, regardless of which
simple decompositions of `Y` and `Y'` are used. -/
private theorem endπAux_dinatural {Y Y' : C} {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (a : ι → C) [∀ i, Simple (a i)] [HasBiproduct a] (e : Y ≅ ⨁ a)
    (b : ι' → C) [∀ j, Simple (b j)] [HasBiproduct b] (e' : Y' ≅ ⨁ b)
    (X : C) (g : Y ⟶ Y') :
    endπAux a e X ≫ g ▷ (X ⊗ Yᘁ) = endπAux b e' X ≫ Y' ◁ X ◁ gᘁ := by
  let p (i : ι) : Y ⟶ (SimpleClasses.classOf (a i)).repr :=
    e.hom ≫ biproduct.π a i ≫ (SimpleClasses.classOfReprIso (a i)).inv
  let q (i : ι) : (SimpleClasses.classOf (a i)).repr ⟶ Y :=
    (SimpleClasses.classOfReprIso (a i)).hom ≫ biproduct.ι a i ≫ e.inv
  let p' (j : ι') : Y' ⟶ (SimpleClasses.classOf (b j)).repr :=
    e'.hom ≫ biproduct.π b j ≫ (SimpleClasses.classOfReprIso (b j)).inv
  let q' (j : ι') : (SimpleClasses.classOf (b j)).repr ⟶ Y' :=
    (SimpleClasses.classOfReprIso (b j)).hom ≫ biproduct.ι b j ≫ e'.inv
  have hY : ∑ i, p i ≫ q i = 𝟙 Y := SimpleClasses.sum_comp_classOfReprIso_eq_id a e
  have hY' : ∑ j, p' j ≫ q' j = 𝟙 Y' := SimpleClasses.sum_comp_classOfReprIso_eq_id b e'
  have hgL (i : ι) : q i ≫ g = ∑ j, (q i ≫ g ≫ p' j) ≫ q' j := by
    simp only [Category.assoc, ← Preadditive.comp_sum, hY', Category.comp_id]
  have hgR (j : ι') : g ≫ p' j = ∑ i, p i ≫ (q i ≫ g ≫ p' j) := by
    simp only [← Category.assoc, ← Preadditive.sum_comp, hY, Category.id_comp]
  -- Fold the summands of `endπAux` in terms of `p`, `q`, `p'`, `q'`.
  change (∑ i, biproduct.π (inductionSummand X) (SimpleClasses.classOf (a i)) ≫
      q i ▷ (X ⊗ (SimpleClasses.classOf (a i)).reprᘁ) ≫ Y ◁ X ◁ (p i)ᘁ) ≫ g ▷ (X ⊗ Yᘁ) =
    (∑ j, biproduct.π (inductionSummand X) (SimpleClasses.classOf (b j)) ≫
      q' j ▷ (X ⊗ (SimpleClasses.classOf (b j)).reprᘁ) ≫ Y' ◁ X ◁ (p' j)ᘁ) ≫ Y' ◁ X ◁ gᘁ
  calc (∑ i, biproduct.π (inductionSummand X) (SimpleClasses.classOf (a i)) ≫
          q i ▷ (X ⊗ _) ≫ Y ◁ X ◁ (p i)ᘁ) ≫ g ▷ (X ⊗ Yᘁ)
      = ∑ i, biproduct.π (inductionSummand X) (SimpleClasses.classOf (a i)) ≫
          (q i ≫ g) ▷ (X ⊗ _) ≫ Y' ◁ X ◁ (p i)ᘁ := by
          simp only [Preadditive.sum_comp, Category.assoc, whisker_exchange,
            ← comp_whiskerRight_assoc]
    _ = ∑ i, ∑ j, (biproduct.π (inductionSummand X) (SimpleClasses.classOf (a i)) ≫
          (q i ≫ g ≫ p' j) ▷ (X ⊗ _)) ≫ q' j ▷ (X ⊗ _) ≫ Y' ◁ X ◁ (p i)ᘁ := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hgL i]
          simp only [sum_whiskerRight, Preadditive.comp_sum, Preadditive.sum_comp,
            Category.assoc, comp_whiskerRight]
    _ = ∑ i, ∑ j, biproduct.π (inductionSummand X) (SimpleClasses.classOf (b j)) ≫
          q' j ▷ (X ⊗ _) ≫ Y' ◁ X ◁ ((q i ≫ g ≫ p' j)ᘁ ≫ (p i)ᘁ) := by
          refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
          rw [repr_dinatural k X (q i ≫ g ≫ p' j), Category.assoc, whisker_exchange_assoc,
            ← whiskerLeft_comp, ← whiskerLeft_comp]
    _ = ∑ j, biproduct.π (inductionSummand X) (SimpleClasses.classOf (b j)) ≫
          q' j ▷ (X ⊗ _) ≫ Y' ◁ X ◁ (g ≫ p' j)ᘁ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          conv_rhs => rw [hgR j, rightAdjointMate_sum]
          simp only [comp_rightAdjointMate, whiskerLeft_sum, Preadditive.comp_sum, Category.assoc]
    _ = (∑ j, biproduct.π (inductionSummand X) (SimpleClasses.classOf (b j)) ≫
          q' j ▷ (X ⊗ _) ≫ Y' ◁ X ◁ (p' j)ᘁ) ≫ Y' ◁ X ◁ gᘁ := by
          simp only [Preadditive.sum_comp, Category.assoc, ← whiskerLeft_comp,
            comp_rightAdjointMate]

end EndWedge

section Endπ

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [Linear k C] [MonoidalLinear k C] [RightRigidCategory C] [IsFiniteSemisimpleCategory C]
  [Fintype (SimpleClasses C)] [∀ S : SimpleClasses C, FiniteDimensional k (S.repr ⟶ S.repr)]

/-- The canonical dinatural end projection `inductionObj X ⟶ Y ⊗ X ⊗ Yᘁ`. -/
def inductionEndπ (X Y : C) : inductionObj X ⟶ Y ⊗ X ⊗ Yᘁ :=
  let h := IsFiniteSemisimpleCategory.exists_biproduct_simples Y
  let _ := h.choose_spec.choose
  let a := h.choose_spec.choose_spec.choose
  let _ := h.choose_spec.choose_spec.choose_spec.choose
  let _ := h.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let e := h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.some
  endπAux a e X

include k in
/-- Dinaturality of `inductionEndπ`: right-whiskering by `g : Y ⟶ Y'` on the first factor
agrees with left-whiskering by `gᘁ : Y'ᘁ ⟶ Yᘁ` on the third factor. -/
@[reassoc]
theorem inductionEndπ_dinatural (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    inductionEndπ X Y ≫ g ▷ (X ⊗ Yᘁ) = inductionEndπ X Y' ≫ Y' ◁ X ◁ gᘁ := by
  let h := IsFiniteSemisimpleCategory.exists_biproduct_simples Y
  let : Fintype h.choose := h.choose_spec.choose
  let a := h.choose_spec.choose_spec.choose
  let : ∀ i, Simple (a i) := h.choose_spec.choose_spec.choose_spec.choose
  let : HasBiproduct a := h.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let e := h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.some
  let h' := IsFiniteSemisimpleCategory.exists_biproduct_simples Y'
  let : Fintype h'.choose := h'.choose_spec.choose
  let b := h'.choose_spec.choose_spec.choose
  let : ∀ j, Simple (b j) := h'.choose_spec.choose_spec.choose_spec.choose
  let : HasBiproduct b := h'.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let e' := h'.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.some
  exact endπAux_dinatural k a e b e' X g

include k in
/-- On the chosen representative `S.repr` of a simple class `S`, `inductionEndπ` is the
biproduct projection onto the `S`-summand. -/
@[reassoc] -- Not `@[simp]` because `k` cannot be inferred from the LHS.
theorem inductionEndπ_repr (X : C) (S : SimpleClasses C) :
    inductionEndπ X S.repr = biproduct.π (inductionSummand X) S := by
  let h := IsFiniteSemisimpleCategory.exists_biproduct_simples S.repr
  let : Fintype h.choose := h.choose_spec.choose
  let a := h.choose_spec.choose_spec.choose
  let : ∀ i, Simple (a i) := h.choose_spec.choose_spec.choose_spec.choose
  let : HasBiproduct a := h.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let e := h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.some
  let p (i : h.choose) : S.repr ⟶ (SimpleClasses.classOf (a i)).repr :=
    e.hom ≫ biproduct.π a i ≫ (SimpleClasses.classOfReprIso (a i)).inv
  let q (i : h.choose) : (SimpleClasses.classOf (a i)).repr ⟶ S.repr :=
    (SimpleClasses.classOfReprIso (a i)).hom ≫ biproduct.ι a i ≫ e.inv
  -- Unfold `inductionEndπ X S.repr` to `endπAux` for the chosen decomposition of `S.repr`.
  change endπAux a e X = biproduct.π (inductionSummand X) S
  symm
  calc biproduct.π (inductionSummand X) S
      = biproduct.π (inductionSummand X) S ≫ (∑ i, p i ≫ q i) ▷ (X ⊗ S.reprᘁ) := by
          rw [SimpleClasses.sum_comp_classOfReprIso_eq_id a e, id_whiskerRight, Category.comp_id]
    _ = ∑ i, (biproduct.π (inductionSummand X) S ≫ p i ▷ (X ⊗ S.reprᘁ)) ≫
          q i ▷ (X ⊗ S.reprᘁ) := by
          simp only [sum_whiskerRight, Preadditive.comp_sum, Category.assoc, comp_whiskerRight]
    _ = ∑ i, biproduct.π (inductionSummand X) (SimpleClasses.classOf (a i)) ≫
          q i ▷ (X ⊗ _) ≫ S.repr ◁ X ◁ (p i)ᘁ := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [repr_dinatural k X (p i), Category.assoc, whisker_exchange]
    _ = endπAux a e X := rfl

omit [MonoidalPreadditive C] in
/-- Naturality of `inductionEndπ` in `X` with respect to `inductionMap f`. -/
@[reassoc]
theorem inductionMap_comp_inductionEndπ {X X' : C} (f : X ⟶ X') (Y : C) :
    inductionMap f ≫ inductionEndπ X' Y = inductionEndπ X Y ≫ Y ◁ f ▷ Yᘁ := by
  dsimp only [inductionEndπ, endπAux]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp, biproduct.map_π_assoc, Category.assoc]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  rw [whisker_exchange_assoc, ← whiskerLeft_comp, ← whiskerLeft_comp, whisker_exchange]

end Endπ

section DualBasis

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [Linear k C] [MonoidalLinear k C] [RightRigidCategory C] [IsFiniteSemisimpleCategory C]
  [Fintype (SimpleClasses C)] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

/-- On the `S`-summand inclusion, `inductionEndπ X Y` expands over any `k`-basis `b` of
`S.repr ⟶ Y` and its composition-dual basis `b.homDual`. -/
@[reassoc]
theorem ι_comp_inductionEndπ (X Y : C) (S : SimpleClasses C) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι k (S.repr ⟶ Y)) :
    biproduct.ι (inductionSummand X) S ≫ inductionEndπ X Y =
      ∑ i, b i ▷ (X ⊗ S.reprᘁ) ≫ Y ◁ X ◁ (b.homDual i)ᘁ := by
  classical
  let c (R : SimpleClasses C) := Module.finBasis k (R.repr ⟶ Y)
  have hbasis : ∑ j, c S j ▷ (X ⊗ S.reprᘁ) ≫ Y ◁ X ◁ ((c S).homDual j)ᘁ =
      ∑ i, b i ▷ (X ⊗ S.reprᘁ) ≫ Y ◁ X ◁ (b.homDual i)ᘁ :=
    (c S).sum_homDual_eq b (LinearMap.mk₂ k
      (fun u v ↦ v ▷ (X ⊗ S.reprᘁ) ≫ Y ◁ X ◁ uᘁ)
      (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp [rightAdjointMate])
      (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp))
  rw [← hbasis]
  calc biproduct.ι (inductionSummand X) S ≫ inductionEndπ X Y
      = biproduct.ι (inductionSummand X) S ≫ inductionEndπ X Y ≫
          (∑ R : SimpleClasses C, ∑ j, (c R).homDual j ≫ c R j) ▷ (X ⊗ Yᘁ) := by
          rw [sum_sum_homDual_comp_eq_id Y c, id_whiskerRight, Category.comp_id]
    _ = ∑ R : SimpleClasses C, ∑ j, biproduct.ι (inductionSummand X) S ≫
          (inductionEndπ X Y ≫ (c R).homDual j ▷ (X ⊗ Yᘁ)) ≫ c R j ▷ (X ⊗ Yᘁ) := by
          simp only [sum_whiskerRight, Preadditive.comp_sum, comp_whiskerRight, Category.assoc]
    _ = ∑ R : SimpleClasses C, ∑ j, (biproduct.ι (inductionSummand X) S ≫
          biproduct.π (inductionSummand X) R) ≫ c R j ▷ (X ⊗ R.reprᘁ) ≫
            Y ◁ X ◁ ((c R).homDual j)ᘁ := by
          refine Finset.sum_congr rfl fun R _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
          rw [inductionEndπ_dinatural k X ((c R).homDual j), inductionEndπ_repr k X R,
            Category.assoc, Category.assoc, whisker_exchange]
    _ = ∑ j, c S j ▷ (X ⊗ S.reprᘁ) ≫ Y ◁ X ◁ ((c S).homDual j)ᘁ := by
          rw [Finset.sum_eq_single S]
          · simp
          · intro R _ hRS
            simp [biproduct.ι_π_ne _ (Ne.symm hRS)]
          · simp

end DualBasis

section UniversalEnd

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [RightRigidCategory C]
  [Fintype (SimpleClasses C)]

/-- Morphisms into `F.obj (inductionObj X)` for an additive functor `F : C ⥤ D` agree once they
agree after every summand projection `F.map (biproduct.π (inductionSummand X) S)`. -/
theorem inductionObj_map_hom_ext {D : Type*} [Category* D] [Preadditive D]
    {F : C ⥤ D} [F.Additive] {W : D} {X : C}
    {f₁ f₂ : W ⟶ F.obj (inductionObj X)}
    (h : ∀ S : SimpleClasses C,
      f₁ ≫ F.map (biproduct.π (inductionSummand X) S) =
        f₂ ≫ F.map (biproduct.π (inductionSummand X) S)) :
    f₁ = f₂ :=
  Fan.IsLimit.hom_ext (isBilimitOfPreserves F (biproduct.isBilimit _)).isLimit _ _ h

/-- Universal end lift into `F.obj (inductionObj X)` associated to a family
`w : ∀ Y : C, W ⟶ F.obj (Y ⊗ X ⊗ Yᘁ)` under a functor `F : C ⥤ D`. -/
def inductionMapLift {D : Type*} [Category* D] [Preadditive D]
    {F : C ⥤ D} {W : D} {X : C}
    (w : ∀ Y : C, W ⟶ F.obj (Y ⊗ X ⊗ Yᘁ)) :
    W ⟶ F.obj (inductionObj X) :=
  ∑ S : SimpleClasses C, w S.repr ≫ F.map (biproduct.ι (inductionSummand X) S)

/-- Evaluating `inductionMapLift w` at the `S`-summand projection recovers `w S.repr`. -/
@[reassoc (attr := simp)]
theorem inductionMapLift_comp_map_π {D : Type*} [Category* D] [Preadditive D]
    {F : C ⥤ D} [F.PreservesZeroMorphisms] {W : D} {X : C}
    (w : ∀ Y : C, W ⟶ F.obj (Y ⊗ X ⊗ Yᘁ)) (S : SimpleClasses C) :
    inductionMapLift w ≫ F.map (biproduct.π (inductionSummand X) S) = w S.repr := by
  classical
  dsimp only [inductionMapLift]
  simp only [Preadditive.sum_comp, Category.assoc, ← F.map_comp]
  rw [Finset.sum_eq_single S]
  · rw [biproduct.ι_π_self, F.map_id, Category.comp_id]
  · intro T _ hTS
    rw [biproduct.ι_π_ne _ hTS, F.map_zero, comp_zero]
  · intro hS
    exact absurd (Finset.mem_univ S) hS

/-- Universal end lift into `inductionObj X` associated to a wedge `w : ∀ Y : C, W ⟶ Y ⊗ X ⊗ Yᘁ`. -/
def inductionLift {W X : C} (w : ∀ Y : C, W ⟶ Y ⊗ X ⊗ Yᘁ) : W ⟶ inductionObj X :=
  inductionMapLift (F := 𝟭 C) w

/-- Evaluating `inductionLift w` at the `S`-summand projection recovers `w S.repr`. -/
@[reassoc (attr := simp)]
theorem inductionLift_comp_π {W X : C} (w : ∀ Y : C, W ⟶ Y ⊗ X ⊗ Yᘁ) (S : SimpleClasses C) :
    inductionLift w ≫ biproduct.π (inductionSummand X) S = w S.repr :=
  inductionMapLift_comp_map_π (F := 𝟭 C) w S

variable [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C]

/-- Universal property of `inductionEndπ` under an additive functor `F : C ⥤ D`: any dinatural
wedge `w : ∀ Y : C, W ⟶ F.obj (Y ⊗ X ⊗ Yᘁ)` factors through `inductionMapLift w`. -/
@[reassoc]
theorem inductionMapLift_comp_map_endπ {D : Type*} [Category* D] [Preadditive D]
    {F : C ⥤ D} [F.Additive] {W : D} {X : C}
    (w : ∀ Y : C, W ⟶ F.obj (Y ⊗ X ⊗ Yᘁ))
    (hw : ∀ {Y Y' : C} (g : Y ⟶ Y'),
      w Y ≫ F.map (g ▷ (X ⊗ Yᘁ)) = w Y' ≫ F.map (Y' ◁ X ◁ gᘁ))
    (Y : C) :
    inductionMapLift w ≫ F.map (inductionEndπ X Y) = w Y := by
  let h := IsFiniteSemisimpleCategory.exists_biproduct_simples Y
  let : Fintype h.choose := h.choose_spec.choose
  let a := h.choose_spec.choose_spec.choose
  let : ∀ i, Simple (a i) := h.choose_spec.choose_spec.choose_spec.choose
  let : HasBiproduct a := h.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let e := h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.some
  let p (i : h.choose) : Y ⟶ (SimpleClasses.classOf (a i)).repr :=
    e.hom ≫ biproduct.π a i ≫ (SimpleClasses.classOfReprIso (a i)).inv
  let q (i : h.choose) : (SimpleClasses.classOf (a i)).repr ⟶ Y :=
    (SimpleClasses.classOfReprIso (a i)).hom ≫ biproduct.ι a i ≫ e.inv
  -- Unfold `inductionEndπ X Y` to `endπAux` for the chosen decomposition of `Y`.
  change inductionMapLift w ≫ F.map (endπAux a e X) = w Y
  dsimp only [endπAux]
  rw [F.map_sum, Preadditive.comp_sum]
  calc ∑ i, inductionMapLift w ≫ F.map (biproduct.π (inductionSummand X)
          (SimpleClasses.classOf (a i)) ≫ q i ▷ (X ⊗ _) ≫ Y ◁ X ◁ (p i)ᘁ)
      = ∑ i, (inductionMapLift w ≫
          F.map (biproduct.π (inductionSummand X) (SimpleClasses.classOf (a i)))) ≫
          F.map ((SimpleClasses.classOf (a i)).repr ◁ X ◁ (p i)ᘁ) ≫
          F.map (q i ▷ (X ⊗ Yᘁ)) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [← whisker_exchange, F.map_comp, F.map_comp, Category.assoc]
    _ = ∑ i, w Y ≫ F.map ((p i ≫ q i) ▷ (X ⊗ Yᘁ)) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [inductionMapLift_comp_map_π, ← Category.assoc, ← hw (p i), Category.assoc,
            ← F.map_comp, ← comp_whiskerRight]
    _ = w Y := by
          rw [← Preadditive.comp_sum, ← F.map_sum, ← sum_whiskerRight,
            SimpleClasses.sum_comp_classOfReprIso_eq_id a e, id_whiskerRight, F.map_id,
            Category.comp_id]

/-- Composing `inductionLift w` with `inductionEndπ X Y` recovers `w Y` whenever `w` is
dinatural. -/
@[reassoc]
theorem inductionLift_comp_endπ {W X : C} (w : ∀ Y : C, W ⟶ Y ⊗ X ⊗ Yᘁ)
    (hw : ∀ {Y Y' : C} (g : Y ⟶ Y'),
      w Y ≫ g ▷ (X ⊗ Yᘁ) = w Y' ≫ Y' ◁ X ◁ gᘁ)
    (Y : C) :
    inductionLift w ≫ inductionEndπ X Y = w Y :=
  inductionMapLift_comp_map_endπ (F := 𝟭 C) w hw Y

variable (k : Type w) [Field k] [IsAlgClosed k] [Linear k C] [MonoidalLinear k C]
  [∀ S : SimpleClasses C, FiniteDimensional k (S.repr ⟶ S.repr)]

include k in
/-- Two morphisms into `inductionObj X` agree once they agree after every end projection
`inductionEndπ X Y`. -/
theorem inductionObj_hom_ext_endπ {W X : C}
    {f₁ f₂ : W ⟶ inductionObj X}
    (h : ∀ Y : C, f₁ ≫ inductionEndπ X Y = f₂ ≫ inductionEndπ X Y) :
    f₁ = f₂ :=
  inductionObj_map_hom_ext (F := 𝟭 C) fun S ↦ by
    simpa [inductionEndπ_repr k X S] using h S.repr

end UniversalEnd

end CategoryTheory.Center
