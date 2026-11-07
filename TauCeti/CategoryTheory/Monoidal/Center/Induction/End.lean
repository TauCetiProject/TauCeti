/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Rigid.DualFunctor
public import TauCeti.CategoryTheory.Monoidal.Rigid.Preadditive
public import TauCeti.CategoryTheory.Preadditive.Schur
public import TauCeti.CategoryTheory.Semisimple.Basic
public import TauCeti.CategoryTheory.Simple.Classes

/-!
# The categorical end `∫_{Y ∈ C} (Y ⊗ X) ⊗ Yᘁ` via simple representatives

Let `C` be a finite semisimple rigid `k`-linear monoidal category over an algebraically closed
field `k`, with finitely many isomorphism classes of simple objects and finite-dimensional simple
endomorphism spaces. For each `X : C`, the finite biproduct

```
⨁ (S : SimpleClasses C), (S.repr ⊗ X) ⊗ S.reprᘁ
```

realizes the categorical end `∫_{Y ∈ C} (Y ⊗ X) ⊗ Yᘁ`: choosing a decomposition of any `Y : C` as a
finite biproduct of simple objects produces a canonical projection
`centerInductionCodinat X Y : (⨁ S, (S.repr ⊗ X) ⊗ S.reprᘁ) ⟶ (Y ⊗ X) ⊗ Yᘁ` which is dinatural in
`Y` (`(g ▷ X) ▷ Yᘁ` against `(Y' ⊗ X) ◁ gᘁ`) by Schur's lemma, independent of the chosen
decomposition, and universal among dinatural wedges. Moreover, since every additive functor
`F : C ⥤ C` preserves finite biproducts, `F` preserves this universal end property.

In `TauCeti.CategoryTheory.Monoidal.Center.Induction`, this universal property under `tensorLeft U`
and `tensorRight U` equips `⨁ S, (S.repr ⊗ X) ⊗ S.reprᘁ` with its canonical half-braiding and yields
the right adjoint `centerInduction k C : C ⥤ Center C` to `Center.forget C`.

## Main declarations

* `TauCeti.centerInductionCodinat`: the canonical dinatural end projection
  `(⨁ S, (S.repr ⊗ X) ⊗ S.reprᘁ) ⟶ (Y ⊗ X) ⊗ Yᘁ`, with dinaturality
  `TauCeti.centerInductionCodinat_dinatural`, evaluation `TauCeti.centerInductionCodinat_repr` on
  simple representatives, and naturality `TauCeti.biproduct_map_comp_centerInductionCodinat` in `X`;
* `TauCeti.centerInductionMapLift`, `TauCeti.centerInductionMapLift_comp_map_codinat`, and
  `TauCeti.centerInduction_map_hom_ext`: the universal end lift and uniqueness principle under any
  additive functor `F : C ⥤ C`;
* `TauCeti.centerInductionLift`, `TauCeti.centerInductionLift_comp_codinat`, and
  `TauCeti.centerInduction_hom_ext`: the universal end lift and uniqueness principle in `C`.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005), §§2, 8
* M. Müger, *From subfactors to categories and topology II: The quantum double of tensor
  categories and subfactors*, J. Pure Appl. Algebra **180** (2003), 159–219
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§7.13, 9.3
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory ExactPairing

universe w v u

namespace TauCeti

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [Linear k C] [MonoidalLinear k C] [RigidCategory C] [IsFiniteSemisimpleCategory C]
  [Finite (SimpleClasses C)] [∀ S : SimpleClasses C, FiniteDimensional k (S.repr ⟶ S.repr)]

attribute [local instance] Abelian.hasFiniteBiproducts

namespace CenterInduction

/-- The underlying object `⨁ S : SimpleClasses C, (S.repr ⊗ X) ⊗ S.reprᘁ` of the categorical end
`∫_{Y ∈ C} (Y ⊗ X) ⊗ Yᘁ`. -/
private abbrev Obj (X : C) : C :=
  ⨁ fun S : SimpleClasses C ↦ (S.repr ⊗ X) ⊗ S.reprᘁ

/-- The summand family `S ↦ (S.repr ⊗ X) ⊗ S.reprᘁ` defining `Obj X`. -/
private abbrev summand (X : C) (S : SimpleClasses C) : C :=
  (S.repr ⊗ X) ⊗ S.reprᘁ

section EndWedge

omit [IsFiniteSemisimpleCategory C]

omit [MonoidalCategory C] [MonoidalPreadditive C] [RigidCategory C] [Finite (SimpleClasses C)] in
/-- Partition of the identity of `Y` through the simple representatives of a biproduct
decomposition `e : Y ≅ ⨁ a`. -/
private theorem sum_decomp_id {Y : C} {ι : Type*} [Fintype ι] (a : ι → C) [∀ i, Simple (a i)]
    [HasBiproduct a] (e : Y ≅ ⨁ a) :
    (∑ i : ι, (e.hom ≫ biproduct.π a i ≫ (SimpleClasses.classOfReprIso (a i)).inv) ≫
      ((SimpleClasses.classOfReprIso (a i)).hom ≫ biproduct.ι a i ≫ e.inv)) = 𝟙 Y := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  calc ∑ i, e.hom ≫ biproduct.π a i ≫ biproduct.ι a i ≫ e.inv
      = e.hom ≫ (∑ i, biproduct.π a i ≫ biproduct.ι a i) ≫ e.inv := by
          simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
    _ = 𝟙 Y := by rw [biproduct.total, Category.id_comp, e.hom_inv_id]

include k in
/-- On representatives of simple classes, the biproduct projections satisfy the end dinaturality
condition by Schur's lemma. -/
private theorem repr_dinatural (X : C) {S T : SimpleClasses C} (m : S.repr ⟶ T.repr) :
    biproduct.π (summand X) S ≫ ((m ▷ X) ▷ S.reprᘁ) =
      biproduct.π (summand X) T ≫ ((T.repr ⊗ X) ◁ rightAdjointMate m) := by
  by_cases h : S = T
  · subst h
    obtain ⟨c, rfl⟩ := endomorphism_simple_eq_smul_id k m
    simp [rightAdjointMate]
  · rw [(SimpleClasses.homOrthogonal_repr h).elim m 0]
    simp

/-- Auxiliary projection from `Obj X` to `(Y ⊗ X) ⊗ Yᘁ` associated to a chosen simple biproduct
decomposition of `Y`. -/
private def codinatAux {Y : C} {ι : Type*} [Fintype ι] (a : ι → C) [∀ i, Simple (a i)]
    [HasBiproduct a] (e : Y ≅ ⨁ a) (X : C) : Obj X ⟶ (Y ⊗ X) ⊗ Yᘁ :=
  ∑ i : ι,
    biproduct.π (summand X) (SimpleClasses.classOf (a i)) ≫
      (((SimpleClasses.classOfReprIso (a i)).hom ≫ biproduct.ι a i ≫ e.inv) ▷ X) ▷
        (SimpleClasses.classOf (a i)).reprᘁ ≫
      ((Y ⊗ X) ◁ rightAdjointMate
        (e.hom ≫ biproduct.π a i ≫ (SimpleClasses.classOfReprIso (a i)).inv))

include k in
/-- `codinatAux` is dinatural with respect to any morphism `g : Y ⟶ Y'`, regardless of which
simple decompositions of `Y` and `Y'` are used. -/
private theorem codinatAux_dinatural {Y Y' : C} {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (a : ι → C) [∀ i, Simple (a i)] [HasBiproduct a] (e : Y ≅ ⨁ a)
    (b : ι' → C) [∀ j, Simple (b j)] [HasBiproduct b] (e' : Y' ≅ ⨁ b)
    (X : C) (g : Y ⟶ Y') :
    codinatAux a e X ≫ ((g ▷ X) ▷ Yᘁ) = codinatAux b e' X ≫ ((Y' ⊗ X) ◁ rightAdjointMate g) := by
  let p (i : ι) : Y ⟶ (SimpleClasses.classOf (a i)).repr :=
    e.hom ≫ biproduct.π a i ≫ (SimpleClasses.classOfReprIso (a i)).inv
  let q (i : ι) : (SimpleClasses.classOf (a i)).repr ⟶ Y :=
    (SimpleClasses.classOfReprIso (a i)).hom ≫ biproduct.ι a i ≫ e.inv
  let p' (j : ι') : Y' ⟶ (SimpleClasses.classOf (b j)).repr :=
    e'.hom ≫ biproduct.π b j ≫ (SimpleClasses.classOfReprIso (b j)).inv
  let q' (j : ι') : (SimpleClasses.classOf (b j)).repr ⟶ Y' :=
    (SimpleClasses.classOfReprIso (b j)).hom ≫ biproduct.ι b j ≫ e'.inv
  have hY : ∑ i, p i ≫ q i = 𝟙 Y := sum_decomp_id a e
  have hY' : ∑ j, p' j ≫ q' j = 𝟙 Y' := sum_decomp_id b e'
  have hgL (i : ι) : q i ≫ g = ∑ j, (q i ≫ g ≫ p' j) ≫ q' j := by
    simp only [Category.assoc, ← Preadditive.comp_sum, hY', Category.comp_id]
  have hgR (j : ι') : g ≫ p' j = ∑ i, p i ≫ (q i ≫ g ≫ p' j) := by
    simp only [← Category.assoc, ← Preadditive.sum_comp, hY, Category.id_comp]
  -- Fold the summands of `codinatAux` in terms of `p`, `q`, `p'`, `q'`.
  change (∑ i, biproduct.π (summand X) (SimpleClasses.classOf (a i)) ≫
      ((q i ▷ X) ▷ (SimpleClasses.classOf (a i)).reprᘁ) ≫
      ((Y ⊗ X) ◁ rightAdjointMate (p i))) ≫ ((g ▷ X) ▷ Yᘁ) =
    (∑ j, biproduct.π (summand X) (SimpleClasses.classOf (b j)) ≫
      ((q' j ▷ X) ▷ (SimpleClasses.classOf (b j)).reprᘁ) ≫
      ((Y' ⊗ X) ◁ rightAdjointMate (p' j))) ≫ ((Y' ⊗ X) ◁ rightAdjointMate g)
  calc (∑ i, biproduct.π (summand X) (SimpleClasses.classOf (a i)) ≫
          ((q i ▷ X) ▷ _) ≫ ((Y ⊗ X) ◁ rightAdjointMate (p i))) ≫ ((g ▷ X) ▷ Yᘁ)
      = ∑ i, biproduct.π (summand X) (SimpleClasses.classOf (a i)) ≫
          (((q i ≫ g) ▷ X) ▷ _) ≫ ((Y' ⊗ X) ◁ rightAdjointMate (p i)) := by
          simp only [Preadditive.sum_comp, Category.assoc, whisker_exchange,
            ← comp_whiskerRight_assoc, ← comp_whiskerRight]
    _ = ∑ i, ∑ j, (biproduct.π (summand X) (SimpleClasses.classOf (a i)) ≫
          (((q i ≫ g ≫ p' j) ▷ X) ▷ _)) ≫
          ((q' j ▷ X) ▷ _) ≫ ((Y' ⊗ X) ◁ rightAdjointMate (p i)) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hgL i]
          simp only [sum_whiskerRight, Preadditive.comp_sum,
            Preadditive.sum_comp, Category.assoc, comp_whiskerRight]
    _ = ∑ i, ∑ j, biproduct.π (summand X) (SimpleClasses.classOf (b j)) ≫
          ((q' j ▷ X) ▷ _) ≫
          ((Y' ⊗ X) ◁ (rightAdjointMate (q i ≫ g ≫ p' j) ≫ rightAdjointMate (p i))) := by
          refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
          rw [repr_dinatural k X (q i ≫ g ≫ p' j), Category.assoc, whisker_exchange_assoc,
            ← MonoidalCategory.whiskerLeft_comp]
    _ = ∑ j, biproduct.π (summand X) (SimpleClasses.classOf (b j)) ≫
          ((q' j ▷ X) ▷ _) ≫ ((Y' ⊗ X) ◁ rightAdjointMate (g ≫ p' j)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          have hsum (s : Finset ι) :
              rightAdjointMate (∑ i ∈ s, p i ≫ (q i ≫ g ≫ p' j)) =
                ∑ i ∈ s, rightAdjointMate (p i ≫ (q i ≫ g ≫ p' j)) := by
            classical
            induction s using Finset.induction_on with
            | empty => simp
            | insert _ _ hi ih => simp [Finset.sum_insert hi, ih]
          conv_rhs => rw [hgR j, hsum Finset.univ]
          simp only [comp_rightAdjointMate, whiskerLeft_sum, Preadditive.comp_sum, Category.assoc]
    _ = (∑ j, biproduct.π (summand X) (SimpleClasses.classOf (b j)) ≫
          ((q' j ▷ X) ▷ _) ≫ ((Y' ⊗ X) ◁ rightAdjointMate (p' j))) ≫
          ((Y' ⊗ X) ◁ rightAdjointMate g) := by
          simp only [Preadditive.sum_comp, Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
            comp_rightAdjointMate]

end EndWedge

end CenterInduction

/-- The canonical dinatural end projection `(⨁ S, (S.repr ⊗ X) ⊗ S.reprᘁ) ⟶ (Y ⊗ X) ⊗ Yᘁ`. -/
def centerInductionCodinat (X Y : C) :
    (⨁ fun S : SimpleClasses C ↦ (S.repr ⊗ X) ⊗ S.reprᘁ) ⟶ (Y ⊗ X) ⊗ Yᘁ :=
  let h := IsFiniteSemisimpleCategory.exists_biproduct_simples Y
  let _ := h.choose_spec.choose
  let a := h.choose_spec.choose_spec.choose
  let _ := h.choose_spec.choose_spec.choose_spec.choose
  let _ := h.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let e := h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.some
  CenterInduction.codinatAux a e X

include k in
/-- Dinaturality of `centerInductionCodinat`: right-whiskering by `g : Y ⟶ Y'` on the first factor
agrees with left-whiskering by `gᘁ : Y'ᘁ ⟶ Yᘁ` on the third factor. -/
@[reassoc]
theorem centerInductionCodinat_dinatural (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    centerInductionCodinat X Y ≫ ((g ▷ X) ▷ Yᘁ) =
      centerInductionCodinat X Y' ≫ ((Y' ⊗ X) ◁ rightAdjointMate g) := by
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
  exact CenterInduction.codinatAux_dinatural k a e b e' X g

include k in
/-- On the chosen representative `S.repr` of a simple class `S`, `centerInductionCodinat` is the
biproduct projection onto the `S`-summand. -/
@[reassoc]
theorem centerInductionCodinat_repr (X : C) (S : SimpleClasses C) :
    centerInductionCodinat X S.repr =
      biproduct.π (fun T : SimpleClasses C ↦ (T.repr ⊗ X) ⊗ T.reprᘁ) S := by
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
  -- Unfold `centerInductionCodinat X S.repr` to `codinatAux` for the chosen decomposition of
  -- `S.repr`.
  change CenterInduction.codinatAux a e X = biproduct.π (CenterInduction.summand X) S
  symm
  calc biproduct.π (CenterInduction.summand X) S
      = biproduct.π (CenterInduction.summand X) S ≫ (((∑ i, p i ≫ q i) ▷ X) ▷ S.reprᘁ) := by
          rw [CenterInduction.sum_decomp_id a e, id_whiskerRight, id_whiskerRight, Category.comp_id]
    _ = ∑ i, (biproduct.π (CenterInduction.summand X) S ≫ ((p i ▷ X) ▷ S.reprᘁ)) ≫
          ((q i ▷ X) ▷ S.reprᘁ) := by
          simp only [sum_whiskerRight, Preadditive.comp_sum, Category.assoc, comp_whiskerRight]
    _ = ∑ i, biproduct.π (CenterInduction.summand X) (SimpleClasses.classOf (a i)) ≫
          ((q i ▷ X) ▷ _) ≫ ((S.repr ⊗ X) ◁ rightAdjointMate (p i)) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [CenterInduction.repr_dinatural k X (p i), Category.assoc, whisker_exchange]
    _ = CenterInduction.codinatAux a e X := rfl

omit [MonoidalPreadditive C] in
/-- Naturality in `X` of `centerInductionCodinat` with respect to the summandwise biproduct map
`biproduct.map (fun S ↦ (S.repr ◁ f) ▷ S.reprᘁ)`. -/
@[reassoc]
theorem biproduct_map_comp_centerInductionCodinat {X X' : C} (f : X ⟶ X') (Y : C) :
    biproduct.map (fun S : SimpleClasses C ↦ (S.repr ◁ f) ▷ S.reprᘁ) ≫
        centerInductionCodinat X' Y =
      centerInductionCodinat X Y ≫ ((Y ◁ f) ▷ Yᘁ) := by
  dsimp only [centerInductionCodinat, CenterInduction.codinatAux]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp, biproduct.map_π_assoc, Category.assoc]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  rw [← comp_whiskerRight_assoc, whisker_exchange, comp_whiskerRight_assoc,
    ← whisker_exchange, ← whisker_exchange_assoc]

section UniversalEnd

omit [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C] in
/-- Morphisms into `F.obj (⨁ S, (S.repr ⊗ X) ⊗ S.reprᘁ)` for an additive functor `F : C ⥤ C` agree
once they agree after every summand projection `F.map (biproduct.π _ S)`. -/
theorem centerInduction_map_hom_ext {F : C ⥤ C} [F.Additive] {W X : C}
    {f₁ f₂ : W ⟶ F.obj (⨁ fun S : SimpleClasses C ↦ (S.repr ⊗ X) ⊗ S.reprᘁ)}
    (h : ∀ S : SimpleClasses C,
      f₁ ≫ F.map (biproduct.π (fun T : SimpleClasses C ↦ (T.repr ⊗ X) ⊗ T.reprᘁ) S) =
        f₂ ≫ F.map (biproduct.π (fun T : SimpleClasses C ↦ (T.repr ⊗ X) ⊗ T.reprᘁ) S)) :
    f₁ = f₂ := by
  let _ : Fintype (SimpleClasses C) := Fintype.ofFinite (SimpleClasses C)
  calc f₁ = f₁ ≫ F.map (𝟙 (CenterInduction.Obj X)) := by rw [F.map_id, Category.comp_id]
    _ = f₁ ≫ F.map (∑ S : SimpleClasses C,
          biproduct.π (CenterInduction.summand X) S ≫
            biproduct.ι (CenterInduction.summand X) S) := by
          rw [biproduct.total]
    _ = ∑ S : SimpleClasses C,
          (f₁ ≫ F.map (biproduct.π (CenterInduction.summand X) S)) ≫
            F.map (biproduct.ι (CenterInduction.summand X) S) := by
          simp only [F.map_sum, F.map_comp, Preadditive.comp_sum, Category.assoc]
    _ = ∑ S : SimpleClasses C,
          (f₂ ≫ F.map (biproduct.π (CenterInduction.summand X) S)) ≫
            F.map (biproduct.ι (CenterInduction.summand X) S) := by
          simp_rw [h]
    _ = f₂ := by
          rw [← Finset.sum_congr rfl fun S _ ↦ (Category.assoc _ _ _).symm]
          simp only [← F.map_comp, ← Preadditive.comp_sum, ← F.map_sum,
            biproduct.total, F.map_id, Category.comp_id]

/-- Universal end lift into `F.obj (⨁ S : SimpleClasses C, (S.repr ⊗ X) ⊗ S.reprᘁ)` associated to a
family `w : ∀ Y : C, W ⟶ F.obj ((Y ⊗ X) ⊗ Yᘁ)` under a functor `F : C ⥤ C`. -/
def centerInductionMapLift {F : C ⥤ C} {W X : C}
    (w : ∀ Y : C, W ⟶ F.obj ((Y ⊗ X) ⊗ Yᘁ)) :
    W ⟶ F.obj (⨁ fun S : SimpleClasses C ↦ (S.repr ⊗ X) ⊗ S.reprᘁ) :=
  let _ : Fintype (SimpleClasses C) := Fintype.ofFinite (SimpleClasses C)
  ∑ S : SimpleClasses C, w S.repr ≫ F.map (biproduct.ι (CenterInduction.summand X) S)

omit [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C] in
/-- Evaluating `centerInductionMapLift w` at the `S`-summand projection recovers `w S.repr`. -/
@[reassoc]
theorem centerInductionMapLift_comp_map_π {F : C ⥤ C} [F.PreservesZeroMorphisms] {W X : C}
    (w : ∀ Y : C, W ⟶ F.obj ((Y ⊗ X) ⊗ Yᘁ)) (S : SimpleClasses C) :
    centerInductionMapLift w ≫
        F.map (biproduct.π (fun T : SimpleClasses C ↦ (T.repr ⊗ X) ⊗ T.reprᘁ) S) =
      w S.repr := by
  let _ : Fintype (SimpleClasses C) := Fintype.ofFinite (SimpleClasses C)
  classical
  dsimp only [centerInductionMapLift]
  simp only [Preadditive.sum_comp, Category.assoc, ← F.map_comp]
  rw [Finset.sum_eq_single S]
  · rw [biproduct.ι_π_self, F.map_id, Category.comp_id]
  · intro T _ hTS
    rw [biproduct.ι_π_ne _ hTS, F.map_zero, comp_zero]
  · intro hS
    exact absurd (Finset.mem_univ S) hS

/-- Universal property of `centerInductionCodinat` under an additive functor `F : C ⥤ C`: any
dinatural wedge `w : ∀ Y : C, W ⟶ F.obj ((Y ⊗ X) ⊗ Yᘁ)` factors through
`centerInductionMapLift w`. -/
@[reassoc]
theorem centerInductionMapLift_comp_map_codinat {F : C ⥤ C} [F.Additive] {W X : C}
    (w : ∀ Y : C, W ⟶ F.obj ((Y ⊗ X) ⊗ Yᘁ))
    (hw : ∀ {Y Y' : C} (g : Y ⟶ Y'),
      w Y ≫ F.map ((g ▷ X) ▷ Yᘁ) = w Y' ≫ F.map ((Y' ⊗ X) ◁ rightAdjointMate g))
    (Y : C) :
    centerInductionMapLift w ≫ F.map (centerInductionCodinat X Y) = w Y := by
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
  -- Unfold `centerInductionCodinat X Y` to `codinatAux` for the chosen decomposition of `Y`.
  change centerInductionMapLift w ≫ F.map (CenterInduction.codinatAux a e X) = w Y
  dsimp only [CenterInduction.codinatAux]
  rw [F.map_sum, Preadditive.comp_sum]
  calc ∑ i, centerInductionMapLift w ≫ F.map (biproduct.π (CenterInduction.summand X)
          (SimpleClasses.classOf (a i)) ≫ ((q i ▷ X) ▷ _) ≫ ((Y ⊗ X) ◁ rightAdjointMate (p i)))
      = ∑ i, (centerInductionMapLift w ≫
          F.map (biproduct.π (CenterInduction.summand X) (SimpleClasses.classOf (a i)))) ≫
          F.map (((SimpleClasses.classOf (a i)).repr ⊗ X) ◁ rightAdjointMate (p i)) ≫
          F.map ((q i ▷ X) ▷ Yᘁ) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [← whisker_exchange, F.map_comp, F.map_comp, Category.assoc]
    _ = ∑ i, w Y ≫ F.map (((p i ≫ q i) ▷ X) ▷ Yᘁ) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [centerInductionMapLift_comp_map_π, ← Category.assoc, ← hw (p i), Category.assoc,
            ← F.map_comp, ← comp_whiskerRight, ← comp_whiskerRight]
    _ = w Y := by
          rw [← Preadditive.comp_sum, ← F.map_sum, ← sum_whiskerRight, ← sum_whiskerRight,
            CenterInduction.sum_decomp_id a e, id_whiskerRight, id_whiskerRight, F.map_id,
            Category.comp_id]

/-- Universal end lift into `⨁ S : SimpleClasses C, (S.repr ⊗ X) ⊗ S.reprᘁ` associated to a wedge
`w : ∀ Y : C, W ⟶ (Y ⊗ X) ⊗ Yᘁ`. -/
def centerInductionLift {W X : C} (w : ∀ Y : C, W ⟶ (Y ⊗ X) ⊗ Yᘁ) :
    W ⟶ ⨁ fun S : SimpleClasses C ↦ (S.repr ⊗ X) ⊗ S.reprᘁ :=
  centerInductionMapLift (F := 𝟭 C) w

/-- Composing `centerInductionLift w` with `centerInductionCodinat X Y` recovers `w Y` whenever `w`
is dinatural. -/
@[reassoc]
theorem centerInductionLift_comp_codinat {W X : C} (w : ∀ Y : C, W ⟶ (Y ⊗ X) ⊗ Yᘁ)
    (hw : ∀ {Y Y' : C} (g : Y ⟶ Y'),
      w Y ≫ ((g ▷ X) ▷ Yᘁ) = w Y' ≫ ((Y' ⊗ X) ◁ rightAdjointMate g))
    (Y : C) :
    centerInductionLift w ≫ centerInductionCodinat X Y = w Y :=
  centerInductionMapLift_comp_map_codinat (F := 𝟭 C) w hw Y

include k in
/-- Two morphisms into `⨁ S : SimpleClasses C, (S.repr ⊗ X) ⊗ S.reprᘁ` agree once they agree after
every end projection `centerInductionCodinat X Y`. -/
theorem centerInduction_hom_ext {W X : C}
    {f₁ f₂ : W ⟶ ⨁ fun S : SimpleClasses C ↦ (S.repr ⊗ X) ⊗ S.reprᘁ}
    (h : ∀ Y : C, f₁ ≫ centerInductionCodinat X Y = f₂ ≫ centerInductionCodinat X Y) :
    f₁ = f₂ :=
  centerInduction_map_hom_ext (F := 𝟭 C) fun S ↦ by
    simpa [centerInductionCodinat_repr k X S] using h S.repr

end UniversalEnd

end TauCeti
