/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Cobase change of relative cell complexes

Let `f : X ⟶ Y` be a relative cell complex, so that `Y` is obtained from `X` by a transfinite
sequence of cell attachments, and let `a : X ⟶ Z` be any morphism. In a pushout square

```
X --a--> Z
|        |
f        f'
v        v
Y --b--> Y'
```

the morphism `f'` is again a relative cell complex, with the same cells, attached at the same
steps (`HomotopicalAlgebra.RelativeCellComplex.ofIsPushout`); the inclusion of a cell of `f'` is
the inclusion of the corresponding cell of `f` followed by `b`
(`HomotopicalAlgebra.RelativeCellComplex.ofIsPushout_cells_ι`). In topology, this says that
gluing a relative CW complex `(Y, X)` to an arbitrary space `Z` along a map `X ⟶ Z` gives a
relative CW complex over `Z`, whose cells are the cells of `(Y, X)`.

The stages of `f'` are the pushouts of the stages of `f` along `a`. That they again form a
transfinite composition (`CategoryTheory.TransfiniteCompositionOfShape.ofIsPushout`) is because
pushing out along `a` is a left adjoint `Under X ⥤ Under Z` (`CategoryTheory.Under.pushout`), and
the forgetful functor `Under Z ⥤ C` preserves connected colimits, such as colimits indexed by a
nonempty well-ordered type. A single cell attachment is carried across the pushout square by
pasting it with the square (`HomotopicalAlgebra.AttachCells.ofIsPushout`).

## References

* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press,
  1990.
* M. Hovey, *Model Categories*, Mathematical Surveys and Monographs 63, American Mathematical
  Society, 1999, Section 2.1, for the stability of relative cell complexes under pushouts.
-/

@[expose] public section

open CategoryTheory Limits

universe w w' t v u

namespace HomotopicalAlgebra.AttachCells

variable {C : Type u} [Category.{v} C] {α : Type t} {A B : α → C} {g : ∀ a, A a ⟶ B a}
  {X₁ X₂ Y₁ Y₂ : C} {f : X₁ ⟶ X₂} (c : AttachCells.{w} g f)
  {p : X₁ ⟶ Y₁} {f' : Y₁ ⟶ Y₂} {b : X₂ ⟶ Y₂} (sq : IsPushout p f f' b)

/-- **Cobase change of a cell attachment.** If `X₂` is obtained from `X₁` by attaching cells along
`f` and the square formed by `p`, `f`, `f'` and `b` is a pushout, then `Y₂` is obtained from `Y₁`
by attaching the same cells along `f'`, with attaching maps composed with `p`. -/
def ofIsPushout : AttachCells.{w} g f' where
  ι := c.ι
  π := c.π
  cofan₁ := c.cofan₁
  cofan₂ := c.cofan₂
  isColimit₁ := c.isColimit₁
  isColimit₂ := c.isColimit₂
  m := c.m
  hm := c.hm
  g₁ := c.g₁ ≫ p
  g₂ := c.g₂ ≫ b
  isPushout := c.isPushout.paste_horiz sq

/-- The inclusion of a cell after cobase change is the original inclusion followed by `b`. -/
@[simp, reassoc]
lemma ofIsPushout_cell (i : c.ι) : (c.ofIsPushout sq).cell i = c.cell i ≫ b :=
  -- Both sides are `c.cofan₂.inj i ≫ c.g₂ ≫ b` by definition, up to associativity.
  (Category.assoc _ _ _).symm

end HomotopicalAlgebra.AttachCells

namespace CategoryTheory.TransfiniteCompositionOfShape

variable {C : Type u} [Category.{v} C]
  {J : Type w'} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y Z Y' : C} {f : X ⟶ Y} (c : TransfiniteCompositionOfShape J f)

/-- The morphisms from the source `X` of a transfinite composition to its stages. -/
@[simps]
def toStage : (Functor.const J).obj X ⟶ c.F where
  app j := c.isoBot.inv ≫ c.F.map (homOfLE bot_le)
  naturality _ _ g := by
    dsimp
    rw [Category.id_comp, Category.assoc, ← Functor.map_comp]
    -- Morphisms in the preorder category `J` between given objects are unique.
    rfl

/-- The morphism from `X` to the initial stage is the inverse of `isoBot`. -/
lemma toStage_app_bot : c.toStage.app ⊥ = c.isoBot.inv := by
  simp

/-- The morphisms from `X` to the stages compose with the inclusions of the stages to `f`. -/
@[reassoc]
lemma toStage_app_comp_incl_app (j : J) : c.toStage.app j ≫ c.incl.app j = f := by
  simp

instance : IsIso (c.toStage.app ⊥) := by
  rw [toStage_app_bot]
  infer_instance

-- Nonempty linear orders are filtered, hence connected, so that `Under.forget` preserves colimits
-- indexed by them.
attribute [local instance] IsFiltered.isConnected

variable (a : X ⟶ Z) [HasPushoutsAlong a]

/-- The stages of the cobase change of a transfinite composition along `a : X ⟶ Z`: the stage
`j` is the pushout of the morphism from `X` to the stage `j` of `c` along `a`. -/
noncomputable abbrev pushoutStage : J ⥤ C where
  obj j := pushout (c.toStage.app j) a
  map {i j} g := pushout.desc (c.F.map g ≫ pushout.inl (c.toStage.app j) a)
    (pushout.inr (c.toStage.app j) a) (by
    rw [← Category.assoc, ← c.toStage.naturality g]
    simpa using pushout.condition (f := c.toStage.app j) (g := a))
  map_id _ := pushout.hom_ext (by simp) (by simp)
  map_comp _ _ := pushout.hom_ext (by simp) (by simp)

@[reassoc]
lemma inl_pushoutStage_map {i j : J} (g : i ⟶ j) :
    pushout.inl (c.toStage.app i) a ≫ (c.pushoutStage a).map g =
      c.F.map g ≫ pushout.inl (c.toStage.app j) a :=
  pushout.inl_desc _ _ _

@[reassoc]
lemma inr_pushoutStage_map {i j : J} (g : i ⟶ j) :
    pushout.inr (c.toStage.app i) a ≫ (c.pushoutStage a).map g =
      pushout.inr (c.toStage.app j) a :=
  pushout.inr_desc _ _ _

/-- Each step of the pushed-out stages is the pushout of the corresponding step of `c`. -/
theorem isPushout_pushoutStage_map {i j : J} (g : i ⟶ j) :
    IsPushout (pushout.inl (c.toStage.app i) a) (c.F.map g) ((c.pushoutStage a).map g)
      (pushout.inl (c.toStage.app j) a) := by
  refine (IsPushout.of_left ?_ (inl_pushoutStage_map c a g).symm
    (IsPushout.of_hasPushout _ _)).flip
  have h : c.toStage.app i ≫ c.F.map g = c.toStage.app j := by
    simpa using (c.toStage.naturality g).symm
  rw [h, inr_pushoutStage_map]
  exact IsPushout.of_hasPushout _ _

/-- The stages of the cobase change are obtained by lifting the stages of `c` to `Under X`,
pushing out along `a` and forgetting. -/
noncomputable def pushoutStageIsoUnder :
    c.pushoutStage a ≅ Under.lift c.F c.toStage ⋙ Under.pushout a ⋙ Under.forget Z :=
  -- Both functors send `g` to the morphism of pushouts induced by `c.F.map g`.
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦
    (Category.comp_id _).trans (Category.id_comp _).symm

instance : (Under.lift c.F c.toStage).IsWellOrderContinuous where
  nonempty_isColimit m hm := by
    -- `Set.Iio m` is nonempty and directed, hence connected.
    have : Nonempty (Set.Iio m) := ⟨⟨⊥, hm.bot_lt⟩⟩
    exact ⟨isColimitOfReflects (Under.forget X) (c.F.isColimitOfIsWellOrderContinuous m hm)⟩

instance : PreservesWellOrderContinuousOfShape J (Under.pushout a ⋙ Under.forget Z) where
  preservesColimitsOfShape m hm := by
    -- `Set.Iio m` is nonempty and directed, hence connected.
    have : Nonempty (Set.Iio m) := ⟨⟨⊥, hm.bot_lt⟩⟩
    infer_instance

instance : (c.pushoutStage a).IsWellOrderContinuous :=
  Functor.isWellOrderContinuous_of_iso (c.pushoutStageIsoUnder a).symm

variable {a} in
/-- A cocone over the pushed-out stages restricts to a cocone over the stages of `c`. -/
noncomputable abbrev restrictCocone (t : Cocone (c.pushoutStage a)) : Cocone c.F where
  pt := t.pt
  ι :=
    { app j := pushout.inl (c.toStage.app j) a ≫ t.ι.app j
      naturality i j g := by simpa using pushout.inl (c.toStage.app i) a ≫= t.w g }

variable {a} {f' : Z ⟶ Y'} {b : Y ⟶ Y'} (sq : IsPushout a f f' b)

/-- **Cobase change of a transfinite composition.** If `f` is a transfinite composition of shape
`J` and the square formed by `a`, `f`, `f'` and `b` is a pushout, then `f'` is a transfinite
composition of shape `J`, whose stage `j` is the pushout of the stage `j` of `f` along `a`. -/
noncomputable def ofIsPushout : TransfiniteCompositionOfShape J f' where
  F := c.pushoutStage a
  isoBot := (asIso (pushout.inr (c.toStage.app ⊥) a)).symm
  incl :=
    { app j := pushout.desc (c.incl.app j ≫ b) f' (by simp [sq.w])
      naturality i j g := by
        dsimp
        apply pushout.hom_ext <;> simp }
  isColimit :=
    { desc t := sq.desc (pushout.inr (c.toStage.app ⊥) a ≫ t.ι.app ⊥)
        (c.isColimit.desc (c.restrictCocone t)) (by
          rw [← pushout.condition_assoc]
          exact (c.toStage.app ⊥ ≫= (c.isColimit.fac (c.restrictCocone t) ⊥).symm).trans
            (c.toStage_app_comp_incl_app_assoc ⊥ _))
      fac t j := by
        refine pushout.hom_ext ?_ ?_
        · simp only [pushout.inl_desc_assoc, Category.assoc]
          rw [sq.inr_desc]
          exact c.isColimit.fac (c.restrictCocone t) j
        · simp only [pushout.inr_desc_assoc]
          rw [sq.inl_desc]
          simpa using pushout.inr (c.toStage.app ⊥) a ≫= (t.w (homOfLE bot_le : ⊥ ⟶ j)).symm
      uniq t m hm := by
        apply sq.hom_ext
        · rw [sq.inl_desc]
          simpa using pushout.inr (c.toStage.app ⊥) a ≫= hm ⊥
        · rw [sq.inr_desc]
          refine c.isColimit.hom_ext fun j ↦ ?_
          have h : c.incl.app j ≫ b ≫ m = pushout.inl (c.toStage.app j) a ≫ t.ι.app j := by
            simpa using pushout.inl (c.toStage.app j) a ≫= hm j
          exact h.trans (c.isColimit.fac (c.restrictCocone t) j).symm }
  fac := by simp

lemma ofIsPushout_F : (c.ofIsPushout sq).F = c.pushoutStage a :=
  rfl

@[simp, reassoc]
lemma inl_ofIsPushout_incl_app (j : J) :
    pushout.inl (c.toStage.app j) a ≫ (c.ofIsPushout sq).incl.app j = c.incl.app j ≫ b := by
  simp [ofIsPushout]

@[simp, reassoc]
lemma inr_ofIsPushout_incl_app (j : J) :
    pushout.inr (c.toStage.app j) a ≫ (c.ofIsPushout sq).incl.app j = f' := by
  simp [ofIsPushout]

end CategoryTheory.TransfiniteCompositionOfShape

namespace HomotopicalAlgebra.RelativeCellComplex

variable {C : Type u} [Category.{v} C]
  {J : Type w'} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : J → Type t} {A B : (j : J) → α j → C} {basicCell : (j : J) → (i : α j) → A j i ⟶ B j i}
  {X Y Z Y' : C} {f : X ⟶ Y} (c : RelativeCellComplex.{w} basicCell f)
  {a : X ⟶ Z} [HasPushoutsAlong a] {f' : Z ⟶ Y'} {b : Y ⟶ Y'} (sq : IsPushout a f f' b)

/-- **Cobase change of a relative cell complex.** If `f` is a relative cell complex and the square
formed by `a`, `f`, `f'` and `b` is a pushout, then `f'` is a relative cell complex with the same
cells, attached at the same steps: the stage `j` of `f'` is the pushout of the stage `j` of `f`
along `a`. -/
noncomputable def ofIsPushout : RelativeCellComplex.{w} basicCell f' where
  toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape.ofIsPushout sq
  attachCells j hj := (c.attachCells j hj).ofIsPushout
    (c.toTransfiniteCompositionOfShape.isPushout_pushoutStage_map a (homOfLE (Order.le_succ j)))

/-- The cells of the cobase change of a relative cell complex are the cells of the original
complex. -/
def ofIsPushoutCellsEquiv : (c.ofIsPushout sq).Cells ≃ c.Cells where
  toFun γ := ⟨γ.j, γ.hj, γ.k⟩
  invFun γ := ⟨γ.j, γ.hj, γ.k⟩

@[simp]
lemma ofIsPushoutCellsEquiv_apply_j (γ : (c.ofIsPushout sq).Cells) :
    (c.ofIsPushoutCellsEquiv sq γ).j = γ.j :=
  rfl

@[simp]
lemma ofIsPushoutCellsEquiv_symm_apply_j (γ : c.Cells) :
    ((c.ofIsPushoutCellsEquiv sq).symm γ).j = γ.j :=
  rfl

/-- The inclusion of a cell of the cobase change of a relative cell complex is the inclusion of
the corresponding cell of the original complex followed by `b`. -/
lemma ofIsPushout_cells_ι (γ : c.Cells) :
    ((c.ofIsPushoutCellsEquiv sq).symm γ).ι = γ.ι ≫ b := by
  obtain ⟨j, hj, k⟩ := γ
  refine ((c.attachCells j hj).ofIsPushout_cell_assoc
    (c.toTransfiniteCompositionOfShape.isPushout_pushoutStage_map a (homOfLE (Order.le_succ j)))
    k _).trans ?_
  exact (Category.assoc _ _ _).trans (((c.attachCells j hj).cell k ≫=
    c.toTransfiniteCompositionOfShape.inl_ofIsPushout_incl_app sq (Order.succ j)).trans
      (Category.assoc _ _ _).symm)

end HomotopicalAlgebra.RelativeCellComplex
