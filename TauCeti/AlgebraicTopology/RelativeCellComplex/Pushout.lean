/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import TauCeti.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape

/-!
# Relative cell complexes are stable under cobase change

If `X₂` is obtained from `X₁` by attaching cells along `f : X₁ ⟶ X₂`, and `f' : Y₁ ⟶ Y₂` is a
pushout of `f`, then `Y₂` is obtained from `Y₁` by attaching the same cells, along the attaching
maps composed with `X₁ ⟶ Y₁` (`HomotopicalAlgebra.AttachCells.ofIsPushout`): this is the pasting
of the two pushout squares.

Combined with the stability of transfinite compositions under cobase change
(`CategoryTheory.TransfiniteCompositionOfShape.ofIsPushout`), the same holds for relative cell
complexes (`HomotopicalAlgebra.RelativeCellComplex.ofIsPushout`): if `f : X ⟶ Y` is a relative
cell complex and

```
X --f--> Y
|        |
a        b
v        v
Z --f'-> P
```

is a pushout square, then `f'` is a relative cell complex with the same cells
(`HomotopicalAlgebra.RelativeCellComplex.cellsOfIsPushoutEquiv`), attached at the same stages, and
the inclusion of each cell of `f'` is the inclusion of the corresponding cell of `f` followed by
`b` (`HomotopicalAlgebra.RelativeCellComplex.Cells.ι_cellsOfIsPushoutEquiv_symm`). Its `j`-th
stage is the pushout along `a` of the `j`-th stage of `f`.

In topology this is the construction of the adjunction space `Z ∪ₐ Y` of a relative CW complex
`(Y, X)` along a map `a : X → Z`, which needs no cell structure on `Z`.

## References

* M. Hovey, *Model Categories*, Mathematical Surveys and Monographs 63, American Mathematical
  Society, 1999, Section 2.1.2.
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press,
  1990.
-/

@[expose] public section

universe w w' t v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

namespace AttachCells

variable {α : Type t} {A B : α → C} {g : ∀ a, A a ⟶ B a} {X₁ X₂ Y₁ Y₂ : C} {f : X₁ ⟶ X₂}
  (c : AttachCells.{w} g f) {u : X₁ ⟶ Y₁} {v : X₂ ⟶ Y₂} {f' : Y₁ ⟶ Y₂} (sq : IsPushout f u v f')

/-- **Cobase change of a cell attachment.** If `X₂` is obtained from `X₁` by attaching cells
along `f`, and `f' : Y₁ ⟶ Y₂` is a pushout of `f` along `u : X₁ ⟶ Y₁`, then `Y₂` is obtained from
`Y₁` by attaching the same cells, with the attaching maps of `c` composed with `u`. -/
@[simps]
def ofIsPushout : AttachCells.{w} g f' where
  ι := c.ι
  π := c.π
  cofan₁ := c.cofan₁
  cofan₂ := c.cofan₂
  isColimit₁ := c.isColimit₁
  isColimit₂ := c.isColimit₂
  m := c.m
  hm := c.hm
  g₁ := c.g₁ ≫ u
  g₂ := c.g₂ ≫ v
  isPushout := c.isPushout.paste_horiz sq.flip

/-- The inclusion of a cell attached along a cobase change is the inclusion of the original cell
followed by the map of pushouts. -/
@[simp, reassoc]
lemma ofIsPushout_cell (i : c.ι) : (c.ofIsPushout sq).cell i = c.cell i ≫ v :=
  (Category.assoc _ _ _).symm

end AttachCells

namespace RelativeCellComplex

variable {J : Type w'} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : J → Type t} {A B : (j : J) → α j → C} {basicCell : (j : J) → (i : α j) → A j i ⟶ B j i}
  {X Y Z P : C} {f : X ⟶ Y} (c : RelativeCellComplex.{w} basicCell f) [HasPushouts C]
  {a : X ⟶ Z} {b : Y ⟶ P} {f' : Z ⟶ P} (sq : IsPushout f a b f')

/-- **Cobase change of a relative cell complex.** If `f : X ⟶ Y` is a relative cell complex and
`f' : Z ⟶ P` is a pushout of `f` along `a : X ⟶ Z`, then `f'` is a relative cell complex. Its
`j`-th stage is the pushout of the `j`-th stage of `f` along `a`, and it attaches the cells of `f`
at the same stages, along their attaching maps followed by the maps of pushouts. -/
noncomputable def ofIsPushout : RelativeCellComplex.{w} basicCell f' where
  toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape.ofIsPushout sq
  attachCells j hj := (c.attachCells j hj).ofIsPushout
    (c.toTransfiniteCompositionOfShape.isPushout_pushoutF_map a (Order.le_succ j))

/-- The cells attached at stage `j` of the cobase change of `c` are those attached at stage `j`
of `c`. -/
lemma ofIsPushout_attachCells (j : J) (hj : ¬IsMax j) :
    (c.ofIsPushout sq).attachCells j hj = (c.attachCells j hj).ofIsPushout
      (c.toTransfiniteCompositionOfShape.isPushout_pushoutF_map a (Order.le_succ j)) :=
  rfl

/-- The cells of the cobase change of a relative cell complex are the cells of the original
complex, attached at the same stages. -/
def cellsOfIsPushoutEquiv : (c.ofIsPushout sq).Cells ≃ c.Cells where
  toFun γ := ⟨γ.j, γ.hj, γ.k⟩
  invFun γ := ⟨γ.j, γ.hj, γ.k⟩

@[simp]
lemma cellsOfIsPushoutEquiv_apply_j (γ : (c.ofIsPushout sq).Cells) :
    (c.cellsOfIsPushoutEquiv sq γ).j = γ.j :=
  rfl

@[simp]
lemma cellsOfIsPushoutEquiv_symm_apply_j (γ : c.Cells) :
    ((c.cellsOfIsPushoutEquiv sq).symm γ).j = γ.j :=
  rfl

/-- The inclusion of the cell of the cobase change of `c` attached at stage `j` with index `k` is
the inclusion of the cell of `c` with the same stage and index, followed by `b : Y ⟶ P`. -/
@[simp, reassoc]
lemma Cells.ι_ofIsPushout_mk (j : J) (hj : ¬IsMax j) (k : (c.attachCells j hj).ι) :
    (⟨j, hj, k⟩ : (c.ofIsPushout sq).Cells).ι = (⟨j, hj, k⟩ : c.Cells).ι ≫ b := by
  -- The attachments of `c.ofIsPushout sq` are stated over `c.pushoutF a`, which is the stage
  -- functor of `c.ofIsPushout sq` only up to unfolding, so this is proved as a term.
  exact (congrArg (· ≫ _) (AttachCells.ofIsPushout_cell _
    (c.toTransfiniteCompositionOfShape.isPushout_pushoutF_map a (Order.le_succ j)) k)).trans <|
    (Category.assoc _ _ _).trans
    (((c.attachCells j hj).cell k ≫=
      c.toTransfiniteCompositionOfShape.pushoutInl_app_comp_pushoutIncl_app sq (Order.succ j)).trans
        (Category.assoc _ _ _).symm)

/-- **The cells of a cobase change.** The inclusion of a cell of the cobase change of `c` is the
inclusion of the corresponding cell of `c` followed by the map of pushouts `b : Y ⟶ P`. -/
@[simp, reassoc]
lemma Cells.ι_cellsOfIsPushoutEquiv_symm (γ : c.Cells) :
    ((c.cellsOfIsPushoutEquiv sq).symm γ).ι = γ.ι ≫ b :=
  Cells.ι_ofIsPushout_mk c sq γ.j γ.hj γ.k

end RelativeCellComplex

end HomotopicalAlgebra
