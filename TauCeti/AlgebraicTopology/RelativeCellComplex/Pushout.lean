/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import TauCeti.AlgebraicTopology.RelativeCellComplex.AttachCells
public import TauCeti.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape

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

The stages of `f'` are the pushouts of the stages of `f` along `a`, which again form a
transfinite composition (`CategoryTheory.TransfiniteCompositionOfShape.ofIsPushout`), and each
cell attachment is carried across the pushout square by pasting it with the square
(`HomotopicalAlgebra.AttachCells.ofIsPushout`).

## References

* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press,
  1990.
* M. Hovey, *Model Categories*, Mathematical Surveys and Monographs 63, American Mathematical
  Society, 1999, Section 2.1, for the stability of relative cell complexes under pushouts.
-/

public section

open CategoryTheory Limits

universe w w' t v u

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
@[expose] noncomputable def ofIsPushout : RelativeCellComplex.{w} basicCell f' where
  toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape.ofIsPushout sq
  attachCells j hj := (c.attachCells j hj).ofIsPushout
    (c.toTransfiniteCompositionOfShape.isPushout_pushoutStage_map a (homOfLE (Order.le_succ j)))

/-- The cells of the cobase change of a relative cell complex are the cells of the original
complex. -/
@[expose] def ofIsPushoutCellsEquiv : (c.ofIsPushout sq).Cells ≃ c.Cells where
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

@[simp]
lemma ofIsPushoutCellsEquiv_symm_mk (j : J) (hj : ¬IsMax j) (k : (c.attachCells j hj).ι) :
    (c.ofIsPushoutCellsEquiv sq).symm ⟨j, hj, k⟩ = ⟨j, hj, k⟩ :=
  rfl

/-- The inclusion of a cell of the cobase change of a relative cell complex is the inclusion of
the corresponding cell of the original complex followed by `b`. -/
lemma ofIsPushout_cells_ι (γ : c.Cells) :
    ((c.ofIsPushoutCellsEquiv sq).symm γ).ι = γ.ι ≫ b := by
  obtain ⟨j, hj, k⟩ := γ
  dsimp only [ofIsPushoutCellsEquiv_symm_mk]
  dsimp only [RelativeCellComplex.Cells.ι, RelativeCellComplex.Cells.i, ofIsPushout,
    AttachCells.ofIsPushout]
  simp [AttachCells.cell]

end HomotopicalAlgebra.RelativeCellComplex
