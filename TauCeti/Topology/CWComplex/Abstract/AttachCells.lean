/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.Filtered.Final
public import TauCeti.AlgebraicTopology.RelativeCellComplex.AttachCells
public import TauCeti.Topology.CWComplex.Abstract.Classical
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Basic

/-!
# Attaching cells of a single dimension is a relative CW complex

Let `c : AttachCells (TopCat.RelativeCWComplex.basicCell n) f` express that `Y` is obtained from
`X` by attaching `n`-disks along their boundary spheres, `f : X ⟶ Y` being the inclusion. Then
`f` is a categorical relative CW complex (`HomotopicalAlgebra.AttachCells.toRelativeCWComplex`):
its sequence of stages is constantly `X` up to stage `n` and constantly `Y` from stage `n + 1` on
(`TauCeti.attachStageFunctor`), the cells attached at stage `n` are those of `c`, and no cells are
attached at the other stages (`HomotopicalAlgebra.AttachCells.ofIsIso`).

Through the comparison `TopCat.RelativeCWComplex.toRelCWComplex`, `Y` is therefore a classical
relative CW complex relative to the range of `f`, whose cells all have dimension `n`
(`HomotopicalAlgebra.AttachCells.isEmpty_cell_toRelCWComplex`,
`HomotopicalAlgebra.AttachCells.cellToRelCWComplexEquiv`), with the characteristic maps of `c`
(`HomotopicalAlgebra.AttachCells.map_cellToRelCWComplexEquiv_symm`). In particular its skeleta
up to dimension `n` are the range of `f`
(`HomotopicalAlgebra.AttachCells.skeletonLT_toRelCWComplex`), so the cellular theory of classical
relative CW complexes, such as Hatcher's Corollary 4.12, applies to a single attachment of cells.
This is how cells are attached to kill homotopy groups.

## Main definitions

* `TauCeti.attachStageFunctor f n`: the sequence `X = ⋯ = X → Y = Y = ⋯`, with `f` from stage `n`
  to stage `n + 1`.
* `HomotopicalAlgebra.AttachCells.toRelativeCWComplex`: the relative CW complex of a single
  attachment of `n`-cells.
* `HomotopicalAlgebra.AttachCells.cellToRelCWComplexEquiv`: its classical `n`-cells are the cells
  of `c`.

## Main results

* `HomotopicalAlgebra.AttachCells.toRelativeCWComplex_cells_ι`: its cells are included as in `c`.
* `HomotopicalAlgebra.AttachCells.isEmpty_cell_toRelCWComplex`: it has no classical cells outside
  dimension `n`.
* `HomotopicalAlgebra.AttachCells.skeletonLT_toRelCWComplex`: its skeleta up to dimension `n` are
  the range of `f`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 for attaching cells, and Section 4.1 for attaching cells to kill homotopy groups.
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press,
  1990, for the categorical definition of relative CW complexes.

## Implementation notes

The stages and their colimit follow the pattern of Mathlib's
`CategoryTheory.TransfiniteCompositionOfShape.iic`, which restricts a transfinite composition
along a monotone reindexing: here the fixed diagram `ComposableArrows.mk₁ f` over `Fin 2` is
reindexed along the monotone step function `TauCeti.attachStageIndex n`, its colimit cocone comes
from the terminal object `Fin.last 1` (`CategoryTheory.Limits.colimitOfDiagramTerminal`), and it
is transported along the final reindexing by `CategoryTheory.Functor.Final.isColimitWhiskerEquiv`.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Topology Set

universe v u

namespace TauCeti

/-- The step function `ℕ → Fin 2` which is `0` up to `n` and `1` afterwards: stage `k` of the
relative CW complex attaching `n`-cells is the source of the attachment for `k ≤ n` and its
target for `n < k`. -/
@[expose] def attachStageIndex (n k : ℕ) : Fin 2 := if k ≤ n then 0 else 1

/-- Up to stage `n`, the index is `0`. -/
@[simp] lemma attachStageIndex_of_le {n k : ℕ} (h : k ≤ n) : attachStageIndex n k = 0 := by
  simp [attachStageIndex, h]

/-- After stage `n`, the index is `1`. -/
@[simp] lemma attachStageIndex_of_lt {n k : ℕ} (h : n < k) : attachStageIndex n k = 1 := by
  simp [attachStageIndex, not_le.2 h]

/-- The index is monotone in the stage. -/
lemma monotone_attachStageIndex (n : ℕ) : Monotone (attachStageIndex n) := by
  intro k l hkl
  by_cases hl : l ≤ n
  · rw [attachStageIndex_of_le hl, attachStageIndex_of_le (hkl.trans hl)]
  · rw [attachStageIndex_of_lt (not_le.1 hl)]
    exact Fin.le_last _

/-- The index changes only from stage `n` to stage `n + 1`. -/
lemma attachStageIndex_succ_of_ne {n k : ℕ} (h : k ≠ n) :
    attachStageIndex n (k + 1) = attachStageIndex n k := by
  rcases lt_or_gt_of_ne h with h | h
  · rw [attachStageIndex_of_le h, attachStageIndex_of_le h.le]
  · rw [attachStageIndex_of_lt h, attachStageIndex_of_lt (by omega)]

/-- The reindexing `ℕ ⥤ Fin 2` along `attachStageIndex n` is final: its value `1` is reached. -/
instance final_monotone_attachStageIndex_functor (n : ℕ) :
    (monotone_attachStageIndex n).functor.Final :=
  (Monotone.final_functor_iff _).2 fun _ ↦ ⟨n + 1, by
    rw [attachStageIndex_of_lt (Nat.lt_succ_self n)]
    exact Fin.le_last _⟩

variable {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) (n : ℕ)

/-- The sequence `X = ⋯ = X → Y = Y = ⋯` which is constantly `X` up to stage `n`, constantly `Y`
from stage `n + 1` on, and `f` from stage `n` to stage `n + 1`. -/
abbrev attachStageFunctor : ℕ ⥤ C :=
  (monotone_attachStageIndex n).functor ⋙ ComposableArrows.mk₁ f

private lemma isIso_mk₁_map_of_eq {a b : Fin 2} (hab : a ≤ b) (h : a = b) :
    IsIso ((ComposableArrows.mk₁ f).map (homOfLE hab)) := by
  subst h
  rw [Subsingleton.elim (homOfLE hab) (𝟙 a), CategoryTheory.Functor.map_id]
  infer_instance

/-- Away from stage `n`, the steps of `attachStageFunctor f n` are isomorphisms. -/
lemma isIso_attachStageFunctor_map {k : ℕ} (hk : k ≠ n) :
    IsIso ((attachStageFunctor f n).map (homOfLE (Order.le_succ k))) :=
  isIso_mk₁_map_of_eq f (monotone_attachStageIndex n (Order.le_succ k))
    (attachStageIndex_succ_of_ne hk).symm

private def mk₁ArrowIso {a b : Fin 2} (hab : a ≤ b) (ha : a = 0) (hb : b = 1) :
    Arrow.mk f ≅ Arrow.mk ((ComposableArrows.mk₁ f).map (homOfLE hab)) := by
  subst ha hb
  exact Iso.refl _

private lemma mk₁ArrowIso_hom_right_comp {a b : Fin 2} (hab : a ≤ b) (ha : a = 0) (hb : b = 1)
    (hb' : b ⟶ Fin.last 1) :
    (mk₁ArrowIso f hab ha hb).hom.right ≫ (ComposableArrows.mk₁ f).map hb' = 𝟙 Y := by
  subst ha hb
  rw [Subsingleton.elim hb' (𝟙 _), CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).trans rfl

/-- The step of `attachStageFunctor f n` from stage `n` to stage `n + 1` is `f`. -/
def attachStageArrowIso :
    Arrow.mk f ≅ Arrow.mk ((attachStageFunctor f n).map (homOfLE (Order.le_succ n))) :=
  mk₁ArrowIso f (monotone_attachStageIndex n (Order.le_succ n)) (attachStageIndex_of_le le_rfl)
    (attachStageIndex_of_lt (Nat.lt_succ_self n))

private lemma attachStageArrowIso_hom_right_comp :
    Arrow.rightFunc.map (attachStageArrowIso f n).hom ≫
      (ComposableArrows.mk₁ f).map ((Fin.isTerminalLast 1).from (attachStageIndex n (n + 1))) =
      𝟙 Y :=
  mk₁ArrowIso_hom_right_comp f _ _ _ _

end TauCeti

namespace HomotopicalAlgebra.AttachCells

open TauCeti

variable {X Y : TopCat.{u}} {f : X ⟶ Y} {n : ℕ}
  (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell n) f)

/-- **Attaching cells of a single dimension is a relative CW complex.** If `Y` is obtained from
`X` by attaching `n`-disks along `f`, then `f` is a relative CW complex whose stages are `X` up to
stage `n` and `Y` afterwards; the cells attached at stage `n` are those of `c`, and no cells are
attached at the other stages. The body is exposed so that the stages are those of
`TauCeti.attachStageFunctor f n` by definition, which the statements about its attached cells
need in order to typecheck; the stages and their inclusions into `Y` are characterised by
`toRelativeCWComplex_F` and `toRelativeCWComplex_incl_app`. -/
@[expose] def toRelativeCWComplex : TopCat.RelativeCWComplex.{u} f where
  F := attachStageFunctor f n
  isoBot := Iso.refl _
  incl := Functor.whiskerLeft (monotone_attachStageIndex n).functor
    (coconeOfDiagramTerminal (Fin.isTerminalLast 1) (ComposableArrows.mk₁ f)).ι
  isColimit := (Functor.Final.isColimitWhiskerEquiv (monotone_attachStageIndex n).functor _).symm
    (colimitOfDiagramTerminal (Fin.isTerminalLast 1) (ComposableArrows.mk₁ f))
  fac := Category.id_comp _
  attachCells k _ :=
    if hk : k = n then hk ▸ c.ofArrowIso (attachStageArrowIso f n)
    else
      have := isIso_attachStageFunctor_map f n hk
      ofIsIso _ _

/-- The stages of `c.toRelativeCWComplex` are those of `TauCeti.attachStageFunctor f n`. -/
lemma toRelativeCWComplex_F : c.toRelativeCWComplex.F = attachStageFunctor f n := rfl

/-- The inclusion of stage `k` of `c.toRelativeCWComplex` into `Y` is the image under
`ComposableArrows.mk₁ f` of the morphism to the last object of `Fin 2`. -/
lemma toRelativeCWComplex_incl_app (k : ℕ) :
    c.toRelativeCWComplex.incl.app k =
      (ComposableArrows.mk₁ f).map ((Fin.isTerminalLast 1).from (attachStageIndex n k)) :=
  rfl

/-- At stage `n`, the cells of `c.toRelativeCWComplex` are attached as in `c`. -/
lemma toRelativeCWComplex_attachCells_self :
    c.toRelativeCWComplex.attachCells n (not_isMax n) =
      c.ofArrowIso (attachStageArrowIso f n) := by
  simp [toRelativeCWComplex]

/-- No cells of `c.toRelativeCWComplex` are attached at the stages other than `n`. -/
theorem isEmpty_toRelativeCWComplex_attachCells_ι {k : ℕ} (hk : k ≠ n) (h : ¬ IsMax k) :
    IsEmpty (c.toRelativeCWComplex.attachCells k h).ι := by
  simp only [toRelativeCWComplex, hk, dite_false]
  infer_instance

/-- The cells of `c.toRelativeCWComplex` attached at stage `n` are the cells of `c`. -/
def toRelativeCWComplexAttachCellsEquiv :
    (c.toRelativeCWComplex.attachCells n (not_isMax n)).ι ≃ c.ι :=
  Equiv.cast (congrArg ι c.toRelativeCWComplex_attachCells_self)

/-- The inclusion of a cell attached at stage `n` of `c.toRelativeCWComplex` is the inclusion of
the corresponding cell of `c`. -/
lemma toRelativeCWComplex_cells_ι (k : (c.toRelativeCWComplex.attachCells n (not_isMax n)).ι) :
    (⟨n, not_isMax n, k⟩ : c.toRelativeCWComplex.Cells).ι =
      c.cell (c.toRelativeCWComplexAttachCellsEquiv k) := by
  -- Generalize the attachment at stage `n`, so that its identification with `c` can be
  -- substituted away.
  have key (a : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell n)
      ((attachStageFunctor f n).map (homOfLE (Order.le_succ n))))
      (h : a = c.ofArrowIso (attachStageArrowIso f n)) (k : a.ι) :
      a.cell k ≫ (ComposableArrows.mk₁ f).map
          ((Fin.isTerminalLast 1).from (attachStageIndex n (n + 1))) =
        c.cell (cast (congrArg AttachCells.ι h) k :
          (c.ofArrowIso (attachStageArrowIso f n)).ι) := by
    subst h
    have hk : (c.ofArrowIso (attachStageArrowIso f n)).cell k =
        c.cell k ≫ Arrow.rightFunc.map (attachStageArrowIso f n).hom :=
      (Category.assoc _ _ _).symm
    rw [hk, Category.assoc, attachStageArrowIso_hom_right_comp, Category.comp_id]
    rfl
  exact key _ c.toRelativeCWComplex_attachCells_self k

/-- The classical relative CW structure on `Y`, relative to the range of `f`, read off
`c.toRelativeCWComplex`, has no cells outside dimension `n`. -/
theorem isEmpty_cell_toRelCWComplex {m : ℕ} (hm : m ≠ n) :
    letI := c.toRelativeCWComplex.toRelCWComplex
    IsEmpty (RelCWComplex.cell (univ : Set Y) m) :=
  (c.toRelativeCWComplex.toRelCWComplexCellEquiv m).isEmpty_congr.2
    (c.isEmpty_toRelativeCWComplex_attachCells_ι hm (not_isMax m))

/-- The `n`-cells of the classical relative CW structure read off `c.toRelativeCWComplex` are the
cells of `c`. -/
def cellToRelCWComplexEquiv :
    letI := c.toRelativeCWComplex.toRelCWComplex
    RelCWComplex.cell (univ : Set Y) n ≃ c.ι :=
  (c.toRelativeCWComplex.toRelCWComplexCellEquiv n).trans c.toRelativeCWComplexAttachCellsEquiv

/-- The characteristic map of an `n`-cell of the classical relative CW structure read off
`c.toRelativeCWComplex` is the inclusion of the corresponding cell of `c`, read on the closed
ball through the radial homeomorphism `TauCeti.diskHomeomorphClosedBall`. -/
theorem map_cellToRelCWComplexEquiv_symm (i : c.ι) (x : closedBall (0 : Fin n → ℝ) 1) :
    letI := c.toRelativeCWComplex.toRelCWComplex
    RelCWComplex.map n (c.cellToRelCWComplexEquiv.symm i) x =
      c.cell i ((diskHomeomorphClosedBall n).symm x) := by
  rw [TopCat.RelativeCWComplex.toRelCWComplex_map_apply, toRelativeCWComplex_cells_ι]
  simp [cellToRelCWComplexEquiv]

/-- Up to dimension `n`, the skeleta of the classical relative CW structure read off
`c.toRelativeCWComplex` are the range of `f`: there are no cells of dimension less than `n`. -/
theorem skeletonLT_toRelCWComplex [T2Space Y] {m : ℕ} (hm : m ≤ n) :
    letI := c.toRelativeCWComplex.toRelCWComplex
    (RelCWComplex.skeletonLT (univ : Set Y) m : Set Y) = range f :=
  c.toRelativeCWComplex.skeletonLT_toRelCWComplex_eq_range fun _ hk ↦
    c.isEmpty_toRelativeCWComplex_attachCells_ι (by omega) _

end HomotopicalAlgebra.AttachCells
