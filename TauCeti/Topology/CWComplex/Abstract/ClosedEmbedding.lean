/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Abstract.Basic
public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Topology.Category.TopCat.ClosedEmbedding

/-!
# Relative CW complexes in `TopCat` are closed embeddings

Mathlib's categorical relative CW complex `c : TopCat.RelativeCWComplex f` presents the target of
`f : X ⟶ Y` as the colimit of a sequence of spaces `c.F.obj n`, starting at `X`, in which each
space is obtained from the previous one by attaching disks along their boundary spheres. This file
proves that `f` is a closed embedding, and that so are all the maps `c.F.obj i ⟶ c.F.obj j` for
`i ≤ j` and the maps `c.F.obj n ⟶ Y` into the colimit. Thus `X` and every intermediate stage are
closed subspaces of `Y`, which is the first step in recognizing a categorical relative CW complex
as a classical relative CW complex `RelCWComplex (Set.univ : Set Y) (Set.range f)`.

The statements hold for any relative cell complex in `TopCat` (of any well-ordered shape) whose
basic cells are closed embeddings, and are proved at that generality first, from the closure
properties of `TopCat.isClosedEmbedding` under coproducts, pushouts and transfinite composition.

## Main declarations

* `HomotopicalAlgebra.RelativeCellComplex.isClosedEmbedding`: a relative cell complex in `TopCat`
  with closed-embedding basic cells is a closed embedding.
* `TopCat.RelativeCWComplex.isClosedEmbedding`: a relative CW complex is a closed embedding.
* `TopCat.RelativeCWComplex.isClosedEmbedding_map` and
  `TopCat.RelativeCWComplex.isClosedEmbedding_incl_app`: the inclusions between stages and of a
  stage into the colimit are closed embeddings.
-/

public section

open CategoryTheory MorphismProperty Topology

universe w t u

namespace HomotopicalAlgebra.RelativeCellComplex

variable {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : J → Type t} {A B : (j : J) → α j → TopCat.{u}}
  {basicCell : (j : J) → (i : α j) → A j i ⟶ B j i} {X Y : TopCat.{u}} {f : X ⟶ Y}
  (c : RelativeCellComplex.{u} basicCell f)
  (hc : ∀ s : c.Cells, IsClosedEmbedding (basicCell s.j s.i))

include hc

/-- A relative cell complex in `TopCat` with closed-embedding basic cells is a transfinite
composition of closed embeddings. -/
private noncomputable def transfiniteCompositionOfShapeIsClosedEmbedding :
    TopCat.isClosedEmbedding.TransfiniteCompositionOfShape J f :=
  (c.transfiniteCompositionOfShape' (I := TopCat.isClosedEmbedding) hc).ofLE (by
    rw [coproducts_eq_self]
    exact TopCat.isClosedEmbedding.pushouts_le)

/-- In a relative cell complex in `TopCat` with closed-embedding basic cells, each stage is a
closed subspace of every later stage. -/
lemma isClosedEmbedding_map {i j : J} (hij : i ≤ j) :
    IsClosedEmbedding (c.F.map (homOfLE hij)) :=
  TopCat.isClosedEmbedding_map_of_isWellOrderContinuous c.F
    (fun j hj ↦ (c.transfiniteCompositionOfShapeIsClosedEmbedding hc).map_mem j hj) hij

/-- In a relative cell complex in `TopCat` with closed-embedding basic cells, each stage is a
closed subspace of the colimit. -/
lemma isClosedEmbedding_incl_app (j : J) : IsClosedEmbedding (c.incl.app j) :=
  have : Nonempty J := ⟨⊥⟩
  TopCat.isClosedEmbedding_ι_of_isColimit
    (fun _ _ g ↦ c.isClosedEmbedding_map hc (leOfHom g)) c.isColimit j

/-- A relative cell complex in `TopCat` whose basic cells are closed embeddings is a closed
embedding. -/
lemma isClosedEmbedding : IsClosedEmbedding f :=
  transfiniteCompositionsOfShape_le _ _ _
    (c.transfiniteCompositionOfShapeIsClosedEmbedding hc).mem

end HomotopicalAlgebra.RelativeCellComplex

namespace TopCat.RelativeCWComplex

variable {X Y : TopCat.{u}} {f : X ⟶ Y} (c : RelativeCWComplex f)

private lemma isClosedEmbedding_basicCell (s : c.Cells) : IsClosedEmbedding (basicCell s.j s.i) :=
  TauCeti.TopCat.isClosedEmbedding_diskBoundaryInclusion s.j

/-- In a relative CW complex, the space `c.F.obj i` obtained after attaching the cells of
dimension `< i` is a closed subspace of `c.F.obj j` for every `i ≤ j`. -/
lemma isClosedEmbedding_map {i j : ℕ} (hij : i ≤ j) :
    IsClosedEmbedding (c.F.map (homOfLE hij)) :=
  HomotopicalAlgebra.RelativeCellComplex.isClosedEmbedding_map c c.isClosedEmbedding_basicCell hij

/-- In a relative CW complex, the space `c.F.obj n` obtained after attaching the cells of
dimension `< n` is a closed subspace of the colimit. -/
lemma isClosedEmbedding_incl_app (n : ℕ) : IsClosedEmbedding (c.incl.app n) :=
  HomotopicalAlgebra.RelativeCellComplex.isClosedEmbedding_incl_app c
    c.isClosedEmbedding_basicCell n

include c in
/-- A relative CW complex `f : X ⟶ Y` is a closed embedding: `X` is a closed subspace of `Y`. -/
lemma isClosedEmbedding : IsClosedEmbedding f :=
  HomotopicalAlgebra.RelativeCellComplex.isClosedEmbedding c c.isClosedEmbedding_basicCell

end TopCat.RelativeCWComplex
