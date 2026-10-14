/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Abstract.Basic
public import TauCeti.Topology.Category.TopCat.ClosedEmbedding

/-!
# Relative CW complexes are closed embeddings

Mathlib's categorical relative CW complex `c : TopCat.RelativeCWComplex f`, for a morphism
`f : X ⟶ Y` of `TopCat`, presents `Y` as the colimit of a sequence of spaces `c.F.obj n` starting at
`X`, each obtained from the previous one by attaching `n`-disks along their boundary spheres. This
file proves that `f` is a closed embedding (`TopCat.RelativeCWComplex.isClosedEmbedding`), as are
the maps `c.F.obj m ⟶ c.F.obj n` between the stages and the maps `c.incl.app n : c.F.obj n ⟶ Y`
to the colimit. So `X` and every stage of the complex are closed subspaces of `Y`; this is the
starting point for reading a classical CW structure on `Y`, relative to the range of `f`, off a
categorical one.

The statements hold for any relative cell complex in `TopCat` whose basic cells are closed
embeddings (`HomotopicalAlgebra.RelativeCellComplex.isClosedEmbedding`). Such a complex is a
transfinite composition of pushouts of coproducts of basic cells, and closed embeddings are stable
under all three operations (`TauCeti.TopCat.isClosedEmbedding`). For CW complexes the basic cells
are the boundary inclusions `∂𝔻 n ⟶ 𝔻 n`, which are closed embeddings because they are injective
maps from a compact space to a Hausdorff one
(`TauCeti.TopCat.isClosedEmbedding_diskBoundaryInclusion`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, on the topology of cell complexes.
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press,
  1990, for the categorical definition.
-/

public section

open CategoryTheory Limits MorphismProperty Topology

universe w w' t u

namespace HomotopicalAlgebra.RelativeCellComplex

variable {J : Type w'} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : J → Type t} {A B : (j : J) → α j → TopCat.{u}}
  {basicCell : (j : J) → (i : α j) → A j i ⟶ B j i} {X Y : TopCat.{u}} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} basicCell f)
  (hc : ∀ s : c.Cells, IsClosedEmbedding (basicCell s.j s.i))

include hc

/-- A relative cell complex in `TopCat` whose cells are closed embeddings is a transfinite
composition of closed embeddings. -/
private def isClosedEmbeddingTransfiniteCompositionOfShape :
    TauCeti.TopCat.isClosedEmbedding.TransfiniteCompositionOfShape J f :=
  (c.transfiniteCompositionOfShape' (I := TauCeti.TopCat.isClosedEmbedding)
    fun s ↦ (TauCeti.TopCat.isClosedEmbedding_iff _).2 (hc s)).ofLE
    (pushouts_le_iff.2 (coproducts_le _))

/-- In a relative cell complex in `TopCat` whose basic cells are closed embeddings, the maps
between the stages are closed embeddings. -/
theorem isClosedEmbedding_map {i j : J} (hij : i ≤ j) :
    IsClosedEmbedding (c.F.map (homOfLE hij)) := by
  have := c.isWellOrderContinuous
  exact TauCeti.TopCat.isClosedEmbedding_map_of_isWellOrderContinuous c.F
    (fun j hj ↦ (TauCeti.TopCat.isClosedEmbedding_iff _).1
      ((c.isClosedEmbeddingTransfiniteCompositionOfShape hc).map_mem j hj)) hij

/-- In a relative cell complex in `TopCat` whose basic cells are closed embeddings, the map from
each stage to the complex is a closed embedding. -/
theorem isClosedEmbedding_incl_app (j : J) : IsClosedEmbedding (c.incl.app j) :=
  TauCeti.TopCat.isClosedEmbedding_incl_app_of_transfiniteCompositionOfShape
    (c.isClosedEmbeddingTransfiniteCompositionOfShape hc) j

/-- A relative cell complex in `TopCat` whose basic cells are closed embeddings is a closed
embedding. -/
theorem isClosedEmbedding : IsClosedEmbedding f :=
  (TauCeti.TopCat.isClosedEmbedding_iff _).1 <|
    transfiniteCompositionsOfShape_le TauCeti.TopCat.isClosedEmbedding J f
      (c.isClosedEmbeddingTransfiniteCompositionOfShape hc).mem

end HomotopicalAlgebra.RelativeCellComplex

/-- The inclusion `∂𝔻 n ⟶ 𝔻 n` of the boundary sphere of the disk is a closed embedding. -/
theorem TauCeti.TopCat.isClosedEmbedding_diskBoundaryInclusion (n : ℕ) :
    IsClosedEmbedding (TopCat.diskBoundaryInclusion.{u} n) :=
  have : T2Space (TopCat.disk.{u} n) :=
    inferInstanceAs (T2Space (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)))
  (TopCat.diskBoundaryInclusion n).hom.continuous.isClosedEmbedding
    ((TopCat.mono_iff_injective _).1 inferInstance)

namespace TopCat.RelativeCWComplex

variable {X Y : TopCat.{u}} {f : X ⟶ Y} (c : RelativeCWComplex f)

/-- In a relative CW complex, the maps between the stages are closed embeddings. -/
theorem isClosedEmbedding_map {m n : ℕ} (hmn : m ≤ n) :
    IsClosedEmbedding (c.F.map (homOfLE hmn)) :=
  HomotopicalAlgebra.RelativeCellComplex.isClosedEmbedding_map c
    (fun s ↦ TauCeti.TopCat.isClosedEmbedding_diskBoundaryInclusion s.j) hmn

/-- In a relative CW complex, the map from each stage to the complex is a closed embedding. -/
theorem isClosedEmbedding_incl_app (n : ℕ) : IsClosedEmbedding (c.incl.app n) :=
  HomotopicalAlgebra.RelativeCellComplex.isClosedEmbedding_incl_app c
    (fun s ↦ TauCeti.TopCat.isClosedEmbedding_diskBoundaryInclusion s.j) n

include c in
/-- A relative CW complex `f : X ⟶ Y` is a closed embedding. -/
theorem isClosedEmbedding : IsClosedEmbedding f :=
  HomotopicalAlgebra.RelativeCellComplex.isClosedEmbedding c
    (fun s ↦ TauCeti.TopCat.isClosedEmbedding_diskBoundaryInclusion s.j)

end TopCat.RelativeCWComplex
