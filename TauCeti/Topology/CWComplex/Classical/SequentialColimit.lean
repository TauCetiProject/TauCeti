/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.ClosedEmbedding
public import TauCeti.Topology.CWComplex.Classical.Image
public import TauCeti.Topology.CWComplex.Classical.TowerUnion
import TauCeti.Topology.Coherent

/-!
# The colimit of a sequence of CW complexes

Let `F : ℕ ⥤ TopCat` be a sequence of spaces `F.obj 0 → F.obj 1 → ⋯` whose maps are closed
embeddings, each space carrying a CW structure, such that every `n`-cell of `F.obj k` is an
`n`-cell of `F.obj (k + 1)` whose characteristic map is the old one followed by the map
`F.obj k → F.obj (k + 1)`. Then the colimit of `F` is a CW complex whose `n`-cells are the
`n`-cells of `F.obj 0` together with, for each `k`, the `n`-cells of `F.obj (k + 1)` which do not
come from `F.obj k` (`TauCeti.sequentialColimitCWComplex`), with the characteristic maps of the
stages followed by the maps to the colimit. The cells of the stages may have arbitrary dimensions
in any order: a later stage may add cells of lower dimension than an earlier one, as happens when
the critical levels of a Morse function are crossed in increasing order.

The maps from the stages to the colimit are closed embeddings
(`TauCeti.TopCat.isClosedEmbedding_ι_of_isColimit_of_succ`), so each stage is a CW complex in the
colimit (`Topology.IsClosedEmbedding.relCWComplex`), and the colimit carries the topology coherent
with these images (`TauCeti.TopCat.isCoherentWith_range_ι_of_isColimit`). Its CW structure is then
the union of a tower of CW complexes (`TauCeti.cwSubcomplexTowerUnion`). That construction asks
the characteristic map of a cell of a stage, as a partial equivalence, to be literally the same in
the next stage. The images of the stages only have the same characteristic maps as functions;
their inverses, which are only specified on the open cells, are chosen independently. So the
characteristic maps are first replaced by the canonical partial equivalences determined by their
values on the open balls (`Topology.RelCWComplex.replaceMap`), which no longer depend on the stage.

## Main results

* `TauCeti.sequentialColimitCWComplex`: the CW structure on the colimit of a sequence of CW
  complexes along closed embeddings which carry cells to cells.
* `TauCeti.sequentialColimitCWComplexCellEquiv`: its `n`-cells are those of the first stage and
  the new ones of the later stages, with the characteristic maps of the stages
  (`TauCeti.coe_map_sequentialColimitCWComplexCellEquiv_symm_inl`,
  `TauCeti.coe_map_sequentialColimitCWComplexCellEquiv_symm_inr`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 and the Appendix, for CW complexes built by attaching cells inductively, with the weak
  topology of the union of the stages.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex CategoryTheory Limits

universe u

namespace TauCeti

variable {F : ℕ ⥤ TopCat.{u}} [∀ k, CWComplex (univ : Set (F.obj k))] {c : Cocone F}
  (hι : ∀ k, IsClosedEmbedding (c.ι.app k))

/-- The characteristic map of an `n`-cell `i` of the `k`-th stage of a sequence of CW complexes,
followed by a closed embedding `c.ι.app k` into a cocone, as the canonical partial equivalence
determined by its values on the open ball. -/
private def stageMap (k n : ℕ) (i : cell (univ : Set (F.obj k)) n) :
    PartialEquiv (Fin n → ℝ) c.pt :=
  ((hι k).injective.comp_injOn (source_eq n i ▸ (map n i).injOn)).toPartialEquiv _ (ball 0 1)

/-- The `k`-th stage of a sequence of CW complexes, as a CW complex in a cocone over the sequence
along a closed embedding, with the characteristic maps `TauCeti.stageMap`. -/
@[instance_reducible]
private def stageCWComplex (k : ℕ) : CWComplex (range (c.ι.app k) : Set c.pt) :=
  letI := (hι k).relCWComplex (C := (univ : Set (F.obj k))) (D := ∅) image_univ (image_empty _)
  letI := RelCWComplex.replaceMap (C := (range (c.ι.app k) : Set c.pt)) (D := ∅)
    (fun n i ↦ stageMap hι k n ((hι k).relCWComplexCellEquiv image_univ (image_empty _) n i))
    (fun n i ↦ ((hι k).coe_map_relCWComplex image_univ (image_empty _) n i).symm)
    (fun n i ↦ (source_eq n i).symm)
  RelCWComplex.toCWComplex _

/-- The cells of a stage in the colimit are the cells of the stage. -/
private def stageCellEquiv (k n : ℕ) :
    @cell _ _ _ ∅ (@CWComplex.instRelCWComplex _ _ _ (stageCWComplex hι k)) n ≃
      cell (univ : Set (F.obj k)) n :=
  letI := (hι k).relCWComplex (C := (univ : Set (F.obj k))) (D := ∅) image_univ (image_empty _)
  (replaceMapCellEquiv (C := (range (c.ι.app k) : Set c.pt)) (D := ∅) _ _ _ n).trans
    ((hι k).relCWComplexCellEquiv image_univ (image_empty _) n)

/-- The characteristic maps of a stage in the colimit are the maps `TauCeti.stageMap`. -/
private lemma map_stageCWComplex (k n : ℕ)
    (i : @cell _ _ _ ∅ (@CWComplex.instRelCWComplex _ _ _ (stageCWComplex hι k)) n) :
    @map _ _ _ ∅ (@CWComplex.instRelCWComplex _ _ _ (stageCWComplex hι k)) n i =
      stageMap hι k n (stageCellEquiv hι k n i) :=
  letI := (hι k).relCWComplex (C := (univ : Set (F.obj k))) (D := ∅) image_univ (image_empty _)
  map_replaceMap (C := (range (c.ι.app k) : Set c.pt)) (D := ∅) _ _ _ n i

variable (ι : ∀ k n, cell (univ : Set (F.obj k)) n → cell (univ : Set (F.obj (k + 1))) n)

/-- The maps `ι k n` on the cells of the stages in the colimit. -/
private def stageι (k n : ℕ) :
    @cell _ _ _ ∅ (@CWComplex.instRelCWComplex _ _ _ (stageCWComplex hι k)) n →
      @cell _ _ _ ∅ (@CWComplex.instRelCWComplex _ _ _ (stageCWComplex hι (k + 1))) n :=
  fun i ↦ (stageCellEquiv hι (k + 1) n).symm (ι k n (stageCellEquiv hι k n i))

variable {ι} (hcell : ∀ k n i x, map n (ι k n i) x = F.map (homOfLE k.le_succ) (map n i x))

include hcell in
/-- A cell of a stage has the same characteristic map in the colimit as its image in the next
stage. -/
private lemma map_stageι (k n : ℕ)
    (i : @cell _ _ _ ∅ (@CWComplex.instRelCWComplex _ _ _ (stageCWComplex hι k)) n) :
    @map _ _ _ ∅ (@CWComplex.instRelCWComplex _ _ _ (stageCWComplex hι (k + 1))) n
        (stageι hι ι k n i) =
      @map _ _ _ ∅ (@CWComplex.instRelCWComplex _ _ _ (stageCWComplex hι k)) n i := by
  rw [map_stageCWComplex, map_stageCWComplex, stageι, Equiv.apply_symm_apply, stageMap, stageMap]
  congr 1
  funext x
  rw [Function.comp_apply, Function.comp_apply, hcell, ← ConcreteCategory.comp_apply, c.w]

/-- The cells of the stage `k + 1` which do not come from the stage `k` in the colimit are those
of `F.obj (k + 1)` outside the range of `ι k n`. -/
private def stageNewCellEquiv (k n : ℕ) :
    {i // i ∉ range (stageι hι ι k n)} ≃ ↥(range (ι k n))ᶜ :=
  (stageCellEquiv hι (k + 1) n).subtypeEquiv fun i ↦ by
    simp only [mem_compl_iff, stageι, mem_range, Equiv.symm_apply_eq]
    exact not_congr ⟨fun ⟨j, hj⟩ ↦ ⟨_, hj⟩, fun ⟨j, hj⟩ ↦
      ⟨(stageCellEquiv hι k n).symm j, by rw [Equiv.apply_symm_apply, hj]⟩⟩

variable (hF : ∀ k : ℕ, IsClosedEmbedding (F.map (homOfLE k.le_succ))) (hc : IsColimit c)

omit [∀ k, CWComplex (univ : Set (F.obj k))] in
include hc in
/-- A subset of the colimit of a sequence of spaces is closed when its traces on the images of the
stages are closed. -/
private lemma isClosed_of_isClosed_inter_range (A : Set c.pt)
    (_ : A ⊆ ⋃ k, (range (c.ι.app k) : Set c.pt)) (hA : ∀ k, IsClosed (A ∩ range (c.ι.app k))) :
    IsClosed A :=
  (TopCat.isCoherentWith_range_ι_of_isColimit hc).isClosed_of_forall_isClosed_inter <| by
    rintro _ ⟨k, rfl⟩
    exact hA k

omit [∀ k, CWComplex (univ : Set (F.obj k))] in
include hc in
/-- The images of the stages cover the colimit of a sequence of spaces. -/
private lemma image_id_iUnion_range_ι : id '' ⋃ k, (range (c.ι.app k) : Set c.pt) = univ := by
  rw [image_id, TopCat.iUnion_range_ι_eq_univ_of_isColimit hc]

/-- The union of the images of the stages in the colimit, as the union of a tower of CW
complexes. -/
@[instance_reducible]
private def stageUnionCWComplex : CWComplex (⋃ k, (range (c.ι.app k) : Set c.pt)) :=
  letI := stageCWComplex (TopCat.isClosedEmbedding_ι_of_isColimit_of_succ hF hc)
  cwSubcomplexTowerUnion (W := fun k ↦ (range (c.ι.app k) : Set c.pt)) (map_stageι _ hcell)
    (isClosed_of_isClosed_inter_range hc)

/-- **The colimit of a sequence of CW complexes.** Let `F` be a sequence of spaces, each carrying
a CW structure, whose maps `F.obj k ⟶ F.obj (k + 1)` are closed embeddings carrying cells to cells:
`ι k n` sends each `n`-cell of `F.obj k` to an `n`-cell of `F.obj (k + 1)` whose characteristic map
is the old one followed by the map of `F`. Then the colimit of `F` is a CW complex whose `n`-cells
are the `n`-cells of `F.obj 0` together with, for every `k`, the `n`-cells of `F.obj (k + 1)`
outside the range of `ι k n` (`TauCeti.sequentialColimitCWComplexCellEquiv`). Their characteristic
maps are those of the stages followed by the maps to the colimit
(`TauCeti.coe_map_sequentialColimitCWComplexCellEquiv_symm_inl` and
`TauCeti.coe_map_sequentialColimitCWComplexCellEquiv_symm_inr`).

The structure is not an instance, since it depends on the maps `ι`. -/
@[instance_reducible]
def sequentialColimitCWComplex : CWComplex (univ : Set c.pt) :=
  letI := stageUnionCWComplex hcell hF hc
  letI := IsClosedEmbedding.id.relCWComplex (image_id_iUnion_range_ι hc) (image_empty _)
  RelCWComplex.toCWComplex _

/-- The `n`-cells of the colimit of a sequence of CW complexes are the `n`-cells of the first
stage together with, for every `k`, the `n`-cells of the stage `k + 1` which do not come from the
stage `k`. -/
def sequentialColimitCWComplexCellEquiv (n : ℕ) :
    @cell _ _ _ ∅ (@CWComplex.instRelCWComplex _ _ _ (sequentialColimitCWComplex hcell hF hc)) n ≃
      cell (univ : Set (F.obj 0)) n ⊕ Σ k, ↥(range (ι k n))ᶜ :=
  have hι := TopCat.isClosedEmbedding_ι_of_isColimit_of_succ hF hc
  letI := stageCWComplex hι
  letI := stageUnionCWComplex hcell hF hc
  (IsClosedEmbedding.id.relCWComplexCellEquiv (image_id_iUnion_range_ι hc) (image_empty _)
    n).trans <|
    (cwSubcomplexTowerUnionCellEquiv (map_stageι hι hcell) (isClosed_of_isClosed_inter_range hc)
      n).trans <|
      (Equiv.sigmaNatSucc _).trans <| Equiv.sumCongr
        ((Equiv.subtypeUnivEquiv (isNewTowerCell_zero (stageι hι ι))).trans (stageCellEquiv hι 0 n))
        (Equiv.sigmaCongrRight fun k ↦ (Equiv.subtypeEquivRight fun i ↦
          isNewTowerCell_succ_iff (stageι hι ι) i).trans (stageNewCellEquiv hι (ι := ι) k n))

/-- The characteristic map of an `n`-cell of the first stage, as a cell of the colimit, is its
characteristic map followed by the map to the colimit. -/
@[simp]
theorem coe_map_sequentialColimitCWComplexCellEquiv_symm_inl {n : ℕ}
    (i : cell (univ : Set (F.obj 0)) n) :
    ⇑(@map _ _ _ ∅ (@CWComplex.instRelCWComplex _ _ _ (sequentialColimitCWComplex hcell hF hc)) n
      ((sequentialColimitCWComplexCellEquiv hcell hF hc n).symm (.inl i))) =
      c.ι.app 0 ∘ map n i := by
  have hι := TopCat.isClosedEmbedding_ι_of_isColimit_of_succ hF hc
  let := stageCWComplex hι
  let := stageUnionCWComplex hcell hF hc
  refine (IsClosedEmbedding.id.coe_map_relCWComplex (image_id_iUnion_range_ι hc) (image_empty _)
    n _).trans ?_
  simp only [sequentialColimitCWComplexCellEquiv, Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  rw [map_cwSubcomplexTowerUnionCellEquiv_symm]
  exact congrArg (fun e : PartialEquiv (Fin n → ℝ) c.pt ↦ id ∘ ⇑e)
    ((map_stageCWComplex hι 0 n ((stageCellEquiv hι 0 n).symm i)).trans
      (congrArg (stageMap hι 0 n) ((stageCellEquiv hι 0 n).apply_symm_apply i)))

/-- The characteristic map of an `n`-cell of the stage `k + 1` which does not come from the
stage `k`, as a cell of the colimit, is its characteristic map followed by the map to the
colimit. -/
@[simp]
theorem coe_map_sequentialColimitCWComplexCellEquiv_symm_inr {n k : ℕ} (i : ↥(range (ι k n))ᶜ) :
    ⇑(@map _ _ _ ∅ (@CWComplex.instRelCWComplex _ _ _ (sequentialColimitCWComplex hcell hF hc)) n
      ((sequentialColimitCWComplexCellEquiv hcell hF hc n).symm (.inr ⟨k, i⟩))) =
      c.ι.app (k + 1) ∘ map n (i : cell (univ : Set (F.obj (k + 1))) n) := by
  have hι := TopCat.isClosedEmbedding_ι_of_isColimit_of_succ hF hc
  let := stageCWComplex hι
  let := stageUnionCWComplex hcell hF hc
  refine (IsClosedEmbedding.id.coe_map_relCWComplex (image_id_iUnion_range_ι hc) (image_empty _)
    n _).trans ?_
  simp only [sequentialColimitCWComplexCellEquiv, Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  rw [map_cwSubcomplexTowerUnionCellEquiv_symm]
  exact congrArg (fun e : PartialEquiv (Fin n → ℝ) c.pt ↦ id ∘ ⇑e)
    ((map_stageCWComplex hι (k + 1) n ((stageCellEquiv hι (k + 1) n).symm i)).trans
      (congrArg (stageMap hι (k + 1) n) ((stageCellEquiv hι (k + 1) n).apply_symm_apply i)))

end TauCeti
