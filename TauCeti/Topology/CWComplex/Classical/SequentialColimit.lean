/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.ClosedEmbedding
public import TauCeti.Topology.CWComplex.Classical.Image
public import TauCeti.Topology.CWComplex.Classical.TowerUnion

/-!
# The colimit of a sequence of CW complexes

Let `F : ℕ ⥤ TopCat` be a sequence of spaces `F.obj 0 → F.obj 1 → ⋯` whose maps are closed
embeddings, each space carrying a CW structure, such that every `n`-cell of `F.obj k` is an
`n`-cell of `F.obj (k + 1)` whose characteristic map is the old one followed by the map
`F.obj k → F.obj (k + 1)`. Then the colimit of `F` is a CW complex whose `n`-cells are the
`n`-cells of `F.obj 0` together with, for each `k`, the `n`-cells of `F.obj (k + 1)` which do not
come from `F.obj k` (`TauCeti.exists_cwComplex_univ_of_isColimit`). The cells of the stages may have
arbitrary dimensions in any order: a later stage may add cells of lower dimension than an earlier
one, as happens when the critical levels of a Morse function are crossed in increasing order.

The maps from the stages to the colimit are closed embeddings
(`TauCeti.TopCat.isClosedEmbedding_ι_of_isColimit`), so each stage is a CW complex in the colimit
(`Topology.IsClosedEmbedding.relCWComplex`), and the colimit carries the topology coherent with
these images. Its CW structure is then the union of a tower of CW complexes
(`TauCeti.cwSubcomplexTowerUnion`). That construction asks the characteristic map of a cell of a
stage, as a partial equivalence, to be literally the same in the next stage. The images of the
stages only have the same characteristic maps as functions; their inverses, which are only
specified on the open cells, are chosen independently. So the characteristic maps are first
replaced by the canonical partial equivalences determined by their values on the open balls
(`Topology.RelCWComplex.replaceMap`), which no longer depend on the stage.

## Main results

* `Topology.RelCWComplex.replaceMap`: the same CW structure, with the characteristic maps replaced
  by other partial equivalences with the same values and sources.
* `TauCeti.exists_cwComplex_univ_of_isColimit`: the CW structure on the colimit of a sequence of
  CW complexes along closed embeddings which carry cells to cells.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 and the Appendix, for CW complexes built by attaching cells inductively, with the weak
  topology of the union of the stages.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex CategoryTheory Limits

universe u

namespace Topology.RelCWComplex

variable {X : Type u} [TopologicalSpace X] {C D : Set X} [RelCWComplex C D]

/-- The CW structure on `C` relative to `D` with the cells of a given one, whose characteristic
maps are replaced by partial equivalences `φ n i` with the same values and the same sources. Such a
partial equivalence has the same image of the source, and its inverse agrees there with the old
one, so all the axioms transfer. This is used to make characteristic maps depend only on their
values, for instance through `Set.InjOn.toPartialEquiv`. -/
@[instance_reducible]
def replaceMap (φ : ∀ n, cell C n → PartialEquiv (Fin n → ℝ) X)
    (hφ : ∀ n i, ⇑(φ n i) = map n i) (hsource : ∀ n i, (φ n i).source = (map n i).source) :
    RelCWComplex C D where
  cell := cell C
  map := φ
  source_eq n i := (hsource n i).trans (source_eq n i)
  continuousOn n i := hφ n i ▸ RelCWComplex.continuousOn n i
  continuousOn_symm n i := by
    have htarget : (φ n i).target = (map n i).target := by
      rw [← (φ n i).image_source_eq_target, ← (map n i).image_source_eq_target, hφ, hsource]
    rw [htarget]
    refine (RelCWComplex.continuousOn_symm n i).congr fun y hy ↦ ?_
    rw [← (map n i).image_source_eq_target] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [(map n i).left_inv hx, ← hφ, (φ n i).left_inv (hsource n i ▸ hx)]
  pairwiseDisjoint' := by
    simpa only [hφ] using RelCWComplex.pairwiseDisjoint' (C := C) (D := D)
  disjointBase' n i := by
    simpa only [hφ] using RelCWComplex.disjointBase' (C := C) n i
  mapsTo n i := by
    simpa only [hφ] using RelCWComplex.mapsTo (C := C) n i
  closed' A hAC hA := RelCWComplex.closed' (C := C) A hAC (by simpa only [hφ] using hA)
  isClosedBase := isClosedBase C
  union' := by
    simpa only [hφ] using RelCWComplex.union' (C := C) (D := D)

variable (φ : ∀ n, cell C n → PartialEquiv (Fin n → ℝ) X) (hφ : ∀ n i, ⇑(φ n i) = map n i)
  (hsource : ∀ n i, (φ n i).source = (map n i).source)

/-- The cells of `Topology.RelCWComplex.replaceMap` are the cells of the original structure. -/
def replaceMapCellEquiv (n : ℕ) : @cell X _ C D (replaceMap φ hφ hsource) n ≃ cell C n :=
  Equiv.refl _

/-- The characteristic maps of `Topology.RelCWComplex.replaceMap` are the given partial
equivalences. -/
@[simp]
lemma map_replaceMap (n : ℕ) (i : @cell X _ C D (replaceMap φ hφ hsource) n) :
    @map X _ C D (replaceMap φ hφ hsource) n i = φ n (replaceMapCellEquiv φ hφ hsource n i) :=
  (rfl)

end Topology.RelCWComplex

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
  (hι k).relCWComplexCellEquiv image_univ (image_empty _) n

/-- The characteristic maps of a stage in the colimit are the maps `TauCeti.stageMap`. -/
private lemma map_stageCWComplex (k n : ℕ)
    (i : @cell _ _ _ ∅ (@CWComplex.instRelCWComplex _ _ _ (stageCWComplex hι k)) n) :
    @map _ _ _ ∅ (@CWComplex.instRelCWComplex _ _ _ (stageCWComplex hι k)) n i =
      stageMap hι k n (stageCellEquiv hι k n i) :=
  (rfl)

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

include hcell in
/-- **The colimit of a sequence of CW complexes.** Let `F` be a sequence of spaces, each carrying
a CW structure, whose maps `F.obj k ⟶ F.obj (k + 1)` are closed embeddings carrying cells to cells:
`ι k n` sends each `n`-cell of `F.obj k` to an `n`-cell of `F.obj (k + 1)` whose characteristic map
is the old one followed by the map of `F`. Then the colimit of `F` carries a CW structure whose
`n`-cells are the `n`-cells of `F.obj 0` together with, for every `k`, the `n`-cells of
`F.obj (k + 1)` outside the range of `ι k n`. -/
theorem exists_cwComplex_univ_of_isColimit
    (hF : ∀ k : ℕ, IsClosedEmbedding (F.map (homOfLE k.le_succ))) (hc : IsColimit c) :
    ∃ _ : CWComplex (univ : Set c.pt), ∀ n, Nonempty (cell (univ : Set c.pt) n ≃
      cell (univ : Set (F.obj 0)) n ⊕ Σ k, ↥(range (ι k n))ᶜ) := by
  have hι : ∀ k, IsClosedEmbedding (c.ι.app k) := TopCat.isClosedEmbedding_ι_of_isColimit
    (fun _ _ ↦ TopCat.isClosedEmbedding_map_of_isWellOrderContinuous F fun k _ ↦ hF k) hc
  let := stageCWComplex hι
  -- A subset of the colimit is closed when its traces on the images of the stages are closed.
  have hW (A : Set c.pt) (_ : A ⊆ ⋃ k, (range (c.ι.app k) : Set c.pt))
      (hA : ∀ k, IsClosed (A ∩ range (c.ι.app k))) : IsClosed A :=
    (TopCat.isClosed_iff_of_isColimit _ hc A).2 fun k ↦ by
      simpa only [preimage_inter, preimage_range, inter_univ] using
        (hA k).preimage (c.ι.app k).hom.continuous
  have hU : ⋃ k, (range (c.ι.app k) : Set c.pt) = univ := eq_univ_of_forall fun y ↦ by
    obtain ⟨k, x, hx⟩ :=
      Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget TopCat) hc) y
    exact mem_iUnion_of_mem k ⟨x, hx⟩
  let := cwSubcomplexTowerUnion (W := fun k ↦ (range (c.ι.app k) : Set c.pt)) (map_stageι hι hcell)
    hW
  let := IsClosedEmbedding.id.relCWComplex (C := ⋃ k, (range (c.ι.app k) : Set c.pt)) (D := ∅)
    (C' := univ) (D' := ∅) (by rw [image_id, hU]) (image_empty _)
  refine ⟨RelCWComplex.toCWComplex _, fun n ↦ ⟨?_⟩⟩
  exact (IsClosedEmbedding.id.relCWComplexCellEquiv _ _ n).trans <|
    (cwSubcomplexTowerUnionCellEquiv (map_stageι hι hcell) hW n).trans <|
      (Equiv.sigmaNatSucc _).trans <| Equiv.sumCongr
        ((Equiv.subtypeUnivEquiv (isNewTowerCell_zero (stageι hι ι))).trans (stageCellEquiv hι 0 n))
        (Equiv.sigmaCongrRight fun k ↦ (Equiv.subtypeEquivRight fun i ↦
          isNewTowerCell_succ_iff (stageι hι ι) i).trans (stageNewCellEquiv hι (ι := ι) k n))

end TauCeti
