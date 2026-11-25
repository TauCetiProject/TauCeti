/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.ClosedEmbedding
public import TauCeti.Topology.Category.TopCat.Compact
public import TauCeti.Topology.Category.TopCat.DisjointOpens
public import TauCeti.Topology.Category.TopCat.Limits.Basic
public import TauCeti.Topology.CWComplex.Classical.Image
public import TauCeti.Topology.CWComplex.Classical.Tower.Union
public import TauCeti.Topology.Homotopy.Extension.CWComplex
public import TauCeti.Topology.Homotopy.Extension.Tower
import TauCeti.Topology.Coherent
import TauCeti.Topology.Homeomorph.SetCongr

/-!
# Sequential colimits of CW complexes

Let `F 0 → F 1 → F 2 → ⋯` be a sequence of spaces in `TopCat`, each carrying a classical CW
structure on `univ`, whose bonding maps are closed embeddings carrying every cell onto a cell:
maps `ι k n : cell (F k) n → cell (F (k + 1)) n` with `map n (ι k n i) = F.map _ ∘ map n i`. Then
every colimit of the sequence carries a CW structure on `univ`
(`TauCeti.cwComplexOfIsColimit`) whose `n`-cells are the `n`-cells of `F 0` together with, for
every `k`, the `n`-cells of `F (k + 1)` that do not come from `F k`
(`TauCeti.cwComplexOfIsColimitCellEquiv`). The characteristic map of a cell is its characteristic
map in the stage where it is born, followed by the map of that stage to the colimit. Nothing is
assumed about the dimensions of the cells added at each stage.

This is how a CW complex built by attaching cells of arbitrary dimensions in countably many steps,
for instance one critical level of a proper Morse function at a time, is recognized as a CW
complex. The stages are read inside the colimit as the ranges of the colimit maps, which are
closed embeddings (`TauCeti.TopCat.isClosedEmbedding_ι_of_isColimit`). Each carries the image of
the CW structure of its stage (`Topology.IsClosedEmbedding.relCWComplex`), and the colimit
topology makes their union a CW complex (`TauCeti.cwSubcomplexTowerUnion`).

The range of each stage `F k` is the subcomplex of the colimit made of the cells born at the
stages up to `k` (`TauCeti.cwComplexOfIsColimitSubcomplex`), and every compact subset of the
colimit lies in one of these subcomplexes, when the stages are `T1`
(`TauCeti.exists_subset_cwComplexOfIsColimitSubcomplex_of_isCompact`). Each of these subcomplexes
is homeomorphic to its stage (`TauCeti.cwComplexOfIsColimitSubcomplexHomeomorph`), so a statement
about the stages can be read on the colimit.

For the comparison of such a colimit with another increasing union up to homotopy, the stages are
linked by closed cofibrations: the range of the `k`-th stage has the homotopy extension property
in the range of the next one (`TauCeti.hasHomotopyExtensionProperty_preimage_range_ι`), since it
is a subcomplex.

If the stages are Hausdorff, so is the colimit (`TauCeti.t2Space_of_isColimit_cwComplex`): the
range of each bonding map has the homotopy extension property, so the bonding maps extend disjoint
open sets (`TauCeti.TopCat.extendsDisjointOpens_of_hasHomotopyExtensionProperty`). The colimit is
then a model for any space exhausted compatibly by spaces of the homotopy types of the stages. Let
`Y` be the union of an increasing sequence of subsets `A 0 ⊆ A 1 ⊆ ⋯`, each with the homotopy
extension property in the next, carrying the topology coherent with them, and let
`h k : F k ≃ₕ A k` be homotopy equivalences commuting strictly with the inclusions. Then the
colimit is homotopy equivalent to `Y` by a homotopy equivalence restricting to `h k` on `F k`
(`TauCeti.exists_homotopyEquiv_of_isColimit_cwComplex`). This is the comparison
`TauCeti.exists_homotopyEquiv_of_isColimit` of a colimit of a tower of cofibrations with such a
union.

## Main definitions

* `TauCeti.cwComplexOfIsColimit`: the CW structure on a colimit of a sequence of cellular closed
  embeddings of CW complexes.
* `TauCeti.cwComplexOfIsColimitCellEquiv`: its `n`-cells are those of the first stage and the new
  `n`-cells of the later stages.
* `TauCeti.cwComplexOfIsColimitSubcomplex`: the range of stage `k`, as a subcomplex of the
  colimit, with `n`-cells in bijection with those of `F k`
  (`TauCeti.cwComplexOfIsColimitSubcomplexCellEquiv`).
* `TauCeti.cwComplexOfIsColimitSubcomplexHomeomorph`: its homeomorphism with the stage.

## Main results

* `TauCeti.coe_map_cwComplexOfIsColimitCellEquiv_symm_inl` and
  `TauCeti.coe_map_cwComplexOfIsColimitCellEquiv_symm_inr`: the characteristic maps of the cells.
* `TauCeti.mem_cwComplexOfIsColimitSubcomplex_I_iff`: the cells of the subcomplex given by the
  stage `F k` are those born at the stages up to `k`.
* `TauCeti.exists_subset_cwComplexOfIsColimitSubcomplex_of_isCompact`: every compact subset of the
  colimit lies in the subcomplex given by a single stage.
* `TauCeti.monotone_cwComplexOfIsColimitSubcomplex`,
  `TauCeti.iUnion_coe_cwComplexOfIsColimitSubcomplex`, and
  `TauCeti.finite_cwComplexOfIsColimitSubcomplex`: the stage subcomplexes form an exhausting
  increasing sequence, and are finite whenever the stages are finite in a Hausdorff colimit.
* `TauCeti.coe_map_cwComplexOfIsColimitSubcomplexCellEquiv_symm` and
  `TauCeti.coe_cwComplexOfIsColimitSubcomplexCellEquiv_symm_ι`: the characteristic maps and stage
  compatibility of the stage subcomplex cells.
* `TauCeti.hasHomotopyExtensionProperty_preimage_range_ι`: each stage has the homotopy extension
  property in the next one, inside the colimit.
* `TauCeti.t2Space_of_isColimit_cwComplex`: a sequential colimit of Hausdorff CW complexes is
  Hausdorff.
* `TauCeti.exists_homotopyEquiv_of_isColimit_cwComplex` and
  `TauCeti.exists_homotopyEquiv_cwComplexOfIsColimitSubcomplex`: a space exhausted by a tower of
  cofibrations with compatible CW models is homotopy equivalent to the colimit of the models,
  compatibly on each stage subcomplex and with a stage-preserving homotopy inverse.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5, whose proof builds a CW model of a manifold one critical level at a time and
  passes to the union of the stages.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 and the Appendix, for CW complexes built by attaching cells inductively, with the
  weak topology of the union of their stages.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Topology.RelCWComplex
open scoped ContinuousMap

namespace TauCeti

universe u

variable {F : ℕ ⥤ TopCat.{u}} [∀ k, CWComplex (univ : Set (F.obj k))]
  (hF : ∀ k : ℕ, IsClosedEmbedding (F.map (homOfLE k.le_succ)))
  {ι : ∀ k n, cell (univ : Set (F.obj k)) n → cell (univ : Set (F.obj (k + 1))) n}
  (hι : ∀ (k n : ℕ) i, ⇑(map n (ι k n i)) = F.map (homOfLE k.le_succ) ∘ map n i)
  {c : Cocone F} (hc : IsColimit c)

/-- The CW structure of the stage `F k`, read on its range in the colimit, relative to `∅`. -/
private abbrev stageRelCWComplex (k : ℕ) : RelCWComplex (range (c.ι.app k)) ∅ :=
  (TopCat.isClosedEmbedding_ι_of_isColimit_of_succ hF hc k).relCWComplex image_univ (image_empty _)

/-- The CW structure of the stage `F k`, read on its range in the colimit. -/
private abbrev stageCWComplex (k : ℕ) : CWComplex (range (c.ι.app k)) :=
  @RelCWComplex.toCWComplex _ _ _ (stageRelCWComplex hF hc k)

/-- The cells of the range of `F k` are those of `F k`. -/
private abbrev stageCellEquiv (k n : ℕ) :
    @cell c.pt _ (range (c.ι.app k)) ∅
        (@CWComplex.instRelCWComplex _ _ _ (stageCWComplex hF hc k)) n ≃
      cell (univ : Set (F.obj k)) n :=
  (TopCat.isClosedEmbedding_ι_of_isColimit_of_succ hF hc k).relCWComplexCellEquiv image_univ
    (image_empty _) n

/-- The characteristic maps of the range of `F k` are those of `F k`, followed by the map to the
colimit. -/
private theorem coe_map_stage (k n : ℕ)
    (i : @cell c.pt _ (range (c.ι.app k)) ∅
      (@CWComplex.instRelCWComplex _ _ _ (stageCWComplex hF hc k)) n) :
    ⇑(@map c.pt _ (range (c.ι.app k)) ∅
        (@CWComplex.instRelCWComplex _ _ _ (stageCWComplex hF hc k)) n i) =
      c.ι.app k ∘ map n (stageCellEquiv hF hc k n i) :=
  (TopCat.isClosedEmbedding_ι_of_isColimit_of_succ hF hc k).coe_map_relCWComplex image_univ
    (image_empty _) n i

/-- The cells of the stage `F k` as cells of the next stage, read in the colimit. -/
private abbrev stageCellMap (k n : ℕ) :
    @cell c.pt _ (range (c.ι.app k)) ∅
        (@CWComplex.instRelCWComplex _ _ _ (stageCWComplex hF hc k)) n →
      @cell c.pt _ (range (c.ι.app (k + 1))) ∅
        (@CWComplex.instRelCWComplex _ _ _ (stageCWComplex hF hc (k + 1))) n :=
  fun i ↦ (stageCellEquiv hF hc (k + 1) n).symm (ι k n (stageCellEquiv hF hc k n i))

include hι in
/-- Read in the colimit, a cell of `F k` and its image in `F (k + 1)` have the same characteristic
map, since `c.ι.app (k + 1) ∘ F.map _ = c.ι.app k`. -/
private theorem coe_map_stageCellMap (k n : ℕ)
    (i : @cell c.pt _ (range (c.ι.app k)) ∅
      (@CWComplex.instRelCWComplex _ _ _ (stageCWComplex hF hc k)) n) :
    ⇑(@map c.pt _ (range (c.ι.app (k + 1))) ∅
        (@CWComplex.instRelCWComplex _ _ _ (stageCWComplex hF hc (k + 1))) n
        (stageCellMap hF hc (ι := ι) k n i)) =
      ⇑(@map c.pt _ (range (c.ι.app k)) ∅
        (@CWComplex.instRelCWComplex _ _ _ (stageCWComplex hF hc k)) n i) := by
  rw [coe_map_stage, coe_map_stage, Equiv.apply_symm_apply, hι, ← Function.comp_assoc,
    ← TopCat.coe_comp, c.w]

omit [∀ k, CWComplex (univ : Set (F.obj k))] in
include hc in
/-- A subset of the colimit meeting the range of every stage in a closed set is closed, since the
colimit carries the topology coherent with these ranges. -/
private theorem isClosed_of_forall_isClosed_inter_range :
    ∀ A ⊆ ⋃ k, (range (c.ι.app k) : Set c.pt),
      (∀ k, IsClosed (A ∩ (range (c.ι.app k) : Set c.pt))) → IsClosed A := fun _ _ hA ↦
  (TopCat.isCoherentWith_range_ι_of_isColimit hc).isClosed_of_forall_isClosed_inter
    (forall_mem_range.2 hA)

/-- The CW structure on the union of the ranges of the stages. -/
private abbrev towerCWComplex : CWComplex (⋃ k, (range (c.ι.app k) : Set c.pt)) :=
  letI := fun k ↦ stageCWComplex hF hc k
  cwSubcomplexTowerUnion (ι := stageCellMap hF hc (ι := ι)) (coe_map_stageCellMap hF hι hc)
    (isClosed_of_forall_isClosed_inter_range hc)

omit [∀ k, CWComplex (univ : Set (F.obj k))] in
include hc in
/-- The union of the ranges of the stages is the whole colimit. -/
private theorem image_id_iUnion_range : id '' ⋃ k, (range (c.ι.app k) : Set c.pt) = univ := by
  rw [image_id]
  exact TopCat.iUnion_range_ι_of_isColimit hc

/-- **The CW structure on a sequential colimit of CW complexes.** Let `F` be a sequence of spaces
carrying CW structures on `univ`, whose bonding maps are closed embeddings carrying every cell
onto a cell, with characteristic maps: `map n (ι k n i) = F.map _ ∘ map n i`. Then the colimit of
`F` carries a CW structure on `univ` whose cells are the cells of the stages, each counted once at
the stage where it is born (`TauCeti.cwComplexOfIsColimitCellEquiv`). -/
@[instance_reducible]
def cwComplexOfIsColimit : CWComplex (univ : Set c.pt) :=
  @RelCWComplex.toCWComplex _ _ _ <|
    @IsClosedEmbedding.relCWComplex c.pt c.pt _ _ id .id (⋃ k, range (c.ι.app k)) ∅
      (@CWComplex.instRelCWComplex _ _ _ (towerCWComplex hF hι hc)) univ ∅
      (image_id_iUnion_range hc) (image_empty _)

/-- The new cells of the stage `F (k + 1)`, read in the colimit, are the cells of `F (k + 1)`
outside the range of `ι k`. -/
private def newCellEquiv (k n : ℕ) :
    {i : @cell c.pt _ (range (c.ι.app (k + 1))) ∅
        (@CWComplex.instRelCWComplex _ _ _ (stageCWComplex hF hc (k + 1))) n //
      i ∉ range (stageCellMap hF hc (ι := ι) k n)} ≃ ↥(range (ι k n))ᶜ :=
  (stageCellEquiv hF hc (k + 1) n).subtypeEquiv fun i ↦ by
    refine not_congr ⟨?_, ?_⟩
    · rintro ⟨j, hj⟩
      exact ⟨_, by rw [← hj, stageCellMap, Equiv.apply_symm_apply]⟩
    · rintro ⟨j, hj⟩
      refine ⟨(stageCellEquiv hF hc k n).symm j, ?_⟩
      rw [stageCellMap, Equiv.apply_symm_apply, hj, Equiv.symm_apply_apply]

/-- The cells of the first stage, read in the colimit, are all new. -/
private def firstCellEquiv (n : ℕ) :
    letI := fun k ↦ stageCWComplex hF hc k
    {i : cell (range (c.ι.app 0) : Set c.pt) n //
      IsNewTowerCell (W := fun k ↦ (range (c.ι.app k) : Set c.pt))
        (stageCellMap hF hc (ι := ι)) 0 i} ≃ cell (univ : Set (F.obj 0)) n :=
  letI := fun k ↦ stageCWComplex hF hc k
  (Equiv.subtypeUnivEquiv fun i ↦ isNewTowerCell_zero
    (W := fun k ↦ (range (c.ι.app k) : Set c.pt)) (stageCellMap hF hc (ι := ι)) i).trans
    (stageCellEquiv hF hc 0 n)

/-- The new cells of the stage `F (k + 1)`, read in the colimit, are the cells of `F (k + 1)`
outside the range of `ι k`, as cells of the tower of ranges. -/
private def newTowerCellEquiv (k n : ℕ) :
    letI := fun k ↦ stageCWComplex hF hc k
    {i : cell (range (c.ι.app (k + 1)) : Set c.pt) n //
      IsNewTowerCell (W := fun k ↦ (range (c.ι.app k) : Set c.pt))
        (stageCellMap hF hc (ι := ι)) (k + 1) i} ≃ ↥(range (ι k n))ᶜ :=
  letI := fun k ↦ stageCWComplex hF hc k
  (Equiv.subtypeEquivRight fun i ↦ isNewTowerCell_succ_iff
    (W := fun k ↦ (range (c.ι.app k) : Set c.pt)) (stageCellMap hF hc (ι := ι)) i).trans
    (newCellEquiv hF hc k n)

/-- The cells of the colimit are the cells of the union of the ranges of the stages. -/
private abbrev towerCell (n : ℕ) :
    letI := fun k ↦ stageCWComplex hF hc k
    @cell c.pt _ univ ∅ (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc)) n ≃
      TowerNewCell (W := fun k ↦ (range (c.ι.app k) : Set c.pt)) (stageCellMap hF hc (ι := ι)) n :=
  letI := fun k ↦ stageCWComplex hF hc k
  (@IsClosedEmbedding.relCWComplexCellEquiv c.pt c.pt _ _ id .id _ ∅
    (@CWComplex.instRelCWComplex _ _ _ (towerCWComplex hF hι hc)) univ ∅
    (image_id_iUnion_range hc) (image_empty _) n).trans
    (cwSubcomplexTowerUnionCellEquiv (coe_map_stageCellMap hF hι hc)
      (isClosed_of_forall_isClosed_inter_range hc) n)

/-- **The cells of a sequential colimit of CW complexes.** The `n`-cells of the CW structure
`TauCeti.cwComplexOfIsColimit` on the colimit are the `n`-cells of the first stage `F 0`, together
with, for every `k`, the `n`-cells of `F (k + 1)` which are not images of cells of `F k`. -/
def cwComplexOfIsColimitCellEquiv (n : ℕ) :
    @cell c.pt _ univ ∅ (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc)) n ≃
      cell (univ : Set (F.obj 0)) n ⊕ Σ k, ↥(range (ι k n))ᶜ :=
  letI := fun k ↦ stageCWComplex hF hc k
  -- The cells of the colimit are the new cells of the tower of ranges, indexed by their birth
  -- stage; every cell of the first stage is new.
  (towerCell hF hι hc n).trans <|
    (Equiv.sigmaNatSucc _).trans <|
      Equiv.sumCongr (firstCellEquiv hF hc n) (Equiv.sigmaCongrRight fun k ↦
        newTowerCellEquiv hF hc k n)

/-- The characteristic maps of the colimit are those of the union of the ranges of the stages. -/
private theorem coe_map_cwComplexOfIsColimit {n : ℕ}
    (i : @cell c.pt _ univ ∅
      (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc)) n) :
    ⇑(@map c.pt _ univ ∅ (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc)) n i) =
      id ∘ @map c.pt _ _ ∅ (@CWComplex.instRelCWComplex _ _ _ (towerCWComplex hF hι hc)) n
        (@IsClosedEmbedding.relCWComplexCellEquiv c.pt c.pt _ _ id .id _ ∅
          (@CWComplex.instRelCWComplex _ _ _ (towerCWComplex hF hι hc)) univ ∅
          (image_id_iUnion_range hc) (image_empty _) n i) :=
  @IsClosedEmbedding.coe_map_relCWComplex c.pt c.pt _ _ id .id _ ∅
    (@CWComplex.instRelCWComplex _ _ _ (towerCWComplex hF hι hc)) univ ∅
    (image_id_iUnion_range hc) (image_empty _) n i

/-- The characteristic map of a cell of the first stage, as a cell of the colimit, is its
characteristic map followed by the map to the colimit. -/
@[simp]
theorem coe_map_cwComplexOfIsColimitCellEquiv_symm_inl {n : ℕ}
    (i : cell (univ : Set (F.obj 0)) n) :
    ⇑(@map c.pt _ univ ∅ (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc)) n
      ((cwComplexOfIsColimitCellEquiv hF hι hc n).symm (.inl i))) = c.ι.app 0 ∘ map n i := by
  simp [cwComplexOfIsColimitCellEquiv, Equiv.sigmaNatSucc, map_cwSubcomplexTowerUnionCellEquiv_symm,
    firstCellEquiv]

/-- The characteristic map of a cell of `F (k + 1)` not coming from `F k`, as a cell of the
colimit, is its characteristic map followed by the map to the colimit. -/
@[simp]
theorem coe_map_cwComplexOfIsColimitCellEquiv_symm_inr {n : ℕ}
    (i : Σ k, ↥(range (ι k n))ᶜ) :
    ⇑(@map c.pt _ univ ∅ (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc)) n
      ((cwComplexOfIsColimitCellEquiv hF hι hc n).symm (.inr i))) =
      c.ι.app (i.1 + 1) ∘ map n (i.2 : cell (univ : Set (F.obj (i.1 + 1))) n) := by
  obtain ⟨k, i⟩ := i
  simp [cwComplexOfIsColimitCellEquiv, Equiv.sigmaNatSucc, map_cwSubcomplexTowerUnionCellEquiv_symm,
    Equiv.sigmaCongrRight_symm, Sigma.map, newTowerCellEquiv, newCellEquiv]

/-- The stage at which a cell of the colimit is born: `0` for the cells of the first stage `F 0`,
and `k + 1` for the cells of `F (k + 1)` not coming from `F k`
(`TauCeti.cwComplexOfIsColimitCellEquiv`). -/
def cwComplexOfIsColimitCellStage {n : ℕ}
    (j : @cell c.pt _ univ ∅
      (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc)) n) : ℕ :=
  Sum.elim (fun _ ↦ 0) (fun i ↦ i.1 + 1) (cwComplexOfIsColimitCellEquiv hF hι hc n j)

/-- The cells of the first stage `F 0` are born at stage `0`. -/
@[simp]
theorem cwComplexOfIsColimitCellStage_symm_inl {n : ℕ} (i : cell (univ : Set (F.obj 0)) n) :
    cwComplexOfIsColimitCellStage hF hι hc ((cwComplexOfIsColimitCellEquiv hF hι hc n).symm
      (.inl i)) = 0 := by
  simp [cwComplexOfIsColimitCellStage]

/-- The cells of `F (k + 1)` not coming from `F k` are born at stage `k + 1`. -/
@[simp]
theorem cwComplexOfIsColimitCellStage_symm_inr {n : ℕ} (i : Σ k, ↥(range (ι k n))ᶜ) :
    cwComplexOfIsColimitCellStage hF hι hc ((cwComplexOfIsColimitCellEquiv hF hι hc n).symm
      (.inr i)) = i.1 + 1 := by
  simp [cwComplexOfIsColimitCellStage]

/-- The stage at which a cell of the colimit is born is the stage of the underlying new cell of
the tower of ranges. -/
private theorem cwComplexOfIsColimitCellStage_eq {n : ℕ}
    (j : @cell c.pt _ univ ∅
      (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc)) n) :
    cwComplexOfIsColimitCellStage hF hι hc j = (towerCell hF hι hc n j).1 := by
  rw [cwComplexOfIsColimitCellStage, cwComplexOfIsColimitCellEquiv, Equiv.trans_apply,
    Equiv.trans_apply]
  rcases towerCell hF hι hc n j with ⟨_ | k, x⟩ <;> simp [Equiv.sigmaNatSucc, firstCellEquiv,
    newTowerCellEquiv, newCellEquiv]

/-- The open cells of the colimit are those of the stages where they are born. -/
private theorem openCell_cwComplexOfIsColimit {n : ℕ}
    (j : @cell c.pt _ univ ∅
      (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc)) n) :
    @openCell c.pt _ univ ∅
        (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc)) n j =
      @openCell c.pt _ (range (c.ι.app (towerCell hF hι hc n j).1)) ∅
        (@CWComplex.instRelCWComplex _ _ _ (stageCWComplex hF hc _)) n
        (towerCell hF hι hc n j).2.val := by
  let := fun k ↦ stageCWComplex hF hc k
  have hj : @IsClosedEmbedding.relCWComplexCellEquiv c.pt c.pt _ _ id .id _ ∅
      (@CWComplex.instRelCWComplex _ _ _ (towerCWComplex hF hι hc)) univ ∅
      (image_id_iUnion_range hc) (image_empty _) n j =
      (cwSubcomplexTowerUnionCellEquiv (coe_map_stageCellMap hF hι hc)
        (isClosed_of_forall_isClosed_inter_range hc) n).symm (towerCell hF hι hc n j) := by
    simp only [towerCell, Equiv.trans_apply, Equiv.symm_apply_apply]
  have hm := coe_map_cwComplexOfIsColimit hF hι hc j
  rw [hj, map_cwSubcomplexTowerUnionCellEquiv_symm, Function.id_comp] at hm
  unfold RelCWComplex.openCell
  rw [hm]

/-- **The stages of a sequential colimit of CW complexes are subcomplexes.** The range of the
stage `F k` in the colimit is the subcomplex of `TauCeti.cwComplexOfIsColimit` made of the cells
born at the stages up to `k`: the cells of `F 0`, and the cells of `F (l + 1)` not coming from
`F l` for `l < k` (`TauCeti.mem_cwComplexOfIsColimitSubcomplex_I_iff`). -/
def cwComplexOfIsColimitSubcomplex (k : ℕ) :
    @Subcomplex c.pt _ univ ∅
      (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc)) :=
  letI := cwComplexOfIsColimit hF hι hc
  { carrier := range (c.ι.app k)
    I := fun n ↦ {j : @cell c.pt _ univ ∅
      (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc)) n |
        cwComplexOfIsColimitCellStage hF hι hc j ≤ k}
    closed' := (TopCat.isClosedEmbedding_ι_of_isColimit_of_succ hF hc k).isClosedMap.isClosed_range
    union' := by
      let := fun k ↦ stageCWComplex hF hc k
      -- Reindex the open cells of the colimit by the new cells of the tower of ranges.
      rw [empty_union, ← iUnion_openCell_towerNewCell_of_le
        (W := fun k ↦ (range (c.ι.app k) : Set c.pt)) (coe_map_stageCellMap hF hι hc) k]
      refine iUnion_congr fun n ↦ ((towerCell hF hι hc n).subtypeEquiv fun j ↦ ?_).iSup_congr
        fun j ↦ (openCell_cwComplexOfIsColimit hF hι hc j.val).symm
      rw [mem_ofPred_eq, cwComplexOfIsColimitCellStage_eq] }

/-- The subcomplex of the colimit given by the stage `F k` is the range of `F k`. -/
@[simp]
theorem coe_cwComplexOfIsColimitSubcomplex (k : ℕ) :
    (cwComplexOfIsColimitSubcomplex hF hι hc k : Set c.pt) = range (c.ι.app k) :=
  (rfl)

/-- The cells of the subcomplex given by the stage `F k` are the cells born at the stages up to
`k`: those of `F 0`, at stage `0`, and those of `F (l + 1)` not coming from `F l`, at stage
`l + 1`. -/
theorem mem_cwComplexOfIsColimitSubcomplex_I_iff {k n : ℕ}
    (j : @cell c.pt _ univ ∅
      (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc)) n) :
    j ∈ @Subcomplex.I c.pt _ univ ∅
      (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc))
      (cwComplexOfIsColimitSubcomplex hF hι hc k) n ↔
      cwComplexOfIsColimitCellStage hF hι hc j ≤ k :=
  Iff.rfl

/-- Every cell of the first stage `F 0` is a cell of every stage. -/
@[simp]
theorem cwComplexOfIsColimitCellEquiv_symm_inl_mem_I {k n : ℕ}
    (i : cell (univ : Set (F.obj 0)) n) :
    (cwComplexOfIsColimitCellEquiv hF hι hc n).symm (.inl i) ∈ @Subcomplex.I c.pt _ univ ∅
      (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc))
      (cwComplexOfIsColimitSubcomplex hF hι hc k) n := by
  simp [mem_cwComplexOfIsColimitSubcomplex_I_iff]

/-- A cell of `F (l + 1)` not coming from `F l` is a cell of the stage `F k` exactly when
`l < k`. -/
@[simp]
theorem cwComplexOfIsColimitCellEquiv_symm_inr_mem_I_iff {k n : ℕ}
    (i : Σ l, ↥(range (ι l n))ᶜ) :
    (cwComplexOfIsColimitCellEquiv hF hι hc n).symm (.inr i) ∈ @Subcomplex.I c.pt _ univ ∅
      (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc))
      (cwComplexOfIsColimitSubcomplex hF hι hc k) n ↔ i.1 < k := by
  simp [mem_cwComplexOfIsColimitSubcomplex_I_iff]

include hF in
/-- Every compact subset of a sequential colimit of `T1` CW complexes lies in the subcomplex given
by a single stage. -/
theorem exists_subset_cwComplexOfIsColimitSubcomplex_of_isCompact [∀ k, T1Space (F.obj k)]
    {K : Set c.pt} (hK : IsCompact K) :
    ∃ k, K ⊆ (cwComplexOfIsColimitSubcomplex hF hι hc k : Set c.pt) :=
  TopCat.exists_subset_range_ι_of_isCompact (fun _ _ hij ↦
    (TopCat.isClosedEmbedding_map_of_isWellOrderContinuous F (fun n _ ↦ hF n) hij).injective) hc hK

/-- The subcomplex of the colimit given by the stage `F k` is homeomorphic to `F k`, by the inverse
of the map `c.ι.app k` onto its range. -/
def cwComplexOfIsColimitSubcomplexHomeomorph (k : ℕ) :
    cwComplexOfIsColimitSubcomplex hF hι hc k ≃ₜ F.obj k :=
  (Homeomorph.setCongr (coe_cwComplexOfIsColimitSubcomplex hF hι hc k)).trans
    (TopCat.isClosedEmbedding_ι_of_isColimit_of_succ hF hc k).isEmbedding.toHomeomorph.symm

/-- The homeomorphism of the subcomplex given by the stage `F k` with `F k` inverts `c.ι.app k`. -/
@[simp]
theorem ι_app_cwComplexOfIsColimitSubcomplexHomeomorph (k : ℕ)
    (x : cwComplexOfIsColimitSubcomplex hF hι hc k) :
    dsimp% c.ι.app k (cwComplexOfIsColimitSubcomplexHomeomorph hF hι hc k x) = (x : c.pt) := by
  have hemb := (TopCat.isClosedEmbedding_ι_of_isColimit_of_succ hF hc k).isEmbedding
  rw [cwComplexOfIsColimitSubcomplexHomeomorph, Homeomorph.trans_apply,
    ← hemb.toHomeomorph_apply_coe, Homeomorph.apply_symm_apply, Homeomorph.setCongr_apply]

/-- The inverse of the homeomorphism of the subcomplex given by the stage `F k` with `F k` is
`c.ι.app k`. -/
@[simp]
theorem coe_cwComplexOfIsColimitSubcomplexHomeomorph_symm_apply (k : ℕ) (w : F.obj k) :
    ((cwComplexOfIsColimitSubcomplexHomeomorph hF hι hc k).symm w : c.pt) = c.ι.app k w := by
  conv_rhs => rw [← (cwComplexOfIsColimitSubcomplexHomeomorph hF hι hc k).apply_symm_apply w]
  rw [ι_app_cwComplexOfIsColimitSubcomplexHomeomorph]

include hF hι hc in
/-- **The stages of a sequential colimit of CW complexes are linked by closed cofibrations.**
Inside the colimit, the range of `F k` has the homotopy extension property in the range of
`F (k + 1)`: it is the image of the subcomplex of `F (k + 1)` made of the cells coming from
`F k`. -/
theorem hasHomotopyExtensionProperty_preimage_range_ι [∀ k, T2Space (F.obj k)] (k : ℕ) :
    HasHomotopyExtensionProperty
      ((↑) ⁻¹' (range (c.ι.app k) : Set c.pt) : Set ↥(range (c.ι.app (k + 1)) : Set c.pt)) :=
  hasHomotopyExtensionProperty_preimage_range_ι_of_isColimit hc hF k
    (hasHomotopyExtensionProperty_range_of_coe_map_eq (ι k) (hι k))

include hF hι hc in
/-- **A sequential colimit of Hausdorff CW complexes is Hausdorff.** The range of each bonding map
is a subcomplex, so it has the homotopy extension property and the bonding map extends disjoint
open sets. -/
theorem t2Space_of_isColimit_cwComplex [∀ k, T2Space (F.obj k)] : T2Space c.pt :=
  TopCat.t2Space_of_isColimit_nat (fun k ↦
    TopCat.extendsDisjointOpens_of_hasHomotopyExtensionProperty _ (hF k).isInducing
      (hasHomotopyExtensionProperty_range_of_coe_map_eq (ι k) (hι k))) hc

include hF hι hc in
/-- **The CW model of a tower.** Let `Y` be the union of an increasing sequence of subsets `A k`,
each with the homotopy extension property in the next, carrying the topology coherent with them.
Let `F` be a sequence of Hausdorff CW complexes whose bonding maps are closed embeddings carrying
every cell onto a cell, and let `h k : F k ≃ₕ A k` be homotopy equivalences commuting with the
inclusions. Then the colimit of `F`, a Hausdorff CW complex (`TauCeti.cwComplexOfIsColimit` and
`TauCeti.t2Space_of_isColimit_cwComplex`), is homotopy equivalent to `Y` by a homotopy equivalence
restricting to `h k` on every stage and whose homotopy inverse maps each `A k` into the range of
`c.ι.app k`. This is `TauCeti.exists_homotopyEquiv_of_isColimit`, as the ranges of the bonding maps
are subcomplexes. -/
theorem exists_homotopyEquiv_of_isColimit_cwComplex [∀ k, T2Space (F.obj k)] {Y : Type u}
    [TopologicalSpace Y] {A : ℕ → Set Y} (hA : Monotone A) (hAY : ⋃ k, A k = univ)
    (hAc : IsCoherentWith (range A))
    (hAH : ∀ k, HasHomotopyExtensionProperty ((↑) ⁻¹' A k : Set (A (k + 1))))
    (h : ∀ k, F.obj k ≃ₕ A k)
    (hh : ∀ k w, (h (k + 1) (F.map (homOfLE k.le_succ) w) : Y) = h k w) :
    ∃ H : c.pt ≃ₕ Y, (∀ k w, H (c.ι.app k w) = (h k w : Y)) ∧
      ∀ k, MapsTo H.symm (A k) (range (c.ι.app k)) :=
  exists_homotopyEquiv_of_isColimit hc (fun k ↦ (hF k).isEmbedding)
    (fun k ↦ hasHomotopyExtensionProperty_range_of_coe_map_eq (ι k) (hι k)) hA hAY hAc hAH h hh

/-- The stage subcomplexes of a sequential CW colimit form an increasing sequence. -/
theorem monotone_cwComplexOfIsColimitSubcomplex :
    @Monotone ℕ (@Subcomplex c.pt _ univ ∅
      (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc))) _ _
      (cwComplexOfIsColimitSubcomplex hF hι hc) := fun _ _ hkl ↦
  let := cwComplexOfIsColimit hF hι hc
  SetLike.coe_subset_coe.1 (TopCat.monotone_range_ι c hkl)

/-- The stage subcomplexes of a sequential CW colimit cover the colimit. -/
theorem iUnion_coe_cwComplexOfIsColimitSubcomplex :
    (⋃ k, ((@SetLike.coe _ c.pt (@RelCWComplex.Subcomplex.instSetLike c.pt _ univ ∅
      (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc))))
      (cwComplexOfIsColimitSubcomplex hF hι hc k))) = univ :=
  TopCat.iUnion_range_ι_of_isColimit hc

/-- **The cells of a stage subcomplex.** In `cwComplexOfIsColimit`, the `n`-cells belonging to the
subcomplex `cwComplexOfIsColimitSubcomplex hF hι hc k` correspond to the `n`-cells of stage
`F k`. -/
def cwComplexOfIsColimitSubcomplexCellEquiv (k n : ℕ) :
    ↥((@Subcomplex.I c.pt _ univ ∅
      (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc))
      (cwComplexOfIsColimitSubcomplex hF hι hc k)) n) ≃ cell (univ : Set (F.obj k)) n :=
  letI := fun m ↦ stageCWComplex hF hc m
  (((Equiv.subtypeEquiv (towerCell hF hι hc n) fun j ↦
      Iff.of_eq (congrArg (· ≤ k) (cwComplexOfIsColimitCellStage_eq hF hι hc j))).trans
    (towerStageCellEquiv (coe_map_stageCellMap hF hι hc) k n).symm).trans
    (stageCellEquiv hF hc k n))

/-- Unfolding the underlying colimit cell of
`(cwComplexOfIsColimitSubcomplexCellEquiv hF hι hc k n).symm i`. -/
private theorem coe_cwComplexOfIsColimitSubcomplexCellEquiv_symm (k n : ℕ)
    (i : cell (univ : Set (F.obj k)) n) :
    letI := fun m ↦ stageCWComplex hF hc m
    letI := cwComplexOfIsColimit hF hι hc
    ((cwComplexOfIsColimitSubcomplexCellEquiv hF hι hc k n).symm i :
      cell (univ : Set c.pt) n) =
      (towerCell hF hι hc n).symm
        (towerStageCellEquiv (coe_map_stageCellMap hF hι hc) k n
          ((stageCellEquiv hF hc k n).symm i)).val :=
  rfl

/-- The characteristic map of a cell of stage `F k`, seen in `cwComplexOfIsColimit` via
`cwComplexOfIsColimitSubcomplexCellEquiv`, is its characteristic map followed by `c.ι.app k`. -/
@[simp]
theorem coe_map_cwComplexOfIsColimitSubcomplexCellEquiv_symm (k : ℕ) {n : ℕ}
    (i : cell (univ : Set (F.obj k)) n) :
    ⇑(@map c.pt _ univ ∅ (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc)) n
      ((cwComplexOfIsColimitSubcomplexCellEquiv hF hι hc k n).symm i :
        @cell c.pt _ univ ∅
          (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc)) n)) =
      c.ι.app k ∘ map n i := by
  let := fun m ↦ stageCWComplex hF hc m
  rw [coe_cwComplexOfIsColimitSubcomplexCellEquiv_symm, coe_map_cwComplexOfIsColimit]
  simp only [towerCell, Equiv.symm_trans_apply, Equiv.apply_symm_apply,
    map_cwSubcomplexTowerUnionCellEquiv_symm, coe_towerStageCellEquiv_apply, Function.id_comp]
  rw [coe_map_towerOrigin (coe_map_stageCellMap hF hι hc), coe_map_stage, Equiv.apply_symm_apply]

/-- A cell of stage `F k` and its image under `ι k n` in stage `F (k + 1)` correspond to the same
cell of `cwComplexOfIsColimit`. -/
@[simp]
theorem coe_cwComplexOfIsColimitSubcomplexCellEquiv_symm_ι (k : ℕ) {n : ℕ}
    (i : cell (univ : Set (F.obj k)) n) :
    ((cwComplexOfIsColimitSubcomplexCellEquiv hF hι hc (k + 1) n).symm (ι k n i) :
      @cell c.pt _ univ ∅
        (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc)) n) =
      ((cwComplexOfIsColimitSubcomplexCellEquiv hF hι hc k n).symm i :
        @cell c.pt _ univ ∅
          (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc)) n) := by
  let := fun m ↦ stageCWComplex hF hc m
  rw [coe_cwComplexOfIsColimitSubcomplexCellEquiv_symm,
    coe_cwComplexOfIsColimitSubcomplexCellEquiv_symm]
  have hst : (stageCellEquiv hF hc (k + 1) n).symm (ι k n i) =
      stageCellMap hF hc (ι := ι) k n ((stageCellEquiv hF hc k n).symm i) := by
    simp [stageCellMap]
  rw [hst, towerStageCellEquiv_ι (coe_map_stageCellMap hF hι hc)]

/-- When stage `F k` is a finite CW complex and the colimit is Hausdorff, the stage subcomplex
`cwComplexOfIsColimitSubcomplex hF hι hc k` is a finite CW complex. -/
theorem finite_cwComplexOfIsColimitSubcomplex [T2Space c.pt] (k : ℕ)
    [RelCWComplex.Finite (univ : Set (F.obj k))] :
    @RelCWComplex.Finite c.pt _
      ((@SetLike.coe _ c.pt (@RelCWComplex.Subcomplex.instSetLike c.pt _ univ ∅
        (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc))))
        (cwComplexOfIsColimitSubcomplex hF hι hc k)) ∅
      (@RelCWComplex.Subcomplex.instRelCWComplex c.pt _ univ ∅ _
        (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc))
        (cwComplexOfIsColimitSubcomplex hF hι hc k)) := by
  let := cwComplexOfIsColimit hF hι hc
  have := RelCWComplex.finite_cells_of_finite (C := (univ : Set (F.obj k)))
  exact RelCWComplex.finite_of_finite_cells (.of_equiv _
    (Equiv.sigmaCongrRight fun n ↦ (cwComplexOfIsColimitSubcomplexCellEquiv hF hι hc k n).symm))

include hF hι hc in
/-- **Subcomplex-compatible CW model of a tower.** Under the hypotheses of
`TauCeti.exists_homotopyEquiv_of_isColimit_cwComplex`, the homotopy equivalence `H : c.pt ≃ₕ Y`
restricts on each stage subcomplex `W k = cwComplexOfIsColimitSubcomplex hF hι hc k` to a homotopy
equivalence `eW k : (W k : Set c.pt) ≃ₕ A k` compatible with `H`, and its homotopy inverse
`H.symm` carries each `A k` into `W k`. -/
theorem exists_homotopyEquiv_cwComplexOfIsColimitSubcomplex [∀ k, T2Space (F.obj k)] {Y : Type u}
    [TopologicalSpace Y] {A : ℕ → Set Y} (hA : Monotone A) (hAY : ⋃ k, A k = univ)
    (hAc : IsCoherentWith (range A))
    (hAH : ∀ k, HasHomotopyExtensionProperty ((↑) ⁻¹' A k : Set (A (k + 1))))
    (h : ∀ k, F.obj k ≃ₕ A k)
    (hh : ∀ k w, (h (k + 1) (F.map (homOfLE k.le_succ) w) : Y) = h k w) :
    ∃ (H : c.pt ≃ₕ Y)
      (eW : ∀ k,
        ((@SetLike.coe _ c.pt (@RelCWComplex.Subcomplex.instSetLike c.pt _ univ ∅
          (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc))))
          (cwComplexOfIsColimitSubcomplex hF hι hc k)) ≃ₕ A k),
      (∀ k x, (eW k x : Y) = H x) ∧
      ∀ k, MapsTo H.symm (A k)
        ((@SetLike.coe _ c.pt (@RelCWComplex.Subcomplex.instSetLike c.pt _ univ ∅
          (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc))))
          (cwComplexOfIsColimitSubcomplex hF hι hc k)) := by
  obtain ⟨H, hH, hsymm⟩ :=
    exists_homotopyEquiv_of_isColimit_cwComplex hF hι hc hA hAY hAc hAH h hh
  exact ⟨H, fun k ↦ (cwComplexOfIsColimitSubcomplexHomeomorph hF hι hc k).toHomotopyEquiv.trans
    (h k), fun k x ↦ (hH k _).symm.trans
      (congrArg H (ι_app_cwComplexOfIsColimitSubcomplexHomeomorph hF hι hc k x)), hsymm⟩

end TauCeti
