/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.ClosedEmbedding
public import TauCeti.Topology.Category.TopCat.DisjointOpens
public import TauCeti.Topology.Category.TopCat.Limits.Basic
public import TauCeti.Topology.CWComplex.Classical.Image
public import TauCeti.Topology.CWComplex.Classical.TowerUnion
public import TauCeti.Topology.Homotopy.Extension.CWComplex
public import TauCeti.Topology.Homotopy.Extension.Tower
import TauCeti.Topology.Coherent

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
`TauCeti.exists_homotopyEquiv_of_isColimit` of a colimit of a tower of closed cofibrations with
such a union.

## Main definitions

* `TauCeti.cwComplexOfIsColimit`: the CW structure on a colimit of a sequence of cellular closed
  embeddings of CW complexes.
* `TauCeti.cwComplexOfIsColimitCellEquiv`: its `n`-cells are those of the first stage and the new
  `n`-cells of the later stages.

## Main results

* `TauCeti.coe_map_cwComplexOfIsColimitCellEquiv_symm_inl` and
  `TauCeti.coe_map_cwComplexOfIsColimitCellEquiv_symm_inr`: the characteristic maps of the cells.
* `TauCeti.hasHomotopyExtensionProperty_preimage_range_ι`: each stage has the homotopy extension
  property in the next one, inside the colimit.
* `TauCeti.t2Space_of_isColimit_cwComplex`: a sequential colimit of Hausdorff CW complexes is
  Hausdorff.
* `TauCeti.exists_homotopyEquiv_of_isColimit_cwComplex`: a space exhausted by a tower of
  cofibrations with compatible CW models is homotopy equivalent to the colimit of the models.

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

/-- **The cells of a sequential colimit of CW complexes.** The `n`-cells of the CW structure
`TauCeti.cwComplexOfIsColimit` on the colimit are the `n`-cells of the first stage `F 0`, together
with, for every `k`, the `n`-cells of `F (k + 1)` which are not images of cells of `F k`. -/
def cwComplexOfIsColimitCellEquiv (n : ℕ) :
    @cell c.pt _ univ ∅ (@CWComplex.instRelCWComplex _ _ _ (cwComplexOfIsColimit hF hι hc)) n ≃
      cell (univ : Set (F.obj 0)) n ⊕ Σ k, ↥(range (ι k n))ᶜ :=
  letI := fun k ↦ stageCWComplex hF hc k
  letI := towerCWComplex hF hι hc
  -- The cells of the colimit are the new cells of the tower of ranges, indexed by their birth
  -- stage; every cell of the first stage is new.
  (IsClosedEmbedding.id.relCWComplexCellEquiv (image_id_iUnion_range hc) (image_empty _) n).trans <|
    (cwSubcomplexTowerUnionCellEquiv (coe_map_stageCellMap hF hι hc)
      (isClosed_of_forall_isClosed_inter_range hc) n).trans <|
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

include hF hι hc in
/-- **The stages of a sequential colimit of CW complexes are linked by closed cofibrations.**
Inside the colimit, the range of `F k` has the homotopy extension property in the range of
`F (k + 1)`: it is the image of the subcomplex of `F (k + 1)` made of the cells coming from
`F k`. -/
theorem hasHomotopyExtensionProperty_preimage_range_ι [∀ k, T2Space (F.obj k)] (k : ℕ) :
    HasHomotopyExtensionProperty
      ((↑) ⁻¹' (range (c.ι.app k) : Set c.pt) : Set ↥(range (c.ι.app (k + 1)) : Set c.pt)) :=
  hasHomotopyExtensionProperty_preimage_range_ι_of_isColimit hF hc k
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
restricting to `h k` on every stage. This is `TauCeti.exists_homotopyEquiv_of_isColimit`, as the
ranges of the bonding maps are subcomplexes. -/
theorem exists_homotopyEquiv_of_isColimit_cwComplex [∀ k, T2Space (F.obj k)] {Y : Type u}
    [TopologicalSpace Y] {A : ℕ → Set Y} (hA : Monotone A) (hAY : ⋃ k, A k = univ)
    (hAc : IsCoherentWith (range A))
    (hAH : ∀ k, HasHomotopyExtensionProperty ((↑) ⁻¹' A k : Set (A (k + 1))))
    (h : ∀ k, F.obj k ≃ₕ A k)
    (hh : ∀ k w, (h (k + 1) (F.map (homOfLE k.le_succ) w) : Y) = h k w) :
    ∃ H : c.pt ≃ₕ Y, ∀ k w, H (c.ι.app k w) = (h k w : Y) :=
  exists_homotopyEquiv_of_isColimit hF hc
    (fun k ↦ hasHomotopyExtensionProperty_range_of_coe_map_eq (ι k) (hι k)) hA hAY hAc hAH h hh

end TauCeti
