/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.Coherent

/-!
# The union of a tower of CW complexes

Let `W 0, W 1, …` be subsets of a space `X`, each carrying a classical CW structure, such that
every cell of `W k` is a cell of `W (k + 1)` with the same characteristic map: this is recorded by
maps `ι k n : cell (W k) n → cell (W (k + 1)) n` with `map n (ι k n i) = map n i`. If `X` carries
the topology coherent with the stages `W k` (`Topology.IsCoherentWith (range W)`), then the union
`⋃ k, W k` is a CW complex (`TauCeti.cwSubcomplexTowerUnion`). When `X` is the union of the
stages this is the CW structure on the final-topology union of the tower.

A cell of `W k` is *new* (`TauCeti.IsNewTowerCell`) if it is not the image under `ι` of a cell of
`W (k - 1)`; every cell of `W 0` is new. The `n`-cells of the union are the new `n`-cells of all
the stages (`TauCeti.cwSubcomplexTowerUnionCellEquiv`), with their characteristic maps. Nothing is
assumed about the dimensions of the cells added at a given stage: a later stage may add cells of
lower dimension than an earlier one, as happens when the critical levels of a Morse function are
crossed in increasing order. Closure-finiteness is inherited from the stages, because a cell
together with the finitely many cells meeting its boundary already lies in the stage where the cell
is born. No separation axiom is needed for the CW structure itself.

Every cell of `W k` is the image of a unique new cell of a stage `k' ≤ k`
(`TauCeti.towerOrigin`), so the `n`-cells of `W k` are exactly the `n`-cells of the union born at
the stages up to `k` (`TauCeti.towerStageCellEquiv`). In a Hausdorff space each stage is therefore
a subcomplex of the union (`TauCeti.cwSubcomplexTowerUnionSubcomplex`).

## Main definitions

* `TauCeti.IsNewTowerCell`: the cells of a stage which do not come from the previous stage.
* `TauCeti.cwSubcomplexTowerUnion`: the CW structure on the union of the tower.
* `TauCeti.cwSubcomplexTowerUnionCellEquiv`: its `n`-cells are the new `n`-cells of the stages.
* `TauCeti.towerStageCellEquiv`: the `n`-cells of a stage are the cells of the union born at the
  stages up to it.
* `TauCeti.cwSubcomplexTowerUnionSubcomplex`: each stage is a subcomplex of the union.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, Chapter 0 and the Appendix, for CW complexes built by
  attaching cells and for the weak topology of their union.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5, where a manifold is built from a sequence of cell attachments, one for each
  critical level of a Morse function.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex

namespace TauCeti

universe u

variable {X : Type u} [TopologicalSpace X] {W : ℕ → Set X} [∀ k, CWComplex (W k)]
  (ι : ∀ k n, cell (W k) n → cell (W (k + 1)) n)

/-- A cell of the stage `W k` of a tower of CW complexes is *new* if it does not come from the
previous stage, that is, if it is not in the range of `ι (k - 1)`. Every cell of `W 0` is new. -/
def IsNewTowerCell : ∀ (k : ℕ) {n : ℕ}, cell (W k) n → Prop
  | 0, _, _ => True
  | k + 1, n, i => i ∉ range (ι k n)

/-- Every cell of the first stage is new. -/
@[simp]
theorem isNewTowerCell_zero {n : ℕ} (i : cell (W 0) n) : IsNewTowerCell ι 0 i :=
  trivial

/-- A cell of the stage `W (k + 1)` is new exactly when it does not come from `W k`. -/
@[simp]
theorem isNewTowerCell_succ_iff {k n : ℕ} (i : cell (W (k + 1)) n) :
    IsNewTowerCell ι (k + 1) i ↔ i ∉ range (ι k n) :=
  Iff.rfl

/-- The `n`-cells of the union of a tower of CW complexes: the new `n`-cells of all the stages. -/
abbrev TowerNewCell (n : ℕ) : Type u :=
  Σ k, {i : cell (W k) n // IsNewTowerCell ι k i}

open Classical in
/-- The new cell from which a cell of the stage `W k` comes: following `ι` backwards as long as
possible, every cell of `W k` is the image of a new cell of some stage `k' ≤ k`
(`TauCeti.towerOrigin_fst_le`), with the same characteristic map (`TauCeti.map_towerOrigin`). -/
def towerOrigin : ∀ (k : ℕ) {n : ℕ}, cell (W k) n → TowerNewCell ι n
  | 0, _, i => ⟨0, i, trivial⟩
  | k + 1, n, i => if h : i ∈ range (ι k n) then towerOrigin k h.choose else ⟨k + 1, i, h⟩

/-- The new cell from which a cell of `W k` comes is born at a stage up to `k`. -/
theorem towerOrigin_fst_le : ∀ (k : ℕ) {n : ℕ} (i : cell (W k) n), (towerOrigin ι k i).1 ≤ k
  | 0, _, _ => le_rfl
  | k + 1, n, i => by
    by_cases h : i ∈ range (ι k n)
    · rw [towerOrigin, dite_eq_left h]
      exact (towerOrigin_fst_le k _).trans k.le_succ
    · rw [towerOrigin, dite_eq_right h]

/-- A new cell is its own origin. -/
theorem towerOrigin_of_isNewTowerCell :
    ∀ {k n : ℕ} (i : cell (W k) n) (hi : IsNewTowerCell ι k i), towerOrigin ι k i = ⟨k, i, hi⟩
  | 0, _, _, _ => rfl
  | _ + 1, _, i, hi => by rw [towerOrigin, dite_eq_right hi]

variable {ι} (hι : ∀ k n (i : cell (W k) n), map n (ι k n i) = map n i)
include hι

/-- The new cell from which a cell of `W k` comes has the same characteristic map. -/
theorem map_towerOrigin : ∀ (k : ℕ) {n : ℕ} (i : cell (W k) n),
    map n (towerOrigin ι k i).2.1 = map n i
  | 0, _, _ => rfl
  | k + 1, n, i => by
    by_cases h : i ∈ range (ι k n)
    · rw [towerOrigin, dite_eq_left h, map_towerOrigin k, ← hι, h.choose_spec]
    · rw [towerOrigin, dite_eq_right h]

/-- The open cell of the new cell from which a cell of `W k` comes is the open cell of that
cell. -/
theorem openCell_towerOrigin (k : ℕ) {n : ℕ} (i : cell (W k) n) :
    openCell n (towerOrigin ι k i).2.1 = openCell n i := by
  simp only [openCell, map_towerOrigin hι]

/-- The closed cell of the new cell from which a cell of `W k` comes is the closed cell of that
cell. -/
theorem closedCell_towerOrigin (k : ℕ) {n : ℕ} (i : cell (W k) n) :
    closedCell n (towerOrigin ι k i).2.1 = closedCell n i := by
  simp only [closedCell, map_towerOrigin hι]

/-- The stages of a tower of CW complexes increase. -/
theorem monotone_of_forall_map_eq : Monotone W := by
  refine monotone_nat_of_le_succ fun k ↦ ?_
  rw [← CWComplex.union (C := W k)]
  refine iUnion₂_subset fun n i ↦ ?_
  have : closedCell n (ι k n i) = closedCell n i := by simp only [closedCell, hι]
  exact this ▸ closedCell_subset_complex n (ι k n i)

/-- The open cell of a new cell of `W (k + 1)` does not meet the previous stage `W k`. -/
theorem disjoint_openCell_of_notMem_range {k n : ℕ} {i : cell (W (k + 1)) n}
    (hi : i ∉ range (ι k n)) : Disjoint (openCell n i) (W k) := by
  rw [← CWComplex.iUnion_openCell_eq_complex (C := W k)]
  refine disjoint_iUnion₂_right.2 fun m j ↦ ?_
  have : openCell m (ι k m j) = openCell m j := by simp only [openCell, hι]
  refine this ▸ RelCWComplex.disjoint_openCell_of_ne fun h ↦ hi ?_
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
  exact ⟨j, (eq_of_heq h).symm⟩

/-- The open cell of a new cell of `W l` does not meet any open cell of an earlier stage `W k`. -/
theorem disjoint_openCell_of_lt_of_isNewTowerCell {k l n m : ℕ} (hkl : k < l) (i : cell (W k) n)
    {j : cell (W l) m} (hj : IsNewTowerCell ι l j) : Disjoint (openCell n i) (openCell m j) := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  exact ((disjoint_openCell_of_notMem_range hι hj).mono_right ((openCell_subset_complex n i).trans
    (monotone_of_forall_map_eq hι (Nat.le_of_lt_succ hkl)))).symm

/-- The open cells of distinct new cells of a tower of CW complexes are disjoint. -/
theorem disjoint_openCell_towerNewCell_of_ne {c d : Σ n, TowerNewCell ι n} (h : c ≠ d) :
    Disjoint (openCell c.1 c.2.2.1) (openCell d.1 d.2.2.1) := by
  obtain ⟨n, k, i, hi⟩ := c
  obtain ⟨m, l, j, hj⟩ := d
  rcases lt_trichotomy k l with hkl | rfl | hlk
  · exact disjoint_openCell_of_lt_of_isNewTowerCell hι hkl i hj
  · refine RelCWComplex.disjoint_openCell_of_ne fun h' ↦ h ?_
    obtain ⟨rfl, h'⟩ := Sigma.mk.inj_iff.1 h'
    cases eq_of_heq h'
    rfl
  · exact (disjoint_openCell_of_lt_of_isNewTowerCell hι hlk j hi).symm

/-- Two new cells of a tower of CW complexes whose open cells meet are equal. -/
theorem eq_of_not_disjoint_openCell_towerNewCell {c d : Σ n, TowerNewCell ι n}
    (h : ¬Disjoint (openCell c.1 c.2.2.1) (openCell d.1 d.2.2.1)) : c = d := by
  by_contra hcd
  exact h (disjoint_openCell_towerNewCell_of_ne hι hcd)

variable (hW : IsCoherentWith (range W))

/-- **The union of a tower of CW complexes.** Let `W 0, W 1, …` be CW complexes in `X` such that
every cell of `W k` is a cell of `W (k + 1)` with the same characteristic map, through
`ι k n : cell (W k) n → cell (W (k + 1)) n`. If `X` carries the topology coherent with the stages,
the union `⋃ k, W k` is a CW complex whose `n`-cells are the new `n`-cells of the stages
(`TauCeti.cwSubcomplexTowerUnionCellEquiv`), with their characteristic maps.

The structure is not an instance, since it depends on the maps `ι`. -/
@[instance_reducible]
def cwSubcomplexTowerUnion : CWComplex (⋃ k, W k) where
  cell n := TowerNewCell ι n
  map n c := map n c.2.1
  source_eq n c := source_eq n c.2.1
  continuousOn n c := RelCWComplex.continuousOn n c.2.1
  continuousOn_symm n c := continuousOn_symm n c.2.1
  pairwiseDisjoint' _ _ _ _ h := disjoint_openCell_towerNewCell_of_ne hι h
  mapsTo' n c := by
    classical
    obtain ⟨I, hI⟩ := RelCWComplex.mapsTo (C := W c.1) n c.2.1
    refine ⟨fun m ↦ (I m).image (towerOrigin ι c.1), hI.mono_right ?_⟩
    rw [empty_union]
    refine iUnion₂_mono fun m _ ↦ iUnion₂_subset fun j hj ↦ ?_
    exact subset_iUnion₂_of_subset (towerOrigin ι c.1 j) (Finset.mem_image_of_mem _ hj)
      (closedCell_towerOrigin hι c.1 j).ge
  closed' A _ hA := by
    refine hW.isClosed_iff.2 ?_
    rintro _ ⟨k, rfl⟩
    have hAk : IsClosed (A ∩ W k) := by
      refine CWComplex.closed' (C := W k) _ inter_subset_right fun n (j : cell (W k) n) ↦ ?_
      change IsClosed (A ∩ W k ∩ closedCell n j)
      rw [inter_assoc, inter_eq_right.2 (closedCell_subset_complex n j),
        ← closedCell_towerOrigin hι k j]
      exact hA n (towerOrigin ι k j)
    have := hAk.preimage (continuous_subtype_val (p := (· ∈ W k)))
    rwa [preimage_inter, Subtype.coe_preimage_self, inter_univ] at this
  union' := by
    refine Subset.antisymm (iUnion₂_subset fun n c ↦ ?_) (iUnion_subset fun k ↦ ?_)
    · exact (closedCell_subset_complex n c.2.1).trans (subset_iUnion W c.1)
    · rw [← CWComplex.union (C := W k)]
      refine iUnion₂_subset fun n j ↦ ?_
      exact subset_iUnion₂_of_subset n (towerOrigin ι k j) (closedCell_towerOrigin hι k j).ge

/-- The `n`-cells of the union of a tower of CW complexes are the new `n`-cells of its stages. -/
def cwSubcomplexTowerUnionCellEquiv (n : ℕ) :
    @cell X _ (⋃ k, W k) ∅ (@CWComplex.instRelCWComplex X _ _ (cwSubcomplexTowerUnion hι hW)) n ≃
      TowerNewCell ι n :=
  Equiv.refl _

/-- The characteristic map of a new cell of a stage, as a cell of the union, is its characteristic
map in that stage. -/
@[simp]
theorem map_cwSubcomplexTowerUnionCellEquiv_symm {n : ℕ} (c : TowerNewCell ι n) :
    @map X _ (⋃ k, W k) ∅ (@CWComplex.instRelCWComplex X _ _ (cwSubcomplexTowerUnion hι hW)) n
      ((cwSubcomplexTowerUnionCellEquiv hι hW n).symm c) = map n c.2.1 :=
  (rfl)

/-- The open cell of a new cell of a stage, as a cell of the union, is its open cell in that
stage. -/
@[simp]
theorem openCell_cwSubcomplexTowerUnionCellEquiv_symm {n : ℕ} (c : TowerNewCell ι n) :
    @openCell X _ (⋃ k, W k) ∅ (@CWComplex.instRelCWComplex X _ _ (cwSubcomplexTowerUnion hι hW))
      n ((cwSubcomplexTowerUnionCellEquiv hι hW n).symm c) = openCell n c.2.1 :=
  (rfl)

/-- The closed cell of a new cell of a stage, as a cell of the union, is its closed cell in that
stage. -/
@[simp]
theorem closedCell_cwSubcomplexTowerUnionCellEquiv_symm {n : ℕ} (c : TowerNewCell ι n) :
    @closedCell X _ (⋃ k, W k) ∅ (@CWComplex.instRelCWComplex X _ _ (cwSubcomplexTowerUnion hι hW))
      n ((cwSubcomplexTowerUnionCellEquiv hι hW n).symm c) = closedCell n c.2.1 :=
  (rfl)

omit hW in
/-- **The cells of a stage.** The `n`-cells of the stage `W k` correspond to the new `n`-cells of
the stages up to `k`, by `TauCeti.towerOrigin`. -/
def towerStageCellEquiv (k n : ℕ) : cell (W k) n ≃ {c : TowerNewCell ι n // c.1 ≤ k} :=
  Equiv.ofBijective (fun i ↦ ⟨towerOrigin ι k i, towerOrigin_fst_le ι k i⟩) <| by
    refine ⟨fun i j h ↦ ?_, fun ⟨c, hc⟩ ↦ ?_⟩
    · have h' : towerOrigin ι k i = towerOrigin ι k j := congrArg Subtype.val h
      have hij : openCell n i = openCell n j := by
        rw [← openCell_towerOrigin hι k i, ← openCell_towerOrigin hι k j, h']
      have hd : ¬Disjoint (openCell n i) (openCell n j) :=
        not_disjoint_iff_nonempty_inter.2 (by rw [hij, inter_self]; exact openCell_nonempty n j)
      exact sigma_mk_injective (RelCWComplex.eq_of_not_disjoint_openCell hd)
    · have hx : map n c.2.1 0 ∈ W k := monotone_of_forall_map_eq hι hc
        (openCell_subset_complex n c.2.1 (map_zero_mem_openCell n c.2.1))
      rw [← CWComplex.iUnion_openCell_eq_complex (C := W k)] at hx
      obtain ⟨m, j, hxj⟩ := mem_iUnion₂.1 hx
      have h := eq_of_not_disjoint_openCell_towerNewCell hι (c := ⟨m, towerOrigin ι k j⟩)
        (d := ⟨n, c⟩) (not_disjoint_iff.2 ⟨_, (openCell_towerOrigin hι k j).symm ▸ hxj,
          map_zero_mem_openCell n c.2.1⟩)
      obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
      exact ⟨j, Subtype.ext (eq_of_heq h)⟩

omit hW in
/-- A cell of the stage `W k` corresponds to the new cell from which it comes. -/
@[simp]
theorem coe_towerStageCellEquiv_apply {k n : ℕ} (i : cell (W k) n) :
    (towerStageCellEquiv hι k n i : TowerNewCell ι n) = towerOrigin ι k i :=
  (rfl)

omit hW in
/-- A cell of the stage `W k` has the characteristic map of the new cell to which it
corresponds. -/
theorem map_towerStageCellEquiv_symm {k n : ℕ} (c : {c : TowerNewCell ι n // c.1 ≤ k}) :
    map n ((towerStageCellEquiv hι k n).symm c) = map n c.1.2.1 := by
  conv_rhs => rw [← (towerStageCellEquiv hι k n).apply_symm_apply c]
  rw [coe_towerStageCellEquiv_apply, map_towerOrigin hι]

/-- **The stages are subcomplexes.** In a Hausdorff space, each stage `W k` of a tower of CW
complexes is the subcomplex of the union consisting of the cells born at the stages up to `k`. -/
def cwSubcomplexTowerUnionSubcomplex [T2Space X] (k : ℕ) :
    @Subcomplex X _ (⋃ k, W k) ∅
      (@CWComplex.instRelCWComplex X _ _ (cwSubcomplexTowerUnion hι hW)) :=
  CWComplex.Subcomplex.mk'' (h := cwSubcomplexTowerUnion hι hW) (⋃ k, W k) (W k)
    (fun n ↦ {c | (cwSubcomplexTowerUnionCellEquiv hι hW n c).1 ≤ k}) <| by
    refine Subset.antisymm (iUnion₂_subset fun n c ↦ ?_) ?_
    · exact (openCell_subset_complex n c.1.2.1).trans (monotone_of_forall_map_eq hι c.2)
    · conv_lhs => rw [← CWComplex.iUnion_openCell_eq_complex (C := W k)]
      refine iUnion₂_subset fun n j ↦ ?_
      rw [← openCell_towerOrigin hι k j]
      exact subset_iUnion₂_of_subset n
        (⟨(cwSubcomplexTowerUnionCellEquiv hι hW n).symm (towerOrigin ι k j),
          towerOrigin_fst_le ι k j⟩ :
            {c | (cwSubcomplexTowerUnionCellEquiv hι hW n c).1 ≤ k}) subset_rfl

/-- The subcomplex of the union given by a stage is that stage. -/
@[simp]
theorem coe_cwSubcomplexTowerUnionSubcomplex [T2Space X] (k : ℕ) :
    (cwSubcomplexTowerUnionSubcomplex hι hW k : Set X) = W k :=
  (rfl)

/-- The cells of the subcomplex given by the stage `W k` are the cells of the union born at the
stages up to `k`. -/
theorem mem_cwSubcomplexTowerUnionSubcomplex_I_iff [T2Space X] {k n : ℕ}
    (c : @cell X _ (⋃ k, W k) ∅
      (@CWComplex.instRelCWComplex X _ _ (cwSubcomplexTowerUnion hι hW)) n) :
    c ∈ @Subcomplex.I X _ (⋃ k, W k) ∅
      (@CWComplex.instRelCWComplex X _ _ (cwSubcomplexTowerUnion hι hW))
      (cwSubcomplexTowerUnionSubcomplex hι hW k) n ↔
      (cwSubcomplexTowerUnionCellEquiv hι hW n c).1 ≤ k :=
  Iff.rfl

end TauCeti
