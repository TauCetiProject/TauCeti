/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# The union of a tower of CW complexes

Let `C 0, C 1, …` be subsets of a space `X`, each with a CW structure relative to a common base
`D`, such that every cell of `C k` is also a cell of `C (k + 1)`, with the same characteristic
map. Then the union `⋃ k, C k` carries a CW structure relative to `D`
(`Topology.RelCWComplex.towerUnion`) as soon as its topology is the final topology of the stages:
a subset of the union is closed when it meets every stage in a closed set. The cells of the union
in dimension `n` are the new `n`-cells of the stages, those whose characteristic map does not
already occur at an earlier stage (`Topology.RelCWComplex.towerUnionCellEquiv`). Every stage of
the tower is a subcomplex of the union (`Topology.RelCWComplex.towerUnionSubcomplex`).

No condition is imposed on the dimensions of the cells added at the successive stages: a stage
may add cells of lower dimension than those of an earlier stage. This is what happens when a CW
model of a manifold is built by attaching handles across the critical levels of a Morse function
in increasing order of the critical values, where the indices of the critical points need not
increase with the values.

The hypothesis on the topology of the union cannot be dropped. In `X = ℝ`, the finite sets
`C k = {0} ∪ {1 / (j + 1) | j < k}` are CW complexes made of `0`-cells, and every cell of `C k` is
a cell of `C (k + 1)`. The weak topology of their union is discrete, but the union is not a
discrete subspace of `ℝ`: the set of points `1 / (j + 1)` meets every stage in a finite, hence
closed, set without being closed in `ℝ`.

## Main definitions

* `Topology.RelCWComplex.IsTowerNewCell`: a cell of a stage whose characteristic map does not
  occur at an earlier stage.
* `Topology.RelCWComplex.towerFirstCell`: the first occurrence of a cell of a stage.
* `Topology.RelCWComplex.towerUnion`: the relative CW structure on the union of a tower.
* `Topology.RelCWComplex.towerUnionCell`: the cell of the union given by a cell of a stage.
* `Topology.RelCWComplex.towerUnionSubcomplex`: a stage, as a subcomplex of the union.
* `Topology.CWComplex.towerUnion`: the absolute CW structure on the union of a tower of absolute
  CW complexes.

## Main results

* `Topology.RelCWComplex.towerUnionCell_eq_iff`: two cells of stages give the same cell of the
  union exactly when they have the same characteristic map.
* `Topology.RelCWComplex.coe_map_towerUnionCell`: the characteristic map of the cell of the union
  given by a cell of a stage is that of the stage.
* `Topology.RelCWComplex.closedCell_towerUnion_subset`: every closed cell of the union lies in the
  stage at which it first occurs.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Cambridge
  University Press, 2002, Chapter 0 and the Appendix, for CW complexes, their subcomplexes and
  their weak topology.
* J. H. C. Whitehead, *Combinatorial homotopy. I*, Bull. Amer. Math. Soc. 55 (1949), 213–245,
  §5, for CW complexes as cells in an ambient space.
-/

public section

noncomputable section

open Metric Set

namespace Topology.RelCWComplex

universe u

variable {X : Type u} [TopologicalSpace X] (C : ℕ → Set X) {D : Set X}
  [∀ k, RelCWComplex (C k) D]

/-- A cell of the stage `C k` of a tower is **new** if no earlier stage has a cell with the same
characteristic map. -/
def IsTowerNewCell {k n : ℕ} (i : cell (C k) n) : Prop :=
  ∀ l < k, ∀ j : cell (C l) n, ⇑(map n j) ≠ ⇑(map n i)

variable {C}

/-- In a tower in which every cell of a stage is a cell of the next stage, every cell of a stage
is a cell of each later stage. -/
theorem exists_coe_map_eq_of_le
    (hcell : ∀ k n (i : cell (C k) n), ∃ j : cell (C (k + 1)) n, ⇑(map n j) = ⇑(map n i))
    {k l n : ℕ} (hkl : k ≤ l) (i : cell (C k) n) :
    ∃ j : cell (C l) n, ⇑(map n j) = ⇑(map n i) := by
  induction l, hkl using Nat.le_induction with
  | base => exact ⟨i, rfl⟩
  | succ l _ ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨j', hj'⟩ := hcell l n j
    exact ⟨j', hj'.trans hj⟩

/-- In a tower in which every cell of a stage is a cell of the next stage, the stages increase. -/
theorem monotone_of_forall_exists_coe_map_eq
    (hcell : ∀ k n (i : cell (C k) n), ∃ j : cell (C (k + 1)) n, ⇑(map n j) = ⇑(map n i)) :
    Monotone C := by
  intro k l hkl x hx
  rw [← RelCWComplex.union (C := C k)] at hx
  rcases hx with hx | hx
  · exact base_subset_complex hx
  · obtain ⟨n, i, hx⟩ := mem_iUnion₂.1 hx
    obtain ⟨j, hj⟩ := exists_coe_map_eq_of_le hcell hkl i
    exact closedCell_subset_complex n j (by simpa only [closedCell, hj] using hx)

variable (C)

open scoped Classical in
/-- The **first occurrence** of a cell `i` of a stage of a tower: the earliest stage having a cell
with the characteristic map of `i`, together with that cell, which is new. -/
def towerFirstCell {k n : ℕ} (i : cell (C k) n) : Σ l, {j : cell (C l) n // IsTowerNewCell C j} :=
  have h : ∃ l, ∃ j : cell (C l) n, ⇑(map n j) = ⇑(map n i) := ⟨k, i, rfl⟩
  ⟨Nat.find h, (Nat.find_spec h).choose, fun _ hl j hj ↦
    Nat.find_min h hl ⟨j, hj.trans (Nat.find_spec h).choose_spec⟩⟩

/-- The first occurrence of a cell has the same characteristic map. -/
@[simp]
theorem coe_map_towerFirstCell {k n : ℕ} (i : cell (C k) n) :
    ⇑(map n (towerFirstCell C i).2.1) = ⇑(map n i) := by
  classical
  exact (Nat.find_spec (⟨k, i, rfl⟩ : ∃ l, ∃ j : cell (C l) n, ⇑(map n j) = ⇑(map n i))).choose_spec

/-- A cell first occurs at its own stage or earlier. -/
theorem towerFirstCell_fst_le {k n : ℕ} (i : cell (C k) n) : (towerFirstCell C i).1 ≤ k := by
  classical
  exact Nat.find_min' _ ⟨i, rfl⟩

variable {C}

/-- Two new cells of stages of a tower with the same characteristic map are equal. -/
private theorem towerNewCell_eq {l l' n : ℕ} {j : cell (C l) n} {j' : cell (C l') n}
    (hj : IsTowerNewCell C j) (hj' : IsTowerNewCell C j') (h : ⇑(map n j') = ⇑(map n j)) :
    (⟨l', j', hj'⟩ : Σ l, {j : cell (C l) n // IsTowerNewCell C j}) = ⟨l, j, hj⟩ := by
  obtain rfl : l' = l := by
    rcases lt_trichotomy l' l with hl | hl | hl
    · exact absurd h (hj l' hl j')
    · exact hl
    · exact absurd h.symm (hj' l hl j)
  obtain rfl : j' = j := openCell_congr n (by simp only [openCell, h])
  rfl

/-- The first occurrence of a cell is the new cell with the same characteristic map. -/
theorem towerFirstCell_eq {k l n : ℕ} {i : cell (C k) n} {j : cell (C l) n}
    (hj : IsTowerNewCell C j) (h : ⇑(map n j) = ⇑(map n i)) :
    towerFirstCell C i = ⟨l, j, hj⟩ :=
  towerNewCell_eq hj (towerFirstCell C i).2.2 ((coe_map_towerFirstCell C i).trans h.symm)

/-- A new cell is its own first occurrence. -/
theorem towerFirstCell_of_isTowerNewCell {k n : ℕ} {i : cell (C k) n} (hi : IsTowerNewCell C i) :
    towerFirstCell C i = ⟨k, i, hi⟩ :=
  towerFirstCell_eq hi rfl

/-- Two cells of stages of a tower have the same first occurrence exactly when they have the same
characteristic map. -/
@[simp]
theorem towerFirstCell_eq_iff {k l n : ℕ} {i : cell (C k) n} {j : cell (C l) n} :
    towerFirstCell C i = towerFirstCell C j ↔ ⇑(map n i) = ⇑(map n j) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := congrArg (fun c : Σ l, {j : cell (C l) n // IsTowerNewCell C j} ↦ ⇑(map n c.2.1)) h
    simpa only [coe_map_towerFirstCell] using this
  · rw [towerFirstCell_eq (towerFirstCell C j).2.2 ((coe_map_towerFirstCell C j).trans h.symm)]

variable (C)

/-- The **union of a tower** of relative CW complexes `C k` with a common base `D`, in which every
cell of a stage is a cell of the next stage, is a relative CW complex with base `D`, provided
that a subset of the union is closed whenever it meets every stage in a closed set. Its cells are
the new cells of the stages (`Topology.RelCWComplex.towerUnionCellEquiv`), with their
characteristic maps. This is not an instance, since its existence depends on the two
hypotheses. -/
@[instance_reducible]
def towerUnion
    (hcell : ∀ k n (i : cell (C k) n), ∃ j : cell (C (k + 1)) n, ⇑(map n j) = ⇑(map n i))
    (hclosed : ∀ A ⊆ ⋃ k, C k, (∀ k, IsClosed (A ∩ C k)) → IsClosed A) :
    RelCWComplex (⋃ k, C k) D where
  cell n := Σ k, {i : cell (C k) n // IsTowerNewCell C i}
  map n c := map n c.2.1
  source_eq n c := source_eq n c.2.1
  continuousOn n c := continuousOn n c.2.1
  continuousOn_symm n c := continuousOn_symm n c.2.1
  pairwiseDisjoint' := by
    rintro ⟨n, k, i, hi⟩ - ⟨m, l, j, hj⟩ - hne
    -- Both cells are cells of the stage `C (max k l)`, where distinct cells are disjoint.
    obtain ⟨i', hi'⟩ := exists_coe_map_eq_of_le hcell (le_max_left k l) i
    obtain ⟨j', hj'⟩ := exists_coe_map_eq_of_le hcell (le_max_right k l) j
    simp only [Function.onFun, ← hi', ← hj']
    refine disjoint_openCell_of_ne fun heq ↦ hne ?_
    obtain ⟨rfl, hij⟩ := Sigma.mk.inj_iff.mp heq
    cases hij
    exact congrArg (Sigma.mk n)
      ((towerFirstCell_of_isTowerNewCell hi).symm.trans
        (towerFirstCell_eq hj (hj'.symm.trans hi')))
  disjointBase' n c := disjointBase n c.2.1
  mapsTo n c := by
    classical
    obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell (C := C c.1) n c.2.1
    refine ⟨fun m ↦ (I m).image (towerFirstCell C), fun x hx ↦ ?_⟩
    rcases hI (mem_image_of_mem _ hx) with hx | hx
    · exact Or.inl hx
    · obtain ⟨m, hm, j, hj, hx⟩ := by simpa only [mem_iUnion, exists_prop] using hx
      refine Or.inr (mem_iUnion₂.2 ⟨m, hm, mem_iUnion₂.2
        ⟨towerFirstCell C j, Finset.mem_image_of_mem _ hj, ?_⟩⟩)
      simp only [coe_map_towerFirstCell]
      exact hx
  closed' A hA h := hclosed A hA fun k ↦ by
    refine RelCWComplex.closed' (C := C k) (A ∩ C k) inter_subset_right ⟨fun n i ↦ ?_, ?_⟩
    · have hi := h.1 n (towerFirstCell C i)
      simp only [coe_map_towerFirstCell] at hi
      rw [inter_assoc, (inter_eq_right (s := C k) (t := map n i '' closedBall 0 1)).2
        (closedCell_subset_complex n i)]
      exact hi
    · rw [inter_assoc, inter_eq_right.2 (base_subset_complex (C := C k))]
      exact h.2
  isClosedBase := isClosedBase (C 0)
  union' := by
    refine Subset.antisymm (union_subset ((base_subset_complex (C := C 0)).trans
      (subset_iUnion C 0)) (iUnion₂_subset fun n c ↦
        (closedCell_subset_complex (C := C c.1) n c.2.1).trans (subset_iUnion C c.1)))
      (iUnion_subset fun k x hx ↦ ?_)
    rw [← RelCWComplex.union (C := C k)] at hx
    refine (union_subset_union_right D (iUnion₂_subset fun n i ↦ ?_)) hx
    refine subset_iUnion₂_of_subset n (towerFirstCell C i) ?_
    simp only [coe_map_towerFirstCell, closedCell, subset_rfl]

variable (hcell : ∀ k n (i : cell (C k) n), ∃ j : cell (C (k + 1)) n, ⇑(map n j) = ⇑(map n i))
  (hclosed : ∀ A ⊆ ⋃ k, C k, (∀ k, IsClosed (A ∩ C k)) → IsClosed A)

/-- The cells of the union of a tower are the new cells of its stages. -/
def towerUnionCellEquiv (n : ℕ) :
    @cell _ _ (⋃ k, C k) D (towerUnion C hcell hclosed) n ≃
      Σ k, {i : cell (C k) n // IsTowerNewCell C i} :=
  Equiv.refl _

/-- The characteristic map of a cell of the union of a tower is that of the new cell of a stage
it corresponds to. -/
theorem coe_map_towerUnion (n : ℕ) (c : @cell _ _ (⋃ k, C k) D (towerUnion C hcell hclosed) n) :
    ⇑(@map _ _ _ _ (towerUnion C hcell hclosed) n c) =
      ⇑(map n (towerUnionCellEquiv C hcell hclosed n c).2.1) :=
  (rfl)

/-- The cell of the union of a tower given by a cell of one of its stages: its first
occurrence. -/
def towerUnionCell {k n : ℕ} (i : cell (C k) n) :
    @cell _ _ (⋃ k, C k) D (towerUnion C hcell hclosed) n :=
  (towerUnionCellEquiv C hcell hclosed n).symm (towerFirstCell C i)

/-- The cell of the union given by a cell of a stage corresponds to its first occurrence. -/
@[simp]
theorem towerUnionCellEquiv_towerUnionCell {k n : ℕ} (i : cell (C k) n) :
    towerUnionCellEquiv C hcell hclosed n (towerUnionCell C hcell hclosed i) =
      towerFirstCell C i :=
  (towerUnionCellEquiv C hcell hclosed n).apply_symm_apply _

/-- The characteristic map of the cell of the union given by a cell of a stage is the
characteristic map of that cell. -/
@[simp]
theorem coe_map_towerUnionCell {k n : ℕ} (i : cell (C k) n) :
    ⇑(@map _ _ _ _ (towerUnion C hcell hclosed) n (towerUnionCell C hcell hclosed i)) =
      ⇑(map n i) := by
  rw [coe_map_towerUnion, towerUnionCellEquiv_towerUnionCell, coe_map_towerFirstCell]

/-- Two cells of stages of a tower give the same cell of the union exactly when they have the
same characteristic map. -/
@[simp]
theorem towerUnionCell_eq_iff {k l n : ℕ} {i : cell (C k) n} {j : cell (C l) n} :
    towerUnionCell C hcell hclosed i = towerUnionCell C hcell hclosed j ↔
      ⇑(map n i) = ⇑(map n j) := by
  rw [← towerFirstCell_eq_iff, towerUnionCell, towerUnionCell, Equiv.apply_eq_iff_eq]

/-- Every cell of the union of a tower is given by the new cell of a stage it corresponds to. -/
@[simp]
theorem towerUnionCell_towerUnionCellEquiv (n : ℕ)
    (c : @cell _ _ (⋃ k, C k) D (towerUnion C hcell hclosed) n) :
    towerUnionCell C hcell hclosed (towerUnionCellEquiv C hcell hclosed n c).2.1 = c := by
  rw [towerUnionCell,
    towerFirstCell_of_isTowerNewCell (towerUnionCellEquiv C hcell hclosed n c).2.2,
    Equiv.symm_apply_apply]

/-- Every cell of the union of a tower is given by a cell of one of its stages. -/
theorem exists_towerUnionCell_eq (n : ℕ)
    (c : @cell _ _ (⋃ k, C k) D (towerUnion C hcell hclosed) n) :
    ∃ k, ∃ i : cell (C k) n, towerUnionCell C hcell hclosed i = c :=
  ⟨_, _, towerUnionCell_towerUnionCellEquiv C hcell hclosed n c⟩

/-- The open cell of the union given by a cell of a stage is the open cell of the stage. -/
@[simp]
theorem openCell_towerUnionCell {k n : ℕ} (i : cell (C k) n) :
    @openCell _ _ _ _ (towerUnion C hcell hclosed) n (towerUnionCell C hcell hclosed i) =
      openCell n i := by
  simp only [openCell, coe_map_towerUnionCell]

/-- The closed cell of the union given by a cell of a stage is the closed cell of the stage. -/
@[simp]
theorem closedCell_towerUnionCell {k n : ℕ} (i : cell (C k) n) :
    @closedCell _ _ _ _ (towerUnion C hcell hclosed) n (towerUnionCell C hcell hclosed i) =
      closedCell n i := by
  simp only [closedCell, coe_map_towerUnionCell]

/-- The boundary of the cell of the union given by a cell of a stage is the boundary of the cell
of the stage. -/
@[simp]
theorem cellFrontier_towerUnionCell {k n : ℕ} (i : cell (C k) n) :
    @cellFrontier _ _ _ _ (towerUnion C hcell hclosed) n (towerUnionCell C hcell hclosed i) =
      cellFrontier n i := by
  simp only [cellFrontier, coe_map_towerUnionCell]

/-- A closed cell of the union of a tower lies in the stage at which the cell first occurs. -/
theorem closedCell_towerUnion_subset (n : ℕ)
    (c : @cell _ _ (⋃ k, C k) D (towerUnion C hcell hclosed) n) :
    @closedCell _ _ _ _ (towerUnion C hcell hclosed) n c ⊆
      C (towerUnionCellEquiv C hcell hclosed n c).1 := by
  rw [← towerUnionCell_towerUnionCellEquiv C hcell hclosed n c, closedCell_towerUnionCell,
    towerUnionCell_towerUnionCellEquiv]
  exact closedCell_subset_complex _ _

/-- A stage of a tower, as a subcomplex of the union of the tower: its cells are the cells of the
union given by the cells of the stage. -/
def towerUnionSubcomplex [T2Space X] (k : ℕ) :
    @Subcomplex _ _ (⋃ k, C k) D (towerUnion C hcell hclosed) :=
  @Subcomplex.mk'' _ _ _ (⋃ k, C k) D (towerUnion C hcell hclosed) (C k)
    (fun n ↦ range (towerUnionCell C hcell hclosed (k := k) (n := n))) _ <| by
    refine Eq.trans ?_ (union_iUnion_openCell_eq_complex (C := C k))
    congr 1
    refine iUnion_congr fun n ↦ Subset.antisymm ?_ ?_
    · refine iUnion_subset fun ⟨c, i, hi⟩ ↦ ?_
      subst hi
      rw [openCell_towerUnionCell]
      exact subset_iUnion (openCell (C := C k) n) i
    · exact iUnion_subset fun i ↦ (openCell_towerUnionCell C hcell hclosed i).symm.subset.trans
        (subset_iUnion_of_subset ⟨_, i, rfl⟩ subset_rfl)

/-- The subcomplex given by a stage of a tower is that stage. -/
@[simp]
theorem coe_towerUnionSubcomplex [T2Space X] (k : ℕ) :
    (towerUnionSubcomplex C hcell hclosed k : Set X) = C k :=
  (rfl)

/-- The cells of the subcomplex given by a stage of a tower are the cells given by the cells of
that stage. -/
@[simp]
theorem towerUnionSubcomplex_I [T2Space X] (k n : ℕ) :
    @Subcomplex.I _ _ _ _ (towerUnion C hcell hclosed) (towerUnionSubcomplex C hcell hclosed k) n =
      range (towerUnionCell C hcell hclosed (k := k)) :=
  (rfl)

end Topology.RelCWComplex

namespace Topology.CWComplex

open RelCWComplex

variable {X : Type*} [TopologicalSpace X] (C : ℕ → Set X) [∀ k, CWComplex (C k)]

/-- The **union of a tower** of CW complexes `C k`, in which every cell of a stage is a cell of the
next stage, is a CW complex, provided that a subset of the union is closed whenever it meets every
stage in a closed set. This is `Topology.RelCWComplex.towerUnion` with empty base. -/
@[instance_reducible]
def towerUnion
    (hcell : ∀ k n (i : cell (C k) n), ∃ j : cell (C (k + 1)) n, ⇑(map n j) = ⇑(map n i))
    (hclosed : ∀ A ⊆ ⋃ k, C k, (∀ k, IsClosed (A ∩ C k)) → IsClosed A) :
    CWComplex (⋃ k, C k) :=
  @RelCWComplex.toCWComplex _ _ _ (RelCWComplex.towerUnion C hcell hclosed)

/-- The relative CW structure underlying the absolute union of a tower is the relative union. -/
theorem towerUnion_instRelCWComplex
    (hcell : ∀ k n (i : cell (C k) n), ∃ j : cell (C (k + 1)) n, ⇑(map n j) = ⇑(map n i))
    (hclosed : ∀ A ⊆ ⋃ k, C k, (∀ k, IsClosed (A ∩ C k)) → IsClosed A) :
    @instRelCWComplex _ _ _ (towerUnion C hcell hclosed) =
      RelCWComplex.towerUnion C hcell hclosed :=
  (rfl)

end Topology.CWComplex
