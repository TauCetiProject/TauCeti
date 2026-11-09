/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# The union of a tower of CW complexes

Let `W 0, W 1, …` be subsets of a space `X`, each a CW complex relative to a common base `D`, and
suppose each stage is a subcomplex of the next with the same cells: a map
`ι k n : cell (W k) n → cell (W (k + 1)) n` labels the `n`-cells of `W k` among those of
`W (k + 1)`, and preserves characteristic maps. Suppose that a subset of the union `⋃ k, W k` is
closed in `X` as soon as its intersection with every stage is closed in `X`. Closedness is meant in
`X` throughout, not in the union: when the stages are closed in `X`, this asks that the union carry
the final topology of its stages and be closed in `X`. Then the union is a CW complex relative to
`D` (`TauCeti.relCWComplexTowerUnion`). With `D = ∅`, `Topology.RelCWComplex.toCWComplex` turns it
into an absolute CW complex.

An `n`-cell of the union is born at a definite stage: it is an `n`-cell of `W 0`, or an `n`-cell of
`W (k + 1)` outside the image of `ι k n` (`TauCeti.towerNewCells`). So the `n`-cells of the union
are the disjoint union over `k` of the new `n`-cells of `W k`, with their characteristic maps in
`W k` (`TauCeti.relCWComplexTowerUnionCellEquiv`). The cells of the stages may have arbitrary
dimensions in any order of the stages: a later stage may add cells of lower dimension than an
earlier one. When `X` is Hausdorff, every stage `W k` is a subcomplex of the union, consisting of
the cells born at stages up to `k` (`TauCeti.towerUnionSubcomplex`).

The proof checks the axioms of a relative CW complex directly. A cell of `W j` reappears in every
later stage with the same characteristic map, so the open cells of two new cells, born at stages
`j ≤ k`, can be compared inside `W k`, where the earlier one is not new. Closure-finiteness of a
cell born at stage `k` is closure-finiteness in `W k`, since every cell of `W k` has the same
closed cell as the cell of the union at which it was born. The weak topology of the union follows
from that of each stage together with the closedness hypothesis on the union.

The hypothesis on the topology holds, for instance, when `X` is the colimit of a sequence of
closed embeddings and `W k` is the image of the `k`-th space: the union of the stages is all of
`X`, and the colimit topology is the final topology of the stages. So the colimit of a sequence of
cell attachments of arbitrary dimensions, each stage a CW complex having the previous one as a
subcomplex, is a CW complex once every stage is identified with its image in the colimit.

## Main definitions

* `TauCeti.towerNewCells`: the `n`-cells of `W k` not coming from `W (k - 1)`.
* `TauCeti.relCWComplexTowerUnion`: the CW structure on `⋃ k, W k` relative to `D`.
* `TauCeti.relCWComplexTowerUnionCellEquiv`: its `n`-cells are the new `n`-cells of the stages.
* `TauCeti.towerUnionSubcomplex`: the stage `W k` as a subcomplex of the union.

## Main results

* `TauCeti.monotone_of_map_eq`: the stages increase.
* `TauCeti.exists_mem_towerNewCells_map_eq`: every cell of `W k` is born at a stage `j ≤ k`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, where a CW complex is built by attaching cells inductively and given the weak
  topology of the union of its stages, and the Appendix for the topology of cell complexes.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {D : Set X} {W : ℕ → Set X}
  [∀ k, RelCWComplex (W k) D]

section NewCells

variable (ι : ∀ k n, cell (W k) n → cell (W (k + 1)) n)

/-- The `n`-cells of the stage `W k` that are new at that stage: every `n`-cell of `W 0`, and the
`n`-cells of `W (k + 1)` outside the image of `ι k n`. -/
def towerNewCells (k n : ℕ) : Set (cell (W k) n) :=
  match k with
  | 0 => univ
  | k + 1 => (range (ι k n))ᶜ

@[simp]
lemma mem_towerNewCells_zero {n : ℕ} (i : cell (W 0) n) : i ∈ towerNewCells ι 0 n :=
  mem_univ i

@[simp]
lemma mem_towerNewCells_succ {k n : ℕ} {i : cell (W (k + 1)) n} :
    i ∈ towerNewCells ι (k + 1) n ↔ i ∉ range (ι k n) :=
  Iff.rfl

end NewCells

variable {ι : ∀ k n, cell (W k) n → cell (W (k + 1)) n}

/-- A cell of `W j` reappears in every later stage `W k` with the same characteristic map, and it
is not new there when `j < k`. -/
private lemma exists_map_eq_of_le (hι : ∀ k n i, map n (ι k n i) = map n i) {j k n : ℕ}
    (hjk : j ≤ k) (i : cell (W j) n) :
    ∃ i' : cell (W k) n, map n i' = map n i ∧ (j < k → i' ∉ towerNewCells ι k n) := by
  induction k, hjk using Nat.le_induction with
  | base => exact ⟨i, rfl, fun h ↦ (lt_irrefl j h).elim⟩
  | succ k _ ih =>
    obtain ⟨i', hi', -⟩ := ih
    exact ⟨ι k n i', (hι k n i').trans hi', fun _ ↦ by simp⟩

/-- The stages of the tower increase. -/
theorem monotone_of_map_eq (hι : ∀ k n i, map n (ι k n i) = map n i) : Monotone W := by
  refine monotone_nat_of_le_succ fun k x hx ↦ ?_
  rw [← RelCWComplex.union (C := W k), mem_union, mem_iUnion₂] at hx
  rcases hx with hx | ⟨n, i, hx⟩
  · exact base_subset_complex hx
  · rw [closedCell, ← hι k n i] at hx
    exact closedCell_subset_complex n (ι k n i) hx

/-- Every cell of the stage `W k` is born at a stage `j ≤ k`: some new cell of `W j` has the same
characteristic map. -/
theorem exists_mem_towerNewCells_map_eq (hι : ∀ k n i, map n (ι k n i) = map n i) {k n : ℕ}
    (i : cell (W k) n) : ∃ j ≤ k, ∃ i' ∈ towerNewCells ι j n, map n i' = map n i := by
  induction k with
  | zero => exact ⟨0, le_rfl, i, mem_towerNewCells_zero ι i, rfl⟩
  | succ k ih =>
    by_cases hi : i ∈ range (ι k n)
    · obtain ⟨i₀, rfl⟩ := hi
      obtain ⟨j, hjk, i', hi', hmap⟩ := ih i₀
      exact ⟨j, hjk.trans k.le_succ, i', hi', hmap.trans (hι k n i₀).symm⟩
    · exact ⟨k + 1, le_rfl, i, (mem_towerNewCells_succ ι).2 hi, rfl⟩

/-- Open cells of two new cells born at stages `j ≤ k` are disjoint unless the cells coincide. -/
private lemma disjoint_image_ball_of_le (hι : ∀ k n i, map n (ι k n i) = map n i) {j k n m : ℕ}
    (hjk : j ≤ k) (i : towerNewCells ι j n) (i' : towerNewCells ι k m)
    (hne : (⟨n, j, i⟩ : Σ n, Σ k, towerNewCells ι k n) ≠ ⟨m, k, i'⟩) :
    Disjoint (map n (i : cell (W j) n) '' ball 0 1) (map m (i' : cell (W k) m) '' ball 0 1) := by
  rcases hjk.lt_or_eq with hjk | rfl
  · obtain ⟨i'', hmap, hnew⟩ := exists_map_eq_of_le hι hjk.le (i : cell (W j) n)
    rw [← hmap]
    refine disjoint_openCell_of_ne fun h ↦ ?_
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
    exact hnew hjk (eq_of_heq h ▸ i'.2)
  · refine disjoint_openCell_of_ne fun h ↦ hne ?_
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
    rw [Subtype.ext (eq_of_heq h)]

variable (ι) in
/-- **The union of a tower of CW complexes.** Let each `W k` be a CW complex relative to `D`, and
let `ι k n` send the `n`-cells of `W k` to `n`-cells of `W (k + 1)` with the same characteristic
maps. If a subset of `⋃ k, W k` is closed in `X` as soon as its intersection with every `W k` is
closed in `X`, then `⋃ k, W k` is a CW complex relative to `D`. When the stages are closed in `X`,
this hypothesis asks that the union carry the final topology of its stages and be closed in `X`.
Its `n`-cells are the new `n`-cells of the stages (`TauCeti.towerNewCells`), with their
characteristic maps in their stage.

The structure is not an instance: it depends on the labels `ι`. -/
@[instance_reducible]
def relCWComplexTowerUnion (hι : ∀ k n i, map n (ι k n i) = map n i)
    (hW : ∀ A ⊆ ⋃ k, W k, (∀ k, IsClosed (A ∩ W k)) → IsClosed A) :
    RelCWComplex (⋃ k, W k) D where
  cell n := Σ k, towerNewCells ι k n
  map n i := map n (i.2 : cell (W i.1) n)
  source_eq n i := source_eq n _
  continuousOn n i := RelCWComplex.continuousOn n _
  continuousOn_symm n i := continuousOn_symm n _
  pairwiseDisjoint' := by
    rintro ⟨n, j, i⟩ - ⟨m, k, i'⟩ - hne
    rcases le_total j k with hjk | hkj
    · exact disjoint_image_ball_of_le hι hjk i i' hne
    · exact (disjoint_image_ball_of_le hι hkj i' i hne.symm).symm
  disjointBase' n i := disjointBase n _
  mapsTo n i := by
    classical
    obtain ⟨I, hI⟩ := RelCWComplex.mapsTo n (i.2 : cell (W i.1) n)
    choose b hbk c hc hb using fun m (j : cell (W i.1) m) ↦ exists_mem_towerNewCells_map_eq hι j
    refine ⟨fun m ↦ (I m).image fun j ↦ ⟨b m j, c m j, hc m j⟩,
      hI.mono_right (union_subset_union_right _ ?_)⟩
    refine iUnion₂_mono fun m _ ↦ iUnion₂_subset fun j hj ↦ ?_
    refine subset_iUnion₂_of_subset _ (Finset.mem_image_of_mem _ hj) ?_
    rw [hb m j]
  closed' A hAW hA := by
    refine hW A hAW fun k ↦ RelCWComplex.closed' (A ∩ W k) inter_subset_right ⟨fun n j ↦ ?_, ?_⟩
    · obtain ⟨l, -, j', hj', hmap⟩ := exists_mem_towerNewCells_map_eq hι j
      have hj : map n j '' closedBall 0 1 ⊆ W k := closedCell_subset_complex n j
      rw [inter_assoc, inter_eq_right.2 hj, ← hmap]
      exact hA.1 n ⟨l, j', hj'⟩
    · rw [inter_assoc, inter_eq_right.2 (base_subset_complex (C := W k))]
      exact hA.2
  isClosedBase := isClosedBase (W 0)
  union' := by
    refine (union_subset (base_subset_complex.trans (subset_iUnion W 0))
      (iUnion₂_subset fun n (i : Σ k, towerNewCells ι k n) ↦
        (closedCell_subset_complex n (i.2 : cell (W i.1) n)).trans (subset_iUnion W i.1))).antisymm
      (iUnion_subset fun k x hx ↦ ?_)
    rw [← RelCWComplex.union (C := W k), mem_union, mem_iUnion₂] at hx
    rcases hx with hx | ⟨n, j, hx⟩
    · exact Or.inl hx
    obtain ⟨l, -, j', hj', hmap⟩ := exists_mem_towerNewCells_map_eq hι j
    rw [closedCell, ← hmap] at hx
    exact Or.inr (mem_iUnion₂_of_mem (⟨l, j', hj'⟩ : Σ k, towerNewCells ι k n) hx)

variable (hι : ∀ k n i, map n (ι k n i) = map n i)
  (hW : ∀ A ⊆ ⋃ k, W k, (∀ k, IsClosed (A ∩ W k)) → IsClosed A)

/-- The `n`-cells of the union of a tower of CW complexes are the new `n`-cells of its stages. -/
def relCWComplexTowerUnionCellEquiv (n : ℕ) :
    @cell X _ (⋃ k, W k) D (relCWComplexTowerUnion ι hι hW) n ≃ Σ k, towerNewCells ι k n :=
  Equiv.refl _

/-- The characteristic map of a new cell of `W k`, as a cell of the union, is its characteristic
map in `W k`. -/
@[simp]
lemma map_relCWComplexTowerUnion (n k : ℕ) (i : towerNewCells ι k n) :
    @map X _ (⋃ k, W k) D (relCWComplexTowerUnion ι hι hW) n
      ((relCWComplexTowerUnionCellEquiv hι hW n).symm ⟨k, i⟩) = map n (i : cell (W k) n) :=
  (rfl)

/-- The open cell of a new cell of `W k`, as a cell of the union, is its open cell in `W k`. -/
@[simp]
lemma openCell_relCWComplexTowerUnion (n k : ℕ) (i : towerNewCells ι k n) :
    @openCell X _ (⋃ k, W k) D (relCWComplexTowerUnion ι hι hW) n
      ((relCWComplexTowerUnionCellEquiv hι hW n).symm ⟨k, i⟩) = openCell n (i : cell (W k) n) :=
  (rfl)

/-- The closed cell of a new cell of `W k`, as a cell of the union, is its closed cell in `W k`. -/
@[simp]
lemma closedCell_relCWComplexTowerUnion (n k : ℕ) (i : towerNewCells ι k n) :
    @closedCell X _ (⋃ k, W k) D (relCWComplexTowerUnion ι hι hW) n
      ((relCWComplexTowerUnionCellEquiv hι hW n).symm ⟨k, i⟩) = closedCell n (i : cell (W k) n) :=
  (rfl)

/-- The boundary of a new cell of `W k`, as a cell of the union, is its boundary in `W k`. -/
@[simp]
lemma cellFrontier_relCWComplexTowerUnion (n k : ℕ) (i : towerNewCells ι k n) :
    @cellFrontier X _ (⋃ k, W k) D (relCWComplexTowerUnion ι hι hW) n
      ((relCWComplexTowerUnionCellEquiv hι hW n).symm ⟨k, i⟩) =
        cellFrontier n (i : cell (W k) n) :=
  (rfl)

variable [T2Space X]

/-- The stage `W k` of a tower of CW complexes is a subcomplex of the union, made of the cells born
at the stages `j ≤ k`. -/
def towerUnionSubcomplex (k : ℕ) :
    @Subcomplex X _ (⋃ k, W k) D (relCWComplexTowerUnion ι hι hW) :=
  letI := relCWComplexTowerUnion ι hι hW
  { carrier := W k
    I n := (relCWComplexTowerUnionCellEquiv hι hW n).symm '' {i | i.1 ≤ k}
    closed' := RelCWComplex.isClosed
    union' := by
      refine (union_subset base_subset_complex (iUnion₂_subset ?_)).antisymm ?_
      · rintro n ⟨-, ⟨j, i⟩, hjk, rfl⟩
        exact (openCell_subset_complex n (i : cell (W j) n)).trans (monotone_of_map_eq hι hjk)
      · rw [← RelCWComplex.union_iUnion_openCell_eq_complex (C := W k)]
        refine union_subset_union_right _ (iUnion₂_subset fun n i ↦ ?_)
        obtain ⟨j, hjk, i', hi', hmap⟩ := exists_mem_towerNewCells_map_eq hι i
        refine subset_iUnion₂_of_subset n ⟨_, ⟨⟨j, i', hi'⟩, hjk, rfl⟩⟩ ?_
        rw [openCell_relCWComplexTowerUnion, openCell, openCell, hmap] }

/-- The stage `W k`, as a subcomplex of the union, is `W k`. -/
@[simp]
lemma coe_towerUnionSubcomplex (k : ℕ) :
    letI := relCWComplexTowerUnion ι hι hW
    (towerUnionSubcomplex hι hW k : Set X) = W k :=
  (rfl)

/-- The `n`-cells of the stage `W k`, as a subcomplex of the union, are the new `n`-cells of the
stages `j ≤ k`. -/
@[simp]
lemma towerUnionSubcomplex_I (k n : ℕ) :
    letI := relCWComplexTowerUnion ι hι hW
    (towerUnionSubcomplex hι hW k).I n =
      (relCWComplexTowerUnionCellEquiv hι hW n).symm '' {i | i.1 ≤ k} :=
  (rfl)

end TauCeti
