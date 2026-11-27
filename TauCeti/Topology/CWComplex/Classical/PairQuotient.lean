/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopPair.Quotient
public import TauCeti.Topology.CWComplex.Classical.FiniteCWType
public import TauCeti.Topology.CWComplex.Classical.Pushout
public import TauCeti.Topology.CWComplex.Classical.Subcomplex

/-!
# The CW structure on the quotient of a CW pair

Let `X` be a Hausdorff space which is a CW complex relative to a subset `B`. The pointed quotient
`X/B` (`TopPair.ordinaryPairQuotient`), which collapses `B` together with an added point to the
basepoint, is a CW complex (`TauCeti.ordinaryPairQuotientCWComplex`), and it is Hausdorff
(`TauCeti.t2Space_ordinaryPairQuotient`). Its cells are a single `0`-cell at the basepoint together
with the cells of `X` relative to `B` (`TauCeti.ordinaryPairQuotientCWComplexCellEquiv`), whose
characteristic maps are those of `X` followed by the collapse map `X → X/B`
(`TauCeti.ordinaryPairQuotientCWComplex_map_inr`). The basepoint is a `0`-cell
(`TauCeti.basepoint_mem_skeletonLT_one_ordinaryPairQuotientCWComplex`).

The main case is a CW pair `(X, A)`: a CW complex `X` and a subcomplex `A`, relative to which `X`
is a CW complex with the cells of `X` not in `A`
(`Topology.RelCWComplex.Subcomplex.relCWComplex`). Then `X/A` is a Hausdorff CW complex whose
basepoint is a `0`-cell (instances), with one cell for each cell of `X` not in `A` besides the
basepoint (`Topology.RelCWComplex.Subcomplex.ordinaryPairQuotientCellEquiv`). For `A` empty, `X/A`
is `X` with a disjoint basepoint. Since the basepoint is a `0`-cell, the CW structures on reduced
suspensions and wedge sums of complexes based at `0`-cells apply to `X/A`. This is the third term
of the cofiber sequence `A → X → X/A` of a CW pair, on which reduced cohomology theories of CW
complexes are required to be exact.

The structure is that of a pushout: `X/B` is the pushout of the inclusion of `B` into `X` along
the map to a point (`TopPair.isPushout_ordinaryPairQuotient`). Every map to a point is cellular, so
the pushout is a CW complex whose cells are those of the point and those of `X` relative to `B`
(`CategoryTheory.IsPushout.cwComplexOfMapsToSkeletonLT`).

## Main definitions

* `TauCeti.ordinaryPairQuotientCWComplex`: the CW structure on `X/B`.
* `TauCeti.ordinaryPairQuotientCWComplexCellEquiv`: its `n`-cells are those of the point and the
  `n`-cells of `X` relative to `B`.
* `Topology.RelCWComplex.Subcomplex.ordinaryPairQuotientCellEquiv`: for a subcomplex `A` of a CW
  complex `X`, the `n`-cells of `X/A` are those of the point and the `n`-cells of `X` not in `A`.

## Main results

* `TauCeti.ordinaryPairQuotientCWComplex_map_inl`, `TauCeti.ordinaryPairQuotientCWComplex_map_inr`:
  the characteristic maps of `X/B`.
* `TauCeti.ordinaryPairQuotientCWComplex_openCell_inr`,
  `TauCeti.ordinaryPairQuotientCWComplex_closedCell_inr`: the open and closed cells of `X/B` over a
  cell of `X` are the images of its open and closed cells under the collapse map.
* `TauCeti.basepoint_mem_skeletonLT_one_ordinaryPairQuotientCWComplex`: the basepoint of `X/B` is a
  `0`-cell.
* `TauCeti.finite_ordinaryPairQuotientCWComplex`: `X/B` is a finite CW complex when `X` is finite
  relative to `B`.
* `Topology.RelCWComplex.Subcomplex.map_ordinaryPairQuotientCellEquiv_symm_inl`,
  `Topology.RelCWComplex.Subcomplex.map_ordinaryPairQuotientCellEquiv_symm_inr`,
  `Topology.RelCWComplex.Subcomplex.openCell_ordinaryPairQuotientCellEquiv_symm_inr`,
  `Topology.RelCWComplex.Subcomplex.closedCell_ordinaryPairQuotientCellEquiv_symm_inr`: the
  characteristic maps and cells of `X/A` for a subcomplex `A`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0, Operations on
  Spaces: the quotient `X/A` of a CW complex by a subcomplex is a CW complex, with the cells of
  `X - A` and one new `0`-cell, the image of `A`.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

section Relative

variable {X : Type u} [TopologicalSpace X] [T2Space X] {B : Set X}
  [hB : RelCWComplex (univ : Set X) B]

omit [T2Space X] in
/-- The pointed quotient `X/B` is the pushout of the inclusion of the base `B` into the complex
`univ` along the map to a point, with the collapse map and the basepoint as the maps into it. -/
private theorem isPushout_ordinaryPairQuotient_relCWBaseInclusion :
    IsPushout (relCWBaseInclusion (univ : Set X))
      (TopCat.ofHom (ContinuousMap.const B PUnit.unit))
      (TopCat.ofHom ((TopPair.ofSubset (X := TopCat.of X) B).ordinaryPairQuotientπ.hom.comp
        ⟨Subtype.val, continuous_subtypeVal⟩))
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1}
        (TopPair.ofSubset (X := TopCat.of X) B).ordinaryPairQuotientBasepoint)) :=
  (TopPair.ofSubset (X := TopCat.of X) B).isPushout_ordinaryPairQuotient.of_iso' (Iso.refl _)
    (TopCat.isoOfHomeo (Homeomorph.Set.univ X)) (Iso.refl _) (Iso.refl _)
    -- Both inclusions of `B` send a point to itself in `X`, the maps to `PUnit` are constant, and
    -- the maps out of `univ` agree on each point by definition.
    (by ext; rfl) (by ext) (by ext; rfl) (by ext; rfl)

/-- **The quotient of a CW pair is a CW complex.** If `X` is a CW complex relative to `B`, the
pointed quotient `X/B` is a CW complex, whose cells are a single `0`-cell at the basepoint together
with the cells of `X` relative to `B` (`TauCeti.ordinaryPairQuotientCWComplexCellEquiv`). -/
@[instance_reducible]
def ordinaryPairQuotientCWComplex :
    CWComplex (univ : Set (TopPair.ofSubset (X := TopCat.of X) B).ordinaryPairQuotient) :=
  isPushout_ordinaryPairQuotient_relCWBaseInclusion.cwComplexOfMapsToSkeletonLT
    (mem_skeletonLT_univ_of_mem_cellFrontier _)

/-- The quotient of a Hausdorff space by the base of a relative CW structure is Hausdorff. -/
theorem t2Space_ordinaryPairQuotient :
    T2Space (TopPair.ofSubset (X := TopCat.of X) B).ordinaryPairQuotient :=
  isPushout_ordinaryPairQuotient_relCWBaseInclusion.t2Space

variable (B) in
/-- **The cells of the quotient of a CW pair.** The `n`-cells of `X/B` are the `n`-cells of the
point, a single `0`-cell for the basepoint, together with the `n`-cells of `X` relative to `B`. -/
def ordinaryPairQuotientCWComplexCellEquiv (n : ℕ) :
    letI := ordinaryPairQuotientCWComplex (B := B)
    cell (univ : Set (TopPair.ofSubset (X := TopCat.of X) B).ordinaryPairQuotient) n ≃
      cell (univ : Set PUnit.{u + 1}) n ⊕ cell (univ : Set X) n :=
  isPushout_ordinaryPairQuotient_relCWBaseInclusion.cwComplexOfMapsToSkeletonLTCellEquiv
    (mem_skeletonLT_univ_of_mem_cellFrontier _) n

/-- The cell of the point in `X/B` is the basepoint. -/
@[simp]
theorem ordinaryPairQuotientCWComplex_map_inl {n : ℕ} (c : cell (univ : Set PUnit.{u + 1}) n)
    (x : Fin n → ℝ) :
    letI := ordinaryPairQuotientCWComplex (B := B)
    map n ((ordinaryPairQuotientCWComplexCellEquiv B n).symm (.inl c)) x =
      (TopPair.ofSubset (X := TopCat.of X) B).ordinaryPairQuotientBasepoint :=
  isPushout_ordinaryPairQuotient_relCWBaseInclusion.cwComplexOfMapsToSkeletonLT_map_inl
    (mem_skeletonLT_univ_of_mem_cellFrontier _) n c x

/-- The characteristic map of the cell of `X/B` over a cell of `X` relative to `B` is its
characteristic map in `X` followed by the collapse map `X → X/B`. -/
@[simp]
theorem ordinaryPairQuotientCWComplex_map_inr {n : ℕ} (c : cell (univ : Set X) n)
    (x : closedBall (0 : Fin n → ℝ) 1) :
    letI := ordinaryPairQuotientCWComplex (B := B)
    map n ((ordinaryPairQuotientCWComplexCellEquiv B n).symm (.inr c)) x =
      (TopPair.ofSubset (X := TopCat.of X) B).ordinaryPairQuotientπ (map n c x) :=
  isPushout_ordinaryPairQuotient_relCWBaseInclusion.cwComplexOfMapsToSkeletonLT_map_inr
    (mem_skeletonLT_univ_of_mem_cellFrontier _) n c x

/-- The image of a subset of the closed unit ball under the characteristic map of the cell of
`X/B` over a cell of `X` relative to `B` is the image under the collapse map of its image under the
characteristic map of that cell. -/
private theorem image_map_inr {n : ℕ} (c : cell (univ : Set X) n) {s : Set (Fin n → ℝ)}
    (hs : s ⊆ closedBall 0 1) :
    letI := ordinaryPairQuotientCWComplex (B := B)
    map n ((ordinaryPairQuotientCWComplexCellEquiv B n).symm (.inr c)) '' s =
      (TopPair.ofSubset (X := TopCat.of X) B).ordinaryPairQuotientπ '' (map n c '' s : Set X) := by
  let := ordinaryPairQuotientCWComplex (B := B)
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, mem_image_of_mem _ hy, (ordinaryPairQuotientCWComplex_map_inr c ⟨y, hs hy⟩).symm⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, ordinaryPairQuotientCWComplex_map_inr c ⟨y, hs hy⟩⟩

/-- The open cell of `X/B` over a cell of `X` relative to `B` is the image of its open cell under
the collapse map. -/
@[simp]
theorem ordinaryPairQuotientCWComplex_openCell_inr {n : ℕ} (c : cell (univ : Set X) n) :
    letI := ordinaryPairQuotientCWComplex (B := B)
    openCell n ((ordinaryPairQuotientCWComplexCellEquiv B n).symm (.inr c)) =
      (TopPair.ofSubset (X := TopCat.of X) B).ordinaryPairQuotientπ '' (openCell n c : Set X) :=
  image_map_inr c ball_subset_closedBall

/-- The closed cell of `X/B` over a cell of `X` relative to `B` is the image of its closed cell
under the collapse map. -/
@[simp]
theorem ordinaryPairQuotientCWComplex_closedCell_inr {n : ℕ} (c : cell (univ : Set X) n) :
    letI := ordinaryPairQuotientCWComplex (B := B)
    closedCell n ((ordinaryPairQuotientCWComplexCellEquiv B n).symm (.inr c)) =
      (TopPair.ofSubset (X := TopCat.of X) B).ordinaryPairQuotientπ ''
        (closedCell n c : Set X) :=
  image_map_inr c subset_rfl

/-- **The basepoint of the quotient of a CW pair is a `0`-cell.** -/
theorem basepoint_mem_skeletonLT_one_ordinaryPairQuotientCWComplex :
    letI := ordinaryPairQuotientCWComplex (B := B)
    haveI := t2Space_ordinaryPairQuotient (B := B)
    (TopPair.ofSubset (X := TopCat.of X) B).ordinaryPairQuotientBasepoint ∈
      skeletonLT (univ : Set (TopPair.ofSubset (X := TopCat.of X) B).ordinaryPairQuotient) 1 := by
  let := ordinaryPairQuotientCWComplex (B := B)
  have := t2Space_ordinaryPairQuotient (B := B)
  let p : cell (univ : Set PUnit.{u + 1}) 0 := ⟨PUnit.unit, mem_univ _⟩
  rw [← ordinaryPairQuotientCWComplex_map_inl (B := B) p ![]]
  exact closedCell_subset_skeletonLT 0 ((ordinaryPairQuotientCWComplexCellEquiv B 0).symm (.inl p))
    (by simp [closedCell_zero_eq_singleton])

/-- The quotient `X/B` is a finite CW complex when `X` is finite relative to `B`. -/
theorem finite_ordinaryPairQuotientCWComplex [RelCWComplex.Finite (univ : Set X)] :
    letI := ordinaryPairQuotientCWComplex (B := B)
    RelCWComplex.Finite (univ : Set (TopPair.ofSubset (X := TopCat.of X) B).ordinaryPairQuotient) :=
  isPushout_ordinaryPairQuotient_relCWBaseInclusion.finite_cwComplexOfMapsToSkeletonLT
    (mem_skeletonLT_univ_of_mem_cellFrontier _)

end Relative

end TauCeti

namespace Topology.RelCWComplex.Subcomplex

open TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
  (A : CWComplex.Subcomplex (univ : Set X))

/-- **The quotient of a CW complex by a subcomplex is a CW complex**: the structure
`TauCeti.ordinaryPairQuotientCWComplex` of `X` relative to the subcomplex `A`. -/
instance instCWComplexOrdinaryPairQuotient :
    CWComplex (univ : Set (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotient) :=
  ordinaryPairQuotientCWComplex (hB := A.relCWComplex)

/-- The quotient of a Hausdorff CW complex by a subcomplex is Hausdorff. -/
instance instT2SpaceOrdinaryPairQuotient :
    T2Space (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotient :=
  t2Space_ordinaryPairQuotient (hB := A.relCWComplex)

/-- The basepoint of the quotient of a CW complex by a subcomplex is a `0`-cell. -/
instance instFactBasepointMemSkeletonLTOneOrdinaryPairQuotient :
    Fact ((TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotientBasepoint ∈
      skeletonLT (univ : Set (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotient)
        1) :=
  ⟨basepoint_mem_skeletonLT_one_ordinaryPairQuotientCWComplex (hB := A.relCWComplex)⟩

/-- The quotient of a finite CW complex by a subcomplex is a finite CW complex. -/
instance instFiniteOrdinaryPairQuotient [RelCWComplex.Finite (univ : Set X)] :
    RelCWComplex.Finite
      (univ : Set (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotient) :=
  haveI := finite_relCWComplex A
  finite_ordinaryPairQuotientCWComplex (hB := A.relCWComplex)

/-- **The cells of the quotient of a CW complex by a subcomplex.** The `n`-cells of `X/A` are the
`n`-cells of the point, a single `0`-cell for the basepoint, together with the `n`-cells of `X`
not in `A`. -/
def ordinaryPairQuotientCellEquiv (n : ℕ) :
    cell (univ : Set (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotient) n ≃
      cell (univ : Set PUnit.{u + 1}) n ⊕ ↥(A.I n)ᶜ :=
  (ordinaryPairQuotientCWComplexCellEquiv (hB := A.relCWComplex) (A : Set X) n).trans
    (Equiv.sumCongr (.refl _) (A.relCWComplexCellEquiv n))

/-- The cell of the point in `X/A` is the basepoint. -/
@[simp]
theorem map_ordinaryPairQuotientCellEquiv_symm_inl {n : ℕ} (c : cell (univ : Set PUnit.{u + 1}) n)
    (x : Fin n → ℝ) :
    map n ((A.ordinaryPairQuotientCellEquiv n).symm (.inl c)) x =
      (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotientBasepoint :=
  ordinaryPairQuotientCWComplex_map_inl (hB := A.relCWComplex) c x

/-- The characteristic map of the cell of `X/A` over a cell of `X` not in `A` is its
characteristic map in `X` followed by the collapse map `X → X/A`. -/
@[simp]
theorem map_ordinaryPairQuotientCellEquiv_symm_inr {n : ℕ} (c : ↥(A.I n)ᶜ)
    (x : closedBall (0 : Fin n → ℝ) 1) :
    map n ((A.ordinaryPairQuotientCellEquiv n).symm (.inr c)) x =
      (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotientπ
        (map n (c : cell (univ : Set X) n) x) := by
  have h := ordinaryPairQuotientCWComplex_map_inr (hB := A.relCWComplex)
    ((A.relCWComplexCellEquiv n).symm c) x
  rw [map_relCWComplex, Equiv.apply_symm_apply] at h
  exact h

/-- The open cell of `X/A` over a cell of `X` not in `A` is the image of its open cell under the
collapse map. -/
@[simp]
theorem openCell_ordinaryPairQuotientCellEquiv_symm_inr {n : ℕ} (c : ↥(A.I n)ᶜ) :
    openCell n ((A.ordinaryPairQuotientCellEquiv n).symm (.inr c)) =
      (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotientπ ''
        (openCell n (c : cell (univ : Set X) n) : Set X) := by
  have h := ordinaryPairQuotientCWComplex_openCell_inr (hB := A.relCWComplex)
    ((A.relCWComplexCellEquiv n).symm c)
  rw [openCell_relCWComplex, Equiv.apply_symm_apply] at h
  exact h

/-- The closed cell of `X/A` over a cell of `X` not in `A` is the image of its closed cell under
the collapse map. -/
@[simp]
theorem closedCell_ordinaryPairQuotientCellEquiv_symm_inr {n : ℕ} (c : ↥(A.I n)ᶜ) :
    closedCell n ((A.ordinaryPairQuotientCellEquiv n).symm (.inr c)) =
      (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotientπ ''
        (closedCell n (c : cell (univ : Set X) n) : Set X) := by
  have h := ordinaryPairQuotientCWComplex_closedCell_inr (hB := A.relCWComplex)
    ((A.relCWComplexCellEquiv n).symm c)
  rw [closedCell_relCWComplex, Equiv.apply_symm_apply] at h
  exact h

end Topology.RelCWComplex.Subcomplex
