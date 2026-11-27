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
# The CW structure on the quotient of a CW complex by a subcomplex

Let `X` be a Hausdorff CW complex and `A` a subcomplex. The pointed quotient `X/A` of the pair
`(X, A)`, which collapses `A` together with a separately added point to a single basepoint
(`TopPair.ordinaryPairQuotient`), is again a CW complex
(`Topology.RelCWComplex.Subcomplex.cwComplexOrdinaryPairQuotient`, an instance), and it is
Hausdorff. Its cells are one new `0`-cell, at the basepoint, together with the cells of `X` that do
not lie in `A` (`Topology.RelCWComplex.Subcomplex.ordinaryPairQuotientCellEquiv`), and the
characteristic map of a cell of `X` is followed by the collapse map `X → X/A`. In particular the
basepoint of `X/A` is a `0`-cell
(`Topology.RelCWComplex.Subcomplex.ordinaryPairQuotientBasepoint_mem_skeletonLT_one`), so `X/A`
is a pointed CW complex based at a `0`-cell. When `A` is empty, `X/A` is `X` with a disjoint
basepoint `X₊`, and its cells are those of `X` together with the added point. When `X` is finite,
so is `X/A`.

This makes `A → X → X/A` a sequence of CW complexes for every CW pair `(X, A)`. Reduced
cohomology theories on pointed CW complexes are required to turn it into an exact sequence, and the
relative groups of a CW pair are compared with the reduced groups of `X/A`; both need `X/A` to be a
CW complex of the same kind as `X` and `A`.

The structure is obtained by gluing. The subcomplex `A` makes `X` a CW complex relative to `A`
(`Topology.RelCWComplex.Subcomplex.relCWComplex`), whose cells are the cells of `X` not in `A`.
The quotient `X/A` is the pushout of the inclusion `A → X` along the map from `A` to a point
(`TopPair.isPushout_ordinaryPairQuotient`). Every map to a point is cellular, so the pushout is a
CW complex whose cells are those of the point and those of `X` relative to `A`
(`CategoryTheory.IsPushout.cwComplexOfMapsToSkeletonLT`).

## Main definitions

* `Topology.RelCWComplex.Subcomplex.cwComplexOrdinaryPairQuotient`: the CW structure on `X/A`.
* `Topology.RelCWComplex.Subcomplex.ordinaryPairQuotientCellEquiv`: the `n`-cells of `X/A` are the
  `n`-cells of the point and the `n`-cells of `X` not in `A`.

## Main results

* `Topology.RelCWComplex.Subcomplex.t2Space_ordinaryPairQuotient`: `X/A` is Hausdorff.
* `Topology.RelCWComplex.Subcomplex.map_ordinaryPairQuotientCellEquiv_symm_inl`: the cell of the
  point is the basepoint.
* `Topology.RelCWComplex.Subcomplex.map_ordinaryPairQuotientCellEquiv_symm_inr`,
  `Topology.RelCWComplex.Subcomplex.openCell_ordinaryPairQuotientCellEquiv_symm_inr`,
  `Topology.RelCWComplex.Subcomplex.closedCell_ordinaryPairQuotientCellEquiv_symm_inr`: the
  characteristic map, open cell and closed cell of the cell over a cell of `X` not in `A` are those
  of that cell, followed by the collapse map.
* `Topology.RelCWComplex.Subcomplex.ordinaryPairQuotientBasepoint_mem_skeletonLT_one`: the
  basepoint is a `0`-cell.
* `Topology.RelCWComplex.Subcomplex.finite_cwComplexOrdinaryPairQuotient`: `X/A` is finite when
  `X` is.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0, Operations on
  Spaces: if `(X, A)` is a CW pair, the quotient `X/A` inherits a CW structure whose cells are the
  cells of `X - A` together with one new `0`-cell, the image of `A`.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology TauCeti

universe u

namespace Topology.RelCWComplex.Subcomplex

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
  (A : Subcomplex (univ : Set X))

/- The structure on `X` relative to `A` is introduced locally below with `letI`. Its base `A` is an
`outParam`, so while it is in scope, instance search for `RelCWComplex univ _` finds it before the
CW structure of `X`. Lemmas about the cells of `X` itself therefore receive that structure
explicitly, as `CWComplex.instRelCWComplex univ`. -/

/-- The quotient `X/A` is the pushout of the inclusion of `A` into `X`, read as the base of the
CW structure on `X` relative to `A`, along the map from `A` to a point. -/
private theorem isPushout_collapse :
    letI := A.relCWComplex
    IsPushout (relCWBaseInclusion (univ : Set X))
      (TopCat.ofHom (ContinuousMap.const (A : Set X) PUnit.unit))
      (TopCat.ofHom
        ((TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotientπ.hom.comp
          ⟨Subtype.val, continuous_subtypeVal⟩) : TopCat.of ↥(univ : Set X) ⟶
          (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotient)
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1}
        (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotientBasepoint)) :=
  letI := A.relCWComplex
  (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).isPushout_ordinaryPairQuotient.of_iso'
    (Iso.refl _) (TopCat.isoOfHomeo (Homeomorph.Set.univ X)) (Iso.refl _) (Iso.refl _)
    -- The two inclusions of `A` agree pointwise, both maps to `PUnit` are constant, and the maps
    -- into the quotient agree on representatives.
    (by ext; rfl) (by ext) (by ext; rfl) (by ext; rfl)

/-- **The quotient of a CW complex by a subcomplex is a CW complex.** For a subcomplex `A` of a
Hausdorff CW complex `X`, the pointed quotient `X/A` has one `0`-cell at the basepoint together
with the cells of `X` not in `A` (`Topology.RelCWComplex.Subcomplex.ordinaryPairQuotientCellEquiv`),
whose characteristic maps are those of `X` followed by the collapse map. -/
@[instance_reducible]
def cwComplexOrdinaryPairQuotient :
    CWComplex (univ : Set (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotient) :=
  letI := A.relCWComplex
  (isPushout_collapse A).cwComplexOfMapsToSkeletonLT (mem_skeletonLT_univ_of_mem_cellFrontier _)

attribute [instance] cwComplexOrdinaryPairQuotient

/-- The quotient of a Hausdorff CW complex by a subcomplex is Hausdorff. -/
instance t2Space_ordinaryPairQuotient :
    T2Space (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotient :=
  letI := A.relCWComplex
  (isPushout_collapse A).t2Space

/-- **The cells of the quotient by a subcomplex.** The `n`-cells of `X/A` are the `n`-cells of the
point, that is a single `0`-cell for the basepoint, together with the `n`-cells of `X` that do not
lie in `A`. -/
def ordinaryPairQuotientCellEquiv (n : ℕ) :
    cell (univ : Set (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotient) n ≃
      cell (univ : Set PUnit.{u + 1}) n ⊕ ↥(A.I n)ᶜ :=
  letI := A.relCWComplex
  ((isPushout_collapse A).cwComplexOfMapsToSkeletonLTCellEquiv
    (mem_skeletonLT_univ_of_mem_cellFrontier _) n).trans
      (Equiv.sumCongr (.refl _)
        (@relCWComplexCellEquiv X _ _ univ ∅ (CWComplex.instRelCWComplex univ) A n))

/-- **The new `0`-cell of the quotient is the basepoint.** The cell of `X/A` coming from the point
has the basepoint as its characteristic map. -/
@[simp]
theorem map_ordinaryPairQuotientCellEquiv_symm_inl {n : ℕ} (c : cell (univ : Set PUnit.{u + 1}) n)
    (x : Fin n → ℝ) :
    map n ((A.ordinaryPairQuotientCellEquiv n).symm (.inl c)) x =
      (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotientBasepoint :=
  letI := A.relCWComplex
  (isPushout_collapse A).cwComplexOfMapsToSkeletonLT_map_inl
    (mem_skeletonLT_univ_of_mem_cellFrontier _) n c x

/-- **The cells of `X` not in `A` are cells of the quotient.** The characteristic map of the cell
of `X/A` over an `n`-cell `c` of `X` not in `A` is the characteristic map of `c`, followed by the
collapse map `X → X/A`. -/
@[simp]
theorem map_ordinaryPairQuotientCellEquiv_symm_inr {n : ℕ} (c : ↥(A.I n)ᶜ)
    (x : closedBall (0 : Fin n → ℝ) 1) :
    map n ((A.ordinaryPairQuotientCellEquiv n).symm (.inr c)) x =
      (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotientπ
        (map n (c : cell (univ : Set X) n) x) := by
  let := A.relCWComplex
  have h := (isPushout_collapse A).cwComplexOfMapsToSkeletonLT_map_inr
    (mem_skeletonLT_univ_of_mem_cellFrontier _) n
      ((@relCWComplexCellEquiv X _ _ univ ∅ (CWComplex.instRelCWComplex univ) A n).symm c) x
  refine h.trans ?_
  -- The characteristic maps of `X` relative to `A` are those of `X`.
  simp only [TopCat.hom_ofHom, ContinuousMap.comp_apply, map_relCWComplex, Equiv.apply_symm_apply]
  -- What remains is the collapse map applied to the inclusion of `univ` into `X` at a point, which
  -- is that point; `ConcreteCategory.hom` of a morphism of `TopCat` is `TopCat.Hom.hom`.
  rfl

/-- The open cell of the quotient over an `n`-cell of `X` not in `A` is the image of its open cell
under the collapse map. -/
@[simp]
theorem openCell_ordinaryPairQuotientCellEquiv_symm_inr {n : ℕ} (c : ↥(A.I n)ᶜ) :
    openCell n ((A.ordinaryPairQuotientCellEquiv n).symm (.inr c)) =
      (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotientπ ''
        (openCell n (c : cell (univ : Set X) n) : Set X) := by
  rw [openCell, openCell]
  refine .trans ?_ (image_image _ _ _).symm
  exact image_congr fun y hy ↦
    A.map_ordinaryPairQuotientCellEquiv_symm_inr c ⟨y, ball_subset_closedBall hy⟩

/-- The closed cell of the quotient over an `n`-cell of `X` not in `A` is the image of its closed
cell under the collapse map. -/
@[simp]
theorem closedCell_ordinaryPairQuotientCellEquiv_symm_inr {n : ℕ} (c : ↥(A.I n)ᶜ) :
    closedCell n ((A.ordinaryPairQuotientCellEquiv n).symm (.inr c)) =
      (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotientπ ''
        (closedCell n (c : cell (univ : Set X) n) : Set X) := by
  rw [closedCell, closedCell]
  refine .trans ?_ (image_image _ _ _).symm
  exact image_congr fun y hy ↦ A.map_ordinaryPairQuotientCellEquiv_symm_inr c ⟨y, hy⟩

/-- **The basepoint of the quotient by a subcomplex is a `0`-cell.** -/
theorem ordinaryPairQuotientBasepoint_mem_skeletonLT_one :
    (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotientBasepoint ∈
      skeletonLT (univ : Set (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotient)
        1 := by
  let c := (A.ordinaryPairQuotientCellEquiv 0).symm (.inl ⟨PUnit.unit, mem_univ _⟩)
  rw [← A.map_ordinaryPairQuotientCellEquiv_symm_inl (n := 0) ⟨PUnit.unit, mem_univ _⟩ ![]]
  exact closedCell_subset_skeletonLT 0 c (by simp [c, closedCell_zero_eq_singleton])

instance : Fact ((TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotientBasepoint ∈
    skeletonLT (univ : Set (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotient)
      1) :=
  ⟨A.ordinaryPairQuotientBasepoint_mem_skeletonLT_one⟩

/-- The quotient of a finite CW complex by a subcomplex is a finite CW complex. -/
instance finite_cwComplexOrdinaryPairQuotient [RelCWComplex.Finite (univ : Set X)] :
    RelCWComplex.Finite
      (univ : Set (TopPair.ofSubset (X := TopCat.of X) (A : Set X)).ordinaryPairQuotient) :=
  letI := A.relCWComplex
  haveI := @finite_relCWComplex X _ _ univ ∅ (CWComplex.instRelCWComplex univ) _ A
  (isPushout_collapse A).finite_cwComplexOfMapsToSkeletonLT
    (mem_skeletonLT_univ_of_mem_cellFrontier _)

end Topology.RelCWComplex.Subcomplex
