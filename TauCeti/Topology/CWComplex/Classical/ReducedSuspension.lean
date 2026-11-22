/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Constructions.ReducedSuspension
public import TauCeti.Topology.CWComplex.Classical.Cylinder
public import TauCeti.Topology.CWComplex.Classical.FiniteCWType
public import TauCeti.Topology.CWComplex.Classical.Pushout
public import TauCeti.Topology.CWComplex.Classical.Subcomplex
public import TauCeti.Topology.CWComplex.Classical.Zero

/-!
# The CW structure on the reduced suspension

Let `X` be a CW complex whose basepoint `x₀` is a `0`-cell. The reduced suspension
`ΣX = (X × I) / (X × ∂I ∪ {x₀} × I)` is again a CW complex
(`TauCeti.ReducedSuspension.cwComplex`, an instance), and it is Hausdorff. It has exactly one
`0`-cell, at the basepoint, and one `(n + 1)`-cell for each `n`-cell of `X` other than the
basepoint (`TauCeti.ReducedSuspension.cellEquiv`). The cell over an `n`-cell with characteristic
map `φ` is its suspension: its characteristic map sends `x` to
`[φ (Fin.init x), (x (Fin.last n) + 1) / 2]`, and its open and closed cells are the images of the
products of those of the `n`-cell with `(0, 1)` and with `I`. Since the basepoint of `ΣX` is again
a `0`-cell (`TauCeti.ReducedSuspension.basepoint_mem_skeletonLT_one`), the instance applies to
iterated suspensions as well. When `X` is finite, so is `ΣX`.

This makes the reduced suspension an operation on pointed CW complexes based at `0`-cells. Reduced
cohomology theories on such complexes compare their values on `X` and on `ΣX` through their
suspension isomorphisms, which needs `ΣX` to be a complex of the same kind.

The structure is built in two steps.

* The basepoint is a subcomplex (`TauCeti.singletonSubcomplex`), so `X` is a CW complex relative
  to `{x₀}`. The cylinder on this relative CW complex (`TauCeti.relCWComplexCylinder`) is a CW
  structure on `X × I` relative to `X × {0, 1} ∪ {x₀} × I`, which is exactly the locus that the
  reduced suspension collapses. Its `(n + 1)`-cells are the products of the `n`-cells of `X` other
  than `x₀` with the open interval.
* The reduced suspension is the pushout of the inclusion of that locus into `X × I` along the map
  to a point (`TopPair.isPushout_ordinaryPairQuotient`). Collapsing to a point is cellular, so
  the pushout is a CW complex whose cells are those of the point and those of the relative
  cylinder (`CategoryTheory.IsPushout.cwComplexOfMapsToSkeletonLT`).

## Main definitions

* `TauCeti.ReducedSuspension.cwComplex`: the CW structure on the reduced suspension.
* `TauCeti.ReducedSuspension.cellEquiv`: its `(n + 1)`-cells are the `n`-cells of `X` whose open
  cell does not contain the basepoint.

## Main results

* `TauCeti.ReducedSuspension.instT2Space`: the reduced suspension of a CW complex based at a
  `0`-cell is Hausdorff.
* `TauCeti.ReducedSuspension.cwComplex_map_cellEquiv_symm`: the characteristic map of the cell
  over an `n`-cell of `X` is the suspension of its characteristic map.
* `TauCeti.ReducedSuspension.cwComplex_openCell_cellEquiv_symm`,
  `TauCeti.ReducedSuspension.cwComplex_closedCell_cellEquiv_symm`: its open and closed cells.
* `TauCeti.ReducedSuspension.uniqueCellZero`, `TauCeti.ReducedSuspension.cwComplex_map_zero`: there
  is exactly one `0`-cell, at the basepoint.
* `TauCeti.ReducedSuspension.basepoint_mem_skeletonLT_one`: the basepoint is a `0`-cell.
* `TauCeti.ReducedSuspension.finite_cwComplex`: the reduced suspension of a finite CW complex is
  finite.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0, Operations on
  Spaces: the cell structures of products with the interval, of quotients by subcomplexes, and of
  the reduced suspension of a CW complex based at a `0`-cell.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

open scoped unitInterval

universe u

namespace TauCeti

namespace ReducedSuspension

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)] {x₀ : X}
  [hx₀ : Fact (x₀ ∈ skeletonLT (univ : Set X) 1)]

variable (X x₀) in
/-- The basepoint `x₀`, as a subcomplex of `X`. -/
private abbrev baseSubcomplex : CWComplex.Subcomplex (univ : Set X) :=
  singletonSubcomplex hx₀.out

variable (X x₀) in
/-- The part `X × {0, 1} ∪ {x₀} × I` of the cylinder, written as the base of the cylinder on `X`
relative to `{x₀}`. -/
private abbrev cylinderBase : Set (X × I) :=
  univ ×ˢ {0, 1} ∪ (baseSubcomplex X x₀ : Set X) ×ˢ univ

variable (X x₀) in
/-- The cylinder `X × I` is a CW complex relative to `X × {0, 1} ∪ {x₀} × I`: the cylinder on `X`
relative to its basepoint. -/
@[instance_reducible]
private def relCWComplexCylinder :
    RelCWComplex (univ ×ˢ univ : Set (X × I)) (cylinderBase X x₀) :=
  @TauCeti.relCWComplexCylinder X _ univ (baseSubcomplex X x₀) (baseSubcomplex X x₀).relCWComplex _

private theorem cylinderBase_eq : cylinderBase X x₀ = reducedSuspensionLocus X x₀ := by
  ext ⟨x, s⟩
  simp only [cylinderBase, coe_singletonSubcomplex, mem_union, mem_prod, mem_univ,
    mem_insert_iff, mem_singleton_iff, true_and, and_true, mem_reducedSuspensionLocus]
  tauto

/-- The reduced suspension is the pushout of the inclusion of `X × {0, 1} ∪ {x₀} × I` into the
cylinder, read as the base of the relative cylinder, along the map to a point. -/
private theorem isPushout_cylinder :
    letI := relCWComplexCylinder X x₀
    IsPushout (relCWBaseInclusion (univ ×ˢ univ : Set (X × I)))
      (TopCat.ofHom (ContinuousMap.const (cylinderBase X x₀) PUnit.unit))
      (TopCat.ofHom (mk.comp ⟨Subtype.val, continuous_subtypeVal⟩) :
        TopCat.of ↥(univ ×ˢ univ : Set (X × I)) ⟶ TopCat.of (ReducedSuspension X x₀))
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (basepoint : ReducedSuspension X x₀))) :=
  let := relCWComplexCylinder X x₀
  (reducedSuspensionPair X x₀).isPushout_ordinaryPairQuotient.of_iso'
    (TopCat.isoOfHomeo (Homeomorph.setCongr cylinderBase_eq))
    (TopCat.isoOfHomeo ((Homeomorph.setCongr univ_prod_univ).trans (Homeomorph.Set.univ _)))
    (Iso.refl _) (TopCat.isoOfHomeo (homeomorphOrdinaryPairQuotient X x₀))
    -- Both inclusions of the base send a point to itself in `X × I`, and both maps to `PUnit` are
    -- constant, so the first two squares commute pointwise by definition.
    (by ext; rfl) (by ext) (by ext p; exact (homeomorphOrdinaryPairQuotient_mk p.val).symm)
    (by ext; exact homeomorphOrdinaryPairQuotient_basepoint.symm)

/-- Collapsing to a point is cellular: the part in the base of the boundary of an `n`-cell of the
relative cylinder is mapped into the skeleton of dimension `n` of the point. -/
private theorem const_mem_skeletonLT_of_mem_cellFrontier (n : ℕ)
    (c : letI := relCWComplexCylinder X x₀; cell (univ ×ˢ univ : Set (X × I)) n)
    (p : cylinderBase X x₀)
    (hp : letI := relCWComplexCylinder X x₀; (p : X × I) ∈ cellFrontier n c) :
    TopCat.ofHom (ContinuousMap.const (cylinderBase X x₀) PUnit.unit) p ∈
      (skeletonLT (univ : Set PUnit.{u + 1}) n : Set PUnit.{u + 1}) := by
  let := relCWComplexCylinder X x₀
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [cellFrontier_zero_eq_empty] at hp
    exact hp.elim
  · rw [skeletonLT_univ_eq_univ_of_ne_zero hn.ne']
    exact mem_univ _

/-- **The reduced suspension of a CW complex based at a `0`-cell is a CW complex.** It has one
`0`-cell, the basepoint, and one `(n + 1)`-cell for each `n`-cell of `X` other than the basepoint
(`TauCeti.ReducedSuspension.cellEquiv`), whose characteristic map is the suspension of that of the
cell of `X` (`TauCeti.ReducedSuspension.cwComplex_map_cellEquiv_symm`). -/
@[instance_reducible]
def cwComplex : CWComplex (univ : Set (ReducedSuspension X x₀)) :=
  letI := relCWComplexCylinder X x₀
  isPushout_cylinder.cwComplexOfMapsToSkeletonLT const_mem_skeletonLT_of_mem_cellFrontier

attribute [instance] cwComplex

/-- The reduced suspension of a CW complex based at a `0`-cell is Hausdorff. -/
instance instT2Space : T2Space (ReducedSuspension X x₀) :=
  let := relCWComplexCylinder X x₀
  isPushout_cylinder.t2Space

/-- The cells of the reduced suspension are those of the point together with those of the
cylinder on `X` relative to its basepoint. -/
private def pushoutCellEquiv (n : ℕ) :
    letI := relCWComplexCylinder X x₀
    cell (univ : Set (ReducedSuspension X x₀)) n ≃
      cell (univ : Set PUnit.{u + 1}) n ⊕ cell (univ ×ˢ univ : Set (X × I)) n :=
  letI := relCWComplexCylinder X x₀
  isPushout_cylinder.cwComplexOfMapsToSkeletonLTCellEquiv
    const_mem_skeletonLT_of_mem_cellFrontier n

/-- The point has no cells of positive dimension. -/
private instance isEmpty_cell_punit_succ (n : ℕ) :
    IsEmpty (cell (univ : Set PUnit.{u + 1}) (n + 1)) :=
  inferInstanceAs (IsEmpty PEmpty)

/-- The `(n + 1)`-cells of the cylinder on `X` relative to its basepoint are the `n`-cells of `X`
other than the basepoint. -/
private def cylinderCellEquiv (n : ℕ) :
    letI := relCWComplexCylinder X x₀
    cell (univ ×ˢ univ : Set (X × I)) (n + 1) ≃ {c : cell (univ : Set X) n // x₀ ∉ openCell n c} :=
  (@cellCylinderEquiv X _ univ (baseSubcomplex X x₀) (baseSubcomplex X x₀).relCWComplex _
    n).trans (((baseSubcomplex X x₀).relCWComplexCellEquiv n).trans
      (Equiv.subtypeEquivRight fun c ↦ not_congr (mem_singletonSubcomplex_I hx₀.out c)))

variable (X x₀) in
/-- **The cells of the reduced suspension.** The `(n + 1)`-cells of `ΣX` are the `n`-cells of
`X` whose open cell does not contain the basepoint, that is, all `n`-cells of `X` except the
`0`-cell at the basepoint. -/
def cellEquiv (n : ℕ) :
    cell (univ : Set (ReducedSuspension X x₀)) (n + 1) ≃
      {c : cell (univ : Set X) n // x₀ ∉ openCell n c} :=
  letI := relCWComplexCylinder X x₀
  ((pushoutCellEquiv (n + 1)).trans (Equiv.emptySum _ _)).trans (cylinderCellEquiv n)

/-- The cell of `X` underlying the cell of the relative cylinder over an `n`-cell `c` of `X` is
`c`. -/
private theorem coe_relCWComplexCellEquiv_cylinderCellEquiv_symm {n : ℕ}
    (c : {c : cell (univ : Set X) n // x₀ ∉ openCell n c}) :
    ((baseSubcomplex X x₀).relCWComplexCellEquiv n
      (@cellCylinderEquiv X _ univ (baseSubcomplex X x₀) (baseSubcomplex X x₀).relCWComplex _ n
        ((cylinderCellEquiv n).symm c)) : cell (univ : Set X) n) = c.val := by
  simp [cylinderCellEquiv]

/-- On the closed unit ball, the characteristic map of the cell of the reduced suspension over an
`n`-cell `c` of `X` is that of the cell of the relative cylinder over `c`, followed by the
projection onto the reduced suspension. -/
private theorem cwComplex_map_cellEquiv_symm_eq {n : ℕ}
    (c : {c : cell (univ : Set X) n // x₀ ∉ openCell n c}) {y : Fin (n + 1) → ℝ}
    (hy : y ∈ closedBall (0 : Fin (n + 1) → ℝ) 1) :
    RelCWComplex.map (n + 1) ((cellEquiv X x₀ n).symm c) y =
      mk (@RelCWComplex.map (X × I) _ _ _ (relCWComplexCylinder X x₀) (n + 1)
        ((cylinderCellEquiv n).symm c) y) :=
  let := relCWComplexCylinder X x₀
  isPushout_cylinder.cwComplexOfMapsToSkeletonLT_map_inr
    const_mem_skeletonLT_of_mem_cellFrontier (n + 1) ((cylinderCellEquiv n).symm c) ⟨y, hy⟩

/-- **The cells of the reduced suspension are suspensions.** The characteristic map of the
`(n + 1)`-cell of `ΣX` over an `n`-cell `c` of `X` with characteristic map `φ` sends `x` to
`[φ (Fin.init x), (x (Fin.last n) + 1) / 2]`. -/
@[simp]
theorem cwComplex_map_cellEquiv_symm {n : ℕ}
    (c : {c : cell (univ : Set X) n // x₀ ∉ openCell n c})
    (x : closedBall (0 : Fin (n + 1) → ℝ) 1) :
    RelCWComplex.map (n + 1) ((cellEquiv X x₀ n).symm c) x =
      mk (RelCWComplex.map n c.val (Fin.init x.val),
        projIcc 0 1 zero_le_one ((x.val (Fin.last n) + 1) / 2)) := by
  rw [cwComplex_map_cellEquiv_symm_eq c x.property, @map_relCWComplexCylinder_apply X _ univ
    (baseSubcomplex X x₀) (baseSubcomplex X x₀).relCWComplex,
    RelCWComplex.Subcomplex.map_relCWComplex, coe_relCWComplexCellEquiv_cylinderCellEquiv_symm]

/-- The open cell of the reduced suspension over an `n`-cell of `X` is the image of the product of
its open cell with the open interval `(0, 1)`. -/
@[simp]
theorem cwComplex_openCell_cellEquiv_symm {n : ℕ}
    (c : {c : cell (univ : Set X) n // x₀ ∉ openCell n c}) :
    openCell (n + 1) ((cellEquiv X x₀ n).symm c) = mk '' (openCell n c.val ×ˢ Ioo 0 1) := by
  let := relCWComplexCylinder X x₀
  rw [← coe_relCWComplexCellEquiv_cylinderCellEquiv_symm c,
    ← RelCWComplex.Subcomplex.openCell_relCWComplex, ← @openCell_relCWComplexCylinder X _ univ
      (baseSubcomplex X x₀) (baseSubcomplex X x₀).relCWComplex, openCell, openCell, image_image]
  exact image_congr fun y hy ↦ cwComplex_map_cellEquiv_symm_eq c (ball_subset_closedBall hy)

/-- The closed cell of the reduced suspension over an `n`-cell of `X` is the image of the product
of its closed cell with the interval. -/
@[simp]
theorem cwComplex_closedCell_cellEquiv_symm {n : ℕ}
    (c : {c : cell (univ : Set X) n // x₀ ∉ openCell n c}) :
    closedCell (n + 1) ((cellEquiv X x₀ n).symm c) = mk '' (closedCell n c.val ×ˢ univ) := by
  let := relCWComplexCylinder X x₀
  rw [← coe_relCWComplexCellEquiv_cylinderCellEquiv_symm c,
    ← RelCWComplex.Subcomplex.closedCell_relCWComplex, ← @closedCell_relCWComplexCylinder X _ univ
      (baseSubcomplex X x₀) (baseSubcomplex X x₀).relCWComplex, closedCell, closedCell,
    image_image]
  exact image_congr fun y hy ↦ cwComplex_map_cellEquiv_symm_eq c hy

/-- **The only `0`-cell of the reduced suspension is the basepoint.** -/
@[simp]
theorem cwComplex_map_zero (c : cell (univ : Set (ReducedSuspension X x₀)) 0) (x : Fin 0 → ℝ) :
    RelCWComplex.map 0 c x = basepoint := by
  let := relCWComplexCylinder X x₀
  obtain ⟨c, rfl⟩ := (pushoutCellEquiv (X := X) (x₀ := x₀) 0).symm.surjective c
  rcases c with c | c
  · exact isPushout_cylinder.cwComplexOfMapsToSkeletonLT_map_inl
      const_mem_skeletonLT_of_mem_cellFrontier 0 c x
  · exact (IsEmpty.false c).elim

/-- **The reduced suspension has exactly one `0`-cell**, whose characteristic map is the basepoint
(`TauCeti.ReducedSuspension.cwComplex_map_zero`). -/
@[instance_reducible]
def uniqueCellZero : Unique (cell (univ : Set (ReducedSuspension X x₀)) 0) where
  default :=
    letI := relCWComplexCylinder X x₀
    (pushoutCellEquiv 0).symm (.inl ⟨PUnit.unit, mem_univ _⟩)
  uniq _ := injective_map_zero _ (by simp only [cwComplex_map_zero])

attribute [instance] uniqueCellZero

/-- **The basepoint of the reduced suspension is a `0`-cell.** -/
theorem basepoint_mem_skeletonLT_one :
    (basepoint : ReducedSuspension X x₀) ∈ skeletonLT (univ : Set (ReducedSuspension X x₀)) 1 := by
  let c : cell (univ : Set (ReducedSuspension X x₀)) 0 := default
  rw [← cwComplex_map_zero c ![]]
  exact closedCell_subset_skeletonLT 0 c (by simp [closedCell_zero_eq_singleton])

instance : Fact ((basepoint : ReducedSuspension X x₀) ∈
    skeletonLT (univ : Set (ReducedSuspension X x₀)) 1) :=
  ⟨basepoint_mem_skeletonLT_one⟩

/-- The reduced suspension of a finite CW complex based at a `0`-cell is a finite CW complex. -/
theorem finite_cwComplex [RelCWComplex.Finite (univ : Set X)] :
    RelCWComplex.Finite (univ : Set (ReducedSuspension X x₀)) := by
  let := relCWComplexCylinder X x₀
  have : RelCWComplex.Finite (univ ×ˢ univ : Set (X × I)) := by
    have := RelCWComplex.finite_cells_of_finite (C := (univ : Set X))
    have : Finite (Σ n, {c : cell (univ : Set X) n // x₀ ∉ openCell n c}) :=
      .of_injective _ (Function.injective_id.sigma_map fun _ ↦ Subtype.val_injective)
    refine RelCWComplex.finite_of_finite_cells (.of_surjective
      (fun c : Σ n, {c : cell (univ : Set X) n // x₀ ∉ openCell n c} ↦
        (⟨c.fst + 1, (cylinderCellEquiv c.fst).symm c.snd⟩ :
          Σ n, cell (univ ×ˢ univ : Set (X × I)) n))
      ?_)
    rintro ⟨_ | n, c⟩
    · exact isEmptyElim c
    · exact ⟨⟨n, cylinderCellEquiv n c⟩, by simp⟩
  exact isPushout_cylinder.finite_cwComplexOfMapsToSkeletonLT
    const_mem_skeletonLT_of_mem_cellFrontier

end ReducedSuspension

end TauCeti
