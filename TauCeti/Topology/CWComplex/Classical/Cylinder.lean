/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.UnitInterval

/-!
# The cylinder on a relative CW complex

For a relative CW complex `(C, D)` in a Hausdorff space `X`, the cylinder `C × I` in `X × I` is a
CW complex relative to `C × {0, 1} ∪ D × I` (`TauCeti.relCWComplexCylinder`). Its `(n + 1)`-cells
are the products of the `n`-cells of `(C, D)` with the open interval `(0, 1)`, and it has no
`0`-cells (`TauCeti.cellCylinderEquiv`). The characteristic map of the cylinder on an `n`-cell
keeps the `n` coordinates of the cell first and puts the interval coordinate last, sending
`x : Fin (n + 1) → ℝ` to `(φ (Fin.init x), projIcc 0 1 _ ((x (Fin.last n) + 1) / 2))` for the
characteristic map `φ` of the cell; on the closed unit ball the interval coordinate is just
`(x (Fin.last n) + 1) / 2`. The base contains the two ends `C × {0}` and `C × {1}`, the images of
the inclusions `x ↦ (x, 0)` and `x ↦ (x, 1)`.

A homotopy of maps out of `C` is a map out of `C × I`, and a homotopy relative to `D` between two
given maps is a map out of `C × I` prescribed on `C × {0, 1} ∪ D × I`. So this relative structure is
what lets cell-by-cell arguments (homotopy extension, compression into a subspace) apply to
homotopies themselves; for instance, the injectivity half of Hatcher, Proposition 4.22 (a weak
homotopy equivalence `f : Y → Z` induces injections `[K, Y] → [K, Z]` for CW complexes `K`)
compresses a homotopy defined on `C × I` relative to its two ends.

The only point that is not formal is the weak topology. Since `I` is compact, the cylinder has
the weak topology of the closed cells `closedCell n j × I` and of the base: this holds for the
product of a relative CW complex with any compact regular space
(`Topology.RelCWComplex.closed_prod`), because the projection `X × Y → X` is then a closed map.

## Main declarations

* `Topology.RelCWComplex.closed_prod`: the product of a relative CW complex with a compact regular
  space has the weak topology of the products of its closed cells and of its base.
* `TauCeti.relCWComplexCylinder`: the relative CW structure on `C ×ˢ univ` in `X × I`, relative to
  `C ×ˢ {0, 1} ∪ D ×ˢ univ`.
* `TauCeti.cellCylinderEquiv`: its `(n + 1)`-cells are the `n`-cells of `C`; it has no `0`-cells
  (`TauCeti.isEmpty_cell_relCWComplexCylinder_zero`). Its characteristic maps, open cells,
  closed cells and cell frontiers are described by `TauCeti.map_relCWComplexCylinder_apply`,
  `TauCeti.openCell_relCWComplexCylinder`, `TauCeti.closedCell_relCWComplexCylinder` and
  `TauCeti.cellFrontier_relCWComplexCylinder`.

## Implementation notes

The construction adapts that of the finite product `TauCeti.cwComplexProd`
(`TauCeti/Topology/CWComplex/Classical/Product.lean`): the characteristic map of a cell of the
cylinder is the product of the characteristic map of a cell of `C` with that of the interval,
precomposed with the sup-norm isometry `Fin.appendIsometry` splitting off the last coordinate.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 (products of CW complexes) and Section 4.1 (Proposition 4.22); Appendix,
  Theorem A.6, for the topology of products of CW complexes.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex unitInterval

universe u

namespace Topology.RelCWComplex

variable {X : Type*} [TopologicalSpace X] [T2Space X] {Y : Type*} [TopologicalSpace Y]
  [CompactSpace Y] [RegularSpace Y]

/-- **The product of a relative CW complex with a compact regular space has the weak topology**:
a subset `A` of `C ×ˢ univ` in `X × Y` is closed if and only if its intersections with the products
`closedCell n j ×ˢ univ` and with `D ×ˢ univ` are closed. -/
theorem closed_prod (C : Set X) {D : Set X} [RelCWComplex C D] (A : Set (X × Y))
    (hA : A ⊆ C ×ˢ univ) :
    IsClosed A ↔
      (∀ n (j : cell C n), IsClosed (A ∩ closedCell n j ×ˢ univ)) ∧ IsClosed (A ∩ D ×ˢ univ) := by
  refine ⟨fun h ↦ ⟨fun n j ↦ h.inter (isClosed_closedCell.prod isClosed_univ),
    h.inter ((isClosedBase C).prod isClosed_univ)⟩, fun ⟨hcell, hD⟩ ↦ ?_⟩
  -- The slice of `A` over a point of a closed set `K` with `A ∩ K ×ˢ univ` closed is closed.
  have hslice {K : Set X} (hK : IsClosed (A ∩ K ×ˢ univ)) {x : X} (hx : x ∈ K) :
      IsClosed {y | (x, y) ∈ A} := by
    convert hK.preimage (Continuous.prodMk_right x) using 1
    ext y
    simp [hx]
  -- So every slice of `A` is closed: a point of `C` lies in `D` or in a closed cell.
  have hslice' (x : X) : IsClosed {y | (x, y) ∈ A} := by
    by_cases hxC : x ∈ C
    · rw [← RelCWComplex.union (C := C), mem_union, mem_iUnion₂] at hxC
      obtain hxD | ⟨n, j, hxj⟩ := hxC
      exacts [hslice hD hxD, hslice (hcell n j) hxj]
    · rw [show {y | (x, y) ∈ A} = ∅ from
        eq_empty_of_forall_notMem fun y (hy : (x, y) ∈ A) ↦ hxC (hA hy).1]
      exact isClosed_empty
  -- The projection to `X` of the part of `A` over a closed subset `F` of `Y` is closed, by the
  -- weak topology of `C`, because the projection `X × Y → X` is a closed map.
  have hproj {F : Set Y} (hF : IsClosed F) : IsClosed (Prod.fst '' (A ∩ univ ×ˢ F)) := by
    have hK {K : Set X} (hK : IsClosed (A ∩ K ×ˢ univ)) :
        IsClosed (Prod.fst '' (A ∩ univ ×ˢ F) ∩ K) := by
      rw [← image_inter_preimage, ← prod_univ, inter_right_comm]
      exact isClosedMap_fst_of_compactSpace _ (hK.inter (isClosed_univ.prod hF))
    refine (RelCWComplex.closed C _ ?_).2 ⟨fun n j ↦ hK (hcell n j), hK hD⟩
    rintro _ ⟨p, hp, rfl⟩
    exact (hA hp.1).1
  -- A point outside `A` has a closed neighbourhood `F` of its second coordinate missing its slice,
  -- and the complement of the projection of `A ∩ univ ×ˢ F` times `F` is a neighbourhood
  -- missing `A`.
  refine isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun ⟨x, t⟩ hxt ↦ ?_)
  obtain ⟨F, hF, hFc, hFA⟩ :=
    exists_mem_nhds_isClosed_subset ((hslice' x).isOpen_compl.mem_nhds hxt)
  have hx : x ∉ Prod.fst '' (A ∩ univ ×ˢ F) := by
    rintro ⟨⟨_, s⟩, ⟨hs, -, hsF⟩, rfl⟩
    exact hFA hsF hs
  filter_upwards [prod_mem_nhds ((hproj hFc).isOpen_compl.mem_nhds hx) hF]
  rintro ⟨x', s⟩ ⟨hx', hs⟩ hxs
  exact hx' ⟨(x', s), ⟨hxs, mem_univ x', hs⟩, rfl⟩

end Topology.RelCWComplex

namespace TauCeti

/-- The characteristic map of the open interval `(0, 1)` as a `1`-cell, read on `ℝ`:
`t ↦ projIcc 0 1 _ ((t + 1) / 2)`, which is `(t + 1) / 2` on `[-1, 1]`, carrying `[-1, 1]` onto
`I`, `(-1, 1)` onto `(0, 1)` and `{-1, 1}` onto `{0, 1}`. -/
private def intervalCellMap : PartialEquiv ℝ I where
  toFun t := projIcc 0 1 zero_le_one ((t + 1) / 2)
  invFun s := 2 * s - 1
  source := ball 0 1
  target := Ioo 0 1
  map_source' t ht := by
    rw [Real.ball_eq_Ioo, zero_sub, zero_add, mem_Ioo] at ht
    rw [projIcc_of_mem _ ⟨by linarith, by linarith⟩, mem_Ioo, ← coe_pos, ← coe_lt_one]
    constructor <;> dsimp only <;> linarith
  map_target' s hs := by
    rw [mem_Ioo, ← coe_pos, ← coe_lt_one] at hs
    rw [Real.ball_eq_Ioo, mem_Ioo]
    constructor <;> linarith
  left_inv' t ht := by
    rw [Real.ball_eq_Ioo, zero_sub, zero_add, mem_Ioo] at ht
    rw [projIcc_of_mem _ ⟨by linarith, by linarith⟩]
    dsimp only
    ring
  right_inv' s _ := by
    rw [show (2 * (s : ℝ) - 1 + 1) / 2 = s by ring, projIcc_val]

private theorem intervalCellMap_source : intervalCellMap.source = ball 0 1 :=
  (rfl)

private theorem intervalCellMap_apply (t : ℝ) :
    intervalCellMap t = projIcc 0 1 zero_le_one ((t + 1) / 2) :=
  (rfl)

private theorem continuous_intervalCellMap : Continuous intervalCellMap :=
  (continuous_projIcc (h := zero_le_one)).comp (by fun_prop : Continuous fun t : ℝ ↦ (t + 1) / 2)

private theorem continuous_intervalCellMap_symm : Continuous intervalCellMap.symm :=
  (continuous_const.mul continuous_subtype_val).sub continuous_const

private theorem image_ball_intervalCellMap : intervalCellMap '' ball 0 1 = Ioo 0 1 :=
  intervalCellMap_source ▸ intervalCellMap.image_source_eq_target

private theorem image_closedBall_intervalCellMap : intervalCellMap '' closedBall 0 1 = univ := by
  refine eq_univ_of_forall fun s ↦ ⟨2 * s - 1, ?_, ?_⟩
  · rw [Real.closedBall_eq_Icc, zero_sub, zero_add, mem_Icc]
    constructor <;> linarith [s.2.1, s.2.2]
  · rw [intervalCellMap_apply, show (2 * (s : ℝ) - 1 + 1) / 2 = s by ring, projIcc_val]

private theorem image_sphere_intervalCellMap : intervalCellMap '' sphere 0 1 = {0, 1} := by
  rw [Real.sphere_eq_pair 0 zero_le_one, image_pair, intervalCellMap_apply, intervalCellMap_apply]
  norm_num [projIcc_left, projIcc_right]

/-- The identification of `Fin (n + 1) → ℝ` with `(Fin n → ℝ) × ℝ`, splitting off the last
coordinate; it is an isometry for the sup norms. -/
private def cylinderIsometry (n : ℕ) : (Fin (n + 1) → ℝ) ≃ᵢ (Fin n → ℝ) × ℝ :=
  (Fin.appendIsometry n 1).symm.trans
    { toEquiv := (Equiv.refl _).prodCongr (Equiv.funUnique (Fin 1) ℝ)
      isometry_toFun := isometry_id.prodMap (IsometryEquiv.funUnique (Fin 1) ℝ).isometry }

private theorem cylinderIsometry_apply {n : ℕ} (x : Fin (n + 1) → ℝ) :
    cylinderIsometry n x = (Fin.init x, x (Fin.last n)) := by
  rw [cylinderIsometry, IsometryEquiv.trans_apply, IsometryEquiv.coe_eq_toEquiv,
    Fin.appendIsometry_symm_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.funUnique_apply]
  -- `x` is restricted along `Fin.castAdd 1` and `Fin.natAdd n`; compare indices by their values.
  refine Prod.ext (funext fun i ↦ congrArg x (Fin.ext ?_)) (congrArg x (Fin.ext ?_)) <;> simp

private theorem cylinderIsometry_zero (n : ℕ) : cylinderIsometry n 0 = 0 := by
  ext <;> simp [cylinderIsometry_apply, Fin.init]

private theorem image_ball_cylinderIsometry (n : ℕ) :
    cylinderIsometry n '' ball 0 1 = ball 0 1 ×ˢ ball 0 1 := by
  rw [IsometryEquiv.image_ball, cylinderIsometry_zero, ball_prod_same, Prod.zero_eq_mk]

private theorem image_closedBall_cylinderIsometry (n : ℕ) :
    cylinderIsometry n '' closedBall 0 1 = closedBall 0 1 ×ˢ closedBall 0 1 := by
  rw [IsometryEquiv.image_closedBall, cylinderIsometry_zero, closedBall_prod_same,
    Prod.zero_eq_mk]

private theorem image_sphere_cylinderIsometry (n : ℕ) :
    cylinderIsometry n '' sphere 0 1 =
      sphere 0 1 ×ˢ closedBall 0 1 ∪ closedBall 0 1 ×ˢ sphere 0 1 := by
  rw [IsometryEquiv.image_sphere, cylinderIsometry_zero, sphere_prod, Prod.fst_zero, Prod.snd_zero]

private theorem preimage_ball_cylinderIsometry (n : ℕ) :
    cylinderIsometry n ⁻¹' (ball 0 1 ×ˢ ball 0 1) = ball 0 1 :=
  ((cylinderIsometry n).toEquiv.preimage_eq_iff_eq_image _ _).2
    (image_ball_cylinderIsometry n).symm

variable {X : Type u} [TopologicalSpace X] {C D : Set X} [RelCWComplex C D]

/-- The characteristic map of the cylinder on the `n`-cell `i` of `C`: the product of the
characteristic map of `i` with that of the interval, after splitting off the last coordinate. -/
private def cylinderCellMap {n : ℕ} (i : cell C n) : PartialEquiv (Fin (n + 1) → ℝ) (X × I) :=
  (cylinderIsometry n).toEquiv.transPartialEquiv ((map n i).prod intervalCellMap)

private theorem cylinderCellMap_apply {n : ℕ} (i : cell C n) (x : Fin (n + 1) → ℝ) :
    cylinderCellMap i x = (map n i (Fin.init x), intervalCellMap (x (Fin.last n))) :=
  (rfl)

private theorem image_cylinderCellMap {n : ℕ} (i : cell C n) (s : Set (Fin (n + 1) → ℝ)) :
    cylinderCellMap i '' s = Prod.map (map n i) intervalCellMap '' (cylinderIsometry n '' s) := by
  rw [image_image]
  exact image_congr fun x _ ↦ by
    rw [cylinderCellMap_apply, cylinderIsometry_apply, Prod.map_apply]

private theorem image_ball_cylinderCellMap {n : ℕ} (i : cell C n) :
    cylinderCellMap i '' ball 0 1 = openCell n i ×ˢ Ioo 0 1 := by
  rw [image_cylinderCellMap, image_ball_cylinderIsometry, prodMap_image_prod,
    image_ball_intervalCellMap, openCell]

private theorem image_closedBall_cylinderCellMap {n : ℕ} (i : cell C n) :
    cylinderCellMap i '' closedBall 0 1 = closedCell n i ×ˢ univ := by
  rw [image_cylinderCellMap, image_closedBall_cylinderIsometry, prodMap_image_prod,
    image_closedBall_intervalCellMap, closedCell]

private theorem image_sphere_cylinderCellMap {n : ℕ} (i : cell C n) :
    cylinderCellMap i '' sphere 0 1 = cellFrontier n i ×ˢ univ ∪ closedCell n i ×ˢ {0, 1} := by
  simp only [image_cylinderCellMap, image_sphere_cylinderIsometry, image_union,
    prodMap_image_prod, image_closedBall_intervalCellMap, image_sphere_intervalCellMap,
    cellFrontier, closedCell]

private theorem source_cylinderCellMap {n : ℕ} (i : cell C n) :
    (cylinderCellMap i).source = ball 0 1 := by
  simp only [cylinderCellMap, Equiv.transPartialEquiv_source, PartialEquiv.prod_source, source_eq,
    intervalCellMap_source, IsometryEquiv.coe_toEquiv, preimage_ball_cylinderIsometry]

variable (C D) in
/-- The cells of the cylinder on `(C, D)`: there are no `0`-cells, and the `(n + 1)`-cells are the
`n`-cells of `C`. It is reducible so that `CylinderCell C D (n + 1)` and `cell C n` are
identified by instance-transparency unification, as `rw` and `simp` need. -/
@[reducible] private def CylinderCell : ℕ → Type u
  | 0 => PEmpty
  | n + 1 => cell C n

/-- The characteristic maps of the cylinder on `(C, D)`. -/
private def cylinderMap : (n : ℕ) → CylinderCell C D n → PartialEquiv (Fin n → ℝ) (X × I)
  | 0, i => PEmpty.elim i
  | _ + 1, i => cylinderCellMap i

private theorem cylinderMap_succ {n : ℕ} (i : CylinderCell C D (n + 1)) :
    cylinderMap (n + 1) i = cylinderCellMap (C := C) (n := n) i :=
  (rfl)

/-- A family of finite sets of cells of `C`, shifted up one dimension to cells of the cylinder. -/
private def cylinderFinset (J : (n : ℕ) → Finset (cell C n)) :
    (n : ℕ) → Finset (CylinderCell C D n)
  | 0 => ∅
  | n + 1 => J n

variable [T2Space X]

variable (C D) in
/-- **The cylinder on a relative CW complex.** For a relative CW complex `(C, D)` in a Hausdorff
space `X`, the cylinder `C ×ˢ univ` in `X × I` is a CW complex relative to
`C ×ˢ {0, 1} ∪ D ×ˢ univ`. Its `(n + 1)`-cells are the `n`-cells of `C`
(`TauCeti.cellCylinderEquiv`), with characteristic maps
`x ↦ (φ (Fin.init x), projIcc 0 1 _ ((x (Fin.last n) + 1) / 2))`
(`TauCeti.map_relCWComplexCylinder_apply`), and it has no `0`-cells.

It is not an instance: the base of a relative CW complex is an `outParam`, and `C ×ˢ univ` carries
other relative CW structures. -/
@[instance_reducible]
def relCWComplexCylinder : RelCWComplex (C ×ˢ (univ : Set I)) (C ×ˢ {0, 1} ∪ D ×ˢ univ) where
  cell := CylinderCell C D
  map := cylinderMap
  source_eq
    | 0, i => PEmpty.elim i
    | _ + 1, i => source_cylinderCellMap i
  continuousOn
    | 0, i => PEmpty.elim i
    | n + 1, i => ((continuousOn n i).prodMap continuous_intervalCellMap.continuousOn).comp
        (cylinderIsometry n).continuous.continuousOn fun x hx ↦
          ⟨(image_closedBall_cylinderIsometry n ▸ mem_image_of_mem _ hx).1, mem_univ _⟩
  continuousOn_symm
    | 0, i => PEmpty.elim i
    | n + 1, i => (cylinderIsometry n).symm.continuous.comp_continuousOn
        ((continuousOn_symm n i).prodMap continuous_intervalCellMap_symm.continuousOn)
  pairwiseDisjoint' := by
    rintro ⟨_ | n, i⟩ - ⟨_ | m, j⟩ - hne
    · exact PEmpty.elim i
    · exact PEmpty.elim i
    · exact PEmpty.elim j
    simp only [Function.onFun, cylinderMap_succ, image_ball_cylinderCellMap]
    refine disjoint_prod.2 (Or.inl (disjoint_openCell_of_ne fun h ↦ hne ?_))
    obtain ⟨rfl, hij⟩ := Sigma.mk.inj_iff.1 h
    rw [eq_of_heq hij]
  disjointBase'
    | 0, i => PEmpty.elim i
    | n + 1, i => by
      rw [cylinderMap_succ, image_ball_cylinderCellMap]
      refine disjoint_union_right.2 ⟨disjoint_prod.2 (Or.inr ?_),
        disjoint_prod.2 (Or.inl (disjointBase n i))⟩
      rw [disjoint_right]
      rintro s (rfl | rfl) hs <;> simp at hs
  mapsTo
    | 0, i => PEmpty.elim i
    | n + 1, i => by
      obtain ⟨J, hJ⟩ := cellFrontier_subset_base_union_finite_closedCell n i
      refine ⟨cylinderFinset J, ?_⟩
      rw [mapsTo_iff_image_subset, cylinderMap_succ, image_sphere_cylinderCellMap]
      rintro ⟨x, s⟩ (⟨hx, -⟩ | ⟨hx, hs⟩)
      · rcases hJ hx with hxD | hx
        · exact Or.inl (Or.inr ⟨hxD, mem_univ s⟩)
        obtain ⟨m, hm, j, hj, hxj⟩ : ∃ m < n, ∃ j ∈ J m, x ∈ closedCell m j := by simpa using hx
        refine Or.inr (mem_iUnion₂.2 ⟨m + 1, by omega, mem_iUnion₂.2 ⟨j, hj, ?_⟩⟩)
        rw [cylinderMap_succ, image_closedBall_cylinderCellMap]
        exact ⟨hxj, mem_univ s⟩
      · exact Or.inl (Or.inl ⟨closedCell_subset_complex n i hx, hs⟩)
  closed' A hA h := by
    refine (closed_prod C A hA).2 ⟨fun n i ↦ ?_, ?_⟩
    · simpa only [cylinderMap_succ, image_closedBall_cylinderCellMap] using h.1 (n + 1) i
    · rw [← inter_eq_right.2 (subset_union_right : D ×ˢ (univ : Set I) ⊆ C ×ˢ {0, 1} ∪ _),
        ← inter_assoc]
      exact h.2.inter ((isClosedBase C).prod isClosed_univ)
  isClosedBase :=
    (RelCWComplex.isClosed.prod (toFinite _).isClosed).union ((isClosedBase C).prod isClosed_univ)
  union' := by
    refine subset_antisymm (union_subset (union_subset (prod_mono subset_rfl (subset_univ _))
      (prod_mono base_subset_complex subset_rfl)) (iUnion₂_subset ?_)) ?_
    · rintro (_ | n) i
      · exact PEmpty.elim i
      rw [cylinderMap_succ, image_closedBall_cylinderCellMap]
      exact prod_mono (closedCell_subset_complex n i) subset_rfl
    · rintro ⟨x, s⟩ ⟨hx, -⟩
      rw [← RelCWComplex.union (C := C), mem_union, mem_iUnion₂] at hx
      obtain hxD | ⟨n, i, hxi⟩ := hx
      · exact Or.inl (Or.inr ⟨hxD, mem_univ s⟩)
      refine Or.inr (mem_iUnion₂.2 ⟨n + 1, i, ?_⟩)
      rw [cylinderMap_succ, image_closedBall_cylinderCellMap]
      exact ⟨hxi, mem_univ s⟩

/-- The cylinder on a relative CW complex has no `0`-cells. -/
instance isEmpty_cell_relCWComplexCylinder_zero :
    IsEmpty (@cell (X × I) _ (C ×ˢ univ) _ (relCWComplexCylinder C D) 0) :=
  inferInstanceAs (IsEmpty PEmpty)

/-- The `(n + 1)`-cells of the cylinder on a relative CW complex `(C, D)` are the `n`-cells
of `C`. -/
def cellCylinderEquiv (n : ℕ) :
    @cell (X × I) _ (C ×ˢ univ) _ (relCWComplexCylinder C D) (n + 1) ≃ cell C n :=
  Equiv.refl _

variable {n : ℕ} (i : @cell (X × I) _ (C ×ˢ univ) _ (relCWComplexCylinder C D) (n + 1))

/-- The characteristic map of the cylinder on an `n`-cell with characteristic map `φ` is
`x ↦ (φ (Fin.init x), projIcc 0 1 _ ((x (Fin.last n) + 1) / 2))`; on the closed unit ball its
interval coordinate is `(x (Fin.last n) + 1) / 2`. -/
@[simp]
theorem map_relCWComplexCylinder_apply (x : Fin (n + 1) → ℝ) :
    @map (X × I) _ (C ×ˢ univ) _ (relCWComplexCylinder C D) (n + 1) i x =
      (map n (cellCylinderEquiv n i) (Fin.init x),
        projIcc 0 1 zero_le_one ((x (Fin.last n) + 1) / 2)) :=
  (rfl)

/-- The open cell of the cylinder on an `n`-cell is the product of the open cell with the open
interval `(0, 1)`. -/
@[simp]
theorem openCell_relCWComplexCylinder :
    @openCell (X × I) _ (C ×ˢ univ) _ (relCWComplexCylinder C D) (n + 1) i =
      openCell n (cellCylinderEquiv n i) ×ˢ Ioo 0 1 :=
  image_ball_cylinderCellMap (D := D) i

/-- The closed cell of the cylinder on an `n`-cell is the product of the closed cell with `I`. -/
@[simp]
theorem closedCell_relCWComplexCylinder :
    @closedCell (X × I) _ (C ×ˢ univ) _ (relCWComplexCylinder C D) (n + 1) i =
      closedCell n (cellCylinderEquiv n i) ×ˢ univ :=
  image_closedBall_cylinderCellMap (D := D) i

/-- The boundary of the cylinder on an `n`-cell is the cylinder on the boundary of the cell
together with the two ends of the cylinder on the closed cell. -/
@[simp]
theorem cellFrontier_relCWComplexCylinder :
    @cellFrontier (X × I) _ (C ×ˢ univ) _ (relCWComplexCylinder C D) (n + 1) i =
      cellFrontier n (cellCylinderEquiv n i) ×ˢ univ ∪
        closedCell n (cellCylinderEquiv n i) ×ˢ {0, 1} :=
  image_sphere_cylinderCellMap (D := D) i

end TauCeti
