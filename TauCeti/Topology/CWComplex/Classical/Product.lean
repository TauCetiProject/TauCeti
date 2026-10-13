/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Topology.MetricSpace.Isometry
public import TauCeti.Topology.CWComplex.Classical.FiniteCWType
public import TauCeti.Topology.PiCurry

/-!
# The product of two finite CW complexes

For finite CW complexes `C` in `X` and `D` in `Y`, the product `C ×ˢ D` in `X × Y` is a finite CW
complex whose `n`-cells are the pairs of a `p`-cell of `C` and a `q`-cell of `D` with `p + q = n`
(`TauCeti.cwComplexProd`, `TauCeti.cellProdEquiv`).  Mathlib's classical CW complexes parametrise
an `n`-cell by the unit ball of `Fin n → ℝ` in the sup norm, and appending coordinates
`Fin.appendIsometryOfEq : (Fin p → ℝ) × (Fin q → ℝ) ≃ᵢ (Fin n → ℝ)` is an isometry, so it
identifies the product of the unit balls of the factors with the unit ball, and similarly for
closed balls.  The characteristic map of a product cell is the product of the characteristic maps
of its factors after this isometry.  The unit sphere of a product is
`(sphere × closedBall) ∪ (closedBall × sphere)`, so the boundary of a product cell lies in
products of cells of smaller total dimension.  With finitely many cells the weak topology
condition is automatic (`Topology.CWComplex.mkFinite`).

## Main declarations

* `TauCeti.cwComplexProd`: the product CW structure on `C ×ˢ D`, an instance, which is finite
  (`TauCeti.finite_cwComplexProd`).
* `TauCeti.cellProdEquiv`: the `n`-cells of `C ×ˢ D` are the pairs of a `p`-cell of `C` and a
  `q`-cell of `D` with `p + q = n`.  The characteristic map, open cell, closed cell and boundary
  of a product cell are described by `TauCeti.map_cellProdEquiv_symm_appendIsometryOfEq`,
  `TauCeti.openCell_cellProdEquiv_symm`, `TauCeti.closedCell_cellProdEquiv_symm` and
  `TauCeti.cellFrontier_cellProdEquiv_symm`.
* `TauCeti.nat_card_cell_prod`: `C ×ˢ D` has `∑_{p + q = n} #(p-cells of C) · #(q-cells of D)`
  cells of dimension `n`.
* `TauCeti.FiniteCWType.prod`: a product of two spaces of finite CW type has finite CW type.
* `TauCeti.FiniteCWType.pi`: a finite product of spaces of finite CW type has finite CW type.

For infinite complexes the product topology can be strictly coarser than the weak topology of the
product cells (Hatcher, Theorem A.6, gives conditions under which they agree); this file treats
finite complexes, where the two agree automatically.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, products of CW complexes, and Appendix, Theorem A.6.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex

universe u v

namespace TauCeti

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {C : Set X} {D : Set Y}
  [CWComplex C] [CWComplex D]

variable (C D) in
/-- The `n`-cells of the product of two CW complexes: a `p`-cell of `C` and a `q`-cell of `D`
with `p + q = n`. -/
private abbrev ProdCell (n : ℕ) : Type (max u v) :=
  Σ pq : Finset.antidiagonal n, cell C pq.1.1 × cell D pq.1.2

/-- The identification of `Fin n → ℝ` with `(Fin p → ℝ) × (Fin q → ℝ)` used to parametrise the
product cell indexed by `c`. -/
private abbrev prodCellIsometry {n : ℕ} (c : ProdCell C D n) :
    (Fin n → ℝ) ≃ᵢ (Fin c.1.1.1 → ℝ) × (Fin c.1.1.2 → ℝ) :=
  (Fin.appendIsometryOfEq (Finset.mem_antidiagonal.1 c.1.2)).symm

/-- The characteristic map of a product cell: the product of the characteristic maps of the two
factors, after splitting the coordinates. -/
private def prodCellMap {n : ℕ} (c : ProdCell C D n) : PartialEquiv (Fin n → ℝ) (X × Y) :=
  (prodCellIsometry c).toEquiv.transPartialEquiv ((map _ c.2.1).prod (map _ c.2.2))

private theorem prodCellMap_apply {n : ℕ} (c : ProdCell C D n) (x : Fin n → ℝ) :
    prodCellMap c x = Prod.map (map _ c.2.1) (map _ c.2.2) (prodCellIsometry c x) :=
  (rfl)

private theorem prodCellIsometry_zero {n : ℕ} (c : ProdCell C D n) :
    prodCellIsometry c 0 = 0 := by
  ext <;> simp

private theorem image_prodCellMap {n : ℕ} (c : ProdCell C D n) (s : Set (Fin n → ℝ)) :
    prodCellMap c '' s = Prod.map (map _ c.2.1) (map _ c.2.2) '' (prodCellIsometry c '' s) := by
  rw [image_image]
  exact image_congr fun x _ ↦ prodCellMap_apply c x

private theorem image_ball_prodCellMap {n : ℕ} (c : ProdCell C D n) :
    prodCellMap c '' ball 0 1 = openCell _ c.2.1 ×ˢ openCell _ c.2.2 := by
  rw [image_prodCellMap, IsometryEquiv.image_ball, prodCellIsometry_zero, Prod.zero_eq_mk,
    ← ball_prod_same, prodMap_image_prod, openCell, openCell]

private theorem image_closedBall_prodCellMap {n : ℕ} (c : ProdCell C D n) :
    prodCellMap c '' closedBall 0 1 = closedCell _ c.2.1 ×ˢ closedCell _ c.2.2 := by
  rw [image_prodCellMap, IsometryEquiv.image_closedBall, prodCellIsometry_zero, Prod.zero_eq_mk,
    ← closedBall_prod_same, prodMap_image_prod, closedCell, closedCell]

/-- The product cells of a given dimension form a finite type when `C` and `D` have finitely
many cells in every dimension. -/
private theorem finite_prodCell [RelCWComplex.Finite C] [RelCWComplex.Finite D] (n : ℕ) :
    _root_.Finite (ProdCell C D n) :=
  have (p : ℕ) : _root_.Finite (cell C p) := FiniteType.finite_cell p
  have (q : ℕ) : _root_.Finite (cell D q) := FiniteType.finite_cell q
  inferInstance

/-- There are no product cells in dimensions where every splitting has an empty factor. -/
private theorem eventually_isEmpty_prodCell [RelCWComplex.Finite C] [RelCWComplex.Finite D] :
    ∀ᶠ n in Filter.atTop, IsEmpty (ProdCell C D n) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅)).and
      (FiniteDimensional.eventually_isEmpty_cell (C := D) (D := ∅)))
  refine Filter.eventually_atTop.2 ⟨N + N, fun n hn ↦ ⟨fun ⟨⟨⟨p, q⟩, hpq⟩, i, j⟩ ↦ ?_⟩⟩
  rw [Finset.mem_antidiagonal] at hpq
  rcases le_total N p with hp | hp
  · exact (hN p hp).1.false i
  · exact (hN q (by omega)).2.false j

/-- Two product cells with intersecting open cells are equal. -/
private theorem pairwiseDisjoint_prodCellMap :
    (univ : Set (Σ n, ProdCell C D n)).PairwiseDisjoint
      (fun c ↦ prodCellMap c.2 '' ball 0 1) := by
  rintro ⟨n, ⟨⟨p, q⟩, hpq⟩, i, j⟩ - ⟨n', ⟨⟨p', q'⟩, hpq'⟩, i', j'⟩ - hne
  simp only [Function.onFun, image_ball_prodCellMap]
  refine disjoint_prod.2 (by_contra fun h ↦ hne ?_)
  rw [not_or] at h
  obtain ⟨rfl, hi⟩ := Sigma.mk.inj_iff.1 (not_not.1 (mt disjoint_openCell_of_ne h.1))
  obtain ⟨rfl, hj⟩ := Sigma.mk.inj_iff.1 (not_not.1 (mt disjoint_openCell_of_ne h.2))
  obtain rfl := eq_of_heq hi
  obtain rfl := eq_of_heq hj
  obtain rfl := (Finset.mem_antidiagonal.1 hpq).symm.trans (Finset.mem_antidiagonal.1 hpq')
  rfl

private theorem prodCellIsometry_mem_closedBall {n : ℕ} (c : ProdCell C D n) {x : Fin n → ℝ}
    (hx : x ∈ closedBall 0 1) : prodCellIsometry c x ∈ closedBall 0 1 ×ˢ closedBall 0 1 := by
  rwa [closedBall_prod_same, ← Prod.zero_eq_mk, ← prodCellIsometry_zero c, mem_closedBall,
    IsometryEquiv.dist_eq]

/-- The boundary of a product cell lies in the product cells of smaller dimension. -/
private theorem mapsTo_prodCellMap (n : ℕ) (c : ProdCell C D n) :
    MapsTo (prodCellMap c) (sphere 0 1)
      (⋃ (m < n) (c' : ProdCell C D m), prodCellMap c' '' closedBall 0 1) := by
  obtain ⟨⟨⟨p, q⟩, hpq⟩, i, j⟩ := c
  rw [Finset.mem_antidiagonal] at hpq
  intro x hx
  have hx' : prodCellIsometry ⟨⟨(p, q), _⟩, i, j⟩ x ∈ sphere 0 1 := by
    rwa [mem_sphere, ← prodCellIsometry_zero ⟨⟨(p, q), _⟩, i, j⟩, IsometryEquiv.dist_eq]
  rw [prodCellMap_apply]
  set y := prodCellIsometry ⟨⟨(p, q), _⟩, i, j⟩ x
  simp only [sphere_prod, Prod.fst_zero, Prod.snd_zero, mem_union, mem_prod] at hx'
  rcases hx' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · -- The first coordinate lies on the boundary of the `p`-cell of `C`.
    obtain ⟨I, hI⟩ := CWComplex.cellFrontier_subset_finite_closedCell p i
    obtain ⟨m, hm, k, -, hk⟩ := by simpa using hI (mem_image_of_mem _ h₁)
    refine mem_iUnion₂.2 ⟨m + q, by omega, mem_iUnion.2 ⟨⟨⟨(m, q), by simp⟩, k, j⟩, ?_⟩⟩
    rw [image_closedBall_prodCellMap]
    exact ⟨hk, y.2, h₂, rfl⟩
  · -- The second coordinate lies on the boundary of the `q`-cell of `D`.
    obtain ⟨I, hI⟩ := CWComplex.cellFrontier_subset_finite_closedCell q j
    obtain ⟨m, hm, k, -, hk⟩ := by simpa using hI (mem_image_of_mem _ h₂)
    refine mem_iUnion₂.2 ⟨p + m, by omega, mem_iUnion.2 ⟨⟨⟨(p, m), by simp⟩, i, k⟩, ?_⟩⟩
    rw [image_closedBall_prodCellMap]
    exact ⟨⟨y.1, h₁, rfl⟩, hk⟩

/-- The closed product cells cover `C ×ˢ D`. -/
private theorem iUnion_prodCellMap :
    ⋃ (n : ℕ) (c : ProdCell C D n), prodCellMap c '' closedBall 0 1 = C ×ˢ D := by
  simp_rw [image_closedBall_prodCellMap]
  conv_rhs => rw [← CWComplex.union (C := C), ← CWComplex.union (C := D)]
  ext ⟨x, y⟩
  simp only [mem_iUnion, mem_prod]
  constructor
  · rintro ⟨n, ⟨⟨⟨p, q⟩, _⟩, i, j⟩, hx, hy⟩
    exact ⟨⟨p, i, hx⟩, q, j, hy⟩
  · rintro ⟨⟨p, i, hx⟩, q, j, hy⟩
    exact ⟨p + q, ⟨⟨(p, q), Finset.mem_antidiagonal.2 rfl⟩, i, j⟩, hx, hy⟩

section

variable [RelCWComplex.Finite C] [RelCWComplex.Finite D]

/-- **The product of two finite CW complexes.**  The `n`-cells of `C ×ˢ D` are the pairs of a
`p`-cell of `C` and a `q`-cell of `D` with `p + q = n` (`TauCeti.cellProdEquiv`), and the
characteristic map of such a pair is the product of the characteristic maps after the isometry
`Fin.appendIsometryOfEq : (Fin p → ℝ) × (Fin q → ℝ) ≃ᵢ (Fin n → ℝ)`. -/
@[instance_reducible]
def cwComplexProd : CWComplex (C ×ˢ D) :=
  CWComplex.mkFinite (C ×ˢ D) (ProdCell C D) (fun _ c ↦ prodCellMap c)
    eventually_isEmpty_prodCell finite_prodCell
    (fun _ c ↦ by
      rw [prodCellMap, Equiv.transPartialEquiv_source, PartialEquiv.prod_source, source_eq,
        source_eq, ball_prod_same, ← Prod.zero_eq_mk, ← prodCellIsometry_zero c]
      exact ((prodCellIsometry c).preimage_ball _ _).trans
        (by rw [IsometryEquiv.symm_apply_apply]))
    (fun _ c ↦ ((continuousOn _ c.2.1).prodMap (continuousOn _ c.2.2)).comp
      (prodCellIsometry c).continuous.continuousOn fun _ ↦ prodCellIsometry_mem_closedBall c)
    (fun _ c ↦ (prodCellIsometry c).symm.continuous.comp_continuousOn
      ((continuousOn_symm _ c.2.1).prodMap (continuousOn_symm _ c.2.2)))
    pairwiseDisjoint_prodCellMap mapsTo_prodCellMap iUnion_prodCellMap

attribute [instance] cwComplexProd

/-- The product of two finite CW complexes is finite. -/
instance finite_cwComplexProd : RelCWComplex.Finite (C ×ˢ D) where
  eventually_isEmpty_cell := eventually_isEmpty_prodCell
  finite_cell := finite_prodCell

/-- The `n`-cells of `C ×ˢ D` are the pairs of a `p`-cell of `C` and a `q`-cell of `D` with
`p + q = n`. -/
def cellProdEquiv (n : ℕ) :
    cell (C ×ˢ D) n ≃ Σ pq : Finset.antidiagonal n, cell C pq.1.1 × cell D pq.1.2 :=
  Equiv.refl _

variable {n : ℕ} (c : Σ pq : Finset.antidiagonal n, cell C pq.1.1 × cell D pq.1.2)

/-- The characteristic maps of `TauCeti.cwComplexProd` are the maps `prodCellMap`, by
construction (`Topology.CWComplex.mkFinite` takes the supplied family as its `map` field). -/
private theorem map_cellProdEquiv_symm : map n ((cellProdEquiv n).symm c) = prodCellMap c :=
  (rfl)

/-- The characteristic map of a product cell is the product of the characteristic maps of its
factors, after splitting the coordinates of `Fin n → ℝ` into `(Fin p → ℝ) × (Fin q → ℝ)`. -/
theorem map_cellProdEquiv_symm_appendIsometryOfEq (x : Fin c.1.1.1 → ℝ) (y : Fin c.1.1.2 → ℝ) :
    map n ((cellProdEquiv n).symm c)
        (Fin.appendIsometryOfEq (Finset.mem_antidiagonal.1 c.1.2) (x, y)) =
      (map _ c.2.1 x, map _ c.2.2 y) := by
  rw [map_cellProdEquiv_symm, prodCellMap_apply,
    IsometryEquiv.symm_apply_apply, Prod.map_apply]

/-- The open product cell is the product of the open cells of its factors. -/
@[simp]
theorem openCell_cellProdEquiv_symm :
    openCell n ((cellProdEquiv n).symm c) = openCell _ c.2.1 ×ˢ openCell _ c.2.2 :=
  image_ball_prodCellMap c

/-- The closed product cell is the product of the closed cells of its factors. -/
@[simp]
theorem closedCell_cellProdEquiv_symm :
    closedCell n ((cellProdEquiv n).symm c) = closedCell _ c.2.1 ×ˢ closedCell _ c.2.2 :=
  image_closedBall_prodCellMap c

/-- The boundary of a product cell `e × e'` is `∂e × e' ∪ e × ∂e'`. -/
@[simp]
theorem cellFrontier_cellProdEquiv_symm :
    cellFrontier n ((cellProdEquiv n).symm c) =
      cellFrontier _ c.2.1 ×ˢ closedCell _ c.2.2 ∪ closedCell _ c.2.1 ×ˢ cellFrontier _ c.2.2 := by
  rw [cellFrontier, map_cellProdEquiv_symm,
    image_prodCellMap, IsometryEquiv.image_sphere, prodCellIsometry_zero, sphere_prod,
    image_union, Prod.fst_zero, Prod.snd_zero, prodMap_image_prod, prodMap_image_prod,
    cellFrontier, cellFrontier, closedCell, closedCell]

omit c in
/-- The number of `n`-cells of `C ×ˢ D` is `∑_{p + q = n} #(p-cells of C) · #(q-cells of D)`. -/
theorem nat_card_cell_prod (n : ℕ) :
    Nat.card (cell (C ×ˢ D) n) =
      ∑ pq ∈ Finset.antidiagonal n, Nat.card (cell C pq.1) * Nat.card (cell D pq.2) := by
  have (p : ℕ) : _root_.Finite (cell C p) := FiniteType.finite_cell p
  have (q : ℕ) : _root_.Finite (cell D q) := FiniteType.finite_cell q
  rw [Nat.card_congr (cellProdEquiv n), Nat.card_sigma]
  simp only [Nat.card_prod]
  exact Finset.sum_coe_sort (Finset.antidiagonal n)
    fun pq ↦ Nat.card (cell C pq.1) * Nat.card (cell D pq.2)

end

/-- A product of two spaces of finite CW type has finite CW type: it is homotopy equivalent to the
product of finite CW complexes modelling the factors. -/
instance FiniteCWType.prod [hX : FiniteCWType X] [hY : FiniteCWType Y] :
    FiniteCWType (X × Y) := by
  obtain ⟨X', _, _, C, _, _, ⟨e⟩⟩ := hX.exists_homotopyEquiv
  obtain ⟨Y', _, _, D, _, _, ⟨f⟩⟩ := hY.exists_homotopyEquiv
  exact ((e.prodCongr f).trans (Homeomorph.Set.prod C D).symm.toHomotopyEquiv).finiteCWType

/-- A finite product of spaces of finite CW type has finite CW type. -/
instance FiniteCWType.pi {ι : Type v} [Finite ι] (X : ι → Type u) [∀ i, TopologicalSpace (X i)]
    [∀ i, FiniteCWType (X i)] : FiniteCWType (∀ i, X i) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih => exact (Homeomorph.piCongrLeft (Y := X) e).symm.finiteCWType
  | h_empty => infer_instance
  | h_option ih => exact (piOptionEquivProdHomeomorph X).finiteCWType

end TauCeti
