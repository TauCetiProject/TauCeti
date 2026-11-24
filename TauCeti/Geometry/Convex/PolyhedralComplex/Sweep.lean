/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Sweep.Exceptional
public import TauCeti.Geometry.Convex.PolyhedralComplex.Map

/-!
# Sweep exceptions for a polyhedral skeleton

For a finite set of directions, the affine spans of the sweeps of the
cells of codimension at least a threshold `k ≥ 2` form an exceptional arrangement.
A base point outside that arrangement has its full line in every specified direction
disjoint from each of those cell spans and hence from the skeleton. Directions may
be combined, restricted, or transported by integral affine equivalences.

Adapted from `Mei/Geometry/Convex/PolyhedralComplex/Discriminant.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0).
-/

public section

namespace TauCeti.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : Toric.IsIntegralLattice i}

/-- The arrangement of affine spans of sweeps of cells of codimension at least `k`
in the specified directions. Zero and tangent directions are allowed. -/
noncomputable def codimensionGESweepExceptions (C : FinitePolyhedralComplex h) {k : ℕ}
    (hk : 2 ≤ k) (vectors : Finset V) : ExceptionalArrangement ℝ V :=
  ExceptionalArrangement.ofSweeps ((C.codimensionGE k).cells ×ˢ vectors) (by
    intro z hz _
    have hd := (mem_cells_codimensionGE.mp (Finset.mem_product.mp hz).1).2
    rw [← direction_affineSpan]
    omega)

/-- Genericity means that the line in each specified direction misses the
affine span of every cell in the codimension-`k` skeleton. -/
@[simp]
theorem isGeneric_codimensionGESweepExceptions_iff {C : FinitePolyhedralComplex h} {k : ℕ}
    {hk : 2 ≤ k} {vectors : Finset V} {x : V} :
    (C.codimensionGESweepExceptions hk vectors).IsGeneric x ↔
      ∀ P ∈ (C.codimensionGE k).cells, ∀ v ∈ vectors, ∀ t : ℝ, x + t • v ∉ affineSpan ℝ P := by
  rw [codimensionGESweepExceptions, ExceptionalArrangement.isGeneric_ofSweeps_iff]
  constructor
  · intro hx P hP v hv t
    exact hx (P, v) (Finset.mem_product.mpr ⟨hP, hv⟩) t
  · rintro hx ⟨P, v⟩ hz t
    obtain ⟨hP, hv⟩ := Finset.mem_product.mp hz
    exact hx P hP v hv t

/-- A full line in a prescribed direction avoids the support of the codimension-`k`
skeleton when its base point is outside the sweep arrangement for those directions. -/
theorem add_smul_notMem_support_codimensionGE {C : FinitePolyhedralComplex h}
    {k : ℕ} {hk : 2 ≤ k} {vectors : Finset V} {x v : V}
    (hx : (C.codimensionGESweepExceptions hk vectors).IsGeneric x)
    (hv : v ∈ vectors) (t : ℝ) : x + t • v ∉ (C.codimensionGE k).support := by
  intro ht
  obtain ⟨P, hP, htP⟩ := mem_support.mp ht
  exact isGeneric_codimensionGESweepExceptions_iff.mp hx P hP v hv t (subset_affineSpan ℝ P htP)

/-- Sweeping in a union of directions combines the two arrangements. -/
@[simp]
theorem codimensionGESweepExceptions_union [DecidableEq V]
    (C : FinitePolyhedralComplex h) {k : ℕ}
    (hk : 2 ≤ k) (S T : Finset V) :
    C.codimensionGESweepExceptions hk (S ∪ T) =
      (C.codimensionGESweepExceptions hk S).union (C.codimensionGESweepExceptions hk T) := by
  classical
  apply ExceptionalArrangement.ext
  simp only [codimensionGESweepExceptions, ExceptionalArrangement.exceptions_ofSweeps,
    ExceptionalArrangement.exceptions_union, Finset.product_union, Finset.image_union]

/-- Genericity is preserved when restricting to a subcomplex and a subset of the directions. -/
theorem IsSubcomplex.isGeneric_codimensionGESweepExceptions {C D : FinitePolyhedralComplex h}
    (hDC : D.IsSubcomplex C) {k : ℕ} {hk : 2 ≤ k} {S T : Finset V}
    (hST : S ⊆ T) {x : V} (hx : (C.codimensionGESweepExceptions hk T).IsGeneric x) :
    (D.codimensionGESweepExceptions hk S).IsGeneric x := by
  rw [isGeneric_codimensionGESweepExceptions_iff] at hx ⊢
  intro P hP v hv t
  exact hx P (isSubcomplex_iff.mp (hDC.codimensionGE k) hP) v (hST hv) t

variable {N' W : Type*} [AddCommGroup N'] [NormedAddCommGroup W] [NormedSpace ℝ W]
  {i' : N' →+ W} {h' : Toric.IsIntegralLattice i'}

/-- Affine transport sends the sweep arrangement to the arrangement of the transported
cells and the directions mapped by the linear part. -/
theorem codimensionGESweepExceptions_image [DecidableEq W] (C : FinitePolyhedralComplex h)
    (e : Toric.IntegralAffineEquiv h h') {k : ℕ} (hk : 2 ≤ k) (vectors : Finset V) :
    (C.image e).codimensionGESweepExceptions hk (vectors.image e.toAffineEquiv.linear) =
      (C.codimensionGESweepExceptions hk vectors).map e.toAffineEquiv := by
  classical
  have hcells : ((C.image e).codimensionGE k).cells =
      ((C.codimensionGE k).cells).image (e '' ·) := by
    rw [codimensionGE_image]
    ext P
    simp only [mem_cells_image, Finset.mem_image]
  apply ExceptionalArrangement.ext
  simp only [codimensionGESweepExceptions, ExceptionalArrangement.exceptions_ofSweeps,
    ExceptionalArrangement.exceptions_map, hcells, ← Finset.prodMap_image_product,
    Finset.image_image]
  apply Finset.image_congr
  rintro ⟨P, v⟩ _
  simp only [Function.comp_apply, Prod.map_apply, AffineSubspace.map_span,
    AffineEquiv.coe_toAffineMap]
  have hsweep := congrArg (affineSpan ℝ) (Set.image_sweep e.toAffineEquiv.toAffineMap P v).symm
  rw [AffineEquiv.coe_toAffineMap, AffineEquiv.linear_toAffineMap] at hsweep
  exact hsweep

end TauCeti.FinitePolyhedralComplex
