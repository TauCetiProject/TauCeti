/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Sweep.Exceptional
public import TauCeti.Geometry.Convex.PolyhedralComplex.Map
public import TauCeti.Geometry.Convex.PolyhedralComplex.Skeleton

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

private theorem exceptionalArrangement_eq {E F : ExceptionalArrangement ℝ V}
    (he : E.exceptions = F.exceptions) : E = F := by
  cases E
  cases F
  cases he
  rfl

/-- Sweeping in a union of directions combines the two arrangements. -/
@[simp]
theorem codimensionGESweepExceptions_union [DecidableEq V]
    (C : FinitePolyhedralComplex h) {k : ℕ}
    (hk : 2 ≤ k) (S T : Finset V) :
    C.codimensionGESweepExceptions hk (S ∪ T) =
      (C.codimensionGESweepExceptions hk S).union (C.codimensionGESweepExceptions hk T) := by
  classical
  apply exceptionalArrangement_eq
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
  have hdim (P : Set V) : Module.finrank ℝ (affineSpan ℝ (e '' P)).direction =
      Module.finrank ℝ (affineSpan ℝ P).direction := by
    rw [← AffineEquiv.coe_toAffineMap, ← AffineSubspace.map_span, AffineSubspace.map_direction]
    exact e.toAffineEquiv.linear.finrank_map_eq _
  have hcells (Q : Set W) : Q ∈ ((C.image e).codimensionGE k).cells ↔
      ∃ P ∈ (C.codimensionGE k).cells, e '' P = Q := by
    simp only [mem_cells_codimensionGE, mem_cells_image]
    have hv := e.toAffineEquiv.linear.finrank_eq
    constructor
    · rintro ⟨⟨P, hP, rfl⟩, hcod⟩
      exact ⟨P, ⟨hP, by rwa [hdim, ← hv] at hcod⟩, rfl⟩
    · rintro ⟨P, ⟨hP, hcod⟩, rfl⟩
      exact ⟨⟨P, hP, rfl⟩, by rwa [hdim, ← hv]⟩
  have hsweep (P : Set V) (v : V) :
      affineSpan ℝ (Set.sweep ℝ (e '' P) (e.toAffineEquiv.linear v)) =
        (affineSpan ℝ (Set.sweep ℝ P v)).map e.toAffineEquiv.toAffineMap := by
    rw [AffineSubspace.map_span]
    congr 1
    have he (x : V) (t : ℝ) : e (x - t • v) = e x - t • e.toAffineEquiv.linear v := by
      simpa [sub_eq_add_neg, add_comm] using e.toAffineEquiv.map_vadd x (-(t • v))
    ext y
    simp only [Set.mem_image, Set.mem_sweep_iff_exists]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, t, ht, rfl⟩
      exact ⟨x - t • v, ⟨x, hx, t, ht, rfl⟩, he x t⟩
    · rintro ⟨_, ⟨x, hx, t, ht, rfl⟩, rfl⟩
      exact ⟨e x, ⟨x, hx, rfl⟩, t, ht, he x t⟩
  apply exceptionalArrangement_eq
  ext A
  simp only [codimensionGESweepExceptions, ExceptionalArrangement.exceptions_ofSweeps,
    ExceptionalArrangement.exceptions_map, Finset.image_image, Function.comp_apply,
    Finset.mem_image, Finset.mem_product, hcells]
  constructor
  · rintro ⟨⟨_, _⟩, ⟨⟨P, hP, rfl⟩, ⟨v, hv, rfl⟩⟩, rfl⟩
    exact ⟨(P, v), ⟨hP, hv⟩, (hsweep P v).symm⟩
  · rintro ⟨⟨P, v⟩, ⟨hP, hv⟩, rfl⟩
    exact ⟨(e '' P, e.toAffineEquiv.linear v), ⟨⟨P, hP, rfl⟩, ⟨v, hv, rfl⟩⟩, hsweep P v⟩

end TauCeti.FinitePolyhedralComplex
