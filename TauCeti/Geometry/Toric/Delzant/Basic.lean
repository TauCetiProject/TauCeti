/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Algebra.Module.Primitive
public import TauCeti.Analysis.Convex.Polyhedron.Extreme

import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Delzant polytopes

Let `i : N →+ V` be an integral lattice (`TauCeti.Toric.IsIntegralLattice`) in a real normed
space `V`, the Lie algebra of a torus with integral cocharacters `N`. A finite family of
*inward facet normals* `u : ι → N` and *support constants* `c : ι → ℝ` cut out the polyhedron

`Δ = {x ∈ V* | c j ≤ ⟨x, u j⟩ for every j}`

(`TauCeti.Toric.facetPolyhedron i u c`) in the dual space `V*`, where the moment map of a
Hamiltonian torus action takes its values. A constraint `j` is *active* at `x` when
`⟨x, u j⟩ = c j`; the active constraints at `x` are
`TauCeti.activeSet (TauCeti.Toric.facetPairing i u) c x`.

A point `x` is a *smooth vertex* (`TauCeti.Toric.IsSmoothVertex`) when the normals of the
constraints active at `x` form a basis of the lattice `N`. The presentation is *Delzant*
(`TauCeti.Toric.IsDelzant`) when `Δ` is bounded, each of its vertices (extreme points) is smooth,
and it is irredundant: for each `j` some point of `Δ` has `j` as its only active constraint, so
that `j` contributes a facet of `Δ`, the facets are listed without repetition, and `u j` is the
inward normal of that facet. These are the moment polytopes of compact symplectic toric
manifolds. Smoothness at a vertex includes simplicity: exactly `rank N` facets meet at each
vertex (`TauCeti.Toric.IsSmoothVertex.ncard_activeSet`), and `rank N = dim V` for an integral
lattice (`TauCeti.Toric.IsIntegralLattice.finrank_eq`).

The vertices of `Δ` are the points where the active normals span `V`, by the description of the
extreme points of a polyhedron (`TauCeti.mem_extremePoints_polyhedron_iff`). The face of a
compact facet polyhedron, such as a Delzant polytope, cut out by the constraints active at any of
its points is nonempty and compact, so it contains a vertex, at which all those constraints are
active (`TauCeti.Toric.exists_mem_extremePoints_activeSet_subset`). In particular each
facet contains a vertex; at that vertex its normal belongs to a lattice basis. Hence every facet
normal is primitive (`TauCeti.Toric.IsDelzant.isPrimitive`): the facet normals are the primitive
inward normals.
When the lattice map is injective, a Delzant polytope also has a point on none of its facets
(`TauCeti.Toric.IsDelzant.exists_activeSet_eq_empty`): with at least two facets, the barycentre
of points lying only on one facet each; with a single facet, such a point pushed off it.

Translating the polytope by `y ∈ V*` changes the support constants to `c j + ⟨y, u j⟩` and keeps
the normals (`TauCeti.Toric.facetPolyhedron_add`). It preserves the active constraints, hence
smoothness of vertices and the Delzant property (`TauCeti.Toric.isDelzant_add_iff`). This is the
freedom of shifting a moment map by a constant.

## Main definitions

* `TauCeti.Toric.facetPairing i u j`: the linear functional `x ↦ ⟨x, u j⟩` on `V*`.
* `TauCeti.Toric.facetPolyhedron i u c`: the polyhedron `{x | ∀ j, c j ≤ ⟨x, u j⟩}`.
* `TauCeti.Toric.IsSmoothVertex i u c x`: the active normals at `x` form a basis of `N`.
* `TauCeti.Toric.IsDelzant i u c`: the presentation describes a Delzant polytope.

## Main results

* `TauCeti.Toric.IsDelzant.isCompact`: a Delzant polytope is compact.
* `TauCeti.Toric.IsDelzant.extremePoints_nonempty`: a Delzant polytope has a vertex.
* `TauCeti.Toric.exists_mem_extremePoints_activeSet_subset`: the constraints active at a point of
  a compact facet polyhedron are active at some vertex.
* `TauCeti.Toric.isSmoothVertex_iff_linearIndepOn`: a smooth vertex is a point whose active
  normals are linearly independent and generate the lattice.
* `TauCeti.Toric.IsSmoothVertex.ncard_activeSet`: exactly `rank N` facets meet at a smooth vertex.
* `TauCeti.Toric.IsDelzant.isPrimitive`: the facet normals of a Delzant polytope are primitive.
* `TauCeti.Toric.IsDelzant.exists_activeSet_eq_empty`: for an injective lattice map, a Delzant
  polytope has a point on none of its facets.
* `TauCeti.Toric.facetPolyhedron_add`, `TauCeti.Toric.isDelzant_add_iff`: translations.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 28.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 1.
-/

public section

noncomputable section

open Set Pointwise

namespace TauCeti.Toric

variable {ι N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  (i : N →+ V) (u : ι → N) (c : ι → ℝ)

/-- The pairing `x ↦ ⟨x, u j⟩` of a point of the dual space `V*` with the `j`-th facet normal. -/
def facetPairing (j : ι) : Module.Dual ℝ (StrongDual ℝ V) :=
  (ContinuousLinearMap.apply ℝ ℝ (i (u j)) : StrongDual ℝ V →ₗ[ℝ] ℝ)

@[simp]
theorem facetPairing_apply (j : ι) (x : StrongDual ℝ V) : facetPairing i u j x = x (i (u j)) :=
  (rfl)

/-- The polyhedron `{x ∈ V* | ∀ j, c j ≤ ⟨x, u j⟩}` cut out by the half-spaces with inward
normals `u j` and support constants `c j`. -/
def facetPolyhedron : Set (StrongDual ℝ V) :=
  polyhedron (facetPairing i u) c

/-- A point `x` of `V*` is a *smooth vertex* of the facet presentation when the normals of the
constraints active at `x` form a basis of the lattice `N`. -/
def IsSmoothVertex (x : StrongDual ℝ V) : Prop :=
  ∃ b : Module.Basis (activeSet (facetPairing i u) c x) ℤ N, ∀ j, b j = u j

/-- The facet presentation `(u, c)` in the integral lattice `i : N →+ V` describes a *Delzant
polytope*: the polyhedron is bounded, the active normals at each vertex form a basis of `N`, and
each constraint is the only active one at some point of the polyhedron, so that it contributes a
facet. -/
structure IsDelzant : Prop where
  /-- The polyhedron is bounded, hence a polytope. -/
  isBounded : Bornology.IsBounded (facetPolyhedron i u c)
  /-- At each vertex, the active normals form a basis of the lattice. -/
  isSmoothVertex : ∀ x ∈ (facetPolyhedron i u c).extremePoints ℝ, IsSmoothVertex i u c x
  /-- Each constraint is the only active one at some point of the polyhedron. -/
  irredundant : ∀ j, ∃ x ∈ facetPolyhedron i u c, activeSet (facetPairing i u) c x = {j}

variable {i u c}

@[simp]
theorem mem_facetPolyhedron {x : StrongDual ℝ V} :
    x ∈ facetPolyhedron i u c ↔ ∀ j, c j ≤ x (i (u j)) := by
  simp [facetPolyhedron]

theorem isSmoothVertex_def {x : StrongDual ℝ V} :
    IsSmoothVertex i u c x ↔
      ∃ b : Module.Basis (activeSet (facetPairing i u) c x) ℤ N, ∀ j, b j = u j :=
  Iff.rfl

/-- A point is a smooth vertex exactly when the active normals are linearly independent and
generate the lattice. -/
theorem isSmoothVertex_iff_linearIndepOn {x : StrongDual ℝ V} :
    IsSmoothVertex i u c x ↔ LinearIndepOn ℤ u (activeSet (facetPairing i u) c x) ∧
      Submodule.span ℤ (u '' activeSet (facetPairing i u) c x) = ⊤ := by
  rw [isSmoothVertex_def, Set.image_eq_range]
  constructor
  · rintro ⟨b, hb⟩
    have hbu : (⇑b : activeSet (facetPairing i u) c x → N) =
        fun j : activeSet (facetPairing i u) c x ↦ u j := funext hb
    refine ⟨?_, hbu ▸ b.span_eq⟩
    rw [LinearIndepOn, ← hbu]
    exact b.linearIndependent
  · rintro ⟨hli, hsp⟩
    exact ⟨Module.Basis.mk hli hsp.ge, Module.Basis.mk_apply hli hsp.ge⟩

theorem convex_facetPolyhedron : Convex ℝ (facetPolyhedron i u c) :=
  convex_polyhedron

theorem isClosed_facetPolyhedron : IsClosed (facetPolyhedron i u c) := by
  have : facetPolyhedron i u c = ⋂ j, {x : StrongDual ℝ V | c j ≤ x (i (u j))} := by
    ext; simp
  rw [this]
  exact isClosed_iInter fun j ↦
    isClosed_le continuous_const (ContinuousLinearMap.apply ℝ ℝ (i (u j))).continuous

/-- **Vertices of a facet polyhedron.** A point `x` of the polyhedron is a vertex exactly when
no nonzero point of `V*` vanishes on all the normals active at `x`. -/
theorem mem_extremePoints_facetPolyhedron_iff [Finite ι] {x : StrongDual ℝ V} :
    x ∈ (facetPolyhedron i u c).extremePoints ℝ ↔ x ∈ facetPolyhedron i u c ∧
      ∀ w : StrongDual ℝ V, (∀ j ∈ activeSet (facetPairing i u) c x, w (i (u j)) = 0) → w = 0 := by
  unfold facetPolyhedron
  exact mem_extremePoints_polyhedron_iff

/-- Exactly `rank N` facets meet at a smooth vertex. -/
theorem IsSmoothVertex.ncard_activeSet {x : StrongDual ℝ V} (hx : IsSmoothVertex i u c x) :
    (activeSet (facetPairing i u) c x).ncard = Module.finrank ℤ N := by
  obtain ⟨b, -⟩ := hx
  rw [Module.finrank_eq_nat_card_basis b, Nat.card_coe_set_eq]

/-- Every point `x` of a compact facet polyhedron lies on the face cut out by its active
constraints, and this face contains a vertex: the constraints active at `x` are active at some
vertex. -/
theorem exists_mem_extremePoints_activeSet_subset (hc : IsCompact (facetPolyhedron i u c))
    {x : StrongDual ℝ V} (hx : x ∈ facetPolyhedron i u c) :
    ∃ v ∈ (facetPolyhedron i u c).extremePoints ℝ,
      activeSet (facetPairing i u) c x ⊆ activeSet (facetPairing i u) c v := by
  set s := activeSet (facetPairing i u) c x
  have hF := isExtreme_polyhedron_inter_setOf_subset_activeSet (f := facetPairing i u) (c := c) s
  have hclosed : IsClosed {y : StrongDual ℝ V | s ⊆ activeSet (facetPairing i u) c y} := by
    simp only [Set.subset_def, mem_activeSet, facetPairing_apply, ofPred_forall]
    exact isClosed_biInter fun j _ ↦
      isClosed_eq (ContinuousLinearMap.apply ℝ ℝ (i (u j))).continuous continuous_const
  obtain ⟨v, hv⟩ := (hc.inter_right hclosed).extremePoints_nonempty ⟨x, hx, Set.Subset.rfl⟩
  exact ⟨v, hF.extremePoints_subset_extremePoints hv, (extremePoints_subset hv).2⟩

namespace IsDelzant

variable (hΔ : IsDelzant i u c)
include hΔ

/-- A Delzant polytope is nonempty. -/
theorem nonempty : (facetPolyhedron i u c).Nonempty := by
  cases isEmpty_or_nonempty ι with
  | inl _ => exact ⟨0, mem_facetPolyhedron.2 fun j ↦ isEmptyElim j⟩
  | inr h =>
    obtain ⟨x, hx, -⟩ := hΔ.irredundant h.some
    exact ⟨x, hx⟩

variable [FiniteDimensional ℝ V]

/-- A Delzant polytope is compact. -/
theorem isCompact : IsCompact (facetPolyhedron i u c) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_facetPolyhedron hΔ.isBounded

/-- A Delzant polytope has a vertex. -/
theorem extremePoints_nonempty : ((facetPolyhedron i u c).extremePoints ℝ).Nonempty :=
  hΔ.isCompact.extremePoints_nonempty hΔ.nonempty

/-- Every facet of a Delzant polytope contains a vertex. -/
theorem exists_mem_extremePoints_mem_activeSet (j : ι) :
    ∃ x ∈ (facetPolyhedron i u c).extremePoints ℝ, j ∈ activeSet (facetPairing i u) c x := by
  obtain ⟨x, hx, hxj⟩ := hΔ.irredundant j
  obtain ⟨v, hv, hsub⟩ := exists_mem_extremePoints_activeSet_subset hΔ.isCompact hx
  exact ⟨v, hv, hsub (hxj ▸ mem_singleton j)⟩

/-- The facet normals of a Delzant polytope are primitive lattice vectors. -/
theorem isPrimitive (j : ι) : IsPrimitive (u j) := by
  obtain ⟨x, hx, hj⟩ := hΔ.exists_mem_extremePoints_mem_activeSet j
  obtain ⟨b, hb⟩ := hΔ.isSmoothVertex x hx
  simpa only [hb] using b.isPrimitive ⟨j, hj⟩

/-- **A Delzant polytope has an interior point.** For an injective lattice map, some point of a
Delzant polytope lies on none of its facets. -/
theorem exists_activeSet_eq_empty [Finite ι] (hi : Function.Injective i) :
    ∃ x ∈ facetPolyhedron i u c, activeSet (facetPairing i u) c x = ∅ := by
  choose x hx hxj using hΔ.irredundant
  have hslack : ∀ j k, j ≠ k → c j < x k (i (u j)) := fun j k hjk ↦
    (mem_facetPolyhedron.1 (hx k) j).lt_of_ne fun h ↦ hjk <| by
      simpa [hxj k] using (mem_activeSet.2 h.symm : j ∈ activeSet (facetPairing i u) c (x k))
  rcases subsingleton_or_nontrivial ι with hι | hι
  · obtain hι' | ⟨⟨j⟩⟩ := isEmpty_or_nonempty ι
    · exact ⟨0, mem_facetPolyhedron.2 isEmptyElim, eq_empty_of_isEmpty _⟩
    -- With a single facet `j`, move off it in a direction `w` with `⟨w, u j⟩ = 1`.
    obtain ⟨w, hw⟩ := SeparatingDual.exists_eq_one (R := ℝ)
      ((map_ne_zero_iff i hi).2 (hΔ.isPrimitive j).ne_zero)
    have hlt : ∀ k, c k < (x j + w) (i (u k)) := fun k ↦ by
      obtain rfl := Subsingleton.elim k j
      have := mem_facetPolyhedron.1 (hx k) k
      simp only [add_apply, hw]
      linarith
    exact ⟨x j + w, mem_facetPolyhedron.2 fun k ↦ (hlt k).le,
      eq_empty_of_forall_notMem fun k hk ↦ (hlt k).ne' (mem_activeSet.1 hk)⟩
  -- With at least two facets, the barycentre of the points `x k` lies on no facet.
  have := Fintype.ofFinite ι
  set n : ℝ := (Fintype.card ι : ℝ)
  have hn : 0 < n := Nat.cast_pos.2 Fintype.card_pos
  have hlt : ∀ j, c j < (n⁻¹ • ∑ k, x k) (i (u j)) := fun j ↦ by
    obtain ⟨k, hk⟩ := exists_ne j
    have hsum : ∑ _k : ι, c j < ∑ k, x k (i (u j)) :=
      Finset.sum_lt_sum (fun k _ ↦ mem_facetPolyhedron.1 (hx k) j) ⟨k, Finset.mem_univ _,
        hslack j k hk.symm⟩
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    simp only [smul_apply, sum_apply, smul_eq_mul]
    rwa [lt_inv_mul_iff₀ hn]
  exact ⟨_, mem_facetPolyhedron.2 fun j ↦ (hlt j).le,
    eq_empty_of_forall_notMem fun j hj ↦ (hlt j).ne' (mem_activeSet.1 hj)⟩

end IsDelzant

/-! ### Translations -/

section Translation

variable (y : StrongDual ℝ V)

/-- Translating a facet polyhedron by `y` changes the support constants by `⟨y, u j⟩`. -/
theorem facetPolyhedron_add :
    facetPolyhedron i u (fun j ↦ c j + y (i (u j))) = y +ᵥ facetPolyhedron i u c := by
  ext x
  simp [mem_vadd_set_iff_neg_vadd_mem, add_comm]

/-- Translation preserves the active constraints. -/
@[simp]
theorem activeSet_add (x : StrongDual ℝ V) :
    activeSet (facetPairing i u) (fun j ↦ c j + y (i (u j))) (y + x) =
      activeSet (facetPairing i u) c x := by
  ext j
  simp only [mem_activeSet, facetPairing_apply, add_apply]
  constructor <;> intro h <;> linarith

@[simp]
theorem isSmoothVertex_add_iff (x : StrongDual ℝ V) :
    IsSmoothVertex i u (fun j ↦ c j + y (i (u j))) (y + x) ↔ IsSmoothVertex i u c x := by
  rw [isSmoothVertex_def, isSmoothVertex_def, activeSet_add]

theorem add_mem_extremePoints_facetPolyhedron_iff (x : StrongDual ℝ V) :
    y + x ∈ (facetPolyhedron i u (fun j ↦ c j + y (i (u j)))).extremePoints ℝ ↔
      x ∈ (facetPolyhedron i u c).extremePoints ℝ := by
  rw [facetPolyhedron_add, ← image_vadd]
  simp only [mem_extremePoints, forall_mem_image, vadd_eq_add,
    (add_right_injective y).mem_set_image, mem_openSegment_translate, add_right_inj]

/-- Translating a facet presentation preserves the Delzant property. -/
theorem isDelzant_add_iff :
    IsDelzant i u (fun j ↦ c j + y (i (u j))) ↔ IsDelzant i u c := by
  constructor
  · intro h
    refine ⟨?_, fun x hx ↦ ?_, fun j ↦ ?_⟩
    · simpa [facetPolyhedron_add] using h.isBounded.vadd (-y)
    · exact (isSmoothVertex_add_iff y x).1
        (h.isSmoothVertex _ ((add_mem_extremePoints_facetPolyhedron_iff y x).2 hx))
    · obtain ⟨x, hx, hxj⟩ := h.irredundant j
      refine ⟨-y + x, ?_, ?_⟩
      · rwa [facetPolyhedron_add, mem_vadd_set_iff_neg_vadd_mem] at hx
      · rw [← activeSet_add y, add_neg_cancel_left, hxj]
  · intro h
    refine ⟨?_, fun x hx ↦ ?_, fun j ↦ ?_⟩
    · rw [facetPolyhedron_add]
      exact h.isBounded.vadd y
    · rw [← add_neg_cancel_left y x] at hx ⊢
      exact (isSmoothVertex_add_iff y _).2
        (h.isSmoothVertex _ ((add_mem_extremePoints_facetPolyhedron_iff y _).1 hx))
    · obtain ⟨x, hx, hxj⟩ := h.irredundant j
      refine ⟨y + x, ?_, by rw [activeSet_add, hxj]⟩
      rw [facetPolyhedron_add]
      exact vadd_mem_vadd_set hx

end Translation

end TauCeti.Toric
