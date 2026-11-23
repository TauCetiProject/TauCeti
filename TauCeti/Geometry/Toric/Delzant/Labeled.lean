/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Lattice.Basic
public import TauCeti.Geometry.Toric.Delzant.Interval

import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.LinearAlgebra.FreeModule.Int

/-!
# Labeled polytopes

Lerman and Tolman extend Delzant's classification of compact symplectic toric manifolds to
compact symplectic toric orbifolds. Their moment data are *labeled polytopes*: a rational simple
polytope together with a positive integer label `m j` on each facet. This file develops the
combinatorics of labels on facet presentations.

Let `i : N →+ V` be a lattice and `(u, c)` a facet presentation of the polyhedron
`Δ = {x ∈ V* | c j ≤ ⟨x, u j⟩ for every j}` (`TauCeti.Toric.facetPolyhedron`). The presentation is
*rational simple* (`TauCeti.Toric.IsRationalSimple`) when `Δ` is bounded, each constraint
contributes a facet, the inward normals are primitive, and exactly `rank N` facets meet at each
vertex. A Delzant presentation is rational simple (`TauCeti.Toric.IsDelzant.isRationalSimple`),
and a rational simple presentation is Delzant exactly when the normals of the facets meeting at
each vertex generate `N`, that is, when every vertex cone is unimodular
(`TauCeti.Toric.isDelzant_iff_isRationalSimple`).

Labels `m j` enter through the *labeled normals* `m j • u j`.

* **The polytope.** Rescaling each constraint by a positive label, `(m j • u j, m j * c j)`, cuts
  out the same polyhedron (`TauCeti.Toric.facetPolyhedron_nsmul`) with the same active constraints
  at every point (`TauCeti.Toric.activeSet_nsmul`), both in
  `TauCeti.Geometry.Toric.Delzant.Basic`.
* **Isotropy.** At a point `x`, the labeled normals of the active facets span the sublattice
  `TauCeti.Toric.labeledActiveLattice`. For a vertex `x` of a labeled polytope, the quotient
  `N ⧸ labeledActiveLattice` is the orbifold structure group over `x` of the toric orbifold that
  Lerman–Tolman's correspondence attaches to the labeled polytope; here it is studied
  combinatorially, without constructing the orbifold. When the active
  normals are linearly independent, its order is the product of the active labels times the index
  of the vertex cone lattice (`TauCeti.Toric.card_quotient_labeledActiveLattice`):

  `|N ⧸ span {m j • u j}| = (∏ m j) · |N ⧸ span {u j}|`,

  so it is finite at every vertex of a rational simple polytope with positive labels
  (`TauCeti.Toric.IsRationalSimple.finite_quotient_labeledActiveLattice`). At a smooth vertex,
  where the active normals form a basis `b` of `N`, the labeled lattice is spanned by the rescaled
  basis vectors (`TauCeti.Toric.labeledActiveLattice_eq_span_range_nsmul`), and
  `Module.Basis.quotientSpanNSMulEquiv` identifies the quotient with `Π j, ZMod (m j)`.
* **Smoothness.** By `TauCeti.Toric.isDelzant_nsmul_iff` in
  `TauCeti.Geometry.Toric.Delzant.Basic`, the labeled presentation is Delzant exactly when all
  labels are one and the unlabeled presentation is Delzant. For a labeled rational simple polytope
  this is Lerman–Tolman's criterion: it is smooth exactly when all labels are one and every vertex
  cone is unimodular (`TauCeti.Toric.IsRationalSimple.isDelzant_nsmul_iff`).

The interval `[0, a]` with labels `m 0` and `m 1` on its two endpoints is the labeled polytope of a
weighted projective line in Lerman–Tolman's correspondence. Its structure groups at the endpoints
have orders `m 0` and `m 1`
(`TauCeti.Toric.card_quotient_labeledActiveLattice_interval_of_eq_zero`,
`TauCeti.Toric.card_quotient_labeledActiveLattice_interval_of_eq`).

## Main definitions

* `TauCeti.Toric.IsRationalSimple`: a bounded irredundant facet presentation with primitive
  normals, with exactly `rank N` facets at each vertex.
* `TauCeti.Toric.labeledActiveLattice`: the sublattice spanned by the labeled normals of the
  facets active at a point.

## Main results

* `TauCeti.Toric.card_quotient_labeledActiveLattice`: the order of the structure group.
* `TauCeti.Toric.IsRationalSimple.linearIndepOn_activeSet`: at a vertex of a rational simple
  polytope in an integral lattice, the active normals are linearly independent.
* `TauCeti.Toric.IsRationalSimple.finite_quotient_labeledActiveLattice`: the structure groups at
  the vertices of a labeled polytope are finite.
* `TauCeti.Toric.isDelzant_iff_isRationalSimple`: Delzant means rational simple with unimodular
  vertex cones.
* `TauCeti.Toric.IsRationalSimple.isDelzant_nsmul_iff`: Lerman–Tolman's smoothness criterion for
  labeled polytopes.

## References

* E. Lerman and S. Tolman, *Hamiltonian torus actions on symplectic orbifolds and toric
  varieties*, Trans. Amer. Math. Soc. 349 (1997), 4201–4230, arXiv:dg-ga/9511008, Sections 1
  and 9.
* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
-/

public section

noncomputable section

open Set

namespace TauCeti.Toric

variable {ι N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {u : ι → N} {c : ι → ℝ}

/-! ### The isotropy lattice of a labeled vertex -/

section Lattice

variable (i u c) (m : ι → ℕ)

/-- The sublattice of `N` spanned by the labeled normals `m j • u j` of the constraints active at
`x`. At a vertex `x` of a labeled polytope, the quotient `N ⧸ labeledActiveLattice i u c m x` is
the orbifold structure group over `x` in Lerman–Tolman's correspondence between labeled polytopes
and compact symplectic toric orbifolds. -/
def labeledActiveLattice (x : StrongDual ℝ V) : Submodule ℤ N :=
  Submodule.span ℤ ((fun j ↦ m j • u j) '' activeSet (facetPairing i u) c x)

variable {i u c m}

theorem labeledActiveLattice_def (x : StrongDual ℝ V) :
    labeledActiveLattice i u c m x =
      Submodule.span ℤ ((fun j ↦ m j • u j) '' activeSet (facetPairing i u) c x) :=
  (rfl)

/-- With all labels one, the labeled lattice is spanned by the active normals. -/
@[simp]
theorem labeledActiveLattice_one (x : StrongDual ℝ V) :
    labeledActiveLattice i u c 1 x = Submodule.span ℤ (u '' activeSet (facetPairing i u) c x) := by
  simp [labeledActiveLattice_def]

/-- **The order of the structure group.** When the normals active at `x` are linearly independent,
the quotient of `N` by the labeled lattice has as many elements as the product of the active labels
times the quotient of `N` by the lattice of the vertex cone. -/
theorem card_quotient_labeledActiveLattice [Finite ι] {x : StrongDual ℝ V}
    (hu : LinearIndepOn ℤ u (activeSet (facetPairing i u) c x)) :
    Nat.card (N ⧸ labeledActiveLattice i u c m x) =
      (∏ᶠ j ∈ activeSet (facetPairing i u) c x, m j) *
        Nat.card (N ⧸ Submodule.span ℤ (u '' activeSet (facetPairing i u) c x)) := by
  set s := activeSet (facetPairing i u) c x
  have := Fintype.ofFinite s
  rw [labeledActiveLattice_def, image_eq_range, image_eq_range, ← finprod_set_coe_eq_finprod_mem,
    finprod_eq_prod_of_fintype]
  exact LinearIndependent.card_quotient_span_range_nsmul hu fun j : s ↦ m j

/-- At a smooth vertex, whose active normals form a lattice basis `b`, the labeled lattice is
spanned by the rescaled basis vectors `m j • b j`, so `Module.Basis.quotientSpanNSMulEquiv`
identifies the structure group with `Π j, ZMod (m j)`. -/
theorem labeledActiveLattice_eq_span_range_nsmul {x : StrongDual ℝ V}
    (b : Module.Basis (activeSet (facetPairing i u) c x) ℤ N) (hb : ∀ j, b j = u j) :
    labeledActiveLattice i u c m x =
      Submodule.span ℤ (range fun j : activeSet (facetPairing i u) c x ↦ m j • b j) := by
  simp [labeledActiveLattice_def, hb, image_eq_range]

/-- At a smooth vertex the structure group has as many elements as the product of the active
labels. -/
theorem IsSmoothVertex.card_quotient_labeledActiveLattice [Finite ι] {x : StrongDual ℝ V}
    (hx : IsSmoothVertex i u c x) :
    Nat.card (N ⧸ labeledActiveLattice i u c m x) =
      ∏ᶠ j ∈ activeSet (facetPairing i u) c x, m j := by
  obtain ⟨hu, hspan⟩ := isSmoothVertex_iff_linearIndepOn.1 hx
  rw [TauCeti.Toric.card_quotient_labeledActiveLattice hu, hspan]
  simp

end Lattice

/-! ### Rational simple polytopes -/

section RationalSimple

variable (i u c)

/-- The facet presentation `(u, c)` in the lattice `i : N →+ V` describes a *rational simple
polytope*: the polyhedron is bounded, each constraint is the only active one at some point of the
polyhedron, the inward normals are primitive lattice vectors, and exactly `rank N` facets meet at
each vertex. With a positive integer label on each facet it is a *labeled polytope* in the sense of
Lerman–Tolman, the moment data of a compact symplectic toric orbifold. -/
structure IsRationalSimple : Prop where
  /-- The polyhedron is bounded, hence a polytope. -/
  isBounded : Bornology.IsBounded (facetPolyhedron i u c)
  /-- Exactly `rank N` facets meet at each vertex. -/
  ncard_activeSet : ∀ x ∈ (facetPolyhedron i u c).extremePoints ℝ,
    (activeSet (facetPairing i u) c x).ncard = Module.finrank ℤ N
  /-- Each constraint is the only active one at some point of the polyhedron. -/
  irredundant : ∀ j, ∃ x ∈ facetPolyhedron i u c, activeSet (facetPairing i u) c x = {j}
  /-- The inward normals are primitive lattice vectors. -/
  isPrimitive : ∀ j, IsPrimitive (u j)

variable {i u c}

/-- A Delzant presentation is rational simple. -/
theorem IsDelzant.isRationalSimple [FiniteDimensional ℝ V] (hΔ : IsDelzant i u c) :
    IsRationalSimple i u c where
  isBounded := hΔ.isBounded
  ncard_activeSet x hx := (hΔ.isSmoothVertex x hx).ncard_activeSet
  irredundant := hΔ.irredundant
  isPrimitive := hΔ.isPrimitive

/-- **Delzant polytopes are the unimodular rational simple polytopes.** A facet presentation is
Delzant exactly when it is rational simple and at each vertex the normals of the active facets
generate the lattice. -/
theorem isDelzant_iff_isRationalSimple [Finite ι] [FiniteDimensional ℝ V] :
    IsDelzant i u c ↔ IsRationalSimple i u c ∧ ∀ x ∈ (facetPolyhedron i u c).extremePoints ℝ,
      Submodule.span ℤ (u '' activeSet (facetPairing i u) c x) = ⊤ := by
  refine ⟨fun hΔ ↦ ⟨hΔ.isRationalSimple, fun x hx ↦
    (isSmoothVertex_iff_linearIndepOn.1 (hΔ.isSmoothVertex x hx)).2⟩, fun ⟨hΔ, hspan⟩ ↦ ?_⟩
  exact ⟨hΔ.isBounded, fun x hx ↦ isSmoothVertex_iff_span_eq_top.2
    ⟨hspan x hx, (hΔ.ncard_activeSet x hx).le⟩, hΔ.irredundant⟩

namespace IsRationalSimple

variable (hΔ : IsRationalSimple i u c)
include hΔ

/-- **Labeled polytopes, Lerman–Tolman's smoothness criterion.** A rational simple polytope with
labels `m j` is Delzant, as a labeled presentation `(m j • u j, m j * c j)`, exactly when every
label is one and every vertex cone is unimodular. -/
theorem isDelzant_nsmul_iff [Finite ι] [FiniteDimensional ℝ V] {m : ι → ℕ}
    (hm : ∀ j, m j ≠ 0) :
    IsDelzant i (fun j ↦ m j • u j) (fun j ↦ m j * c j) ↔ (∀ j, m j = 1) ∧
      ∀ x ∈ (facetPolyhedron i u c).extremePoints ℝ,
        Submodule.span ℤ (u '' activeSet (facetPairing i u) c x) = ⊤ := by
  rw [TauCeti.Toric.isDelzant_nsmul_iff hm, isDelzant_iff_isRationalSimple, and_iff_right hΔ]

variable [Finite ι] [FiniteDimensional ℝ V]

/-- **Simple vertices.** At a vertex of a rational simple polytope in an integral lattice, the
normals of the active facets are linearly independent: there are `dim V` of them and they span `V`.
-/
theorem linearIndepOn_activeSet (hi : IsIntegralLattice i) {x : StrongDual ℝ V}
    (hx : x ∈ (facetPolyhedron i u c).extremePoints ℝ) :
    LinearIndepOn ℤ u (activeSet (facetPairing i u) c x) := by
  set s := activeSet (facetPairing i u) c x
  have := Fintype.ofFinite s
  have hspan := (mem_extremePoints_facetPolyhedron_iff_span_eq_top.1 hx).2
  rw [image_eq_range] at hspan
  -- The `dim V` real vectors `i (u j)` span `V`, so they are linearly independent over `ℝ`.
  have hR : LinearIndependent ℝ fun j : s ↦ i (u j) :=
    linearIndependent_of_top_le_span_of_card_le_finrank hspan.ge <| by
      rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq, hΔ.ncard_activeSet x hx, hi.finrank_eq]
  exact LinearIndependent.of_comp i.toIntLinearMap (hR.restrict_scalars' (R := ℤ))

/-- **Finite isotropy.** At each vertex of a rational simple polytope in an integral lattice with
positive labels, the structure group `N ⧸ labeledActiveLattice i u c m x` is finite. -/
theorem finite_quotient_labeledActiveLattice (hi : IsIntegralLattice i) {m : ι → ℕ}
    (hm : ∀ j, m j ≠ 0) {x : StrongDual ℝ V} (hx : x ∈ (facetPolyhedron i u c).extremePoints ℝ) :
    Finite (N ⧸ labeledActiveLattice i u c m x) := by
  have := hi.free
  have := hi.finite
  set s := activeSet (facetPairing i u) c x
  have := Fintype.ofFinite s
  have hu := hΔ.linearIndepOn_activeSet hi hx
  -- The vertex cone lattice has rank `|s| = rank N`, hence finite index.
  have : Finite (N ⧸ Submodule.span ℤ (u '' s)) := by
    rw [Submodule.finiteQuotient_iff, image_eq_range, finrank_span_eq_card hu,
      Fintype.card_eq_nat_card, Nat.card_coe_set_eq, hΔ.ncard_activeSet x hx]
  refine Nat.finite_of_card_ne_zero ?_
  rw [card_quotient_labeledActiveLattice hu]
  exact mul_ne_zero (finprod_mem_induction (· ≠ 0) one_ne_zero (fun _ _ ↦ mul_ne_zero)
    fun j _ ↦ hm j) Nat.card_pos.ne'

end IsRationalSimple

end RationalSimple

/-! ### The weighted projective line -/

section Interval

variable {a : ℝ} {m : Fin 2 → ℕ}

/-- The structure group at the endpoint `0` of the labeled interval `[0, a]` has order `m 0`. -/
theorem card_quotient_labeledActiveLattice_interval_of_eq_zero (ha : a ≠ 0) {x : StrongDual ℝ ℝ}
    (hx : x 1 = 0) :
    Nat.card (ℤ ⧸ labeledActiveLattice (Int.castAddHom ℝ) ![1, -1] ![0, -a] m x) = m 0 := by
  rw [labeledActiveLattice_def, activeSet_interval_of_eq_zero ha hx, image_singleton]
  simpa using Nat.card_congr (Int.quotientSpanNatEquivZMod (m 0)).toEquiv

/-- The structure group at the endpoint `a` of the labeled interval `[0, a]` has order `m 1`. -/
theorem card_quotient_labeledActiveLattice_interval_of_eq (ha : a ≠ 0) {x : StrongDual ℝ ℝ}
    (hx : x 1 = a) :
    Nat.card (ℤ ⧸ labeledActiveLattice (Int.castAddHom ℝ) ![1, -1] ![0, -a] m x) = m 1 := by
  rw [labeledActiveLattice_def, activeSet_interval_of_eq ha hx, image_singleton]
  simpa using Nat.card_congr (Int.quotientSpanNatEquivZMod (m 1)).toEquiv

end Interval

end TauCeti.Toric
