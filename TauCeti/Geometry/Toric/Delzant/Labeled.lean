/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Lattice.Basic
public import TauCeti.Geometry.Toric.Delzant.Interval

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
*rational simple* (`TauCeti.Toric.IsRationalSimple`) when `Δ` is bounded, each constraint is the
only active one at some point of `Δ`, the normals are primitive, and exactly `rank N` constraints
are active at each vertex. Like `TauCeti.Toric.IsDelzant`, the predicate omits
`IsIntegralLattice i`. For a finite presentation in an integral lattice, the active normals at each
vertex are linearly independent (`TauCeti.Toric.IsRationalSimple.linearIndepOn_activeSet`), so that
the constraints are the facets of a simple polytope. A Delzant presentation is rational simple
(`TauCeti.Toric.IsDelzant.isRationalSimple`), and a rational simple presentation is Delzant exactly
when the normals of the constraints active at each vertex generate `N`, that is, when every vertex
cone is unimodular (`TauCeti.Toric.isDelzant_iff_isRationalSimple`).

Labels `m j` enter through the *labeled normals* `m j • u j`.

* **The polytope.** Rescaling each constraint by a positive label, `(m j • u j, m j * c j)`, cuts
  out the same polyhedron (`TauCeti.Toric.facetPolyhedron_nsmul`) with the same active constraints
  at every point (`TauCeti.Toric.activeSet_nsmul`), both in
  `TauCeti.Geometry.Toric.Delzant.Basic`.
* **Isotropy.** At a point `x`, the labeled normals of the active constraints span the sublattice
  `TauCeti.Toric.labeledActiveLattice`. For a vertex `x` of a labeled polytope, the quotient
  `N ⧸ labeledActiveLattice` is the orbifold structure group over `x` of the toric orbifold that
  Lerman–Tolman's correspondence attaches to the labeled polytope; here it is studied
  combinatorially, without constructing the orbifold. When the active
  normals are linearly independent, its `Nat.card` is the product of the active labels times the
  `Nat.card` of the quotient by the vertex cone lattice
  (`TauCeti.Toric.card_quotient_labeledActiveLattice`):

  `Nat.card (N ⧸ span {m j • u j}) = (∏ m j) · Nat.card (N ⧸ span {u j})`,

  where both sides are `0` when a quotient is infinite. At a vertex of a rational simple polytope
  in an integral lattice whose active labels are positive, both quotients are finite
  (`TauCeti.Toric.IsRationalSimple.finite_quotient_labeledActiveLattice`), so the formula
  multiplies genuine group orders. At a smooth vertex, where the active normals form a basis `b`
  of `N`, the labeled lattice is spanned by the rescaled basis vectors
  (`TauCeti.Toric.labeledActiveLattice_eq_span_range_nsmul`); when the active set is finite,
  `Module.Basis.quotientSpanSMulEquiv` identifies the quotient with `Π j, ℤ ⧸ (m j)`.
* **Delzant labeled presentations.** By `TauCeti.Toric.isDelzant_nsmul_iff` in
  `TauCeti.Geometry.Toric.Delzant.Basic`, the labeled presentation is Delzant exactly when all
  labels are one and the unlabeled presentation is Delzant. For a labeled rational simple polytope,
  the labeled presentation `(m j • u j, m j * c j)` is therefore Delzant exactly when all labels
  are one and every vertex cone is unimodular
  (`TauCeti.Toric.IsRationalSimple.isDelzant_nsmul_iff`). This is the combinatorial shape of
  Lerman–Tolman's smoothness criterion; the statement concerns the presentation only, not the
  structure groups or the orbifold.

For `0 < a`, the interval `[0, a]` with labels `m 0` and `m 1` on its two endpoints is, in
Lerman–Tolman's correspondence, the labeled polytope of a spindle orbifold: a sphere with cone
points of orders `m 0` and `m 1`, which is the weighted projective line `ℙ(m 0, m 1)` when the
labels are coprime. For every `a ≠ 0`, the quotients of `ℤ` by the labeled lattices of the
constraints active at the points `0` and `a` have `Nat.card` equal to `m 0` and `m 1`
(`TauCeti.Toric.card_quotient_labeledActiveLattice_interval_of_eq_zero`,
`TauCeti.Toric.card_quotient_labeledActiveLattice_interval_of_eq`). For `0 < a` and positive
labels these are the orders of the structure groups at the endpoints; a zero label gives the
infinite quotient `ℤ`, of cardinality `0` in `Nat.card`.

## Main definitions

* `TauCeti.Toric.IsRationalSimple`: a bounded irredundant facet presentation with primitive
  normals, with exactly `rank N` active constraints at each vertex.
* `TauCeti.Toric.labeledActiveLattice`: the sublattice spanned by the labeled normals of the
  constraints active at a point.

## Main results

* `TauCeti.Toric.card_quotient_labeledActiveLattice`: when finitely many active normals are
  linearly independent, the `Nat.card` of the quotient of `N` by the labeled lattice; at a vertex
  of a labeled polytope this quotient is the structure group.
* `TauCeti.Toric.linearIndepOn_activeSet_of_ncard_eq`: at a vertex of a finite presentation in an
  integral lattice where exactly `rank N` constraints are active, the active normals are linearly
  independent; `TauCeti.Toric.IsRationalSimple.linearIndepOn_activeSet` applies it to every vertex
  of a rational simple polytope.
* `TauCeti.Toric.finite_quotient_labeledActiveLattice_of_ncard_eq`: at such a vertex, with positive
  active labels, the quotient by the labeled lattice is finite;
  `TauCeti.Toric.IsRationalSimple.finite_quotient_labeledActiveLattice` applies it to every vertex
  of a rational simple polytope.
* `TauCeti.Toric.isDelzant_iff_isRationalSimple`: Delzant means rational simple with unimodular
  vertex cones.
* `TauCeti.Toric.IsRationalSimple.isDelzant_nsmul_iff`: the labeled presentation of a rational
  simple polytope is Delzant exactly when all labels are one and every vertex cone is unimodular.

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

/-- **The cardinality of the labeled quotient.** When the normals active at `x` are finitely many
and linearly independent, the `Nat.card` of the quotient of `N` by the labeled lattice is the
product of the active labels times the `Nat.card` of the quotient of `N` by the lattice spanned by
the active normals. Both sides are `0` when one of the quotients is infinite, for instance when an
active label vanishes; at a vertex of a rational simple polytope in an integral lattice with
positive active labels both quotients are finite
(`IsRationalSimple.finite_quotient_labeledActiveLattice`) and the formula multiplies the orders of
the structure group and of the quotient by the vertex cone lattice. -/
theorem card_quotient_labeledActiveLattice {x : StrongDual ℝ V}
    [Finite (activeSet (facetPairing i u) c x)]
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
spanned by the rescaled basis vectors `m j • b j`. When the active set is finite,
`Module.Basis.quotientSpanSMulEquiv` therefore identifies the quotient by the labeled lattice with
`Π j, ℤ ⧸ (m j)`. -/
theorem labeledActiveLattice_eq_span_range_nsmul {x : StrongDual ℝ V}
    (b : Module.Basis (activeSet (facetPairing i u) c x) ℤ N) (hb : ∀ j, b j = u j) :
    labeledActiveLattice i u c m x =
      Submodule.span ℤ (range fun j : activeSet (facetPairing i u) c x ↦ m j • b j) := by
  simp [labeledActiveLattice_def, hb, image_eq_range]

/-- At a smooth vertex with finitely many active constraints, the `Nat.card` of the quotient by
the labeled lattice is the product of the active labels. It is a genuine group order when the
active labels are positive, and both sides are `0` when one of them vanishes. -/
theorem IsSmoothVertex.card_quotient_labeledActiveLattice {x : StrongDual ℝ V}
    [Finite (activeSet (facetPairing i u) c x)]
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

/-- The facet presentation `(u, c)` in the lattice `i : N →+ V` is *rational simple*: the
polyhedron is bounded, each constraint is the only active one at some point of the polyhedron
(`irredundant`), the normals `u j` are primitive lattice vectors, and exactly `rank N` constraints
are active at each vertex (`ncard_activeSet`).

Like `IsDelzant`, the predicate does not include `IsIntegralLattice i`: results that need the
lattice assume it separately. Without it the active constraints need not behave like the facets of
a simple polytope (the octahedron, via a non-injective map `ℤ⁴ →+ ℝ³`, has four active constraints
at each vertex but dependent normals). For a finite constraint family in an integral lattice, the
active normals at each vertex are linearly independent (`linearIndepOn_activeSet`), the constraints
cut out the facets of a simple rational polytope, and with a positive integer label on each
constraint the presentation is a *labeled polytope* in the sense of Lerman–Tolman, the moment data
of a compact symplectic toric orbifold. -/
structure IsRationalSimple : Prop where
  /-- The polyhedron is bounded; for a finite constraint family it is therefore a polytope. -/
  isBounded : Bornology.IsBounded (facetPolyhedron i u c)
  /-- Exactly `rank N` constraints are active at each vertex. -/
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
Delzant exactly when it is rational simple and at each vertex the normals of the active constraints
generate the lattice. -/
theorem isDelzant_iff_isRationalSimple [Finite ι] [FiniteDimensional ℝ V] :
    IsDelzant i u c ↔ IsRationalSimple i u c ∧ ∀ x ∈ (facetPolyhedron i u c).extremePoints ℝ,
      Submodule.span ℤ (u '' activeSet (facetPairing i u) c x) = ⊤ := by
  refine ⟨fun hΔ ↦ ⟨hΔ.isRationalSimple, fun x hx ↦
    (isSmoothVertex_iff_linearIndepOn.1 (hΔ.isSmoothVertex x hx)).2⟩, fun ⟨hΔ, hspan⟩ ↦ ?_⟩
  exact ⟨hΔ.isBounded, fun x hx ↦ isSmoothVertex_iff_span_eq_top.2
    ⟨hspan x hx, (hΔ.ncard_activeSet x hx).le⟩, hΔ.irredundant⟩

section Vertex

variable [Finite ι]

/-- **Simple vertices.** At a vertex of a finite presentation in an integral lattice where exactly
`rank N` constraints are active, the normals of the active constraints are linearly independent:
there are `dim V` of them and they span `V`. -/
theorem linearIndepOn_activeSet_of_ncard_eq (hi : IsIntegralLattice i) {x : StrongDual ℝ V}
    (hx : x ∈ (facetPolyhedron i u c).extremePoints ℝ)
    (hcard : (activeSet (facetPairing i u) c x).ncard = Module.finrank ℤ N) :
    LinearIndepOn ℤ u (activeSet (facetPairing i u) c x) := by
  have := hi.finiteDimensional
  set s := activeSet (facetPairing i u) c x
  have := Fintype.ofFinite s
  have hspan := (mem_extremePoints_facetPolyhedron_iff_span_eq_top.1 hx).2
  rw [image_eq_range] at hspan
  -- The `dim V` real vectors `i (u j)` span `V`, so they are linearly independent over `ℝ`.
  have hR : LinearIndependent ℝ fun j : s ↦ i (u j) :=
    linearIndependent_of_top_le_span_of_card_le_finrank hspan.ge <| by
      rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq, hcard, hi.finrank_eq]
  exact LinearIndependent.of_comp i.toIntLinearMap (hR.restrict_scalars' (R := ℤ))

/-- **Finite isotropy.** At a vertex `x` of a finite presentation in an integral lattice where
exactly `rank N` constraints are active, if the labels of the active constraints are positive, then
the quotient `N ⧸ labeledActiveLattice i u c m x` is finite. -/
theorem finite_quotient_labeledActiveLattice_of_ncard_eq (hi : IsIntegralLattice i) {m : ι → ℕ}
    {x : StrongDual ℝ V} (hx : x ∈ (facetPolyhedron i u c).extremePoints ℝ)
    (hcard : (activeSet (facetPairing i u) c x).ncard = Module.finrank ℤ N)
    (hm : ∀ j ∈ activeSet (facetPairing i u) c x, m j ≠ 0) :
    Finite (N ⧸ labeledActiveLattice i u c m x) := by
  have := hi.free
  have := hi.finite
  set s := activeSet (facetPairing i u) c x
  have := Fintype.ofFinite s
  have hu := linearIndepOn_activeSet_of_ncard_eq hi hx hcard
  -- The vertex cone lattice has rank `|s| = rank N`, hence finite index.
  have : Finite (N ⧸ Submodule.span ℤ (u '' s)) := by
    rw [Submodule.finiteQuotient_iff, image_eq_range, finrank_span_eq_card hu,
      Fintype.card_eq_nat_card, Nat.card_coe_set_eq, hcard]
  refine Nat.finite_of_card_ne_zero ?_
  rw [card_quotient_labeledActiveLattice hu]
  exact mul_ne_zero (finprod_mem_induction (· ≠ 0) one_ne_zero (fun _ _ ↦ mul_ne_zero)
    hm) Nat.card_pos.ne'

end Vertex

namespace IsRationalSimple

variable (hΔ : IsRationalSimple i u c)
include hΔ

/-- **Delzant labeled presentations.** For a rational simple polytope with positive labels `m j`,
the labeled presentation `(m j • u j, m j * c j)` is Delzant exactly when every label is one and
every vertex cone is unimodular. This is the combinatorial shape of Lerman–Tolman's smoothness
criterion: it concerns the presentation only, not the structure groups
`N ⧸ labeledActiveLattice i u c m x`. -/
theorem isDelzant_nsmul_iff [Finite ι] [FiniteDimensional ℝ V] {m : ι → ℕ}
    (hm : ∀ j, m j ≠ 0) :
    IsDelzant i (fun j ↦ m j • u j) (fun j ↦ m j * c j) ↔ (∀ j, m j = 1) ∧
      ∀ x ∈ (facetPolyhedron i u c).extremePoints ℝ,
        Submodule.span ℤ (u '' activeSet (facetPairing i u) c x) = ⊤ := by
  rw [TauCeti.Toric.isDelzant_nsmul_iff hm, isDelzant_iff_isRationalSimple, and_iff_right hΔ]

variable [Finite ι]

/-- At a vertex of a rational simple polytope in an integral lattice, the normals of the active
constraints are linearly independent (`linearIndepOn_activeSet_of_ncard_eq`). -/
theorem linearIndepOn_activeSet (hi : IsIntegralLattice i) {x : StrongDual ℝ V}
    (hx : x ∈ (facetPolyhedron i u c).extremePoints ℝ) :
    LinearIndepOn ℤ u (activeSet (facetPairing i u) c x) :=
  linearIndepOn_activeSet_of_ncard_eq hi hx (hΔ.ncard_activeSet x hx)

/-- **Finite isotropy.** At a vertex `x` of a rational simple polytope in an integral lattice, if
the labels of the constraints active at `x` are positive, then the structure group
`N ⧸ labeledActiveLattice i u c m x` is finite (`finite_quotient_labeledActiveLattice_of_ncard_eq`).
-/
theorem finite_quotient_labeledActiveLattice (hi : IsIntegralLattice i) {m : ι → ℕ}
    {x : StrongDual ℝ V} (hx : x ∈ (facetPolyhedron i u c).extremePoints ℝ)
    (hm : ∀ j ∈ activeSet (facetPairing i u) c x, m j ≠ 0) :
    Finite (N ⧸ labeledActiveLattice i u c m x) :=
  finite_quotient_labeledActiveLattice_of_ncard_eq hi hx (hΔ.ncard_activeSet x hx) hm

end IsRationalSimple

end RationalSimple

/-! ### The labeled interval -/

section Interval

variable {a : ℝ} {m : Fin 2 → ℕ}

/-- For `a ≠ 0`, at a point `x` with `x 1 = 0` the quotient of `ℤ` by the labeled lattice of the
active constraint has `Nat.card` equal to `m 0`. When `0 < a` and `0 < m 0`, this point is the
endpoint `0` of the labeled interval `[0, a]` and the quotient is its structure group, of order
`m 0`. A zero label
`m 0 = 0` gives the infinite quotient `ℤ`, of cardinality `0` in `Nat.card`. -/
theorem card_quotient_labeledActiveLattice_interval_of_eq_zero (ha : a ≠ 0) {x : StrongDual ℝ ℝ}
    (hx : x 1 = 0) :
    Nat.card (ℤ ⧸ labeledActiveLattice (Int.castAddHom ℝ) ![1, -1] ![0, -a] m x) = m 0 := by
  rw [labeledActiveLattice_def, activeSet_interval_of_eq_zero ha hx, image_singleton]
  simpa using (Module.Basis.singleton Unit ℤ).card_quotient_span_range_nsmul fun _ ↦ m 0

/-- For `a ≠ 0`, at a point `x` with `x 1 = a` the quotient of `ℤ` by the labeled lattice of the
active constraint has `Nat.card` equal to `m 1`. When `0 < a` and `0 < m 1`, this point is the
endpoint `a` of the labeled interval `[0, a]` and the quotient is its structure group, of order
`m 1`. A zero label
`m 1 = 0` gives the infinite quotient `ℤ`, of cardinality `0` in `Nat.card`. -/
theorem card_quotient_labeledActiveLattice_interval_of_eq (ha : a ≠ 0) {x : StrongDual ℝ ℝ}
    (hx : x 1 = a) :
    Nat.card (ℤ ⧸ labeledActiveLattice (Int.castAddHom ℝ) ![1, -1] ![0, -a] m x) = m 1 := by
  rw [labeledActiveLattice_def, activeSet_interval_of_eq ha hx, image_singleton]
  -- The labeled normal at `a` is `-(m 1 • 1)`, which spans the same sublattice as `m 1 • 1`.
  rw [show m 1 • ![(1 : ℤ), -1] 1 = -(m 1 • 1) by simp, ← Set.neg_singleton, Submodule.span_neg]
  simpa using (Module.Basis.singleton Unit ℤ).card_quotient_span_range_nsmul fun _ ↦ m 1

end Interval

end TauCeti.Toric
