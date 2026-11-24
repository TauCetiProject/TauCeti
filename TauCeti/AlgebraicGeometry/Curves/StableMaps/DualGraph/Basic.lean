/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Basic
import Mathlib.Tactic.Linarith

/-!
# Degree-decorated dual graphs of stable maps

The dual graph of a prestable map carries, in addition to the genera, nodes, and markings of its
source curve, the degree of the map on each irreducible component. This file packages those
component degrees as `TauCeti.DualGraph.DegreeDecoration` and develops the numerical stability
criterion.

For degrees measured by an ample polarization, a component has degree zero exactly when it is
contracted by the map, so it must have positive log-canonical degree. Positive-degree components
impose no stability condition. Equivalently, every vertex has positive **weighted log-canonical
degree**

`2g(v) - 2 + val(v) + n(v) + 3d(v)`.

Summing over the graph gives `2g - 2 + n + 3d`, where `d` is the total degree. In particular, a
stable degree-decorated graph lies in the corresponding stable range. The stability condition
depends only on which components have degree zero; this is the combinatorial reason it is
independent of the chosen ample polarization.

Counting instead the number `a` of components of positive degree bounds the size of a stable
decorated graph: every degree-zero component has log-canonical degree at least `1` and every other
component at least `-2`. These bounds do not involve the degrees themselves, so they also apply to
stable maps into a symplectic manifold, decorated by `1` on the nonconstant components.

## Main definitions

* `TauCeti.DualGraph.DegreeDecoration`: component degrees on a dual graph.
* `TauCeti.DualGraph.DegreeDecoration.totalDegree`: the sum of the component degrees.
* `TauCeti.DualGraph.DegreeDecoration.weightedLogCanonicalDegree`: the value
  `2g(v) - 2 + val(v) + n(v) + 3d(v)` at a vertex.
* `TauCeti.DualGraph.DegreeDecoration.IsStable`: the stable-map component criterion.

## Main results

* `TauCeti.DualGraph.DegreeDecoration.isStable_iff_weightedLogCanonicalDegree_pos`: the
  contracted-component criterion is equivalent to positivity of every weighted degree.
* `TauCeti.DualGraph.DegreeDecoration.sum_weightedLogCanonicalDegree`: the weighted degrees sum
  to `2g - 2 + n + 3d`.
* `IsStable.two_mul_arithmeticGenus_sub_two_add_card_add_three_mul_totalDegree_pos` (in
  `TauCeti.DualGraph.DegreeDecoration`): the numerical stable range `2g - 2 + n + 3d > 0`.
* `TauCeti.DualGraph.DegreeDecoration.isStable_congr`: stability depends only on the degree-zero
  components.
* `IsStable.card_filter_componentDegree_eq_zero_le`, `IsStable.card_vertex_le` and
  `IsStable.card_edge_le` (in `TauCeti.DualGraph.DegreeDecoration`): with `a` components of
  positive degree, a stable decorated graph has at most `2g - 2 + n + 2a` components of degree
  zero, `2g - 2 + n + 3a` vertices and `3g - 3 + n + 3a` edges.

## References

* K. Behrend and Yu. Manin, *Stacks of stable maps and Gromov--Witten invariants*, Duke Math. J.
  85 (1996), 1--60, Section 2.
* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*, Proc. Sympos.
  Pure Math. 62 (1997), Part 2, 45--96, Section 1.
-/

public section

namespace TauCeti

open Finset

universe u v

namespace DualGraph

variable {ι : Type v} (G : DualGraph.{u} ι)

/-- A decoration of a dual graph by the nonnegative degree of the map on each component.

For a map to a projective target with a chosen ample invertible sheaf, `componentDegree v` is the
degree of its pullback to the normalized component represented by `v`. -/
@[ext]
structure DegreeDecoration where
  /-- The degree of the map on each component. -/
  componentDegree : G.Vertex → ℕ

namespace DegreeDecoration

variable {G} (D : G.DegreeDecoration)

/-- The total degree of a decorated dual graph, obtained by summing the component degrees. -/
def totalDegree : ℕ :=
  ∑ v, D.componentDegree v

lemma totalDegree_def : D.totalDegree = ∑ v, D.componentDegree v :=
  (rfl)

/-- A decorated graph has total degree zero exactly when every component has degree zero. -/
@[simp]
theorem totalDegree_eq_zero_iff : D.totalDegree = 0 ↔ ∀ v, D.componentDegree v = 0 := by
  simp [totalDegree]

/-- Every component degree is at most the total degree. -/
theorem componentDegree_le_totalDegree (v : G.Vertex) : D.componentDegree v ≤ D.totalDegree :=
  single_le_sum (fun w _ ↦ Nat.zero_le (D.componentDegree w)) (mem_univ v)

/-- The weighted log-canonical degree at a vertex:
`2g(v) - 2 + val(v) + n(v) + 3d(v)`. -/
def weightedLogCanonicalDegree [Fintype ι] (v : G.Vertex) : ℤ :=
  G.logCanonicalDegree v + 3 * (D.componentDegree v : ℤ)

lemma weightedLogCanonicalDegree_def [Fintype ι] (v : G.Vertex) :
    D.weightedLogCanonicalDegree v = G.logCanonicalDegree v + 3 * (D.componentDegree v : ℤ) :=
  (rfl)

/-- The numerical stability condition for a stable map: every degree-zero component has positive
log-canonical degree. Components of positive degree are not constrained. -/
def IsStable [Fintype ι] : Prop :=
  ∀ v, D.componentDegree v = 0 → 0 < G.logCanonicalDegree v

lemma isStable_iff [Fintype ι] :
    D.IsStable ↔ ∀ v, D.componentDegree v = 0 → 0 < G.logCanonicalDegree v :=
  Iff.rfl

/-- A positive-degree vertex has positive weighted log-canonical degree, without any stability
hypothesis on its underlying pointed component. -/
theorem weightedLogCanonicalDegree_pos_of_componentDegree_pos [Fintype ι] {v : G.Vertex}
    (hv : 0 < D.componentDegree v) : 0 < D.weightedLogCanonicalDegree v := by
  rw [weightedLogCanonicalDegree_def, G.logCanonicalDegree_def]
  omega

/-- A vertex of nonpositive weighted log-canonical degree has map degree zero. -/
theorem componentDegree_eq_zero_of_weightedLogCanonicalDegree_nonpos [Fintype ι] {v : G.Vertex}
    (hv : D.weightedLogCanonicalDegree v ≤ 0) : D.componentDegree v = 0 := by
  by_contra hd
  exact (not_lt_of_ge hv)
    (D.weightedLogCanonicalDegree_pos_of_componentDegree_pos (Nat.pos_of_ne_zero hd))

/-- At a degree-zero vertex, the weighted and ordinary log-canonical degrees agree. -/
theorem weightedLogCanonicalDegree_eq_of_componentDegree_eq_zero [Fintype ι] {v : G.Vertex}
    (hv : D.componentDegree v = 0) :
    D.weightedLogCanonicalDegree v = G.logCanonicalDegree v := by
  simp [weightedLogCanonicalDegree_def, hv]

/-- The contracted-component stability criterion is equivalent to positivity of
`2g(v) - 2 + val(v) + n(v) + 3d(v)` at every vertex. -/
theorem isStable_iff_weightedLogCanonicalDegree_pos [Fintype ι] :
    D.IsStable ↔ ∀ v, 0 < D.weightedLogCanonicalDegree v := by
  constructor
  · intro hD v
    by_cases hv : D.componentDegree v = 0
    · simpa [weightedLogCanonicalDegree_def, hv] using hD v hv
    · exact D.weightedLogCanonicalDegree_pos_of_componentDegree_pos (Nat.pos_of_ne_zero hv)
  · intro hD v hv
    simpa [weightedLogCanonicalDegree_def, hv] using hD v

/-- The weighted log-canonical degrees add up to `2g - 2 + n + 3d`. -/
theorem sum_weightedLogCanonicalDegree [Fintype ι] :
    ∑ v, D.weightedLogCanonicalDegree v =
      2 * G.arithmeticGenus - 2 + Fintype.card ι + 3 * D.totalDegree := by
  rw [sum_congr rfl fun v _ ↦ D.weightedLogCanonicalDegree_def v, sum_add_distrib,
    G.sum_logCanonicalDegree]
  simp [totalDegree, ← mul_sum]

/-- In the numerical stable range, a zero-weighted-degree vertex is a rational tail with one
marking or an unmarked rational bridge. -/
theorem isRationalTail_or_isRationalBridge_of_weightedLogCanonicalDegree_eq_zero [Fintype ι]
    (hrange : 0 < 2 * (G.arithmeticGenus : ℤ) - 2 + Fintype.card ι + 3 * D.totalDegree)
    {v : G.Vertex} (hv : D.weightedLogCanonicalDegree v = 0) :
    (G.IsRationalTail v ∧ G.numMarkings v = 1) ∨
      (G.IsRationalBridge v ∧ ∀ i, G.marking i ≠ v) := by
  have hd := D.componentDegree_eq_zero_of_weightedLogCanonicalDegree_nonpos hv.le
  have hlog : G.logCanonicalDegree v = 0 := by
    rwa [D.weightedLogCanonicalDegree_eq_of_componentDegree_eq_zero hd] at hv
  have hw : ∃ w, w ≠ v := by
    by_contra! h
    have hsum : ∑ w, D.weightedLogCanonicalDegree w = 0 := by
      apply sum_eq_zero
      intro w _
      rw [h w, hv]
    rw [D.sum_weightedLogCanonicalDegree] at hsum
    omega
  rcases G.isRationalTail_or_isRationalBridge_of_logCanonicalDegree_nonpos hlog.le hw with
      ⟨ht, _⟩ | hb
  · have htail := ht.logCanonicalDegree_eq
    exact .inl ⟨ht, by omega⟩
  · exact .inr hb

/-- Stability is unchanged when two decorations have the same degree-zero components. -/
theorem isStable_congr [Fintype ι] {D' : G.DegreeDecoration}
    (h : ∀ v, D.componentDegree v = 0 ↔ D'.componentDegree v = 0) :
    D.IsStable ↔ D'.IsStable := by
  simp only [isStable_iff]
  constructor
  · exact fun hD v hv ↦ hD v ((h v).mpr hv)
  · exact fun hD v hv ↦ hD v ((h v).mp hv)

/-- A stable pointed dual graph remains stable after assigning arbitrary component degrees. -/
theorem isStable_of_dualGraph_isStable [Fintype ι] (hG : G.IsStable) : D.IsStable :=
  fun v _ ↦ G.isStable_iff.mp hG v

/-- Decorations add componentwise. The zero decoration assigns degree zero to every component;
it describes the degree data of a constant map. -/
instance : AddCommMonoid G.DegreeDecoration where
  zero := ⟨0⟩
  add D D' := ⟨D.componentDegree + D'.componentDegree⟩
  nsmul m D := ⟨m • D.componentDegree⟩
  add_assoc _ _ _ := DegreeDecoration.ext (add_assoc _ _ _)
  zero_add _ := DegreeDecoration.ext (zero_add _)
  add_zero _ := DegreeDecoration.ext (add_zero _)
  add_comm _ _ := DegreeDecoration.ext (add_comm _ _)
  nsmul_zero _ := DegreeDecoration.ext (zero_nsmul _)
  nsmul_succ _ _ := DegreeDecoration.ext (succ_nsmul _ _)

@[simp]
lemma componentDegree_zero (v : G.Vertex) : (0 : G.DegreeDecoration).componentDegree v = 0 :=
  (rfl)

@[simp]
lemma componentDegree_add (D' : G.DegreeDecoration) (v : G.Vertex) :
    (D + D').componentDegree v = D.componentDegree v + D'.componentDegree v :=
  (rfl)

@[simp]
lemma componentDegree_smul (m : ℕ) (v : G.Vertex) :
    (m • D).componentDegree v = m * D.componentDegree v :=
  (rfl)

@[simp]
lemma totalDegree_zero : (0 : G.DegreeDecoration).totalDegree = 0 := by
  simp [totalDegree]

@[simp]
theorem totalDegree_add (D' : G.DegreeDecoration) :
    (D + D').totalDegree = D.totalDegree + D'.totalDegree := by
  simp [totalDegree, sum_add_distrib]

@[simp]
theorem totalDegree_smul (m : ℕ) : (m • D).totalDegree = m * D.totalDegree := by
  simp [totalDegree, mul_sum]

@[simp]
lemma weightedLogCanonicalDegree_zero [Fintype ι] (v : G.Vertex) :
    (0 : G.DegreeDecoration).weightedLogCanonicalDegree v = G.logCanonicalDegree v := by
  simp [weightedLogCanonicalDegree_def]

@[simp]
lemma weightedLogCanonicalDegree_add [Fintype ι] (D' : G.DegreeDecoration) (v : G.Vertex) :
    (D + D').weightedLogCanonicalDegree v =
      G.logCanonicalDegree v + 3 * (D.componentDegree v : ℤ) + 3 * (D'.componentDegree v : ℤ) := by
  simp [weightedLogCanonicalDegree_def, mul_add, add_assoc]

@[simp]
lemma weightedLogCanonicalDegree_smul [Fintype ι] (m : ℕ) (v : G.Vertex) :
    (m • D).weightedLogCanonicalDegree v =
      G.logCanonicalDegree v + 3 * m * (D.componentDegree v : ℤ) := by
  simp [weightedLogCanonicalDegree_def, mul_assoc]

/-- The zero decoration is stable exactly when the pointed source graph is stable. This is the
numerical form of the fact that a constant prestable map is stable exactly when its source is. -/
@[simp]
theorem isStable_zero_iff [Fintype ι] : (0 : G.DegreeDecoration).IsStable ↔ G.IsStable := by
  simp [isStable_iff, DualGraph.isStable_iff]

/-- Scaling all component degrees by a positive integer does not change stability. In particular,
the exponent used for an ample polarization does not change the numerical criterion. -/
@[simp]
theorem isStable_smul_iff [Fintype ι] {m : ℕ} (hm : 0 < m) :
    (m • D).IsStable ↔ D.IsStable :=
  (m • D).isStable_congr (D' := D) fun v ↦ by
    simp [Nat.ne_of_gt hm]

/-- A stable decorated dual graph satisfies `2g - 2 + n + 3d > 0`. -/
theorem IsStable.two_mul_arithmeticGenus_sub_two_add_card_add_three_mul_totalDegree_pos [Fintype ι]
    (hD : D.IsStable) :
    0 < 2 * (G.arithmeticGenus : ℤ) - 2 + Fintype.card ι + 3 * D.totalDegree := by
  rw [← D.sum_weightedLogCanonicalDegree]
  exact Finset.sum_pos (fun v _ ↦ D.isStable_iff_weightedLogCanonicalDegree_pos.mp hD v)
    Finset.univ_nonempty

/-! ### Bounds in terms of the number of nonconstant components -/

/-- The number of components of positive degree is at most the total degree. -/
theorem card_filter_componentDegree_ne_zero_le_totalDegree :
    #{v | D.componentDegree v ≠ 0} ≤ D.totalDegree := by
  calc #{v | D.componentDegree v ≠ 0}
      = ∑ v ∈ {v | D.componentDegree v ≠ 0}, 1 := card_eq_sum_ones _
    _ ≤ ∑ v ∈ {v | D.componentDegree v ≠ 0}, D.componentDegree v :=
      sum_le_sum fun v hv ↦ Nat.one_le_iff_ne_zero.mpr (mem_filter.mp hv).2
    _ ≤ D.totalDegree := sum_le_sum_of_subset (filter_subset _ _)

/-- **The ghost bound.** A stable decorated graph of arithmetic genus `g` with `n` markings and
`a` components of positive degree has at most `2g - 2 + n + 2a` components of degree zero.

Every degree-zero component has log-canonical degree at least `1` and every other component at
least `-2`, and the log-canonical degrees add up to `2g - 2 + n`. -/
theorem IsStable.card_filter_componentDegree_eq_zero_le [Fintype ι] (hD : D.IsStable) :
    (#{v | D.componentDegree v = 0} : ℤ) ≤
      2 * G.arithmeticGenus - 2 + Fintype.card ι + 2 * #{v | D.componentDegree v ≠ 0} := by
  have hsum := G.sum_logCanonicalDegree
  rw [← sum_filter_add_sum_filter_not univ fun v ↦ D.componentDegree v = 0] at hsum
  simp only [← ne_eq] at hsum
  have h₀ := card_nsmul_le_sum {v | D.componentDegree v = 0} G.logCanonicalDegree 1
    fun v hv ↦ by have := hD v (mem_filter.mp hv).2; omega
  have h₁ := card_nsmul_le_sum {v | D.componentDegree v ≠ 0} G.logCanonicalDegree (-2)
    fun v _ ↦ by rw [G.logCanonicalDegree_def]; omega
  simp only [nsmul_eq_mul, mul_one] at h₀ h₁
  linarith

/-- A stable decorated graph of arithmetic genus `g` with `n` markings and `a` components of
positive degree has at most `2g - 2 + n + 3a` vertices. For the zero decoration this is
`TauCeti.DualGraph.IsStable.card_vertex_le`. -/
theorem IsStable.card_vertex_le [Fintype ι] (hD : D.IsStable) :
    (Fintype.card G.Vertex : ℤ) ≤
      2 * G.arithmeticGenus - 2 + Fintype.card ι + 3 * #{v | D.componentDegree v ≠ 0} := by
  have hcard := card_filter_add_card_filter_not (s := univ) fun v ↦ D.componentDegree v = 0
  simp only [← ne_eq, card_univ] at hcard
  have := hD.card_filter_componentDegree_eq_zero_le
  omega

/-- A stable decorated graph of arithmetic genus `g` with `n` markings and `a` components of
positive degree has at most `3g - 3 + n + 3a` edges. For the zero decoration this is
`TauCeti.DualGraph.IsStable.card_edge_le`. -/
theorem IsStable.card_edge_le [Fintype ι] (hD : D.IsStable) :
    (Fintype.card G.Edge : ℤ) ≤
      3 * G.arithmeticGenus - 3 + Fintype.card ι + 3 * #{v | D.componentDegree v ≠ 0} := by
  have := hD.card_vertex_le
  have := G.card_edge_add_one_le_arithmeticGenus_add_card_vertex
  omega

namespace IsStable

/-- A stable decorated graph satisfies `2g - 2 + n + 3a > 0`, where `a` is the number of
components of positive degree. Since `a` is at most the total degree, this sharpens
`IsStable.two_mul_arithmeticGenus_sub_two_add_card_add_three_mul_totalDegree_pos`. -/
theorem
    two_mul_arithmeticGenus_sub_two_add_card_add_three_mul_card_filter_componentDegree_ne_zero_pos
    [Fintype ι] (hD : D.IsStable) :
    0 < 2 * (G.arithmeticGenus : ℤ) - 2 + Fintype.card ι +
      3 * #{v | D.componentDegree v ≠ 0} := by
  have := hD.card_vertex_le
  have : 0 < Fintype.card G.Vertex := Fintype.card_pos
  omega

end IsStable

end DegreeDecoration

end DualGraph

end TauCeti
