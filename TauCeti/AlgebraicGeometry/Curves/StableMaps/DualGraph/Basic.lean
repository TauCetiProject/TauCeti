/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Basic

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

end DegreeDecoration

end DualGraph

end TauCeti
