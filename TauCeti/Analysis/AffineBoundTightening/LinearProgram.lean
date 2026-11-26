/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.AffineBoundTightening.Operator

/-!
# The scalar linear program of simultaneous affine bound tightening

This file writes down, directly from a coefficient matrix `A` and initial endpoints `q₀`, a system
of scalar affine constraints whose solutions are exactly the ordered joint boxes fixed by the
simultaneous tightening step `step A q₀`, together with their signed coefficient products.

An `Assignment n m` has independent unknowns: joint endpoints `endpoints`, and two product
unknowns `zL i j`, `zU i j` for every coefficient `A i j`. The predicate `IsFeasible A q₀ p` lists
the constraints: ordered endpoints, containment in `q₀`, the signed product equalities (which are
affine for fixed `A`, and force both products to `0` at a zero coefficient), the row-image
inequalities, and the inverse inequalities in the positive and negative coefficient branches.
The objective is the total width over variables and rows.

## Main definitions

* `TauCeti.AffineBoundTightening.Assignment`: endpoint and product unknowns of the program.
* `TauCeti.AffineBoundTightening.canonical`: the assignment whose products are the signed products
  of its endpoints.
* `TauCeti.AffineBoundTightening.IsFeasible`, `TauCeti.AffineBoundTightening.feasibleSet`: the
  scalar constraints and the set of assignments satisfying them.
* `TauCeti.AffineBoundTightening.objective`: total variable and row width of the endpoints.
* `TauCeti.AffineBoundTightening.graphAssignment`: the canonical assignment of the singleton box
  at a graph point `(x, A.mulVec x)`.

## Main results

* `TauCeti.AffineBoundTightening.isFeasible_iff`: an assignment is feasible exactly when it is the
  canonical assignment of ordered endpoints fixed by `step A q₀`.
* `TauCeti.AffineBoundTightening.isFeasible_graphAssignment`: every initially enclosed graph point
  gives a feasible singleton assignment.
* `TauCeti.AffineBoundTightening.graph_preimage_Icc_eq_empty`: if the program is infeasible, no
  graph point lies in the initial box. The converse fails: a feasible program need not have an
  enclosed graph point.

## References

* P. Belotti, S. Cafieri, J. Lee, and L. Liberti, *Feasibility-Based Bounds Tightening via Fixed
  Points*, COCOA 2010, LNCS 6508, pp. 65–76, the linear program (14)–(34) and Theorem 4.2, p. 73.
  The constraints here read that display with four corrections: the row index in (17)–(18) is `i`,
  (28) ranges over the negative coefficients, products at a zero coefficient are fixed to `0`, and
  the bounds are contained in the initial box `(X⁰, B⁰)`.
* P. Belotti, S. Cafieri, J. Lee, and L. Liberti, *On feasibility based bounds tightening*,
  Optimization Online, 2012, Proposition 4.2, p. 14 (infeasibility for a variable-width program).
-/

public section

open scoped BigOperators
open Set

namespace TauCeti.AffineBoundTightening

noncomputable section

variable {n m : ℕ}

/-! ### Assignments, canonical products and the objective -/

/-- Independent unknowns of the bound-tightening linear program: joint endpoints and two product
unknowns for each coefficient. -/
@[ext]
structure Assignment (n m : ℕ) where
  /-- Lower and upper endpoints of the joint variable-and-row box. -/
  endpoints : Raw n m
  /-- Lower product unknowns, one for each coefficient `A i j`. -/
  zL : Matrix (Fin m) (Fin n) ℝ
  /-- Upper product unknowns, one for each coefficient `A i j`. -/
  zU : Matrix (Fin m) (Fin n) ℝ

/-- The assignment whose products are the signed products of its endpoints. -/
def canonical (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) : Assignment n m :=
  ⟨q, zLo A q, zHi A q⟩

/-- Endpoints of a canonical assignment. -/
@[simp]
theorem canonical_endpoints (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) :
    (canonical A q).endpoints = q :=
  (rfl)

/-- Lower products of a canonical assignment. -/
@[simp]
theorem canonical_zL (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) :
    (canonical A q).zL i j = zLo A q i j :=
  (rfl)

/-- Upper products of a canonical assignment. -/
@[simp]
theorem canonical_zU (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) :
    (canonical A q).zU i j = zHi A q i j :=
  (rfl)

/-- Distinct endpoints give distinct canonical assignments. -/
theorem canonical_injective (A : Matrix (Fin m) (Fin n) ℝ) :
    Function.Injective (canonical (n := n) A) :=
  fun q r h => by simpa using congrArg Assignment.endpoints h

/-- The program objective: total variable and row width of the endpoints. -/
def objective (p : Assignment n m) : ℝ :=
  width p.endpoints

/-- The objective depends only on the endpoints, through their total width. -/
theorem objective_def (p : Assignment n m) : objective p = width p.endpoints :=
  (rfl)

/-- The objective of a canonical assignment is the width of its endpoints. -/
@[simp]
theorem objective_canonical (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) :
    objective (canonical A q) = width q :=
  (rfl)

/-- The objective is the variable width plus the row width. -/
theorem objective_eq_sum_add_sum (p : Assignment n m) :
    objective p =
      (∑ j : Fin n, (p.endpoints.2 (.inl j) - p.endpoints.1 (.inl j))) +
        ∑ i : Fin m, (p.endpoints.2 (.inr i) - p.endpoints.1 (.inr i)) :=
  width_eq_sum_add_sum p.endpoints

/-! ### The scalar constraints -/

/-- The scalar affine constraints of the bound-tightening linear program for `A` and initial
endpoints `q₀`: ordered endpoints contained in `q₀`, products equal to the signed products of the
variable endpoints, each row interval inside the sum of its product intervals, and, for every
positive or negative coefficient `A i j`, the variable interval of `j` inside the interval that row
`i` forces on it given the products of the other variables. A zero coefficient imposes no inverse
constraint. -/
structure IsFeasible (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (p : Assignment n m) :
    Prop where
  /-- The endpoints are ordered. -/
  fst_le_snd : p.endpoints.1 ≤ p.endpoints.2
  /-- The endpoints lie within the initial endpoints. -/
  within : Within p.endpoints q₀
  /-- Each lower product is the signed lower product of the variable endpoints. -/
  zL_eq : ∀ i j, p.zL i j = zLo A p.endpoints i j
  /-- Each upper product is the signed upper product of the variable endpoints. -/
  zU_eq : ∀ i j, p.zU i j = zHi A p.endpoints i j
  /-- The lower products of a row sum to at most its lower endpoint. -/
  sum_zL_le : ∀ i, ∑ j, p.zL i j ≤ p.endpoints.1 (.inr i)
  /-- The upper endpoint of a row is at most the sum of its upper products. -/
  le_sum_zU : ∀ i, p.endpoints.2 (.inr i) ≤ ∑ j, p.zU i j
  /-- Lower inverse constraint for a positive coefficient. -/
  div_le_of_pos : ∀ i j, 0 < A i j →
    (p.endpoints.1 (.inr i) - ∑ k ∈ Finset.univ.erase j, p.zU i k) / A i j ≤
      p.endpoints.1 (.inl j)
  /-- Upper inverse constraint for a positive coefficient. -/
  le_div_of_pos : ∀ i j, 0 < A i j →
    p.endpoints.2 (.inl j) ≤
      (p.endpoints.2 (.inr i) - ∑ k ∈ Finset.univ.erase j, p.zL i k) / A i j
  /-- Lower inverse constraint for a negative coefficient. -/
  div_le_of_neg : ∀ i j, A i j < 0 →
    (p.endpoints.2 (.inr i) - ∑ k ∈ Finset.univ.erase j, p.zL i k) / A i j ≤
      p.endpoints.1 (.inl j)
  /-- Upper inverse constraint for a negative coefficient. -/
  le_div_of_neg : ∀ i j, A i j < 0 →
    p.endpoints.2 (.inl j) ≤
      (p.endpoints.1 (.inr i) - ∑ k ∈ Finset.univ.erase j, p.zU i k) / A i j

/-- The feasible set of the bound-tightening linear program. -/
def feasibleSet (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) : Set (Assignment n m) :=
  {p | IsFeasible A q₀ p}

/-- Membership in the feasible set is feasibility. -/
@[simp]
theorem mem_feasibleSet {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m} {p : Assignment n m} :
    p ∈ feasibleSet A q₀ ↔ IsFeasible A q₀ p :=
  Iff.rfl

namespace IsFeasible

variable {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m} {p : Assignment n m}

/-- A feasible assignment is the canonical assignment of its endpoints. -/
theorem eq_canonical (h : IsFeasible A q₀ p) : p = canonical A p.endpoints := by
  ext <;> simp [h.zL_eq, h.zU_eq]

/-- The product intervals of a feasible assignment are ordered. -/
theorem zL_le_zU (h : IsFeasible A q₀ p) (i : Fin m) (j : Fin n) : p.zL i j ≤ p.zU i j := by
  rw [h.zL_eq, h.zU_eq]
  exact zLo_le_zHi (h.fst_le_snd _)

/-- Feasible assignments with the same endpoints are equal: the endpoints determine all
products. -/
theorem eq_of_endpoints_eq {p' : Assignment n m} (h : IsFeasible A q₀ p)
    (h' : IsFeasible A q₀ p') (he : p.endpoints = p'.endpoints) : p = p' := by
  rw [h.eq_canonical, h'.eq_canonical, he]

/-- A feasible assignment has nonnegative objective. -/
theorem objective_nonneg (h : IsFeasible A q₀ p) : 0 ≤ objective p :=
  width_nonneg h.fst_le_snd

/-- A zero coefficient forces the lower product unknown of a feasible assignment to `0`. -/
theorem zL_eq_zero (h : IsFeasible A q₀ p) {i : Fin m} {j : Fin n} (hA : A i j = 0) :
    p.zL i j = 0 := by
  rw [h.zL_eq, zLo_of_zero hA]

/-- A zero coefficient forces the upper product unknown of a feasible assignment to `0`. -/
theorem zU_eq_zero (h : IsFeasible A q₀ p) {i : Fin m} {j : Fin n} (hA : A i j = 0) :
    p.zU i j = 0 := by
  rw [h.zU_eq, zHi_of_zero hA]

/-- A feasible assignment has objective at most the width of the initial endpoints. -/
theorem objective_le (h : IsFeasible A q₀ p) : objective p ≤ width q₀ :=
  h.within.width_le

end IsFeasible

/-! ### Feasibility is ordered fixedness -/

/-- A canonical assignment is feasible exactly when its endpoints are ordered and fixed by
`step A q₀`. -/
theorem isFeasible_canonical_iff {A : Matrix (Fin m) (Fin n) ℝ} {q₀ q : Raw n m} :
    IsFeasible A q₀ (canonical A q) ↔ q.1 ≤ q.2 ∧ Function.IsFixedPt (step A q₀) q := by
  rw [isFixedPt_step_iff]
  constructor
  · intro h
    exact ⟨h.fst_le_snd, h.within, fun i => ⟨by simpa [imageLo_def] using h.sum_zL_le i,
      by simpa [imageHi_def] using h.le_sum_zU i⟩, fun i j =>
      ⟨inverseLo_le_fst_inl_iff.mpr
        ⟨by simpa [restHi_def] using h.div_le_of_pos i j,
          by simpa [restLo_def] using h.div_le_of_neg i j⟩,
        snd_inl_le_inverseHi_iff.mpr
        ⟨by simpa [restLo_def] using h.le_div_of_pos i j,
          by simpa [restHi_def] using h.le_div_of_neg i j⟩⟩⟩
  · rintro ⟨hle, hq₀, hrow, hinv⟩
    have hlo i j := inverseLo_le_fst_inl_iff.mp (hinv i j).1
    have hhi i j := snd_inl_le_inverseHi_iff.mp (hinv i j).2
    refine
      { fst_le_snd := hle
        within := hq₀
        zL_eq := fun _ _ => by simp
        zU_eq := fun _ _ => by simp
        sum_zL_le := fun i => ?_
        le_sum_zU := fun i => ?_
        div_le_of_pos := fun i j => ?_
        le_div_of_pos := fun i j => ?_
        div_le_of_neg := fun i j => ?_
        le_div_of_neg := fun i j => ?_ }
    · simpa [imageLo_def] using (hrow i).1
    · simpa [imageHi_def] using (hrow i).2
    · simpa [restHi_def] using (hlo i j).1
    · simpa [restLo_def] using (hhi i j).1
    · simpa [restLo_def] using (hlo i j).2
    · simpa [restHi_def] using (hhi i j).2

/-- **Feasibility is ordered fixedness.** An assignment satisfies the scalar constraints exactly
when it is the canonical assignment of ordered endpoints fixed by `step A q₀`. -/
theorem isFeasible_iff {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m} {p : Assignment n m} :
    IsFeasible A q₀ p ↔
      p = canonical A p.endpoints ∧ p.endpoints.1 ≤ p.endpoints.2 ∧
        Function.IsFixedPt (step A q₀) p.endpoints := by
  constructor
  · intro h
    have hp := h.eq_canonical
    rw [hp] at h
    exact ⟨hp, isFeasible_canonical_iff.mp h⟩
  · rintro ⟨hp, hfix⟩
    rw [hp]
    exact isFeasible_canonical_iff.mpr hfix

/-- The feasible set is the image under `canonical A` of the ordered fixed tuples of
`step A q₀`. -/
theorem feasibleSet_eq_image (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) :
    feasibleSet A q₀ = canonical A '' {q | q.1 ≤ q.2 ∧ Function.IsFixedPt (step A q₀) q} := by
  ext p
  rw [mem_feasibleSet, mem_image]
  constructor
  · intro h
    exact ⟨p.endpoints, (isFeasible_iff.mp h).2, h.eq_canonical.symm⟩
  · rintro ⟨q, hq, rfl⟩
    exact isFeasible_canonical_iff.mpr hq

/-- The program is feasible exactly when `step A q₀` has an ordered fixed tuple. -/
theorem exists_isFeasible_iff {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m} :
    (∃ p, IsFeasible A q₀ p) ↔ ∃ q : Raw n m, q.1 ≤ q.2 ∧ Function.IsFixedPt (step A q₀) q := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.endpoints, (isFeasible_iff.mp hp).2⟩
  · rintro ⟨q, hq⟩
    exact ⟨canonical A q, isFeasible_canonical_iff.mpr hq⟩

/-! ### Singleton graph assignments and infeasibility -/

/-- The canonical assignment of the singleton box at the graph point `(x, A.mulVec x)`. -/
def graphAssignment (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) : Assignment n m :=
  canonical A (graph A x, graph A x)

/-- A graph assignment is the canonical assignment of the singleton box at the graph point. -/
theorem graphAssignment_def (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    graphAssignment A x = canonical A (graph A x, graph A x) :=
  (rfl)

/-- Both endpoints of a graph assignment are the graph point. -/
@[simp]
theorem graphAssignment_endpoints (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    (graphAssignment A x).endpoints = (graph A x, graph A x) :=
  (rfl)

/-- The lower products of a graph assignment are the ordinary products `A i j * x j`. -/
@[simp]
theorem graphAssignment_zL (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (i : Fin m)
    (j : Fin n) : (graphAssignment A x).zL i j = A i j * x j := by
  simp [graphAssignment_def]

/-- The upper products of a graph assignment are the ordinary products `A i j * x j`. -/
@[simp]
theorem graphAssignment_zU (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (i : Fin m)
    (j : Fin n) : (graphAssignment A x).zU i j = A i j * x j := by
  simp [graphAssignment_def]

/-- Every graph point in the initial box gives a feasible singleton assignment. -/
theorem isFeasible_graphAssignment {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m}
    {x : Fin n → ℝ} (hx : graph A x ∈ Icc q₀.1 q₀.2) : IsFeasible A q₀ (graphAssignment A x) :=
  isFeasible_canonical_iff.mpr ⟨le_rfl, isFixedPt_step_graph hx⟩

/-- A graph point in the initial box makes the program feasible. -/
theorem exists_isFeasible_of_graph_mem_Icc {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m}
    {x : Fin n → ℝ} (hx : graph A x ∈ Icc q₀.1 q₀.2) : ∃ p, IsFeasible A q₀ p :=
  ⟨graphAssignment A x, isFeasible_graphAssignment hx⟩

/-- **Infeasibility excludes graph points.** If the program has no feasible assignment, no graph
point `(x, A.mulVec x)` lies in the initial box. No hypothesis on the iterates is needed. -/
theorem graph_preimage_Icc_eq_empty {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m}
    (h : ¬ ∃ p, IsFeasible A q₀ p) : graph A ⁻¹' Icc q₀.1 q₀.2 = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun _ hx => h (exists_isFeasible_of_graph_mem_Icc hx)

end

end TauCeti.AffineBoundTightening
