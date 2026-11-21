/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Analysis.AffineBoundTightening.Operator

/-!
# The scalar linear program for simultaneous affine bound tightening

The decision variables are the joint endpoints and two independent product coordinates per
matrix entry. `lpFeasible` uses scalar affine constraints for a fixed coefficient matrix; it
makes no reference to the tightening step. `lp_iff_fixed` identifies its feasible assignments
with ordered raw fixed boxes, and `lpFeasible_canonical_graph` gives a feasible assignment from
any initially enclosed affine graph point. The objective counts both variable and row widths.

## References

* P. Belotti, S. Cafieri, J. Lee, and L. Liberti, *Feasibility-Based Bounds Tightening via Fixed
  Points*, COCOA 2010, §4, (14)–(34) and Theorem 4.2,
  [DOI:10.1007/978-3-642-17458-2_7](https://doi.org/10.1007/978-3-642-17458-2_7).
  In (17)–(18) the row index is `i`, in (28) the coefficients are negative, the products of
  zero coefficients are constrained to zero, and initial containment applies to both kinds
  of endpoints.
-/

public section

open Set

namespace TauCeti.AffineBoundTightening

variable {n m : ℕ}

/-- Independent decision variables: joint endpoints and a pair of products per coefficient. -/
@[ext]
structure Assignment (n m : ℕ) where
  /-- The variable and row endpoint functions. -/
  endpoints : Raw n m
  /-- The lower product coordinates. -/
  zL : Matrix (Fin m) (Fin n) ℝ
  /-- The upper product coordinates. -/
  zU : Matrix (Fin m) (Fin n) ℝ

/-- The assignment obtained by filling in the signed products of the given endpoints. -/
noncomputable def canonical (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) : Assignment n m :=
  ⟨q, zLo A q, zHi A q⟩

/-- The canonical assignment keeps the given endpoints. -/
@[simp]
theorem canonical_endpoints (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) :
    (canonical A q).endpoints = q :=
  (rfl)

/-- The canonical lower products are the signed lower endpoints. -/
@[simp]
theorem canonical_zL (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) :
    (canonical A q).zL = zLo A q :=
  (rfl)

/-- The canonical upper products are the signed upper endpoints. -/
@[simp]
theorem canonical_zU (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) :
    (canonical A q).zU = zHi A q :=
  (rfl)

/-- The scalar affine constraints for an assignment. The branch in each signed product equality
is determined by `A`, not by a decision variable. A zero coefficient imposes the product
equalities but no inverse-row inequalities. -/
structure lpFeasible (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (p : Assignment n m) : Prop where
  /-- The joint box is ordered. -/
  ordered : p.endpoints.1 ≤ p.endpoints.2
  /-- Both the variable and row bounds lie inside the initial bounds. -/
  within : Within p.endpoints q₀
  /-- Each lower product equals the signed lower endpoint, including at zero. -/
  productLo : ∀ i j, p.zL i j = zLo A p.endpoints i j
  /-- Each upper product equals the signed upper endpoint, including at zero. -/
  productHi : ∀ i j, p.zU i j = zHi A p.endpoints i j
  /-- Each row interval is contained in the interval of sums of its product coordinates. -/
  row : ∀ i, (∑ j, p.zL i j) ≤ p.endpoints.1 (.inr i) ∧
    p.endpoints.2 (.inr i) ≤ ∑ j, p.zU i j
  /-- The inverse-row bounds for a positive coefficient. -/
  positive : ∀ i j, 0 < A i j →
    (p.endpoints.1 (.inr i) - ∑ k ∈ Finset.univ.erase j, p.zU i k) / A i j ≤
      p.endpoints.1 (.inl j) ∧
    p.endpoints.2 (.inl j) ≤
      (p.endpoints.2 (.inr i) - ∑ k ∈ Finset.univ.erase j, p.zL i k) / A i j
  /-- The inverse-row bounds for a negative coefficient, with lower and upper bounds exchanged. -/
  negative : ∀ i j, A i j < 0 →
    (p.endpoints.2 (.inr i) - ∑ k ∈ Finset.univ.erase j, p.zL i k) / A i j ≤
      p.endpoints.1 (.inl j) ∧
    p.endpoints.2 (.inl j) ≤
      (p.endpoints.1 (.inr i) - ∑ k ∈ Finset.univ.erase j, p.zU i k) / A i j

/-- Feasible assignments of the scalar linear program. -/
def feasibleSet (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) : Set (Assignment n m) :=
  {p | lpFeasible A q₀ p}

/-- Membership in the scalar feasible set is satisfaction of the affine constraints. -/
@[simp]
theorem mem_feasibleSet {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m} {p : Assignment n m} :
    p ∈ feasibleSet A q₀ ↔ lpFeasible A q₀ p :=
  (Iff.rfl)

/-- The objective to maximize: total width of the joint box, independent of the products. -/
noncomputable def objective (p : Assignment n m) : ℝ := width p.endpoints

/-- The objective is the width of the endpoints. -/
@[simp]
theorem objective_eq_width (p : Assignment n m) : objective p = width p.endpoints :=
  (rfl)

/-- The objective counts both variable widths and row widths. -/
theorem objective_eq_sum_add_sum (p : Assignment n m) :
    objective p = (∑ j : Fin n, (p.endpoints.2 (.inl j) - p.endpoints.1 (.inl j))) +
      ∑ i : Fin m, (p.endpoints.2 (.inr i) - p.endpoints.1 (.inr i)) := by
  rw [objective_eq_width, width_eq_sum_add_sum]

/-- Every feasible assignment has ordered product coordinates. -/
theorem lpFeasible.zL_le_zU {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m} {p : Assignment n m}
    (hp : lpFeasible A q₀ p) (i : Fin m) (j : Fin n) : p.zL i j ≤ p.zU i j := by
  rw [hp.productLo i j, hp.productHi i j]
  exact zLo_le_zHi (hp.ordered (.inl j))

/-- Feasible assignments are exactly the canonical assignments of ordered raw fixed boxes. -/
theorem lp_iff_fixed (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (p : Assignment n m) :
    lpFeasible A q₀ p ↔ p = canonical A p.endpoints ∧ p.endpoints.1 ≤ p.endpoints.2 ∧
      Function.IsFixedPt (step A q₀) p.endpoints := by
  suffices hc : ∀ q : Raw n m, lpFeasible A q₀ (canonical A q) ↔
      q.1 ≤ q.2 ∧ Function.IsFixedPt (step A q₀) q by
    constructor
    · intro hp
      have heq : p = canonical A p.endpoints := Assignment.ext (canonical_endpoints A _).symm
        (by simpa using Matrix.ext hp.productLo) (by simpa using Matrix.ext hp.productHi)
      exact ⟨heq, (hc p.endpoints).mp (heq ▸ hp)⟩
    · rintro ⟨heq, hq, hf⟩
      exact heq.symm ▸ (hc p.endpoints).mpr ⟨hq, hf⟩
  -- Once the products are canonical, the scalar sums are the image and omitted sums.
  intro q
  rw [isFixedPt_step_iff]
  constructor
  · intro hp
    refine ⟨by simpa using hp.ordered, by simpa using hp.within, ?_, fun i j => ?_⟩
    · simpa [imageLo_def, imageHi_def] using hp.row
    rcases lt_trichotomy (A i j) 0 with h | h | h
    · simpa [inverseLo_of_neg h, inverseHi_of_neg h, restLo_def, restHi_def] using
        hp.negative i j h
    · simp [inverseLo_of_zero h, inverseHi_of_zero h]
    · simpa [inverseLo_of_pos h, inverseHi_of_pos h, restLo_def, restHi_def] using
        hp.positive i j h
  · rintro ⟨hq, hwithin, hrow, hinv⟩
    refine ⟨by simpa using hq, by simpa using hwithin, by simp, by simp, ?_, ?_, ?_⟩
    · simpa [imageLo_def, imageHi_def] using hrow
    · intro i j h
      simpa [inverseLo_of_pos h, inverseHi_of_pos h, restLo_def, restHi_def] using hinv i j
    · intro i j h
      simpa [inverseLo_of_neg h, inverseHi_of_neg h, restLo_def, restHi_def] using hinv i j

/-- An initially enclosed graph point gives a feasible canonical singleton assignment. -/
theorem lpFeasible_canonical_graph {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m} {x : Fin n → ℝ}
    (hx : graph A x ∈ Icc q₀.1 q₀.2) :
    lpFeasible A q₀ (canonical A (graph A x, graph A x)) := by
  have hmem : graph A x ∈ Icc (graph A x) (graph A x) := ⟨le_rfl, le_rfl⟩
  have hp := graph_mem_Icc_step (q := (graph A x, graph A x)) hmem hx
  have hf : Function.IsFixedPt (step A q₀) (graph A x, graph A x) :=
    (step_within_self A q₀ (graph A x, graph A x)).antisymm (within_iff.mpr hp)
  apply (lp_iff_fixed A q₀ _).mpr
  simpa using hf

/-- Infeasibility rules out every affine graph point inside the initial joint box, without any
assumption on the iterates. -/
theorem preimage_Icc_eq_empty_of_feasibleSet_eq_empty {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m}
    (h : feasibleSet A q₀ = ∅) : graph A ⁻¹' Icc q₀.1 q₀.2 = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun _ hx =>
    eq_empty_iff_forall_notMem.mp h _ (mem_feasibleSet.mpr (lpFeasible_canonical_graph hx))

end TauCeti.AffineBoundTightening
