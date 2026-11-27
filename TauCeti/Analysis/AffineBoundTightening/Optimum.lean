/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.AffineBoundTightening.LinearProgram
public import TauCeti.Analysis.AffineBoundTightening.Limit

/-!
# The unique joint-width optimum of simultaneous affine bound tightening

The scalar program is feasible exactly when every actual public iterate is nonempty.
Under this condition its maximum total variable and row width is attained by the canonical
assignment of the actual endpoint limit. This maximizer is unique as an entire assignment:
equal optimal width forces equal endpoints, and the scalar product equalities determine all
remaining coordinates. No affine graph point or optimization oracle is assumed.

## Main results

* `TauCeti.AffineBoundTightening.run_nonempty_iff_lp`: equivalence of nonempty actual public
  iterates and existence of a scalar-feasible assignment.
* `TauCeti.AffineBoundTightening.unique_full_width_optimum`: feasibility, maximum joint width
  and uniqueness of the entire canonical limit assignment.

## References

* P. Belotti, S. Cafieri, J. Lee, and L. Liberti, *Feasibility-Based Bounds Tightening via Fixed
  Points*, COCOA 2010, LNCS 6508, pp. 65–76, Proposition 4.1, p. 72 and Theorem 4.2, p. 73.
  The scalar constraints have the display corrections documented in `LinearProgram`.
  The endpoint-limit conclusion here explicitly requires nonempty actual iterates and uses
  the joint variable-and-row objective, not the variable-only objective of the 2012 extension.
-/

public section

open Set

namespace TauCeti.AffineBoundTightening

noncomputable section

variable {n m : ℕ}

/-- Every actual public iterate is nonempty exactly when there is a scalar-feasible assignment.
Either condition implies that the initial endpoints are ordered; no separate order premise
is needed. -/
theorem run_nonempty_iff_lp (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) :
    (∀ k, (publicRun A q₀ k : Set (Coord n m → ℝ)).Nonempty) ↔
      ∃ p, IsFeasible A q₀ p :=
  (forall_coe_publicRun_nonempty_iff_exists_isFixedPt_step A q₀).trans
    exists_isFeasible_iff.symm

/-- Under nonempty actual public iterates, the canonical endpoint limit is feasible and attains
the maximum joint variable-and-row width. Nonemptiness at the initial iterate supplies initial
endpoint ordering. It is the unique maximizing entire assignment,
including all row endpoints and signed product coordinates. -/
theorem unique_full_width_optimum (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m)
    (h : ∀ k, (publicRun A q₀ k : Set (Coord n m → ℝ)).Nonempty) :
    IsFeasible A q₀ (canonical A (endpointLimit A q₀)) ∧
    IsMaxOn objective (feasibleSet A q₀) (canonical A (endpointLimit A q₀)) ∧
    (∀ p, IsFeasible A q₀ p → IsMaxOn objective (feasibleSet A q₀) p →
      p = canonical A (endpointLimit A q₀)) := by
  have hl := actual_limit A q₀ h
  have hfeas : IsFeasible A q₀ (canonical A (endpointLimit A q₀)) :=
    isFeasible_canonical_iff.mpr ⟨hl.1, hl.2.2.2.1⟩
  have hwithin (p : Assignment n m) (hp : IsFeasible A q₀ p) :
      Within p.endpoints (endpointLimit A q₀) :=
    within_endpointLimit_of_isFixedPt_step (isFeasible_iff.mp hp).2.2
  refine ⟨hfeas, ?_, ?_⟩
  · apply isMaxOn_iff.mpr
    intro p hp
    simpa only [objective_def, canonical_endpoints] using
      (hwithin p (mem_feasibleSet.mp hp)).width_le
  · intro p hp hmax
    have hle : width (endpointLimit A q₀) ≤ width p.endpoints := by
      simpa only [objective_def, canonical_endpoints] using
        (isMaxOn_iff.mp hmax) _ (mem_feasibleSet.mpr hfeas)
    have he : p.endpoints = endpointLimit A q₀ :=
      eq_of_within_of_width_eq (hwithin p hp)
        (le_antisymm (hwithin p hp).width_le hle)
    rw [hp.eq_canonical, he]

end

end TauCeti.AffineBoundTightening
