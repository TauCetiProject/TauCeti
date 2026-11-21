/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import TauCeti.Analysis.Normed.Module.CohenFactorization.Basic

/-!
# Cohen–Hewitt factorization for Banach left modules over C⋆-algebras

Instantiates `ContinuousLinearMap.exists_apply_eq_of_mem_topologicalClosure_span` and
`ContinuousLinearMap.coe_topologicalClosure_span_range_eq` from
`TauCeti.Analysis.Normed.Module.CohenFactorization.Basic` along the canonical approximate unit
`CStarAlgebra.increasingApproximateUnit A`, formulated in terms of `⋃ a, Set.range (L a)` to match
the essential-subspace convention for C⋆-algebra representations and multiplier homomorphisms.

## References

* P. J. Cohen, *Factorization in group algebras*, Duke Math. J. 26 (1959), 199–205.
* E. Hewitt, *The ranges of certain convolution operators*, Math. Scand. 15 (1964), 147–155.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, Theorem 2.9.24.
-/

public section

open scoped CStarAlgebra

namespace ContinuousLinearMap

variable {A E : Type*} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **Cohen–Hewitt factorization for Banach left modules over a C⋆-algebra.** Every `x` in the
closed linear span of `⋃ a, Set.range (L a)` factors as `x = L a y` with `‖a‖ ≤ 1`,
`y ∈ closure (Set.range fun b => L b x)`, and `‖y - x‖ < ε`. -/
theorem exists_apply_eq_of_mem_topologicalClosure_span_iUnion (L : A →L[ℂ] E →L[ℂ] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) {x : E}
    (hx : x ∈ (Submodule.span ℂ (⋃ a, Set.range (L a))).topologicalClosure) {ε : ℝ} (hε : 0 < ε) :
    ∃ a y, ‖a‖ ≤ 1 ∧ y ∈ closure (Set.range fun b => L b x) ∧ ‖y - x‖ < ε ∧ L a y = x := by
  let := CStarAlgebra.spectralOrder A; have := CStarAlgebra.spectralOrderedRing A
  have hl := CStarAlgebra.increasingApproximateUnit A; have := hl.neBot
  have hrange : (Set.range fun p : A × E => L p.1 p.2) = ⋃ a, Set.range (L a) :=
    Set.ext fun _ => by simp [Prod.exists]
  exact L.exists_apply_eq_of_mem_topologicalClosure_span hL
    hl.eventually_norm hl.tendsto_mul_right (by rwa [hrange]) hε

/-- Over a C⋆-algebra `A`, the set `⋃ a, Set.range (L a)` of products for a bounded left action
`L : A →L[ℂ] E →L[ℂ] E` on a complex Banach space `E` already equals its closed linear span. -/
theorem coe_topologicalClosure_span_iUnion_range_eq (L : A →L[ℂ] E →L[ℂ] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) :
    ((Submodule.span ℂ (⋃ a, Set.range (L a))).topologicalClosure : Set E) =
      ⋃ a, Set.range (L a) := by
  let := CStarAlgebra.spectralOrder A; have := CStarAlgebra.spectralOrderedRing A
  have hl := CStarAlgebra.increasingApproximateUnit A; have := hl.neBot
  have hrange : (Set.range fun p : A × E => L p.1 p.2) = ⋃ a, Set.range (L a) :=
    Set.ext fun _ => by simp [Prod.exists]
  rw [← hrange]
  exact L.coe_topologicalClosure_span_range_eq hL hl.eventually_norm hl.tendsto_mul_right

end ContinuousLinearMap
