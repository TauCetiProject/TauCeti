/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import TauCeti.Analysis.Normed.Module.Essential
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import TauCeti.Analysis.Normed.Module.CohenFactorization.Basic

/-!
# Cohen–Hewitt factorization for Banach left modules over C⋆-algebras

Instantiates `ContinuousLinearMap.exists_apply_eq_of_mem_essentialSubmodule` and
`ContinuousLinearMap.coe_essentialSubmodule_eq_range` from
`TauCeti.Analysis.Normed.Module.CohenFactorization.Basic` along the canonical approximate unit
`CStarAlgebra.increasingApproximateUnit A`, formulated in terms of `L.essentialSubmodule` and
`⋃ a, Set.range (L a)` to match the essential-subspace convention for C⋆-algebra representations
and multiplier homomorphisms.

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

/-- **Cohen–Hewitt factorization for Banach left modules over a C⋆-algebra.** Every `x` in
`L.essentialSubmodule` factors as `x = L a y` with `‖a‖ ≤ 1`,
`y ∈ closure (Set.range fun b => L b x)`, and `‖y - x‖ < ε`. -/
theorem exists_norm_le_one_apply_eq_of_mem_essentialSubmodule (L : A →L[ℂ] E →L[ℂ] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) {x : E}
    (hx : x ∈ L.essentialSubmodule) {ε : ℝ} (hε : 0 < ε) :
    ∃ a y, ‖a‖ ≤ 1 ∧ y ∈ closure (Set.range fun b => L b x) ∧ ‖y - x‖ < ε ∧ L a y = x := by
  let := CStarAlgebra.spectralOrder A; have := CStarAlgebra.spectralOrderedRing A
  have hl := CStarAlgebra.increasingApproximateUnit A; have := hl.neBot
  exact L.exists_apply_eq_of_mem_essentialSubmodule hL
    hl.eventually_norm hl.tendsto_mul_right hx hε

/-- Over a C⋆-algebra `A`, the set `⋃ a, Set.range (L a)` of products for a bounded left action
`L : A →L[ℂ] E →L[ℂ] E` on a complex Banach space `E` already equals `L.essentialSubmodule`. -/
theorem coe_essentialSubmodule_eq_iUnion_range (L : A →L[ℂ] E →L[ℂ] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) :
    (L.essentialSubmodule : Set E) = ⋃ a, Set.range (L a) := by
  let := CStarAlgebra.spectralOrder A; have := CStarAlgebra.spectralOrderedRing A
  have hl := CStarAlgebra.increasingApproximateUnit A; have := hl.neBot
  have hrange : (Set.range fun p : A × E => L p.1 p.2) = ⋃ a, Set.range (L a) :=
    Set.ext fun _ => by simp [Prod.exists]
  rw [← hrange]
  exact L.coe_essentialSubmodule_eq_range hL hl.eventually_norm hl.tendsto_mul_right

end ContinuousLinearMap
