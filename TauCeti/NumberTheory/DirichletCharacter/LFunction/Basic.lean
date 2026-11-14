/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Analyticity and meromorphy of continued Dirichlet L-functions

Mathlib's `DirichletCharacter.LFunction χ` continues the Dirichlet series of a character `χ` mod
`N` (`N ≠ 0`) to a function differentiable everywhere except at `s = 1` when `χ = 1`, where
`(s - 1) L(s, 1)` extends to the entire function `DirichletCharacter.LFunctionTrivChar₁ N`. Since
differentiability on an open subset of `ℂ` implies analyticity, `χ.LFunction` is analytic away from
that pole and meromorphic on the whole complex plane.

## Main results

* `DirichletCharacter.analyticAt_LFunction`: `χ.LFunction` is analytic at `s` whenever `s ≠ 1` or
  `χ ≠ 1`.
* `DirichletCharacter.meromorphic_LFunction`: `χ.LFunction` is meromorphic on `ℂ`.

## References

* D. Loeffler, M. Stoll, `Mathlib.NumberTheory.LSeries.DirichletContinuation`.
* H. Davenport, *Multiplicative Number Theory*, Ch. 4.
-/

public section

open scoped Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- The continued Dirichlet L-function is analytic everywhere except possibly at `s = 1` for the
principal character. -/
@[fun_prop]
theorem analyticAt_LFunction {s : ℂ} (h1 : s ≠ 1 ∨ χ ≠ 1) : AnalyticAt ℂ χ.LFunction s := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have he1 : ∀ᶠ z in 𝓝 s, z ≠ 1 ∨ χ ≠ 1 := by
    rcases h1 with h1 | h1
    · filter_upwards [eventually_ne_nhds h1] with z hz using Or.inl hz
    · exact Filter.Eventually.of_forall fun _ ↦ Or.inr h1
  filter_upwards [he1] with z hz1
  exact χ.differentiableAt_LFunction z hz1

/-- Every Dirichlet character has a meromorphic continued L-function on the whole complex plane. -/
@[fun_prop]
theorem meromorphic_LFunction : Meromorphic χ.LFunction := by
  intro z
  rcases eq_or_ne z 1 with rfl | hz
  · by_cases hχ : χ = 1
    · subst hχ
      refine MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr
        ⟨-1, LFunctionTrivChar₁ N, (differentiable_LFunctionTrivChar₁ N).analyticAt 1, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s (hs : s ≠ 1)
      rw [LFunctionTrivChar₁, Function.update_of_ne hs, LFunctionTrivChar, smul_eq_mul,
        zpow_neg_one]
      field_simp [sub_ne_zero.mpr hs]
    · exact (χ.analyticAt_LFunction (.inr hχ)).meromorphicAt
  · exact (χ.analyticAt_LFunction (.inl hz)).meromorphicAt

end DirichletCharacter
