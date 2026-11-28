/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Lightweight analyticity and meromorphy for continued Dirichlet `L`-functions

This module packages the basic local regularity lemmas for `DirichletCharacter.LFunction` that
depend only on `Mathlib.NumberTheory.LSeries.DirichletContinuation` and
`Mathlib.Analysis.Meromorphic.Order`, without importing `Mathlib.NumberTheory.LSeries.Nonvanishing`:

* `DirichletCharacter.LFunctionTrivChar₁_apply_of_ne_one`: away from `s = 1`, the pole-removed
  principal `L`-function is `(s - 1) L(s)`.
* `DirichletCharacter.analyticAt_LFunction`: `χ.LFunction` is analytic at `s` whenever `s ≠ 1` or
  `χ ≠ 1` (`@[fun_prop]`).
* `DirichletCharacter.meromorphic_LFunction`: `χ.LFunction` is meromorphic on `ℂ` (`@[fun_prop]`).

## References

* D. Loeffler, M. Stoll, `Mathlib.NumberTheory.LSeries.DirichletContinuation`.
-/

public section

open Complex Filter
open scoped Topology

namespace DirichletCharacter

/-- Away from `s = 1`, the pole-removed principal `L`-function is `(s - 1) L(s)`. -/
theorem LFunctionTrivChar₁_apply_of_ne_one (N : ℕ) [NeZero N] {s : ℂ} (hs : s ≠ 1) :
    LFunctionTrivChar₁ N s = (s - 1) * LFunctionTrivChar N s :=
  Function.update_of_ne hs ..

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
      rw [LFunctionTrivChar₁_apply_of_ne_one N hs, smul_eq_mul, zpow_neg_one]
      field_simp [sub_ne_zero.mpr hs]
    · exact (χ.analyticAt_LFunction (.inr hχ)).meromorphicAt
  · exact (χ.analyticAt_LFunction (.inl hz)).meromorphicAt

end DirichletCharacter
