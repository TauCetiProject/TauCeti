/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Meromorphy of uncompleted Dirichlet L-functions

For every Dirichlet character `χ` modulo `N ≥ 1`, Mathlib's analytically continued L-function
`χ.LFunction` is meromorphic on the whole complex plane
(`DirichletCharacter.meromorphic_LFunction`). For a nonprincipal character `χ.LFunction` is entire
(`DirichletCharacter.differentiable_LFunction`), while for the principal character it agrees away
from `1` with the quotient of the entire function `DirichletCharacter.LFunctionTrivChar₁ N` by
`s - 1`.

The analytic input is David Loeffler and Michael Stoll's development in
`Mathlib.NumberTheory.LSeries.DirichletContinuation`.
-/

public section

open scoped Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- Every Dirichlet character has a meromorphic L-function on the whole plane. -/
@[fun_prop]
theorem meromorphic_LFunction : Meromorphic χ.LFunction := by
  intro z
  by_cases hχ : χ = 1
  · have hne : ∀ᶠ s in 𝓝[≠] z, s ≠ 1 := by
      rcases eq_or_ne z 1 with rfl | hz1
      · exact self_mem_nhdsWithin
      · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds hz1)
    refine (((differentiable_LFunctionTrivChar₁ N).analyticAt z).meromorphicAt.div
      (analyticAt_id.sub (analyticAt_const (v := (1 : ℂ)))).meromorphicAt).congr
      (hne.mono fun s hs ↦ ?_)
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    rw [hχ, Pi.div_apply, Pi.sub_apply, id_eq, LFunctionTrivChar₁, Function.update_of_ne hs,
      LFunctionTrivChar, mul_div_cancel_left₀ _ hs1]
  · exact ((differentiable_LFunction hχ).analyticAt z).meromorphicAt

end DirichletCharacter
