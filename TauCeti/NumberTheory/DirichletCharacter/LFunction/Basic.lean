/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Meromorphic.Order

/-!
# Regularity, meromorphy, and poles of continued Dirichlet `L`-functions

Mathlib's continued Dirichlet `L`-function `DirichletCharacter.LFunction χ` is entire for every
nonprincipal character `χ ≠ 1` and differentiable away from `s = 1` for the principal character
`LFunctionTrivChar N` (`DirichletCharacter.differentiableAt_LFunction`,
`DirichletCharacter.LFunctionTrivChar_residue_one`).

This file packages the basic regularity and meromorphic-order API for the uncompleted continued
function `χ.LFunction`, without going through completed `L`-functions or Gamma factors:

* `DirichletCharacter.not_differentiableAt_LFunctionTrivChar_one` and
  `DirichletCharacter.differentiableAt_LFunction_iff`: `χ.LFunction` is differentiable at `s` if
  and only if `s ≠ 1` or `χ ≠ 1`.
* `DirichletCharacter.analyticAt_LFunction` and `DirichletCharacter.meromorphic_LFunction`:
  `χ.LFunction` is analytic away from the principal pole `s = 1` and meromorphic on `ℂ` (both
  registered as `@[fun_prop]` rules).
* `DirichletCharacter.meromorphicOrderAt_LFunctionTrivChar_one` and
  `DirichletCharacter.meromorphicOrderAt_LFunction_pos_iff`: `LFunctionTrivChar N` has a simple
  pole (meromorphic order `-1`) at `s = 1`, so positive meromorphic order characterizes the zeros
  of `χ.LFunction` away from that pole.

## References

* D. Loeffler, M. Stoll, `Mathlib.NumberTheory.LSeries.DirichletContinuation`.
* H. Davenport, *Multiplicative Number Theory*, Ch. 4.
-/

public section

open Complex Filter
open scoped Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

omit χ in
/-- The principal Dirichlet `L`-function modulo `N` is not differentiable at its simple pole
`s = 1`. -/
theorem not_differentiableAt_LFunctionTrivChar_one :
    ¬ DifferentiableAt ℂ (LFunctionTrivChar N) 1 := by
  intro hd
  have h0 : Tendsto (fun z ↦ (z - 1) * LFunctionTrivChar N z) (𝓝[≠] 1) (𝓝 0) := by
    have h := (((continuous_id.sub (continuous_const (y := (1 : ℂ)))).tendsto (1 : ℂ)).mul
      hd.continuousAt.tendsto).mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
    simpa using h
  have h1 := tendsto_nhds_unique h0 (LFunctionTrivChar_residue_one (N := N))
  exact LFunctionTrivChar₁_apply_one_ne_zero N (by simpa using h1.symm)

/-- The continued Dirichlet `L`-function `χ.LFunction` is differentiable at `s` if and only if
`s ≠ 1` or `χ ≠ 1`. -/
@[simp]
theorem differentiableAt_LFunction_iff (s : ℂ) :
    DifferentiableAt ℂ χ.LFunction s ↔ s ≠ 1 ∨ χ ≠ 1 := by
  refine ⟨fun hd ↦ by_contra fun h ↦ ?_, χ.differentiableAt_LFunction s⟩
  obtain ⟨hs1, hχ1⟩ := not_or.mp h
  rw [not_ne_iff.mp hs1, not_ne_iff.mp hχ1] at hd
  exact not_differentiableAt_LFunctionTrivChar_one hd

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

omit χ in
/-- The principal Dirichlet `L`-function modulo `N` has a simple pole (meromorphic order `-1`) at
`s = 1`. -/
@[simp]
theorem meromorphicOrderAt_LFunctionTrivChar_one :
    meromorphicOrderAt (LFunctionTrivChar N) 1 = -1 := by
  simpa using ((1 : DirichletCharacter ℂ N).meromorphic_LFunction 1)
    |>.meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul (LFunctionTrivChar₁_apply_one_ne_zero N)
    (by simpa using LFunctionTrivChar_residue_one (N := N))

/-- The continued Dirichlet `L`-function `χ.LFunction` has positive meromorphic order at `s` if and
only if `χ.LFunction s = 0` and `(s ≠ 1 ∨ χ ≠ 1)`. -/
theorem meromorphicOrderAt_LFunction_pos_iff {s : ℂ} :
    0 < meromorphicOrderAt χ.LFunction s ↔ χ.LFunction s = 0 ∧ (s ≠ 1 ∨ χ ≠ 1) := by
  by_cases hs : s = 1 ∧ χ = 1
  · obtain ⟨rfl, rfl⟩ := hs
    rw [← LFunctionTrivChar]
    simp
  · have hs' := not_and_or.mp hs
    simp [(χ.analyticAt_LFunction hs').meromorphicOrderAt_pos_iff_eq_zero, hs']

end DirichletCharacter
