/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Uniform zero-free neighborhoods for finite Dirichlet families

For a nonprincipal Dirichlet character, the canonical continued L-function is continuous
and nonzero at one. Finiteness of the characters at each positive level, followed by
finiteness of the levels up to a fixed bound, makes this nonvanishing uniform on a
single complex disk. The resulting real-zero gap depends on the fixed level bound;
it does not exclude exceptional zeros in an unbounded family. The regularized L-functions,
including those of principal characters, also have a common positive lower bound on a
neighborhood of one, in norm.

For primitive characters the level equals the conductor, so these results provide the
rational finite-family input to the small-conductor step of zero-free-region arguments.
No primitivity or reality hypothesis is needed for the disk theorem itself.

The analytic inputs are Mathlib's `DirichletCharacter.differentiable_LFunction`
from `Mathlib.NumberTheory.LSeries.DirichletContinuation` and
`DirichletCharacter.LFunction_apply_one_ne_zero` from
`Mathlib.NumberTheory.LSeries.Nonvanishing`. The finite character instance is
supplied by `Mathlib.NumberTheory.DirichletCharacter.Orthogonality`. The quantitative
finite-family step follows the argument in lsernau/grh-lean (revision `72fead1`,
`New.eventually_norm_logDeriv_entireL_le_near_one`).

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 14.
-/

public section

open Filter Topology Metric DirichletCharacter

namespace TauCeti.DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- At a fixed positive level, all nonprincipal continued L-functions are nonzero
on a common neighborhood of one. -/
theorem eventually_forall_LFunction_ne_zero :
    ∀ᶠ s : ℂ in 𝓝 1, ∀ χ : DirichletCharacter ℂ N, χ ≠ 1 → χ.LFunction s ≠ 0 := by
  apply Filter.eventually_all.mpr
  intro χ
  by_cases hχ : χ = 1
  · exact Filter.Eventually.of_forall fun _ h ↦ (h hχ).elim
  · exact ((differentiable_LFunction hχ).continuous.continuousAt.eventually_ne
      (LFunction_apply_one_ne_zero hχ)).mono fun _ h _ ↦ h

/-- For each fixed level bound, a single positive closed-disk radius works for all
nonprincipal characters. The radius is selected before the level and character. -/
theorem exists_pos_forall_LFunction_ne_zero (Q : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) [NeZero N], N ≤ Q →
      ∀ χ : DirichletCharacter ℂ N, χ ≠ 1 →
        ∀ s : ℂ, ‖s - 1‖ ≤ δ → χ.LFunction s ≠ 0 := by
  have h : ∀ᶠ s : ℂ in 𝓝 1, ∀ N ∈ Finset.range (Q + 1),
      ∀ _ : NeZero N, ∀ χ : DirichletCharacter ℂ N, χ ≠ 1 → χ.LFunction s ≠ 0 := by
    apply (Filter.eventually_all_finset _).mpr
    intro N _
    by_cases hN : N = 0
    · exact Filter.Eventually.of_forall fun _ h ↦ (h.out hN).elim
    · let : NeZero N := ⟨hN⟩
      filter_upwards [eventually_forall_LFunction_ne_zero (N := N)] with s hs _
      exact hs
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro N _ hN χ hχ s hs
  exact h (by rw [dist_eq_norm]; linarith) N
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hN)) inferInstance χ hχ

/-- Real zeros of nonprincipal characters of bounded positive level have a common
positive distance from one. This does not assert a uniform gap as the bound grows. -/
theorem exists_pos_real_zero_gap (Q : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) [NeZero N], N ≤ Q →
      ∀ χ : DirichletCharacter ℂ N, χ ≠ 1 →
        ∀ β : ℝ, β < 1 → χ.LFunction β = 0 → δ < 1 - β := by
  obtain ⟨δ, hδ, h⟩ := exists_pos_forall_LFunction_ne_zero Q
  refine ⟨δ, hδ, ?_⟩
  intro N _ hN χ hχ β hβ hz
  by_contra hn
  apply h N hN χ hχ (β : ℂ) _ hz
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_neg (sub_neg.mpr hβ)]
  linarith

/-- The regularized L-functions of all characters of positive level at most `B` are uniformly
bounded away from zero on a common neighborhood of `1`. -/
theorem exists_pos_eventually_le_norm_regularizedLFunction_of_level_le (B : ℕ) :
    ∃ c > (0 : ℝ), ∀ᶠ s : ℂ in 𝓝 1, ∀ (n : ℕ) [NeZero n], n ≤ B →
      ∀ χ : DirichletCharacter ℂ n, c ≤ ‖χ.regularizedLFunction s‖ := by
  let ι := ↥(Finset.Icc 1 B)
  have (n : ι) : NeZero n.val := ⟨Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp n.property).1⟩
  have hm (n : ι) (χ : DirichletCharacter ℂ n.val) :
      ∀ᶠ c : ℝ in 𝓝 (0 : ℝ), c < ‖χ.regularizedLFunction 1‖ :=
    eventually_lt_nhds (norm_pos_iff.mpr (χ.regularizedLFunction_ne_zero_of_one_le_re (by simp)))
  obtain ⟨c, hc, hmin⟩ :
      ∃ c : ℝ, 0 < c ∧ ∀ (n : ι) (χ : DirichletCharacter ℂ n.val),
        c < ‖χ.regularizedLFunction 1‖ := by
    have h : ∀ᶠ c : ℝ in 𝓝[Set.Ioi 0] 0, ∀ (n : ι) (χ : DirichletCharacter ℂ n.val),
        c < ‖χ.regularizedLFunction 1‖ :=
      ((eventually_all.mpr fun n ↦ eventually_all.mpr (hm n))).filter_mono nhdsWithin_le_nhds
    exact (eventually_mem_nhdsWithin.and h).exists
  refine ⟨c, hc, ?_⟩
  have hnear : ∀ᶠ s : ℂ in 𝓝 1, ∀ (n : ι) (χ : DirichletCharacter ℂ n.val),
      c < ‖χ.regularizedLFunction s‖ :=
    eventually_all.mpr fun n ↦ eventually_all.mpr fun χ ↦ by
      have hc₁ := (χ.differentiableAt_regularizedLFunction (s := 1) (.inl one_ne_zero)).continuousAt
      exact hc₁.norm.tendsto.eventually_const_lt (hmin n χ)
  filter_upwards [hnear] with s hs n inst hn χ
  exact (hs ⟨n, Finset.mem_Icc.mpr ⟨NeZero.pos n, hn⟩⟩ χ).le

end TauCeti.DirichletCharacter
