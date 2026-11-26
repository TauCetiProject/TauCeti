/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Calculus.IteratedFDeriv.Reciprocal

/-!
# Iterated derivatives of partial fractions

The Taylor coefficients of a finite sum of simple fractions are weighted sums of inverse powers
of the displacements of its poles. The formulas apply over a nontrivially normed field
and allow zero-weight terms at the expansion point.
-/

public section

open scoped Nat

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

-- A single simple fraction is smooth at `c` unless its pole is at `c` with nonzero weight.
private theorem contDiffAt_div_sub (a ρ c : 𝕜) (n : WithTop ℕ∞) (h : ρ = c → a = 0) :
    ContDiffAt 𝕜 n (fun z ↦ a / (z - ρ)) c := by
  by_cases hρ : ρ = c
  · simp [hρ, h hρ, contDiffAt_const]
  · have hne := sub_ne_zero.mpr (Ne.symm hρ)
    fun_prop

namespace Finset

/-- A finite partial-fraction sum `z ↦ ∑ ρ ∈ S, m ρ / (z - ρ)` is `C^n` at `c`, provided any pole
at `c` itself has weight `m c = 0`. -/
theorem contDiffAt_sum_div_sub (S : Finset 𝕜) (m : 𝕜 → 𝕜) (c : 𝕜) (n : WithTop ℕ∞)
    (hc : c ∈ S → m c = 0) : ContDiffAt 𝕜 n (fun z ↦ ∑ ρ ∈ S, m ρ / (z - ρ)) c :=
  ContDiffAt.sum fun ρ hρ ↦ contDiffAt_div_sub _ _ _ _ (by rintro rfl; exact hc hρ)

/-- The `k`-th iterated derivative of `z ↦ ∑ ρ ∈ S, m ρ / (z - ρ)` at `c` is
`(-1) ^ k * k ! * ∑ ρ ∈ S, m ρ / (c - ρ) ^ (k + 1)`. A pole at `c` itself is allowed when its
weight `m c` is zero. -/
theorem iteratedDeriv_sum_div_sub (S : Finset 𝕜) (m : 𝕜 → 𝕜) (c : 𝕜) (k : ℕ)
    (hc : c ∈ S → m c = 0) :
    iteratedDeriv k (fun z ↦ ∑ ρ ∈ S, m ρ / (z - ρ)) c =
      ((-1 : 𝕜) ^ k * k !) * ∑ ρ ∈ S, m ρ / (c - ρ) ^ (k + 1) := by
  have ha (ρ : 𝕜) (hρ : ρ ∈ S) : ContDiffAt 𝕜 k (fun z ↦ m ρ / (z - ρ)) c :=
    contDiffAt_div_sub _ _ _ _ (by rintro rfl; exact hc hρ)
  rw [iteratedDeriv_fun_sum ha, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ _
  rw [congrFun (iteratedDeriv_comp_sub_const (n := k) (f := fun y ↦ m ρ / y) (s := ρ)) c,
    TauCeti.iteratedDeriv_const_div]
  ring

end Finset
