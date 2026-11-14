/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Iterated derivatives of towers and shifted power sums

A sequence of functions linked by ordinary derivatives gives a smooth initial function
(`TauCeti.contDiff_of_derivative_tower`). We also record closed formulas for the iterated
derivatives of shifted monomials `t ↦ (t - t₀) ^ m` (`TauCeti.iteratedDeriv_sub_const_pow`) and of
finite linear combinations `t ↦ ∑ i ∈ s, c i * (t - t₀) ^ e i`
(`TauCeti.iteratedDeriv_sum_mul_sub_pow`).
-/

public section

open scoped ContDiff

namespace TauCeti

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A tower of functions with the stated successive ordinary derivatives gives a smooth zeroth
function. -/
theorem contDiff_of_derivative_tower (F : ℕ → 𝕜 → E)
    (hF : ∀ k x, HasDerivAt (F k) (F (k + 1) x) x) : ContDiff 𝕜 ∞ (F 0) := by
  have hiter (k : ℕ) : iteratedDeriv k (F 0) = F k := by
    induction k with
    | zero => exact iteratedDeriv_zero
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      exact funext (fun x ↦ (hF k x).deriv)
  apply contDiff_of_differentiable_iteratedDeriv (n := ⊤)
  intro k _
  rw [hiter k]
  exact fun x ↦ (hF k x).differentiableAt

/-- The `k`-th iterated derivative of `t ↦ (t - t₀) ^ m` at `z` is
`m.descFactorial k * (z - t₀) ^ (m - k)`. -/
theorem iteratedDeriv_sub_const_pow (k m : ℕ) (t₀ z : 𝕜) :
    iteratedDeriv k (fun t ↦ (t - t₀) ^ m) z = m.descFactorial k * (z - t₀) ^ (m - k) := by
  simpa only [Function.comp_def, iteratedDeriv_pow] using
    congrFun (iteratedDeriv_comp_sub_const k (· ^ m : 𝕜 → 𝕜) t₀) z

/-- The `k`-th iterated derivative of a finite linear combination
`t ↦ ∑ i ∈ s, c i * (t - t₀) ^ e i` of shifted powers. -/
theorem iteratedDeriv_sum_mul_sub_pow {ι : Type*} (k : ℕ) (s : Finset ι) (c : ι → 𝕜)
    (e : ι → ℕ) (t₀ z : 𝕜) :
    iteratedDeriv k (fun t ↦ ∑ i ∈ s, c i * (t - t₀) ^ e i) z =
      ∑ i ∈ s, c i * (e i).descFactorial k * (z - t₀) ^ (e i - k) := by
  rw [iteratedDeriv_fun_sum fun i _ ↦ by fun_prop]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_sub_const_pow, mul_assoc]

end TauCeti
