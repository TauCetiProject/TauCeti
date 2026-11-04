/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.DirichletEulerLog
import TauCeti.NumberTheory.LSeries.BoundaryConvergence.Endpoint
import TauCeti.NumberTheory.LSeries.BoundaryConvergence.OrderedEulerProduct
import TauCeti.NumberTheory.SumPrimeReciprocals

/-!
# The trivial Dirichlet character at `s = 1`

For a nontrivial Dirichlet character `χ` of positive level, the logarithm of `L(χ, s)` continues
holomorphically to an open neighbourhood of the closed half-plane `1 ≤ re s`
(`DirichletCharacter.exists_differentiableOn_exp_eq_LFunction`), and the ordered Euler products
`∏ p ≤ B, (1 - χ p / p)⁻¹` converge to `L(χ, 1)`
(`DirichletCharacter.tendsto_prod_primesLE_inv_LFunction_one`). This file shows that the
hypothesis `χ ≠ 1` cannot be dropped from either result.

For the trivial character `1` of positive level `N`, the Euler factor at a prime `p` is
`(1 - 1 / p)⁻¹` when `p ∤ N` and `1` when `p ∣ N`. So its ordered Euler products are partial Euler
products of the Riemann zeta function at `s = 1`, with the primes dividing `N` deleted. By the
divergence of the sum of the reciprocals of the primes
(`Nat.tendsto_prod_primesLE_filter_notMem_one_sub_inv_inv_atTop`), they tend to infinity in norm,
also after deleting the factors at any finite set of primes; in particular they have no limit in
`ℂ`.

Consequently the `L`-series of the coefficients `DirichletCharacter.eulerLogCoeff 1` has no
holomorphic extension to an open neighbourhood of `1 ≤ re s`. Otherwise the bounded Tauberian
theorem `TauCeti.LSeries.boundedDirichlet_tendsto_ordered_at_one` would make its ordered partial
sums at `1` converge, and `TauCeti.LSeries.tendsto_prod_primesLE_inv_of_tendsto_sum` would make the
ordered Euler products converge.

## Main results

* `DirichletCharacter.prod_primesLE_filter_notMem_inv_one_eq_ofReal`: the ordered Euler products
  of the trivial character are real partial Euler products of the Riemann zeta function at `1`.
* `DirichletCharacter.tendsto_norm_prod_primesLE_filter_notMem_inv_one_atTop`: they tend to
  infinity in norm.
* `DirichletCharacter.not_tendsto_prod_primesLE_filter_notMem_inv_one`,
  `DirichletCharacter.not_tendsto_prod_primesLE_inv_one`: they have no limit.
* `DirichletCharacter.not_differentiableOn_of_LSeriesHasSum_eulerLogCoeff_one`: the logarithm of
  the Euler product of the trivial character does not continue across `re s = 1`.
-/

public section

open Filter Finset
open scoped Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- **The ordered Euler products of the trivial character.** For the trivial Dirichlet character
`1` of positive level `N` and a finite set `S`, the finite Euler product over the primes `p ≤ B`
outside `S` is the real product of `(1 - 1 / p)⁻¹` over the primes `p ≤ B` that lie outside `S`
and do not divide `N`. -/
theorem prod_primesLE_filter_notMem_inv_one_eq_ofReal (S : Finset ℕ) (B : ℕ) :
    ∏ p ∈ Nat.primesLE B with p ∉ S, (1 - (1 : DirichletCharacter ℂ N) p / (p : ℂ))⁻¹ =
      ((∏ p ∈ Nat.primesLE B with p ∉ S ∪ N.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ : ℝ) : ℂ) := by
  have hsub : {p ∈ Nat.primesLE B | p ∉ S ∪ N.primeFactors} ⊆ {p ∈ Nat.primesLE B | p ∉ S} :=
    fun p ↦ by simp only [mem_filter, mem_union, not_or]; tauto
  rw [Complex.ofReal_prod, ← prod_subset hsub fun p hp hpT ↦ ?_]
  · refine prod_congr rfl fun p hp ↦ ?_
    simp only [mem_filter, mem_union, not_or, Nat.mem_primeFactors, not_and] at hp
    have hpp := Nat.prime_of_mem_primesLE hp.1
    rw [MulChar.one_apply ((ZMod.isUnit_prime_iff_not_dvd hpp).mpr
      fun hdvd ↦ hp.2.2 hpp hdvd (NeZero.ne N))]
    simp [one_div]
  · rw [mem_filter] at hp
    have hpp := Nat.prime_of_mem_primesLE hp.1
    have hdvd : p ∣ N := by
      by_contra h
      exact hpT (mem_filter.mpr ⟨hp.1, by simp [hp.2, Nat.mem_primeFactors, h]⟩)
    rw [MulChar.map_nonunit _ fun hu ↦ (ZMod.isUnit_prime_iff_not_dvd hpp).mp hu hdvd, zero_div,
      sub_zero, inv_one]

/-- **The ordered Euler products of the trivial character diverge.** For the trivial Dirichlet
character `1` of positive level and a finite set `S`, the norms of the finite Euler products
`∏ p ≤ B, p ∉ S, (1 - 1 p / p)⁻¹` tend to infinity as `B → ∞`. -/
theorem tendsto_norm_prod_primesLE_filter_notMem_inv_one_atTop (S : Finset ℕ) :
    Tendsto (fun B : ℕ ↦
      ‖∏ p ∈ Nat.primesLE B with p ∉ S, (1 - (1 : DirichletCharacter ℂ N) p / (p : ℂ))⁻¹‖)
      atTop atTop := by
  simp_rw [prod_primesLE_filter_notMem_inv_one_eq_ofReal, Complex.norm_real, Real.norm_eq_abs]
  exact tendsto_abs_atTop_atTop.comp
    (Nat.tendsto_prod_primesLE_filter_notMem_one_sub_inv_inv_atTop _)

/-- For the trivial Dirichlet character `1` of positive level and a finite set `S`, the finite
Euler products over the primes `p ≤ B` outside `S` have no limit in `ℂ`. Thus the hypothesis
`χ ≠ 1` of `DirichletCharacter.tendsto_prod_primesLE_filter_notMem_inv_LFunction_one` cannot be
dropped. -/
theorem not_tendsto_prod_primesLE_filter_notMem_inv_one (S : Finset ℕ) (L : ℂ) :
    ¬ Tendsto (fun B : ℕ ↦
      ∏ p ∈ Nat.primesLE B with p ∉ S, (1 - (1 : DirichletCharacter ℂ N) p / (p : ℂ))⁻¹)
      atTop (𝓝 L) := fun h ↦
  not_tendsto_nhds_of_tendsto_atTop (tendsto_norm_prod_primesLE_filter_notMem_inv_one_atTop S)
    _ h.norm

/-- For the trivial Dirichlet character `1` of positive level, the ordered Euler products
`∏ p ≤ B, (1 - 1 p / p)⁻¹` have no limit in `ℂ`. Thus the hypothesis `χ ≠ 1` of
`DirichletCharacter.tendsto_prod_primesLE_inv_LFunction_one` cannot be dropped. -/
theorem not_tendsto_prod_primesLE_inv_one (L : ℂ) :
    ¬ Tendsto (fun B : ℕ ↦
      ∏ p ∈ Nat.primesLE B, (1 - (1 : DirichletCharacter ℂ N) p / (p : ℂ))⁻¹) atTop (𝓝 L) := by
  simpa using not_tendsto_prod_primesLE_filter_notMem_inv_one (N := N) ∅ L

/-- **The Euler logarithm of the trivial character does not continue across `re s = 1`.** For the
trivial Dirichlet character `1` of positive level, no function summing the `L`-series of
`DirichletCharacter.eulerLogCoeff 1` on `1 < re s` is holomorphic on an open neighbourhood of the
closed half-plane `1 ≤ re s`. Thus the hypothesis `χ ≠ 1` of
`DirichletCharacter.exists_differentiableOn_exp_eq_LFunction` cannot be dropped. -/
theorem not_differentiableOn_of_LSeriesHasSum_eulerLogCoeff_one {Ω : Set ℂ} {F : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hcover : {s : ℂ | 1 ≤ s.re} ⊆ Ω)
    (hseries : ∀ s : ℂ, 1 < s.re →
      LSeriesHasSum (1 : DirichletCharacter ℂ N).eulerLogCoeff s (F s)) :
    ¬ DifferentiableOn ℂ F Ω := fun hF ↦
  not_tendsto_prod_primesLE_inv_one (N := N) _ <|
    TauCeti.LSeries.tendsto_prod_primesLE_inv_of_tendsto_sum
      (c := fun n ↦ (1 : DirichletCharacter ℂ N) n)
      (fun p _ ↦ (1 : DirichletCharacter ℂ N).norm_le_one p)
      (fun _ hn ↦ eulerLogCoeff_eq_zero_of_not_isPrimePow _ hn)
      (fun _ _ hp hk ↦ eulerLogCoeff_prime_pow _ hp hk)
      (TauCeti.LSeries.boundedDirichlet_tendsto_ordered_at_one
        (fun n _ ↦ norm_eulerLogCoeff_le_one _ n) hΩ hcover hF hseries)

end DirichletCharacter
