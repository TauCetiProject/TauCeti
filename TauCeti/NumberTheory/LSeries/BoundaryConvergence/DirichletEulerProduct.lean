/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.BoundaryConvergence.Endpoint
public import TauCeti.NumberTheory.LSeries.BoundaryConvergence.OrderedEulerProduct
public import TauCeti.NumberTheory.LSeries.DirichletEulerLog
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Ordered limits of a Dirichlet `L`-function at `s = 1`

For a nontrivial Dirichlet character `χ` of positive level, the ordered partial sums
`∑ n ∈ Icc 1 K, χ n / n` of its Dirichlet series converge to `L(χ, 1)`
(`DirichletCharacter.tendsto_sum_Icc_div_LFunction_one`). This is the bounded Tauberian theorem
`TauCeti.LSeries.boundedDirichlet_tendsto_ordered_at_one` applied to the coefficients `χ n`,
which have norm at most `1`, and to `L(χ, s)`, which is entire because `χ ≠ 1`.

Similarly, the finite Euler products
`∏ p ≤ B, (1 - χ p / p)⁻¹` over the primes up to `B` converge to `L(χ, 1)` as `B → ∞`
(`DirichletCharacter.tendsto_prod_primesLE_inv_LFunction_one`). Deleting the factors at a finite
set `S` of primes multiplies the limit by `∏ p ∈ S, (1 - χ p / p)`. Mathlib's
`DirichletCharacter.LSeries_eulerProduct` is the corresponding statement on the half-plane
`1 < re s`, where the Euler product converges absolutely; the boundary point `s = 1` needs the
nonvanishing of `L(χ, s)` on the whole line `re s = 1` and a Tauberian argument.

These are limits of ordered cutoffs. At `s = 1` neither the Euler product nor the Dirichlet series
of `χ` converges absolutely, so nothing here asserts an unconditional `HasProd` or `HasSum`, or a
value of the totalized `LSeries` at `1`. Limits along real cutoffs `⌊x⌋₊` follow from
`TauCeti.tendsto_comp_natFloor_iff`.

The proof of the Euler product limit combines three results:
* `DirichletCharacter.exists_differentiableOn_exp_eq_LFunction` continues the logarithm of
  `L(χ, s)`, the `L`-series of the coefficients `DirichletCharacter.eulerLogCoeff χ`, to an open
  neighbourhood of the closed half-plane `1 ≤ re s`;
* the bounded Tauberian theorem `TauCeti.LSeries.boundedDirichlet_tendsto_ordered_at_one` turns
  that continuation into convergence of the ordered sums `∑ n ∈ Icc 1 K, χ.eulerLogCoeff n / n`
  to a logarithm `L` of `L(χ, 1)`;
* `TauCeti.LSeries.tendsto_prod_primesLE_inv_of_tendsto_sum` compares those sums with the
  logarithms of the finite Euler products, which therefore converge to `exp L = L(χ, 1)`.

Conjugating every Euler factor replaces `χ` by `χ⁻¹`, since the values of `χ` on units have norm
`1` (Mathlib's `MulChar.star_apply'`); ordered convergence transports along this with the
conjugated limit (`DirichletCharacter.tendsto_prod_primesLE_filter_notMem_inv_inv_iff`).

## Main results

* `DirichletCharacter.tendsto_sum_Icc_div_LFunction_one`: the ordered partial sums of the
  Dirichlet series of `χ` converge to `L(χ, 1)`.
* `DirichletCharacter.exists_tendsto_sum_Icc_eulerLogCoeff_div`: the ordered sums of
  `χ.eulerLogCoeff n / n` converge to a logarithm of `L(χ, 1)`.
* `DirichletCharacter.tendsto_prod_primesLE_inv_LFunction_one`: the ordered Euler product
  converges to `L(χ, 1)`.
* `DirichletCharacter.tendsto_prod_primesLE_filter_notMem_inv_LFunction_one`: the same with the
  factors at a finite set of primes deleted.
* `DirichletCharacter.tendsto_prod_primesLE_filter_notMem_inv_inv_iff`: conjugation of the
  ordered Euler products.

## References

* D. J. Newman, *Simple analytic proof of the prime number theorem*, Amer. Math. Monthly 87
  (1980), 693–696.
* D. Zagier, *Newman's short proof of the prime number theorem*, Amer. Math. Monthly 104
  (1997), 705–708.
-/

public section

open Filter Finset Complex
open scoped Topology ComplexConjugate

namespace DirichletCharacter

variable {N : ℕ} (χ : DirichletCharacter ℂ N)

/-- **The ordered Dirichlet series of a character at `s = 1`.** For a nontrivial Dirichlet
character `χ` of positive level, the ordered partial sums `∑ n ∈ Icc 1 K, χ n / n` converge to
`L(χ, 1)`. This is a limit of ordered cutoffs: the series `∑ χ n / n` does not converge
absolutely (Mathlib's `DirichletCharacter.not_LSeriesSummable_at_one`), and no unconditional
`HasSum` is asserted. -/
theorem tendsto_sum_Icc_div_LFunction_one [NeZero N] (hχ : χ ≠ 1) :
    Tendsto (fun K : ℕ ↦ ∑ n ∈ Icc 1 K, χ n / (n : ℂ)) atTop (𝓝 (LFunction χ 1)) :=
  TauCeti.LSeries.boundedDirichlet_tendsto_ordered_at_one (fun n _ ↦ χ.norm_le_one n)
    isOpen_univ (Set.subset_univ _) (differentiable_LFunction hχ).differentiableOn
    fun _ hs ↦ χ.LFunction_eq_LSeries hs ▸ (χ.LSeriesSummable_of_one_lt_re hs).LSeriesHasSum

/-- **The ordered logarithmic sums at `s = 1`.** For a nontrivial Dirichlet character `χ` of
positive level, the ordered partial sums `∑ n ∈ Icc 1 K, χ n Λ n / (n log n)` converge to a
logarithm of `L(χ, 1)`.

The limit is the value at `1` of the holomorphic continuation of the logarithm of `L(χ, s)` from
`DirichletCharacter.exists_differentiableOn_exp_eq_LFunction`; it need not be the principal
logarithm of `L(χ, 1)`. -/
theorem exists_tendsto_sum_Icc_eulerLogCoeff_div [NeZero N] (hχ : χ ≠ 1) :
    ∃ L : ℂ, Tendsto (fun K : ℕ ↦ ∑ n ∈ Icc 1 K, χ.eulerLogCoeff n / n) atTop (𝓝 L) ∧
      exp L = LFunction χ 1 := by
  obtain ⟨Ω, hΩ, hcover, F, hF, hexp, hseries⟩ := χ.exists_differentiableOn_exp_eq_LFunction hχ
  exact ⟨F 1, TauCeti.LSeries.boundedDirichlet_tendsto_ordered_at_one
    (fun n _ ↦ χ.norm_eulerLogCoeff_le_one n) hΩ hcover hF hseries,
    hexp 1 (hcover (by simp))⟩

/-- **The ordered Euler product with finitely many factors deleted.** For a nontrivial Dirichlet
character `χ` of positive level and a finite set `S` of primes, the finite Euler products over
the primes `p ≤ B` outside `S` converge to `L(χ, 1) * ∏ p ∈ S, (1 - χ p / p)` as `B → ∞`. -/
theorem tendsto_prod_primesLE_filter_notMem_inv_LFunction_one [NeZero N] (hχ : χ ≠ 1)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Tendsto (fun B : ℕ ↦ ∏ p ∈ Nat.primesLE B with p ∉ S, (1 - χ p / (p : ℂ))⁻¹) atTop
      (𝓝 (LFunction χ 1 * ∏ p ∈ S, (1 - χ p / (p : ℂ)))) := by
  obtain ⟨L, hL, hexp⟩ := χ.exists_tendsto_sum_Icc_eulerLogCoeff_div hχ
  rw [← hexp]
  exact TauCeti.LSeries.tendsto_prod_primesLE_filter_notMem_inv_of_tendsto_sum
    (c := fun n ↦ χ n) (fun p _ ↦ χ.norm_le_one p)
    (fun _ hn ↦ χ.eulerLogCoeff_eq_zero_of_not_isPrimePow hn)
    (fun _ _ hp hk ↦ χ.eulerLogCoeff_prime_pow hp hk) hL hS

/-- **The ordered Euler product of a Dirichlet `L`-function at `s = 1`.** For a nontrivial
Dirichlet character `χ` of positive level, the finite Euler products `∏ p ≤ B, (1 - χ p / p)⁻¹`
converge to `L(χ, 1)` as `B → ∞`. This is a limit of ordered cutoffs, not an unconditional
product. -/
theorem tendsto_prod_primesLE_inv_LFunction_one [NeZero N] (hχ : χ ≠ 1) :
    Tendsto (fun B : ℕ ↦ ∏ p ∈ Nat.primesLE B, (1 - χ p / (p : ℂ))⁻¹) atTop
      (𝓝 (LFunction χ 1)) := by
  simpa using χ.tendsto_prod_primesLE_filter_notMem_inv_LFunction_one hχ (S := ∅) (by simp)

/-- **Conjugating the ordered Euler products.** Conjugating each Euler factor of `χ` gives the
corresponding factor of `χ⁻¹`, so the ordered Euler products of `χ⁻¹`, with the factors at a
finite set `S` deleted, converge to `conj L` if and only if those of `χ` converge to `L`. -/
theorem tendsto_prod_primesLE_filter_notMem_inv_inv_iff (S : Finset ℕ) (L : ℂ) :
    Tendsto (fun B : ℕ ↦ ∏ p ∈ Nat.primesLE B with p ∉ S, (1 - χ⁻¹ p / (p : ℂ))⁻¹) atTop
        (𝓝 (conj L)) ↔
      Tendsto (fun B : ℕ ↦ ∏ p ∈ Nat.primesLE B with p ∉ S, (1 - χ p / (p : ℂ))⁻¹) atTop
        (𝓝 L) := by
  have hconj : (fun B : ℕ ↦ ∏ p ∈ Nat.primesLE B with p ∉ S, (1 - χ⁻¹ p / (p : ℂ))⁻¹) =
      fun B ↦ conj (∏ p ∈ Nat.primesLE B with p ∉ S, (1 - χ p / (p : ℂ))⁻¹) := by
    ext B
    simp [← MulChar.star_apply']
  rw [hconj]
  refine ⟨fun h ↦ ?_, fun h ↦ (continuous_conj.tendsto L).comp h⟩
  simpa only [Function.comp_def, conj_conj] using (continuous_conj.tendsto (conj L)).comp h

end DirichletCharacter
