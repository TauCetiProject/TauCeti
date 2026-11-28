/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Basic
public import TauCeti.NumberTheory.ArithmeticFunction.BellSeries
import TauCeti.NumberTheory.NumberField.PrimeIdeal

/-!
# Bell series of norm coefficients and local Euler factors of Dedekind zeta functions

For a multiplicative ideal arithmetic function `f` on a number field `K` and a rational prime `p`,
the Bell series of `normCoeff K f` at `p` factors as the product of the Bell series of the
canonical local factors `localArithmeticFactor f P` over any finite set of height-one primes
covering all primes of `𝓞 K` above `p`.

For the trivial ideal function `1` (whose norm coefficients are the Dirichlet coefficients of the
Dedekind zeta function `ζ_K`), each prime `𝔭` above `p` has absolute norm `p ^ f(𝔭 / p)`, so its
local Bell series is the formal reciprocal of `1 - X ^ f(𝔭 / p)`. Multiplying over all primes
above `p` yields the local Euler-factor identity
`bellSeries p hp (normCoeff K 1) * ∏ 𝔭 ∣ p, (1 - X ^ 𝔭.inertiaDeg ℤ) = 1`.

## Main results

* `TauCeti.IdealArithmeticFunction.bellSeries_normCoeff_eq_prod_bellSeries_localArithmeticFactor`:
  the Bell series of `normCoeff K f` at `p` equals the product of the Bell series of
  `localArithmeticFactor f P` over any finite set of height-one primes covering all primes above
  `p`.
* `TauCeti.IdealArithmeticFunction.bellSeries_normCoeff_one_mul_prod_one_sub_X_pow`:
  `bellSeries p hp (normCoeff K 1) * ∏ 𝔭 ∈ primesOverFinset (span {(p : ℤ)}) (𝓞 K),
    (1 - PowerSeries.X ^ 𝔭.inertiaDeg ℤ) = 1`.
-/

public section

open Ideal IsDedekindDomain
open scoped NumberField

namespace TauCeti.IdealArithmeticFunction

/-- **The Bell series of norm coefficients factors over the primes above `p`.** For a
multiplicative ideal arithmetic function `f` and a finite set `S` of height-one primes containing
every prime above `p`, the Bell series of `normCoeff K f` at `p` equals the product of the Bell
series of the local factors at `P ∈ S`. -/
theorem bellSeries_normCoeff_eq_prod_bellSeries_localArithmeticFactor
    {K : Type*} [Field K] [NumberField K]
    {f : IdealArithmeticFunction K} (hf : f.IsMultiplicative) {p : ℕ} (hp : p.Prime)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ P : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ P.asIdeal → P ∈ S) :
    ArithmeticFunction.bellSeries p hp (normCoeff K f) =
      ∏ P ∈ S, ArithmeticFunction.bellSeries p hp (localArithmeticFactor f P) := by
  rw [← map_prod]
  exact PowerSeries.ext fun j ↦ by
    rw [ArithmeticFunction.coeff_bellSeries, ArithmeticFunction.coeff_bellSeries,
      normCoeff_apply_prime_pow_eq_prod_localArithmeticFactor hf hp S hS j]

/-- **Local Euler-factor Bell-series identity for `ζ_K`.** For every number field `K` and rational
prime `p`, the Bell series of `normCoeff K 1` at `p` is the formal inverse of
`∏ 𝔭 ∈ primesOverFinset (span {(p : ℤ)}) (𝓞 K), (1 - X ^ 𝔭.inertiaDeg ℤ)`. -/
theorem bellSeries_normCoeff_one_mul_prod_one_sub_X_pow (K : Type*) [Field K] [NumberField K]
    {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.bellSeries p hp (normCoeff K 1) *
      ∏ 𝔭 ∈ primesOverFinset (span {(p : ℤ)}) (𝓞 K),
        (1 - PowerSeries.X ^ 𝔭.inertiaDeg ℤ) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [bellSeries_normCoeff_eq_prod_bellSeries_localArithmeticFactor isMultiplicative_one hp
      (TauCeti.NumberField.heightOneSpectrumPrimesOverFinset K p)
      (fun _ ↦ TauCeti.NumberField.mem_heightOneSpectrumPrimesOverFinset_iff.mpr),
    TauCeti.NumberField.prod_primesOverFinset_eq_prod_heightOneSpectrumPrimesOverFinset,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun P hP ↦ ?_
  have := TauCeti.NumberField.liesOver_of_mem_heightOneSpectrumPrimesOverFinset hP
  rw [localArithmeticFactor_def, localPowerSeries_one, ← pow_inertiaDeg p P.asIdeal]
  exact ArithmeticFunction.bellSeries_ofPowerSeries_mk_one_mul_one_sub_X_pow hp
    (Ideal.inertiaDeg_pos P.asIdeal ℤ).ne'

end TauCeti.IdealArithmeticFunction
