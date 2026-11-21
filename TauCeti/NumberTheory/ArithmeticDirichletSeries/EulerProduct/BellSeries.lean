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
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp0 : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  set T : Finset (Ideal (𝓞 K)) := primesOverFinset (span {(p : ℤ)}) (𝓞 K)
  let toH1 : {𝔭 // 𝔭 ∈ T} → HeightOneSpectrum (𝓞 K) := fun ⟨𝔭, h𝔭⟩ ↦
    have hmem := (mem_primesOverFinset_iff hp0 (𝓞 K)).mp h𝔭
    have : 𝔭.IsPrime := hmem.1
    have : 𝔭.LiesOver (span {(p : ℤ)}) := hmem.2
    TauCeti.NumberField.heightOneSpectrumOfLiesOver p 𝔭
  have htoH1_asIdeal (q : {𝔭 // 𝔭 ∈ T}) : (toH1 q).asIdeal = q.val := by
    have hmem := (mem_primesOverFinset_iff hp0 (𝓞 K)).mp q.property
    have : q.val.IsPrime := hmem.1
    have : q.val.LiesOver (span {(p : ℤ)}) := hmem.2
    exact TauCeti.NumberField.heightOneSpectrumOfLiesOver_asIdeal p q.val
  have hinj : Function.Injective toH1 := fun q₁ q₂ h ↦
    Subtype.ext (by rw [← htoH1_asIdeal q₁, ← htoH1_asIdeal q₂, h])
  let S : Finset (HeightOneSpectrum (𝓞 K)) := T.attach.image toH1
  have hS_cover : ∀ P : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ P.asIdeal → P ∈ S :=
    TauCeti.NumberField.mem_of_natCast_mem_asIdeal fun P hP ↦ by
      have hPT : P.asIdeal ∈ T := (mem_primesOverFinset_iff hp0 (𝓞 K)).mpr hP
      exact Finset.mem_image.mpr
        ⟨⟨P.asIdeal, hPT⟩, Finset.mem_attach T _,
          HeightOneSpectrum.ext (htoH1_asIdeal ⟨P.asIdeal, hPT⟩)⟩
  rw [bellSeries_normCoeff_eq_prod_bellSeries_localArithmeticFactor
    isMultiplicative_one hp S hS_cover,
    Finset.prod_image (fun _ _ _ _ h ↦ hinj h), ← Finset.prod_attach T, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun q _ ↦ ?_
  have hmem := (mem_primesOverFinset_iff hp0 (𝓞 K)).mp q.property
  have : q.val.IsPrime := hmem.1
  have : q.val.LiesOver (span {(p : ℤ)}) := hmem.2
  rw [localArithmeticFactor_def, localPowerSeries_one, htoH1_asIdeal, ← pow_inertiaDeg p q.val]
  exact ArithmeticFunction.bellSeries_ofPowerSeries_mk_one_mul_one_sub_X_pow hp
    (Ideal.inertiaDeg_pos q.val ℤ).ne'

end TauCeti.IdealArithmeticFunction
