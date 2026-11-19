/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.PrimeCounting
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Prime summatory functions over `ℚ`

The nonzero primes of `𝓞 ℚ` correspond to the rational primes through their absolute norms
(Mathlib's `Rat.HeightOneSpectrum.primesEquiv`, with `Rat.HeightOneSpectrum.absNorm_asIdeal`
identifying the norm of `v` with its generator). This file transports a prime summatory function
over `ℚ` whose weight depends only on the norm to the corresponding sum over Mathlib's
`Nat.primesLE`, so that results stated for the primes of a number field specialize to the
classical sums over rational primes. The same transport applies to infinite sums over all primes.

## Main results

* `TauCeti.primeSummatory_rat_eq_sum_primesLE`: for a weight `f : ℕ → M`,
  `∑_{N𝔭 ≤ x} f (N𝔭)` over the primes of `𝓞 ℚ` is `∑_{p ∈ Nat.primesLE ⌊x⌋₊} f p`.
* `TauCeti.summable_rat_iff_summable_primes`, `TauCeti.tsum_rat_eq_tsum_primes`: `f (N𝔭)` is
  summable over the primes of `𝓞 ℚ` if and only if `f p` is summable over `Nat.Primes`, and the
  two sums agree.
-/

public section

namespace TauCeti

open NumberField

/-- Over `ℚ`, the sum of a weight depending only on the norm over the primes of norm at most `x` is
the corresponding sum over the rational primes in `Nat.primesLE ⌊x⌋₊`. -/
theorem primeSummatory_rat_eq_sum_primesLE {M : Type*} [AddCommMonoid M] (f : ℕ → M) (x : ℝ) :
    primeSummatory ℚ (fun v ↦ f (Ideal.absNorm v.asIdeal)) x = ∑ p ∈ Nat.primesLE ⌊x⌋₊, f p := by
  have hprime (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) : (Ideal.absNorm v.asIdeal).Prime := by
    rw [Rat.HeightOneSpectrum.absNorm_asIdeal]
    exact Rat.HeightOneSpectrum.prime_natGenerator v
  have hmem (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
      v ∈ primesLE ℚ x ↔ Ideal.absNorm v.asIdeal ∈ Nat.primesLE ⌊x⌋₊ := by
    rw [mem_normLE, Nat.mem_primesLE, Nat.le_floor_iff' (hprime v).ne_zero]
    exact (and_iff_left (hprime v)).symm
  rw [primeSummatory_apply]
  refine Finset.sum_bij (fun v _ ↦ Ideal.absNorm v.asIdeal) (fun v hv ↦ (hmem v).mp hv)
    (fun v _ w _ h ↦ Rat.HeightOneSpectrum.absNorm_asIdeal_injective h) (fun p hp ↦ ?_)
    fun _ _ ↦ rfl
  obtain ⟨v, hv⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq (Nat.prime_of_mem_primesLE hp)
  exact ⟨v, (hmem v).mpr (hv ▸ hp), hv⟩

/-- Over `ℚ`, transporting along `Rat.HeightOneSpectrum.primesEquiv` turns a weight depending only
on the norm into the same weight on the rational primes. -/
private theorem comp_primesEquiv_eq {M : Type*} (f : ℕ → M) :
    (fun p : Nat.Primes ↦ f p) ∘ Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) =
      fun v ↦ f (Ideal.absNorm v.asIdeal) := by
  -- Mathlib defines the value of `primesEquiv v` to be `natGenerator v`, which is the absolute
  -- norm of `v` by `Rat.HeightOneSpectrum.absNorm_asIdeal`.
  funext v
  exact congrArg f (Rat.HeightOneSpectrum.absNorm_asIdeal v).symm

/-- Over `ℚ`, a weight depending only on the norm is summable over the primes of `𝓞 ℚ` if and only
if it is summable over the rational primes. -/
theorem summable_rat_iff_summable_primes {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (f : ℕ → M) :
    Summable (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) ↦ f (Ideal.absNorm v.asIdeal)) ↔
      Summable fun p : Nat.Primes ↦ f p := by
  rw [← comp_primesEquiv_eq, Equiv.summable_iff]

/-- Over `ℚ`, the sum of a weight depending only on the norm over the primes of `𝓞 ℚ` is the
corresponding sum over the rational primes. -/
theorem tsum_rat_eq_tsum_primes {M : Type*} [AddCommMonoid M] [TopologicalSpace M] (f : ℕ → M) :
    ∑' v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), f (Ideal.absNorm v.asIdeal) =
      ∑' p : Nat.Primes, f p := by
  rw [← comp_primesEquiv_eq]
  exact (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).tsum_eq fun p : Nat.Primes ↦ f p

end TauCeti
