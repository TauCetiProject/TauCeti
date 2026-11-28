/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Valuation.ValuationRing

import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Valuation divisors of ideal products and Noetherian prime factorizations

Let `φ : T →+* V` be a ring homomorphism into a valuation domain `V`, and let `x : V` be a nonzero
non-unit. If a finite product `∏ l : J, 𝔮 l` of ideals of `T` is contained in an ideal `α` and
`x ^ (Fintype.card J + 1)` divides `φ r` for every `r ∈ α`, then `x` already divides `φ r` for
every `r ∈ 𝔮 l` for some `l : J` (`TauCeti.exists_forall_dvd_of_prod_le`).

In a Noetherian commutative ring `T`, every ideal `α` contains a finite product of prime ideals
lying over `α` (`TauCeti.exists_primes_over_prod_le`). Combining the two gives a uniform exponent
`N : ℕ` depending only on `(T, α)` such that whenever `x ^ N` divides `φ(α)` in a valuation
domain `V`, `x` divides `φ(𝔭)` for some prime ideal `𝔭 ≥ α`
(`TauCeti.exists_prime_over_forall_dvd_of_pow_dvd`).

## Main results

* `TauCeti.exists_forall_dvd_of_prod_le`: if `∏ l, 𝔮 l ≤ α` and `x ^ (card J + 1) ∣ φ(α)` in a
  valuation domain, then `x ∣ φ(𝔮 l)` for some `l`.
* `TauCeti.exists_primes_over_prod_le`: in a Noetherian ring, every ideal `α` contains a finite
  product of prime ideals containing `α`.
* `TauCeti.exists_prime_over_forall_dvd_of_pow_dvd`: uniform exponent `N` reducing divisibility
  of `φ(α)` by `x ^ N` to divisibility of `φ(𝔭)` by `x` for some prime `𝔭 ≥ α`.

## Provenance

Adapted from grh-lean (<https://github.com/lsernau/grh-lean>, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/PadicComparison/CrystallineFrobenius.lean`, declarations
`New.Variety.exists_factor_forall_dvd` and `New.Variety.exists_primes_over_prod_le`, lifted to
arbitrary universes via `Fin n` indexing and combined into a uniform exponent statement.
-/

public section

namespace TauCeti

/-- Let `φ : T →+* V` map into a valuation domain `V`, and let `x : V` be nonzero and not a unit.
If `∏ l : J, 𝔮 l ≤ α` and `x ^ (Fintype.card J + 1) ∣ φ r` for every `r ∈ α`, then `x ∣ φ r`
for every `r ∈ 𝔮 l` for some `l : J`. -/
theorem exists_forall_dvd_of_prod_le {T V J : Type*} [CommRing T] [CommRing V] [IsDomain V]
    [ValuationRing V] [Fintype J] (φ : T →+* V) {α : Ideal T} {𝔮 : J → Ideal T}
    (h𝔮 : ∏ l : J, 𝔮 l ≤ α) {x : V} (hx_ne : x ≠ 0) (hx_nonunit : ¬IsUnit x)
    (hα : ∀ r ∈ α, x ^ (Fintype.card J + 1) ∣ φ r) :
    ∃ l : J, ∀ r ∈ 𝔮 l, x ∣ φ r := by
  by_contra! h_none
  choose r hr_mem hr_ndvd using h_none
  have h_prod_dvd : φ (∏ l, r l) ∣ x ^ Fintype.card J := by
    rw [map_prod, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun l _ ↦
      (ValuationRing.dvd_total _ _).resolve_left (hr_ndvd l)
  have h_pow_dvd : x ^ (Fintype.card J + 1) ∣ x ^ Fintype.card J :=
    (hα _ (h𝔮 (Ideal.prod_mem_prod fun l _ ↦ hr_mem l))).trans h_prod_dvd
  exact Nat.not_succ_le_self _ ((pow_dvd_pow_iff hx_ne hx_nonunit).mp h_pow_dvd)

/-- In a Noetherian commutative ring `T`, every ideal `α` contains a finite product of prime
ideals, each containing `α`. -/
theorem exists_primes_over_prod_le {T : Type*} [CommRing T] [IsNoetherianRing T] (α : Ideal T) :
    ∃ (n : ℕ) (𝔮 : Fin n → Ideal T),
      (∀ l, (𝔮 l).IsPrime) ∧ (∀ l, α ≤ 𝔮 l) ∧ ∏ l, 𝔮 l ≤ α := by
  classical
  obtain ⟨Z, hZ⟩ := PrimeSpectrum.exists_primeSpectrum_prod_le (T ⧸ α) ⊥
  let L := Z.toList
  refine ⟨L.length, fun l ↦ (L.get l).asIdeal.comap (Ideal.Quotient.mk α),
    fun _ ↦ inferInstance, fun _ ↦ Ideal.mk_ker.ge.trans (Ideal.ker_le_comap _), ?_⟩
  have hZ_fin : ∏ l : Fin L.length, (L.get l).asIdeal ≤ ⊥ := by
    simpa [L, List.prod_ofFn] using hZ
  refine le_trans (Ideal.le_comap_of_map_le ?_) ((Ideal.comap_mono hZ_fin).trans Ideal.mk_ker.le)
  exact (map_prod (Ideal.mapHom _) _ _).trans_le
    (Finset.prod_le_prod fun _ _ ↦ Ideal.map_comap_le)

/-- In a Noetherian commutative ring `T`, for every ideal `α` there is an exponent `N` such that
for any homomorphism `φ : T →+* V` into a valuation domain `V` and any nonzero non-unit `x : V`
with `x ^ N ∣ φ r` for all `r ∈ α`, there is a prime ideal `𝔭 ≥ α` with `x ∣ φ r` for all
`r ∈ 𝔭`. -/
theorem exists_prime_over_forall_dvd_of_pow_dvd {T : Type*} [CommRing T] [IsNoetherianRing T]
    (α : Ideal T) :
    ∃ N : ℕ, ∀ {V : Type*} [CommRing V] [IsDomain V] [ValuationRing V] (φ : T →+* V) {x : V},
      x ≠ 0 → ¬IsUnit x → (∀ r ∈ α, x ^ N ∣ φ r) →
        ∃ 𝔭 : Ideal T, 𝔭.IsPrime ∧ α ≤ 𝔭 ∧ ∀ r ∈ 𝔭, x ∣ φ r := by
  obtain ⟨n, 𝔮, hprime, hle, hprod⟩ := exists_primes_over_prod_le α
  refine ⟨n + 1, fun φ x hx_ne hx_nonunit hα ↦ ?_⟩
  obtain ⟨l, hl⟩ := exists_forall_dvd_of_prod_le φ hprod hx_ne hx_nonunit (by simpa using hα)
  exact ⟨𝔮 l, hprime l, hle l, hl⟩

end TauCeti
