/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.RamificationInertia.Inertia
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.RingTheory.DedekindDomain.PrimesAbove

/-!
# Embeddings of number fields into `ℚ_[p]`

A ring embedding `φ : K →+* ℚ_[p]` of a number field carries the ring of integers `𝓞 K` into
`ℤ_[p]`, because `ℤ_[p]` is integrally closed in `ℚ_[p]`. Reducing modulo `p` then gives a
surjection `𝓞 K → 𝔽_p`, whose kernel is a prime of `𝓞 K` above `p` with residue field `𝔽_p`, so of
residue degree one. This is how an embedding into `ℚ_[p]` is seen by the Frobenius at `p`: at a
prime unramified in a Galois closure, a residue-degree-one prime is the same as a Frobenius
element fixing the corresponding coset.

The converse, for a prime of ramification index and residue degree one, whose completion is
`ℚ_[p]`, is not proved here. Residue degree one alone does not suffice: `2` is totally ramified in
`ℚ(∛2)`, so the prime above it has residue degree one, but `ℚ(∛2)` does not embed in `ℚ_[2]`.

## Main results

* `RingHom.exists_inertiaDeg_eq_one_of_padic`: an embedding of a number field into `ℚ_[p]` gives a
  prime of residue degree one over the prime of `𝓞 ℚ` above `p`.
-/

public section

open NumberField IsDedekindDomain

/-- **An embedding into `ℚ_[p]` gives a prime of residue degree one.** If a number field `K` embeds
into `ℚ_[p]` and `𝔭` is the prime of `𝓞 ℚ` above `p`, then some prime of `𝓞 K` above `𝔭` has
residue degree one over `𝔭`. -/
theorem RingHom.exists_inertiaDeg_eq_one_of_padic {K : Type*} [Field K] [NumberField K] {p : ℕ}
    [hp : Fact p.Prime] (φ : K →+* ℚ_[p]) {𝔭 : HeightOneSpectrum (𝓞 ℚ)}
    (h𝔭 : Ideal.absNorm 𝔭.asIdeal = p) :
    ∃ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) = 𝔭 ∧ 𝔓.asIdeal.inertiaDeg (𝓞 ℚ) = 1 := by
  -- `φ` maps `𝓞 K` into `ℤ_[p]`; reducing modulo `p` gives a surjection `ψ : 𝓞 K → 𝔽_p`.
  let ι : 𝓞 K →+* ℤ_[p] :=
    (φ.comp (algebraMap (𝓞 K) K)).codRestrict (PadicInt.subring p) fun x ↦
      Padic.norm_le_one_of_isIntegral (x.isIntegral_coe.map φ.toIntAlgHom)
  let ψ : 𝓞 K →+* ZMod p := PadicInt.toZMod.comp ι
  have hψ : Function.Surjective ψ := ZMod.ringHom_surjective ψ
  have hpker : (p : 𝓞 K) ∈ RingHom.ker ψ := by simp [RingHom.mem_ker]
  have hne : RingHom.ker ψ ≠ ⊥ := fun h ↦ by
    rw [h, Ideal.mem_bot] at hpker
    exact hp.out.ne_zero (by exact_mod_cast hpker)
  obtain ⟨𝔓, h𝔓⟩ : ∃ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.asIdeal = RingHom.ker ψ :=
    ⟨⟨RingHom.ker ψ, (RingHom.ker_isMaximal_of_surjective ψ hψ).isPrime, hne⟩, rfl⟩
  have hcard : Ideal.absNorm 𝔓.asIdeal = p := by
    rw [h𝔓, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Nat.card_congr (RingHom.quotientKerEquivOfSurjective hψ).toEquiv, Nat.card_zmod]
  -- `𝔓` contains `p`, so it lies over the maximal ideal `𝔭 = (p)` of `𝓞 ℚ`.
  have hunder : 𝔓.under (𝓞 ℚ) = 𝔭 := by
    refine HeightOneSpectrum.ext
      ((𝔭.isMaximal.eq_of_le (Ideal.IsPrime.under _ _).ne_top ?_).symm)
    rw [← Rat.RingOfIntegers.ideal_span_absNorm_eq_self 𝔭.asIdeal, h𝔭,
      Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast, h𝔓]
    exact hpker
  have := HeightOneSpectrum.under_eq_iff_liesOver.mp hunder
  refine ⟨𝔓, hunder, ?_⟩
  -- Both residue fields have `p` elements, so `p ^ f = p`.
  have h := Ideal.absNorm_pow_inertiaDeg 𝔭.asIdeal 𝔓.asIdeal
  rwa [hcard, h𝔭, Nat.pow_eq_self_iff hp.out.one_lt] at h
