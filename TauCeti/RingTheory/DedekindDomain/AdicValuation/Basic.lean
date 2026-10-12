/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import TauCeti.RingTheory.Valuation.Center
public import TauCeti.RingTheory.Valuation.Discrete.Order
-- Proof-only: the normalization of a valuation, which is how a merely bounded one is brought into
-- the normalized form the centre construction compares against.
import TauCeti.RingTheory.Valuation.Discrete.Normalize

/-!
# Adic valuations on the fraction field of a Dedekind domain

Mathlib attaches to every height one prime `𝔭` of a Dedekind domain `R` a normalized
`ℤᵐ⁰`-valued valuation `𝔭.valuation K` of the fraction field `K`, and shows that distinct primes
give inequivalent valuations. This file proves the converse: a normalized valuation of `K` whose
valuation ring contains `R` *is* `𝔭.valuation K` for a unique height one prime `𝔭` of `R`, namely
the centre of the valuation on `R`.

The adic valuation is trivial on any semifield of constants acting on `R`: every nonzero
constant is a unit of `R`, so it lies outside every prime ideal.

The general centre construction and its membership lemmas are in
`TauCeti.RingTheory.Valuation.Center`. There, `Valuation.heightOneSpectrum` bundles a nonzero
prime ideal as `HeightOneSpectrum R`; the Dedekind assumption here makes it a height one prime.

The value group of the adic valuation itself is read off from Mathlib's definition, and this file
records the one conversion the rest of the library needs: an element has order of vanishing `1`
at `v` exactly when its adic value is `WithZero.exp (-1)`, so the additive order of vanishing used
by the class-group interface and the multiplicative value can be read off from one another.

## Main results

* `Valuation.eq_valuation_of_forall_mem_asIdeal_iff`: a normalized valuation bounded by `1` on `R`
  and of positive value exactly on a height one prime `𝔭` is the adic valuation of `𝔭`.
* `Valuation.valuation_heightOneSpectrum`: the adic valuation of the centre of `w` on `R` is `w`.
* `Valuation.existsUnique_heightOneSpectrum_valuation_eq`: the centre is the only height one prime
  whose adic valuation is `w`.
* `IsDedekindDomain.HeightOneSpectrum.neg_log_valuation_eq_one_iff`: order of vanishing `1` at `v`
  is the value `WithZero.exp (-1)`, which relates the multiplicative value group of the adic
  valuation to the additive order of vanishing used by the class-group interface.
* `IsDedekindDomain.HeightOneSpectrum.algebraMap_mem_maximalIdeal_valuationSubring_iff`: an
  element of `R` lies in `v` exactly when its image in the valuation ring of `K` at `v` lies in
  the maximal ideal.
* `IsDedekindDomain.HeightOneSpectrum.isTrivialOn_valuation`: adic valuations are trivial on
  semifield constants.
* `IsDedekindDomain.HeightOneSpectrum.exists_mem_intValuation_eq_exp_neg_one`: a set generating a
  height one prime contains an element of order of vanishing `1`.

## Implementation notes

The comparison goes through `Valuation.isEquiv_iff_val_le_one` and the normalization lemma
`Valuation.eq_of_isEquiv_of_surjective`: both valuations are surjective onto `ℤᵐ⁰`, so it is
enough to see that they have the same valuation ring. That in turn uses only that the two
valuations are bounded by `1` on `R` and are `< 1` on the same elements of `R`, together with
Mathlib's `IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq`, which writes an
arbitrary element of `K` as a fraction with denominator outside `𝔭`, in one of the two possible
directions.

The comparison theorems assume `R` is Dedekind and `w` is surjective. Surjectivity supplies
nontriviality through `Valuation.isNontrivial_of_surjective`, allowing the nonzero prime centre
to be bundled using the general construction.
-/

public section

open scoped WithZero

open IsDedekindDomain

namespace Valuation

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
  {w : _root_.Valuation K ℤᵐ⁰}

section Comparison

variable [IsFractionRing R K]

/-- **A normalized valuation of the fraction field of a Dedekind domain `R` that is bounded by `1`
on `R` and of positive value exactly at a height one prime `𝔭` is the adic valuation of `𝔭`.** -/
theorem eq_valuation_of_forall_mem_asIdeal_iff [IsDedekindDomain R] {𝔭 : HeightOneSpectrum R}
    (hw : Function.Surjective w) (hR : ∀ r : R, w (algebraMap R K r) ≤ 1)
    (h𝔭 : ∀ r : R, r ∈ 𝔭.asIdeal ↔ w (algebraMap R K r) < 1) :
    𝔭.valuation K = w := by
  -- On `R` both valuations are bounded by `1` and are `< 1` on the members of `𝔭`, so they take
  -- the value `1` on exactly the same elements of `R`.
  have hone : ∀ r : R, 𝔭.valuation K (algebraMap R K r) = 1 ↔ w (algebraMap R K r) = 1 := by
    intro r
    rw [𝔭.valuation_eq_one_iff_notMem, h𝔭 r]
    exact ⟨fun h ↦ le_antisymm (hR r) (not_lt.mp h), fun h ↦ by simp [h]⟩
  refine eq_of_isEquiv_of_surjective (𝔭.valuation_surjective K) hw
    (isEquiv_iff_val_le_one.mpr fun {x} ↦ ?_)
  obtain ⟨n, d, hnd | hnd⟩ := 𝔭.exists_primeCompl_mul_eq_or_mul_eq x
  · -- `x = n / d` with `d` outside `𝔭`: both valuations of `x` are those of `n`, hence `≤ 1`.
    have hd : 𝔭.valuation K (algebraMap R K (d : R)) = 1 :=
      𝔭.valuation_eq_one_iff_notMem.mpr d.2
    have h₁ : 𝔭.valuation K x = 𝔭.valuation K (algebraMap R K n) := by
      rw [← hnd, map_mul, hd, mul_one]
    have h₂ : w x = w (algebraMap R K n) := by
      rw [← hnd, w.map_mul, (hone (d : R)).mp hd, mul_one]
    exact iff_of_true (h₁ ▸ 𝔭.valuation_le_one n) (h₂ ▸ hR n)
  · -- `x = d / n` with `d` outside `𝔭`: either valuation of `x` is `≤ 1` exactly when the
    -- corresponding valuation of `n` equals `1`.
    have key : ∀ v : _root_.Valuation K ℤᵐ⁰, v (algebraMap R K n) ≤ 1 →
        v (algebraMap R K (d : R)) = 1 → (v x ≤ 1 ↔ v (algebraMap R K n) = 1) := by
      intro v hvn hvd
      have hx : v x * v (algebraMap R K n) = 1 := by rw [← v.map_mul, hnd, hvd]
      refine ⟨fun hle ↦ ?_, fun hn ↦ le_of_eq (by rwa [hn, mul_one] at hx)⟩
      by_contra hne
      have hlt : v x * v (algebraMap R K n) < 1 :=
        calc v x * v (algebraMap R K n) ≤ 1 * v (algebraMap R K n) := mul_le_mul_left hle _
          _ = v (algebraMap R K n) := one_mul _
          _ < 1 := lt_of_le_of_ne hvn hne
      exact absurd hx hlt.ne
    have hd : 𝔭.valuation K (algebraMap R K (d : R)) = 1 :=
      𝔭.valuation_eq_one_iff_notMem.mpr d.2
    rw [key _ (𝔭.valuation_le_one n) hd, key _ (hR n) ((hone (d : R)).mp hd), hone n]

/-- **The adic valuation of the centre of `w` on `R` is `w` itself**: a normalized valuation of the
fraction field of a Dedekind domain whose valuation ring contains that domain is adic. -/
@[simp]
theorem valuation_heightOneSpectrum [IsDedekindDomain R] (hw : Function.Surjective w)
    (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) :
    haveI := isNontrivial_of_surjective hw
    (heightOneSpectrum R w hR).valuation K = w :=
  haveI := isNontrivial_of_surjective hw
  eq_valuation_of_forall_mem_asIdeal_iff hw hR fun _ ↦ by
    rw [asIdeal_heightOneSpectrum, mem_centerIdeal]

/-- A height one prime whose adic valuation is `w` is the centre of `w`. -/
theorem eq_heightOneSpectrum [IsDedekindDomain R] {𝔮 : HeightOneSpectrum R}
    (hw : Function.Surjective w) (hR : ∀ r : R, w (algebraMap R K r) ≤ 1)
    (h : 𝔮.valuation K = w) :
    haveI := isNontrivial_of_surjective hw
    𝔮 = heightOneSpectrum R w hR :=
  HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := K)
    (by rw [h, valuation_heightOneSpectrum hw hR])

variable (R) in
/-- **A normalized valuation of the fraction field of a Dedekind domain `R` whose valuation ring
contains `R` is the adic valuation of a unique height one prime of `R`.** -/
theorem existsUnique_heightOneSpectrum_valuation_eq [IsDedekindDomain R]
    (hw : Function.Surjective w) (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) :
    ∃! 𝔭 : HeightOneSpectrum R, 𝔭.valuation K = w :=
  haveI := isNontrivial_of_surjective hw
  ⟨heightOneSpectrum R w hR, valuation_heightOneSpectrum hw hR,
    fun _ h ↦ eq_heightOneSpectrum hw hR h⟩

variable (R) in
/-- **A nontrivial valuation of `K` bounded by `1` on `R` is adic up to equivalence.** It is
equivalent to the adic valuation of the centre of its normalization, and that centre collects
exactly the elements of `R` whose value drops below `1`.

Normalizing is what makes the centre's adic valuation equal the valuation rather than merely
equivalent to it (`valuation_heightOneSpectrum`); a valuation that is only bounded, not normalized,
still picks out the same prime, which is what this states. -/
theorem exists_heightOneSpectrum_isEquiv_of_le_one [IsDedekindDomain R]
    (u : _root_.Valuation K ℤᵐ⁰) [u.IsNontrivial]
    (hR : ∀ r : R, u (algebraMap R K r) ≤ 1) :
    ∃ 𝔭 : HeightOneSpectrum R, (𝔭.valuation K).IsEquiv u ∧
      ∀ r : R, r ∈ 𝔭.asIdeal ↔ u (algebraMap R K r) < 1 := by
  have hEq : (normalization u).IsEquiv u := isEquiv_normalization u
  have hsurj : Function.Surjective (normalization u) :=
    normalization_surjective u (ordIndex_ne_zero_of_isNontrivial u)
  have hRw : ∀ r : R, normalization u (algebraMap R K r) ≤ 1 :=
    fun r ↦ hEq.le_one_iff_le_one.mpr (hR r)
  have : (normalization u).IsNontrivial := isNontrivial_of_surjective hsurj
  refine ⟨heightOneSpectrum R (normalization u) hRw, ?_, fun r ↦ ?_⟩
  · rw [valuation_heightOneSpectrum hsurj hRw]
    exact hEq
  · rw [asIdeal_heightOneSpectrum, mem_centerIdeal]
    simpa using hEq.lt_iff_lt (x := algebraMap R K r) (y := 1)

end Comparison

end Valuation

section ValueGroup

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

namespace IsDedekindDomain.HeightOneSpectrum

/-- **An element has order of vanishing exactly `1` at `v` exactly when its adic value is
`WithZero.exp (-1)`.**

The value group of `HeightOneSpectrum.valuation` is `WithZero (Multiplicative ℤ)`, whose
multiplicative identity `1` is the value zero, that is, order of vanishing zero; an element of
order of vanishing `1` is instead written `WithZero.exp (-1)`, the value of a generator of
`v.asIdeal`.  So `v.valuation K x = 1` says that `x` is a local unit at `v`, which an element of
nonzero order of vanishing is not.  This is the equivalence that relates the multiplicative value
of an element to the additive order of vanishing used by the class-group interface, whose
`adicOrd` is `-WithZero.log` of this valuation. -/
theorem neg_log_valuation_eq_one_iff (v : HeightOneSpectrum R) (x : K) :
    -WithZero.log (v.valuation K x) = 1 ↔
      v.valuation K x = (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) := by
  constructor
  · intro h
    have hlog : WithZero.log (v.valuation K x) = -1 := (neg_eq_iff_eq_neg).mp h
    have hx : v.valuation K x ≠ 0 := by
      intro hx0
      rw [hx0] at hlog
      simp at hlog
    calc v.valuation K x = WithZero.exp (WithZero.log (v.valuation K x)) :=
        (WithZero.exp_log hx).symm
      _ = WithZero.exp (-1) := by rw [hlog]
  · intro h
    rw [h, WithZero.log_exp, neg_neg]

/-- An element of `R` lies in the prime `v` exactly when its image in the valuation ring of `K` at
`v` lies in the maximal ideal. The algebra structure of `R` on the valuation ring is taken as a
hypothesis, compatible with `K`, since there is no such instance in general; for `R = ℤ` it is
the canonical one. -/
theorem algebraMap_mem_maximalIdeal_valuationSubring_iff (v : HeightOneSpectrum R)
    [Algebra R (v.valuation K).valuationSubring]
    [IsScalarTower R (v.valuation K).valuationSubring K] (r : R) :
    algebraMap R (v.valuation K).valuationSubring r ∈ IsLocalRing.maximalIdeal _ ↔
      r ∈ v.asIdeal := by
  rw [Valuation.mem_maximalIdeal_iff, ← ValuationSubring.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply, v.valuation_lt_one_iff_mem]

end IsDedekindDomain.HeightOneSpectrum

end ValueGroup

namespace IsDedekindDomain.HeightOneSpectrum

variable (k : Type*) (F : Type*) {R : Type*} [Semifield k] [Field F] [CommRing R]
  [IsDedekindDomain R] [Algebra k R] [Algebra R F] [IsFractionRing R F] [Algebra k F]
  [IsScalarTower k R F]

/-- The adic valuation of a height-one prime of a Dedekind `k`-algebra is trivial on the
semifield `k`: a nonzero constant is a unit of `R`, hence lies outside every prime ideal. -/
instance isTrivialOn_valuation (p : HeightOneSpectrum R) :
    (p.valuation F).IsTrivialOn k where
  eq_one c hc := by
    rw [IsScalarTower.algebraMap_apply k R F, valuation_eq_one_iff_notMem]
    exact Ideal.notMem_of_isUnit _ ((isUnit_iff_ne_zero.mpr hc).map (algebraMap k R))

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (v : HeightOneSpectrum R)

/-- **An element of a height one prime outside its square has order of vanishing `1`.** -/
theorem intValuation_eq_exp_neg_one_of_mem_of_notMem_sq {r : R} (hr : r ∈ v.asIdeal)
    (hr2 : r ∉ v.asIdeal ^ 2) : v.intValuation r = WithZero.exp (-1) := by
  have h1 := (v.intValuation_le_pow_iff_mem r 1).mpr (by rwa [pow_one])
  have h2 := mt (v.intValuation_le_pow_iff_mem r 2).mp hr2
  have hne : v.intValuation r ≠ 0 :=
    v.intValuation_ne_zero r fun h0 ↦ hr2 (h0 ▸ Ideal.zero_mem _)
  rw [← WithZero.exp_log hne, WithZero.exp_le_exp] at h1 h2
  rw [← WithZero.exp_log hne, WithZero.exp_inj]
  push_cast at h1 h2
  omega

/-- **A set generating a height one prime contains an element of order of vanishing `1`**:
otherwise the prime would lie in its own square. -/
theorem exists_mem_intValuation_eq_exp_neg_one {s : Set R} (hs : Ideal.span s = v.asIdeal) :
    ∃ r ∈ s, v.intValuation r = WithZero.exp (-1) := by
  by_contra! h
  have hle : v.asIdeal ≤ v.asIdeal ^ 2 := by
    refine hs.symm.trans_le (Ideal.span_le.mpr fun r hr ↦ ?_)
    by_contra hr2
    exact h r hr (v.intValuation_eq_exp_neg_one_of_mem_of_notMem_sq (hs ▸ Ideal.subset_span hr)
      hr2)
  exact (Ideal.pow_succ_lt_pow v.ne_bot 1).not_ge (by rwa [pow_one])

end IsDedekindDomain.HeightOneSpectrum
