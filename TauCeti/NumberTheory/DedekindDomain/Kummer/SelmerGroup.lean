/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Unramified.Kummer
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import TauCeti.RingTheory.DedekindDomain.SelmerGroup

/-!
# Kummer classes unramified outside `S` and the Selmer group `K(S, n)`

Let `R` be a Dedekind domain with finite residue fields and fraction field `K`, let `n` be a natural
number invertible in `K`, and let `S` be a set of height-one primes of `R` containing every prime
that divides `n`. For each prime `v` fix a `K`-embedding `τ v : Kˢ → K_vˢ` of separable closures,
along which a class of `H¹(G_K, μₙ)` restricts to a class of `H¹(G_{K_v}, μₙ)`. A class is
**unramified outside `S`** when, for every `v ∉ S`, its restriction to `K_v` vanishes on the
inertia subgroup of `K_v` (`TauCeti.unramifiedOutsideKummerCohomology`).

Under the Kummer isomorphism `Kˣ ⧸ (Kˣ)ⁿ ≃ H¹(G_K, μₙ)` these are exactly the classes of the
Selmer group `K(S, n)`, the power classes whose `v`-adic valuation is divisible by `n` at every
`v ∉ S` (`TauCeti.kummerMap_mem_unramifiedOutsideKummerCohomology_iff`). Indeed restriction to
`K_v` carries the Kummer class of `a ∈ Kˣ` to the Kummer class of its image in `K_v`
(`TauCeti.explicitMap1_kummerMap`), which is unramified exactly when `n` divides the normalized
valuation of `a` at `v` (`TauCeti.explicitRes1_kummerMap_eq_zero_iff`, using that `v` does not
divide `n`). In particular, under these hypotheses the condition does not depend on the chosen
embeddings `τ`.

Over a number field, the finiteness of `K(S, n)` turns this into the finiteness of the classes
unramified outside a finite `S`; see
`TauCeti/NumberTheory/NumberField/Kummer/SelmerGroup.lean`.

## Main definitions

* `TauCeti.unramifiedOutsideKummerCohomology τ S n`: the classes of `H¹(G_K, μₙ)` whose restriction
  to every `K_v` with `v ∉ S` vanishes on inertia.

## Main results

* `TauCeti.kummerMap_mem_unramifiedOutsideKummerCohomology_iff`: the Kummer class of `a ∈ Kˣ` is
  unramified outside `S` exactly when the power class of `a` lies in `K(S, n)`.
* `TauCeti.mem_unramifiedOutsideKummerCohomology_iff_exists`: the classes unramified outside `S`
  are exactly the Kummer classes of the elements of `K(S, n)`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.1, Proposition VIII.1.6
  and its proof.
-/

public section

noncomputable section

namespace TauCeti

open ContCohomology IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (τ : ∀ v : HeightOneSpectrum R,
    SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
  (S : Set (HeightOneSpectrum R)) (n : ℕ)

/-- **The Kummer classes unramified outside `S`**: the classes of `H¹(G_K, μₙ)` whose restriction
to the completion `K_v` along `τ v`, for every prime `v ∉ S`, vanishes on the inertia subgroup of
`K_v`. -/
def unramifiedOutsideKummerCohomology :
    AddSubgroup (H1 (AbsoluteGaloisGroup K) (KummerCoeff K n)) :=
  ⨅ (v : HeightOneSpectrum R) (_ : v ∉ S),
    ((explicitRes1 (AbsoluteGaloisGroup (v.adicCompletion K)) (KummerCoeff (v.adicCompletion K) n)
      ((inertiaSubgroup (v.adicCompletion K)).map
        (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K)).toMonoidHom)).comp
      (explicitMap1 (AbsoluteGaloisGroup K) (KummerCoeff K n)
        (AbsoluteGaloisGroup (v.adicCompletion K)) (KummerCoeff (v.adicCompletion K) n)
        (absoluteGaloisGroupMap (τ v)) (kummerCoeffBaseChange n (τ v))
        continuous_of_discreteTopology (kummerCoeffBaseChange_smul n (τ v)))).ker

variable {τ S n}

/-- A class is unramified outside `S` exactly when, at every `v ∉ S`, its restriction to `K_v`
vanishes on inertia. -/
theorem mem_unramifiedOutsideKummerCohomology_iff
    {c : H1 (AbsoluteGaloisGroup K) (KummerCoeff K n)} :
    c ∈ unramifiedOutsideKummerCohomology τ S n ↔ ∀ v ∉ S,
      explicitRes1 (AbsoluteGaloisGroup (v.adicCompletion K)) (KummerCoeff (v.adicCompletion K) n)
        ((inertiaSubgroup (v.adicCompletion K)).map
          (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K)).toMonoidHom)
        (explicitMap1 (AbsoluteGaloisGroup K) (KummerCoeff K n)
          (AbsoluteGaloisGroup (v.adicCompletion K)) (KummerCoeff (v.adicCompletion K) n)
          (absoluteGaloisGroupMap (τ v)) (kummerCoeffBaseChange n (τ v))
          continuous_of_discreteTopology (kummerCoeffBaseChange_smul n (τ v)) c) = 0 := by
  simp only [unramifiedOutsideKummerCohomology, AddSubgroup.mem_iInf, AddMonoidHom.mem_ker,
    AddMonoidHom.comp_apply]

/-- **Kummer classes unramified outside `S` are the Selmer group `K(S, n)`.** If `n` is invertible
in `K` and no prime outside `S` divides `n`, the Kummer class of `a ∈ Kˣ` is unramified outside
`S` exactly when the power class of `a` lies in `K(S, n)`, that is, when `n` divides the `v`-adic
valuation of `a` at every `v ∉ S`. -/
theorem kummerMap_mem_unramifiedOutsideKummerCohomology_iff (hn : IsUnit (n : K))
    (hS : ∀ v ∉ S, (n : R) ∉ v.asIdeal) (a : Kˣ) :
    (kummerMap K n hn a).toAdd ∈ unramifiedOutsideKummerCohomology τ S n ↔
      (QuotientGroup.mk a : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) ∈
        selmerGroup (R := R) (K := K) (S := S) (n := n) := by
  rw [mem_unramifiedOutsideKummerCohomology_iff]
  refine forall₂_congr fun v hv ↦ ?_
  -- restriction to `K_v` is the Kummer class of the image of `a`, whose normalized valuation is
  -- minus the `v`-adic valuation of `a`
  have hval : (normalizedValuation (v.adicCompletion K)
      (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) a)).toAdd =
        -(v.valuationOfNeZero a).toAdd := by
    have h := v.coe_normalizedValuation_unitsMap_algebraMap (K := K) a
    rw [← HeightOneSpectrum.valuationOfNeZero_eq, ← WithZero.coe_inv, WithZero.coe_inj] at h
    rw [h, toAdd_inv]
  rw [explicitMap1_kummerMap n (τ v) hn a,
    explicitRes1_kummerMap_eq_zero_iff (v.adicCompletion K) _
      (mt v.ringChar_residueField_adicCompletion_dvd_iff.1 (hS v hv)),
    hval, Int.dvd_neg, HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]

/-- **The classes unramified outside `S` are the Kummer classes of `K(S, n)`.** If `n` is
invertible in `K` and no prime outside `S` divides `n`, a class of `H¹(G_K, μₙ)` is unramified
outside `S` exactly when it is the Kummer class of an element of `Kˣ` whose power class lies in
`K(S, n)`. -/
theorem mem_unramifiedOutsideKummerCohomology_iff_exists (hn : IsUnit (n : K))
    (hS : ∀ v ∉ S, (n : R) ∉ v.asIdeal) {c : H1 (AbsoluteGaloisGroup K) (KummerCoeff K n)} :
    c ∈ unramifiedOutsideKummerCohomology τ S n ↔
      ∃ a : Kˣ, (QuotientGroup.mk a : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) ∈
        selmerGroup (R := R) (K := K) (S := S) (n := n) ∧ (kummerMap K n hn a).toAdd = c := by
  obtain ⟨a, ha⟩ := kummerMap_surjective hn (Multiplicative.ofAdd c)
  obtain rfl : (kummerMap K n hn a).toAdd = c := by rw [ha, toAdd_ofAdd]
  refine ⟨fun h ↦ ⟨a, (kummerMap_mem_unramifiedOutsideKummerCohomology_iff hn hS a).1 h, rfl⟩,
    fun ⟨b, hb, hba⟩ ↦ ?_⟩
  rw [← hba]
  exact (kummerMap_mem_unramifiedOutsideKummerCohomology_iff hn hS b).2 hb

end TauCeti
