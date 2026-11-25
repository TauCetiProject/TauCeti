/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import TauCeti.Algebra.Polynomial.Lifts
public import TauCeti.RingTheory.Polynomial.Resultant.Basic

/-!
# Recognising a monic polynomial over a DVR by valuations of resultants

Let `O` be a discrete valuation ring with uniformizer `π`. A monic polynomial `P ∈ O[X]` is
determined by the valuations of its resultants `Res(P, ψ)` against monic test polynomials `ψ`,
even when the tests only come from a ring `D` whose image in `O` is dense for the `π`-adic
topology.
This is Milne's characteristic-polynomial uniqueness criterion (used to identify the
characteristic polynomial of an endomorphism on the Dieudonné module of an abelian variety with
its integral characteristic polynomial), stated here for an arbitrary DVR: completeness,
separability, characteristic zero and a finite residue field are not needed.

The tests detect multiplicities through shifted factors. If `R` is monic of degree `d` and
`ψ ≡ R + πⁿ (mod π²ⁿ)`, then `ψ = R + πⁿ g` with `g ≡ 1 (mod πⁿ)`, so
`Res(R, ψ) = π ^ (n d) Res(R, g)` with `Res(R, g)` a unit, and `v Res(R, ψ) = n d` exactly. For
`P = Rᵉ S` with `Res(S, R) ≠ 0` and `ψ` of degree `d`, the factor `Res(S, ψ)` is congruent to
`Res(S, R)` modulo `πⁿ`, so its valuation is eventually constant and
`v Res(P, ψ) = n d e + v Res(S, R)` for all large `n`. The slope in `n` recovers the multiplicity
`e` of every irreducible factor, including repeated and inseparable ones.

The density hypothesis cannot be dropped: for `D = 𝔽₂` inside `O = 𝔽₂⟦t⟧`, the distinct
polynomials `X + t` and `X + t + t²` have equal resultant valuations against every monic
`ψ ∈ 𝔽₂[X]`.

## Main results

* `Polynomial.Monic.addVal_resultant_of_dvd_sub`: if `R` is monic, `ψ ≡ R + πⁿ (mod π²ⁿ)` and
  `n ≥ 1`, then `v Res(R, ψ) = n · deg R`.
* `Polynomial.Monic.eventually_addVal_resultant_pow_mul`: for `P = Rᵉ S` with `Res(S, R) ≠ 0`,
  eventually in `n`, `v Res(P, ψ) = n · deg R · e + v Res(S, R)` for every such `ψ`.
* `Polynomial.Monic.eq_of_forall_addVal_resultant_eq`: two monic polynomials over a DVR with
  equal valuations of all common nonzero resultants against monic tests lifted from a `π`-adically
  dense ring are equal.

## References

* J. S. Milne, *Extensions of abelian varieties defined over a finite field*, Invent. Math. 5
  (1968), 63–84, §1 (the uniqueness criterion for characteristic polynomials, p. 65).
-/

public section

open IsDiscreteValuationRing UniqueFactorizationMonoid

namespace Polynomial

/-- A polynomial `ψ ≡ R + aⁿ (mod a²ⁿ)` has the form `ψ = aⁿ g + R` with `g ≡ 1 (mod aⁿ)`. -/
private theorem exists_eq_C_mul_add_of_dvd_sub {O : Type*} [CommRing O] {R ψ : O[X]} {a : O}
    {n : ℕ} (hcong : C (a ^ (2 * n)) ∣ ψ - (R + C (a ^ n))) :
    ∃ h : O[X], ψ = C (a ^ n) * (1 + C (a ^ n) * h) + R := by
  obtain ⟨h, hh⟩ := hcong
  have hC : C (a ^ (2 * n)) = C (a ^ n) * C (a ^ n) := by rw [mul_comm 2 n, pow_mul, sq, C_mul]
  exact ⟨h, by linear_combination hh + h * hC⟩

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The valuation of a shifted-factor resultant.** Let `R` be monic and `ψ ≡ R + πⁿ (mod π²ⁿ)`
with `n ≥ 1`. Then `Res(R, ψ)` is `π ^ (n · deg R)` times a unit, so its valuation is
`n · deg R`. -/
theorem Monic.addVal_resultant_of_dvd_sub {R ψ : O[X]} (hR : R.Monic) {π : O}
    (hπ : Irreducible π) {n : ℕ} (hn : n ≠ 0) (hcong : C (π ^ (2 * n)) ∣ ψ - (R + C (π ^ n))) :
    addVal O (R.resultant ψ) = (n * R.natDegree : ℕ) := by
  obtain ⟨h, hψ⟩ := exists_eq_C_mul_add_of_dvd_sub hcong
  set g := 1 + C (π ^ n) * h
  -- compute with the degree bound `k` for `ψ`, which is also valid for `R`
  obtain ⟨k, hψk, hRk⟩ : ∃ k, ψ.natDegree ≤ k ∧ R.natDegree ≤ k :=
    ⟨_, le_max_left _ _, le_max_right _ _⟩
  have hres : R.resultant ψ = (π ^ n) ^ R.natDegree * R.resultant g R.natDegree k := by
    rw [← hR.resultant_of_le hψk, hψ, show C (π ^ n) * g + R = C (π ^ n) * g + R * 1 by
      rw [mul_one], resultant_add_mul_right _ _ _ _ _ (by simpa using hRk) le_rfl,
      resultant_C_mul_right]
  -- modulo the maximal ideal `g` reduces to `1`, so `Res(R, g)` reduces to `1` and is a unit
  have hunit : IsUnit (R.resultant g R.natDegree k) := by
    have hπ0 : IsLocalRing.residue O π = 0 :=
      not_not.mp fun h ↦ hπ.not_isUnit ((IsLocalRing.residue_ne_zero_iff_isUnit π).mp h)
    have hg : g.map (IsLocalRing.residue O) = 1 := by
      simp [g, hπ0, zero_pow hn]
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← resultant_map_map, hg, resultant_one_right,
      coeff_map]
    simp [hR.leadingCoeff]
  rw [hres, addVal_mul, (addVal_eq_zero_iff).mpr hunit, add_zero, ← pow_mul, hπ.addVal_pow]

/-- **Multiplicity detected by shifted factors.** Let `R` be monic, `e ≥ 0`, and let `S` satisfy
`Res(S, R) ≠ 0` (over the fraction field this says that `S` and `R` are coprime). Eventually in
`n`, every `ψ` of the degree of `R` with `ψ ≡ R + πⁿ (mod π²ⁿ)` has
`Res(Rᵉ S, ψ) ≠ 0` and `v Res(Rᵉ S, ψ) = n · deg R · e + v Res(S, R)`. -/
theorem Monic.eventually_addVal_resultant_pow_mul {R S : O[X]} (hR : R.Monic) {π : O}
    (hπ : Irreducible π) (hSR : S.resultant R ≠ 0) (e : ℕ) :
    ∀ᶠ n in Filter.atTop, ∀ ψ : O[X], ψ.natDegree = R.natDegree →
      C (π ^ (2 * n)) ∣ ψ - (R + C (π ^ n)) →
        (R ^ e * S).resultant ψ ≠ 0 ∧
          addVal O ((R ^ e * S).resultant ψ) =
            (n * R.natDegree * e : ℕ) + addVal O (S.resultant R) := by
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp ((addVal_eq_top_iff (R := O)).not.mpr hSR)
  replace hc := hc.symm
  have hdeg : (R ^ e * S).natDegree = (R ^ e).natDegree + S.natDegree := by
    rcases eq_or_ne S 0 with rfl | hS
    · have hR0 : R.natDegree = 0 := by
        by_contra h
        simp [zero_pow h] at hSR
      simp [hR0]
    · exact (hR.pow e).natDegree_mul' hS
  filter_upwards [Filter.eventually_gt_atTop c] with n hn ψ hψ hcong
  have hn0 : n ≠ 0 := by omega
  -- `Res(S, ψ)` is congruent to `Res(S, R)` modulo `πⁿ`
  have hSψ : addVal O (S.resultant ψ) = c := by
    obtain ⟨h, hψ'⟩ := exists_eq_C_mul_add_of_dvd_sub hcong
    have hmk : ψ.map (Ideal.Quotient.mk (Ideal.span {π ^ n})) =
        R.map (Ideal.Quotient.mk (Ideal.span {π ^ n})) := by
      simp [hψ', -map_pow]
    have hmem : S.resultant ψ - S.resultant R ∈ Ideal.span {π ^ n} := by
      simpa only [hψ] using resultant_sub_mem_of_map_eq (f := S) rfl hmk S.natDegree ψ.natDegree
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hmem
    rw [show S.resultant ψ = S.resultant R + π ^ n * t by rw [← ht]; ring,
      AddValuation.map_add_eq_of_lt_left, hc]
    rw [hc, addVal_mul, hπ.addVal_pow]
    exact (Nat.cast_lt.mpr hn).trans_le le_self_add
  have hval : addVal O ((R ^ e * S).resultant ψ) = (n * R.natDegree * e : ℕ) + c := by
    have hlc : R.leadingCoeff ^ e ≠ 0 := by rw [hR.leadingCoeff, one_pow]; exact one_ne_zero
    have hmul : (R ^ e * S).resultant ψ = R.resultant ψ ^ e * S.resultant ψ := by
      rw [show (R ^ e * S).resultant ψ =
          (R ^ e * S).resultant ψ ((R ^ e).natDegree + S.natDegree) ψ.natDegree by rw [hdeg],
        resultant_mul_left _ _ _ _ le_rfl,
        resultant_pow_left (f := R) (g := ψ) (m := e) (n := ψ.natDegree) hlc le_rfl]
    rw [hmul, addVal_mul, addVal_pow, hR.addVal_resultant_of_dvd_sub hπ hn0 hcong, hSψ]
    push_cast
    ring
  refine ⟨fun h0 ↦ ?_, by rw [hval, hc]⟩
  rw [h0, addVal_zero] at hval
  exact ENat.top_ne_natCast _ (hval.trans (Nat.cast_add _ _).symm)

section Recognition

variable {D : Type*} [Semiring D]

/-- Shifted-factor tests lifted from a `π`-adically dense ring: for monic `R` of positive degree
there is a monic `ψ` over `D` whose image has the degree of `R` and satisfies
`ψ ≡ R + πⁿ (mod π²ⁿ)`. -/
private theorem exists_monic_map_dvd_sub {R : O[X]} (hR : R.Monic) (hd : 0 < R.natDegree)
    (φ : D →+* O) {π : O} (hφ : ∀ N : ℕ, ∀ o : O, ∃ d : D, o - φ d ∈ Ideal.span {π ^ N})
    (n : ℕ) : ∃ ψ : D[X], ψ.Monic ∧ (ψ.map φ).natDegree = R.natDegree ∧
      C (π ^ (2 * n)) ∣ ψ.map φ - (R + C (π ^ n)) := by
  have hT : (R + C (π ^ n)).Monic :=
    hR.add_of_left (degree_C_le.trans_lt (natDegree_pos_iff_degree_pos.mp hd))
  obtain ⟨ψ, hψ, hdeg, hmem⟩ := hT.exists_monic_map_sub_mem_map_C φ (hφ (2 * n))
  refine ⟨ψ, hψ, by rw [hψ.natDegree_map, hdeg, natDegree_add_C], ?_⟩
  rwa [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hmem

/-- Splitting off the full power of a monic prime factor `R` of a monic `P` leaves a cofactor `S`
with `Res(S, R) ≠ 0`. -/
private theorem exists_eq_pow_multiplicity_mul {R P : O[X]} (hR : R.Monic) (hRp : Prime R)
    (hP : P.Monic) : ∃ S : O[X], P = R ^ multiplicity R P * S ∧ S.resultant R ≠ 0 := by
  obtain ⟨S, hS⟩ := pow_multiplicity_dvd R P
  refine ⟨S, hS, hR.resultant_ne_zero_of_not_dvd hRp.irreducible ?_⟩
  rintro ⟨T, rfl⟩
  exact (FiniteMultiplicity.of_prime_left hRp hP.ne_zero).not_pow_dvd_of_multiplicity_lt
    (lt_add_one _) ⟨T, hS.trans (by ring)⟩

/-- Under the hypotheses of `Polynomial.Monic.eq_of_forall_addVal_resultant_eq`, every monic prime
factor occurs in `P` and `Q` with the same multiplicity: it is the slope in `n` of the valuations
`v Res(P, ψₙ)` and `v Res(Q, ψₙ)` along shifted-factor tests `ψₙ`. -/
private theorem emultiplicity_eq_of_forall_addVal_resultant_eq {P Q R : O[X]} (hP : P.Monic)
    (hQ : Q.Monic) (hR : R.Monic) (hRp : Prime R) (φ : D →+* O) {π : O} (hπ : Irreducible π)
    (hφ : ∀ N : ℕ, ∀ o : O, ∃ d : D, o - φ d ∈ Ideal.span {π ^ N})
    (h : ∀ ψ : D[X], ψ.Monic → P.resultant (ψ.map φ) ≠ 0 → Q.resultant (ψ.map φ) ≠ 0 →
      addVal O (P.resultant (ψ.map φ)) = addVal O (Q.resultant (ψ.map φ))) :
    emultiplicity R P = emultiplicity R Q := by
  have hd : 0 < R.natDegree := by
    by_contra hd
    rw [not_lt, Nat.le_zero] at hd
    exact hRp.not_isUnit (by rw [eq_one_of_monic_natDegree_zero hR hd]; exact isUnit_one)
  obtain ⟨SP, hSP, hSPR⟩ := exists_eq_pow_multiplicity_mul hR hRp hP
  obtain ⟨SQ, hSQ, hSQR⟩ := exists_eq_pow_multiplicity_mul hR hRp hQ
  obtain ⟨cP, hcP⟩ := ENat.ne_top_iff_exists.mp ((addVal_eq_top_iff (R := O)).not.mpr hSPR)
  obtain ⟨cQ, hcQ⟩ := ENat.ne_top_iff_exists.mp ((addVal_eq_top_iff (R := O)).not.mpr hSQR)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((hR.eventually_addVal_resultant_pow_mul hπ hSPR (multiplicity R P)).and
      (hR.eventually_addVal_resultant_pow_mul hπ hSQR (multiplicity R Q)))
  have key (n : ℕ) (hn : N ≤ n) :
      n * R.natDegree * multiplicity R P + cP = n * R.natDegree * multiplicity R Q + cQ := by
    obtain ⟨hPn, hQn⟩ := hN n hn
    obtain ⟨ψ, hψ, hdeg, hcong⟩ := exists_monic_map_dvd_sub hR hd φ hφ n
    obtain ⟨hP0, hPv⟩ := hPn _ hdeg hcong
    obtain ⟨hQ0, hQv⟩ := hQn _ hdeg hcong
    rw [← hSP] at hP0 hPv
    rw [← hSQ] at hQ0 hQv
    have := h ψ hψ hP0 hQ0
    rw [hPv, hQv, ← hcP, ← hcQ] at this
    exact_mod_cast this
  have h1 := key N le_rfl
  have h2 := key (N + 1) (Nat.le_succ N)
  have hmul : R.natDegree * multiplicity R P = R.natDegree * multiplicity R Q := by
    zify at h1 h2 ⊢
    linear_combination h2 - h1
  rw [(FiniteMultiplicity.of_prime_left hRp hP.ne_zero).emultiplicity_eq_multiplicity,
    (FiniteMultiplicity.of_prime_left hRp hQ.ne_zero).emultiplicity_eq_multiplicity,
    Nat.eq_of_mul_eq_mul_left hd hmul]

/-- **Recognition from nonzero monic resultant tests.** Let `O` be a discrete valuation ring with
uniformizer `π`, and let `φ : D →+* O` be surjective modulo every power of `π`. If the monic
polynomials `P, Q ∈ O[X]` have `v Res(P, ψ) = v Res(Q, ψ)` for every monic `ψ ∈ D[X]` for which
both resultants against the image of `ψ` are nonzero, then `P = Q`.

Equal degrees, completeness, separability, characteristic zero and a finite residue field are not
assumed; repeated and inseparable factors are detected. Milne, §1. -/
theorem Monic.eq_of_forall_addVal_resultant_eq {P Q : O[X]} (hP : P.Monic) (hQ : Q.Monic)
    (φ : D →+* O) {π : O} (hπ : Irreducible π)
    (hφ : ∀ N : ℕ, ∀ o : O, ∃ d : D, o - φ d ∈ Ideal.span {π ^ N})
    (h : ∀ ψ : D[X], ψ.Monic → P.resultant (ψ.map φ) ≠ 0 → Q.resultant (ψ.map φ) ≠ 0 →
      addVal O (P.resultant (ψ.map φ)) = addVal O (Q.resultant (ψ.map φ))) :
    P = Q := by
  -- every prime of `O[X]` has the same multiplicity in `P` and in `Q`
  have key (p : O[X]) (hp : Prime p) : emultiplicity p P = emultiplicity p Q := by
    by_cases hdvd : p ∣ P ∨ p ∣ Q
    · -- `p` divides a monic polynomial, so it is a unit multiple of a monic prime `R`
      have hu : IsUnit p.leadingCoeff :=
        hdvd.elim hP.isUnit_leadingCoeff_of_dvd hQ.isUnit_leadingCoeff_of_dvd
      have hassoc : Associated p (p * C (↑hu.unit⁻¹ : O)) :=
        associated_mul_unit_right _ _ (isUnit_C.mpr (Units.isUnit _))
      have hR : (p * C (↑hu.unit⁻¹ : O)).Monic := by
        rw [Monic, leadingCoeff_mul, leadingCoeff_C, hu.mul_val_inv]
      rw [← emultiplicity_eq_of_associated_left hassoc,
        ← emultiplicity_eq_of_associated_left hassoc]
      exact emultiplicity_eq_of_forall_addVal_resultant_eq hP hQ hR (hassoc.prime hp) φ hπ hφ h
    · rw [not_or] at hdvd
      rw [emultiplicity_eq_zero.mpr hdvd.1, emultiplicity_eq_zero.mpr hdvd.2]
  refine eq_of_monic_of_associated hP hQ (associated_of_dvd_dvd ?_ ?_)
  · exact (dvd_iff_emultiplicity_le hP.ne_zero).mpr fun p hp ↦ (key p hp).le
  · exact (dvd_iff_emultiplicity_le hQ.ne_zero).mpr fun p hp ↦ (key p hp).ge

end Recognition

end Polynomial
