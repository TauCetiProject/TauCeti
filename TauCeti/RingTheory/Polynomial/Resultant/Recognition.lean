/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import TauCeti.Algebra.Polynomial.Lifts
import TauCeti.RingTheory.Polynomial.Monic.Factorization
import TauCeti.RingTheory.Polynomial.Resultant.AdjoinRoot

/-!
# Resultant recognition over a discrete valuation ring

A monic polynomial `P : O[X]` over a discrete valuation ring `O` is uniquely determined by the
valuations of its nonzero resultants `P.resultant (ψ.map φ)` against monic polynomials `ψ : D[X]`
lifted from a semiring `D` whose image under `φ : D →+* O` is dense modulo every power of a
uniformizer `π`. No equal-degree, completeness, separability, characteristic-zero, or finite-
residue-field assumption is required.

The key mechanism is a shifted-factor test: for any monic `R : O[X]` of positive degree `d`,
if `ψ : O[X]` is congruent to `R + C (π ^ n)` modulo `π ^ (2 * n)` with `n ≥ 1`, then in
`AdjoinRoot R` we have `mk R ψ = π ^ n * (1 + π ^ n * H)` for a polynomial `H`, so its norm
`R.resultant ψ` equals `π ^ (n * d) * u` for a unit `u ≡ 1 (mod π ^ n)` and thus has additive
valuation `n * d`. When `P = R ^ e * S` with `S.resultant R ≠ 0`, the second factor
`S.resultant ψ` stabilizes in valuation once `n > addVal O (S.resultant R)`, giving
`addVal O (P.resultant ψ) = n * d * e + addVal O (S.resultant R)`. Comparing slopes across two
large values of `n` recovers the multiplicity `e` of every monic irreducible factor over
`FractionRing O`.

## Main results

* `Polynomial.addVal_resultant_of_sub_add_C_pow_mem`: valuation of the resultant of a monic
  polynomial with a shifted lift.
* `Polynomial.addVal_resultant_pow_mul_of_sub_add_C_pow_mem`: shifted-factor multiplicity slope
  formula over a discrete valuation ring.
* `Polynomial.resultantRecognition`: monic tests from a uniformizer-adically dense semiring uniquely
  determine a monic polynomial over a discrete valuation ring.

## References

* J. S. Milne, *The Tate-Šafarevič group of a constant abelian variety*, Invent. Math. 6 (1968),
  §1, p. 65 ([1968a](https://jmilne.org/math/articles/1968a.pdf)), the uniqueness criterion for
  characteristic polynomials over `ℤ_p`; the arbitrary-ideal and general-DVR formulations here are
  a Tau Ceti adaptation.
-/

public section

noncomputable section

open Polynomial

namespace Polynomial

section DVR

open IsDiscreteValuationRing

/-- For a monic polynomial `R : O[X]` over a discrete valuation ring `O` with uniformizer `π` and
`n ≥ 1`, any `ψ : O[X]` whose coefficients match `R + C (π ^ n)` modulo `π ^ (2 * n)` has
nonzero resultant with `R` of additive valuation `n * R.natDegree`. -/
theorem addVal_resultant_of_sub_add_C_pow_mem {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {π : O} (hπ : Irreducible π) {R ψ : O[X]} (hR : R.Monic)
    {n : ℕ} (hn : 1 ≤ n)
    (hψ : ∀ i, (ψ - (R + C (π ^ n))).coeff i ∈ Ideal.span {π ^ (2 * n)}) :
    R.resultant ψ ≠ 0 ∧ addVal O (R.resultant ψ) = (n * R.natDegree : ℕ) := by
  have hψ' : ∀ i, (ψ - (R + C (π ^ n))).coeff i ∈ Ideal.span {π ^ n * π ^ n} := by
    simpa [← pow_add, ← two_mul] using hψ
  obtain ⟨u, hu, hres⟩ :=
    exists_resultant_eq_pow_mul_of_coeff_mem_span_mul hR (π ^ n) (π ^ n) hψ'
  have hu_unit : IsUnit u := IsLocalRing.isUnit_of_mem_nonunits_one_sub_self u <|
    (IsLocalRing.mem_maximalIdeal _).mp <| Ideal.span_le.mpr
      (Set.singleton_subset_iff.mpr <| Ideal.pow_mem_of_mem _
        ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit) n hn)
      (neg_sub u 1 ▸ Submodule.neg_mem _ hu)
  have hne : R.resultant ψ ≠ 0 := by
    rw [hres]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hπ.ne_zero)) hu_unit.ne_zero
  refine ⟨hne, ?_⟩
  have hval_u : addVal O u = 0 := addVal_eq_zero_iff.mpr hu_unit
  rw [hres, addVal_mul, hval_u, add_zero, ← pow_mul, hπ.addVal_pow]

/-- **Multiplicity detected by shifted factors.** Let `O` be a discrete valuation ring with
uniformizer `π`, and let `R, S : O[X]` be monic with `S.resultant R ≠ 0`. For `P = R ^ e * S`,
any `n` strictly larger than `addVal O (S.resultant R)`, and any `ψ : O[X]` congruent to
`R + C (π ^ n)` modulo `π ^ (2 * n)`, we have `P.resultant ψ ≠ 0` and
`addVal O (P.resultant ψ) = (n * R.natDegree * e : ℕ) + addVal O (S.resultant R)`. -/
theorem addVal_resultant_pow_mul_of_sub_add_C_pow_mem {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {π : O} (hπ : Irreducible π) {R S ψ : O[X]} (hR : R.Monic)
    (hS : S.Monic) (e : ℕ) {n : ℕ} (hlt : addVal O (S.resultant R) < n)
    (hψ : ∀ i, (ψ - (R + C (π ^ n))).coeff i ∈ Ideal.span {π ^ (2 * n)}) :
    (R ^ e * S).resultant ψ ≠ 0 ∧
      addVal O ((R ^ e * S).resultant ψ) =
        ((n * R.natDegree * e : ℕ) : ℕ∞) + addVal O (S.resultant R) := by
  have hn : 1 ≤ n := Nat.cast_pos.mp (lt_of_le_of_lt bot_le hlt)
  have hR_val := addVal_resultant_of_sub_add_C_pow_mem hπ hR hn hψ
  have hsub : ∀ i, (ψ - R).coeff i ∈ Ideal.span {π ^ n} := by
    intro i
    have hi : (ψ - (R + C (π ^ n))).coeff i ∈ Ideal.span {π ^ n} := by
      have hdiv : Ideal.span {π ^ (2 * n)} ≤ Ideal.span {π ^ n} :=
        Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_span_singleton.mpr
          (pow_dvd_pow π (by lia))))
      exact hdiv (hψ i)
    have hc : (C (π ^ n)).coeff i ∈ Ideal.span {π ^ n} := by
      rw [coeff_C]
      split_ifs
      · exact Ideal.subset_span rfl
      · exact Ideal.zero_mem _
    have heq : (ψ - R).coeff i = (ψ - (R + C (π ^ n))).coeff i + (C (π ^ n)).coeff i := by
      simp [sub_eq_add_neg, add_assoc]
    rw [heq]
    exact Ideal.add_mem _ hi hc
  have hS_diff : (n : ℕ∞) ≤ addVal O (S.resultant ψ - S.resultant R) := by
    have hmem := hS.resultant_sub_mem_of_coeff_sub_mem hsub
    rw [← hπ.addVal_pow n, addVal_le_iff_dvd]
    exact Ideal.mem_span_singleton.mp hmem
  have hS_lt : addVal O (S.resultant R) < addVal O (S.resultant ψ - S.resultant R) :=
    lt_of_lt_of_le hlt hS_diff
  have hS_val : addVal O (S.resultant ψ) = addVal O (S.resultant R) :=
    (addVal O).map_eq_of_lt_sub hS_lt
  have hS_ne : S.resultant ψ ≠ 0 :=
    addVal_eq_top_iff.not.mp (by rw [hS_val]; exact (lt_of_lt_of_le hlt le_top).ne)
  rw [hR.resultant_pow_mul_left hS.ne_zero e ψ]
  refine ⟨mul_ne_zero (pow_ne_zero e hR_val.1) hS_ne, ?_⟩
  rw [addVal_mul, addVal_pow, hR_val.2, hS_val, nsmul_eq_mul, ← Nat.cast_mul, mul_comm e]

end DVR

section Recognition

/-- **Resultant recognition.** Let `O` be a discrete valuation ring with uniformizer `π`,
and let `φ : D →+* O` be a ring homomorphism whose image is dense modulo every power `π ^ N`.
If monic polynomials `P, Q : O[X]` have equal additive valuations
`addVal O (P.resultant (ψ.map φ))` and `addVal O (Q.resultant (ψ.map φ))` for every monic
`ψ : D[X]` such that both resultants are nonzero, then `P = Q`. -/
theorem resultantRecognition {D O : Type*} [Semiring D] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (φ : D →+* O) (π : O) (hπ : Irreducible π)
    (hφ : ∀ N : ℕ, ∀ o : O, ∃ d : D, o - φ d ∈ Ideal.span {π ^ N})
    (P Q : Polynomial O) (hP : P.Monic) (hQ : Q.Monic)
    (h : ∀ ψ : Polynomial D, ψ.Monic →
      Polynomial.resultant P (ψ.map φ) ≠ 0 →
      Polynomial.resultant Q (ψ.map φ) ≠ 0 →
      IsDiscreteValuationRing.addVal O (Polynomial.resultant P (ψ.map φ)) =
        IsDiscreteValuationRing.addVal O (Polynomial.resultant Q (ψ.map φ))) :
    P = Q := by
  by_contra hne
  let K := FractionRing O
  obtain ⟨R₀, hR₀_m, hR₀_irr, e₁, e₂, S₁, S₂,
      hS₁_m, hS₂_m, hS₁_nd, hS₂_nd, rfl, rfl, he⟩ :=
    hP.exists_factor_ne_multiplicity (K := K) hQ hne
  have hinj := IsFractionRing.injective O K
  have hd_pos : 0 < R₀.natDegree := by
    rw [← natDegree_map_eq_of_injective hinj]
    exact hR₀_irr.natDegree_pos
  have hSR (S : O[X]) (hS_nd : ¬ (R₀.map (algebraMap O K) ∣ S.map (algebraMap O K))) :
      S.resultant R₀ ≠ 0 :=
    resultant_ne_zero_of_isCoprime_map (algebraMap O K)
      (natDegree_map_eq_of_injective hinj _) (natDegree_map_eq_of_injective hinj _)
      (hR₀_irr.coprime_iff_not_dvd.mpr hS_nd).symm
  obtain ⟨k₁, hk₁⟩ := ENat.ne_top_iff_exists.mp
    (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr (hSR S₁ hS₁_nd))
  obtain ⟨k₂, hk₂⟩ := ENat.ne_top_iff_exists.mp
    (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr (hSR S₂ hS₂_nd))
  have hslope (n : ℕ) (hn₁ : k₁ < n) (hn₂ : k₂ < n) :
      n * R₀.natDegree * e₁ + k₁ = n * R₀.natDegree * e₂ + k₂ := by
    let T : O[X] := R₀ + C (π ^ n)
    have hCdeg : (C (π ^ n)).degree < R₀.degree :=
      (degree_C_le).trans_lt (natDegree_pos_iff_degree_pos.mp hd_pos)
    have hT_monic : T.Monic := hR₀_m.add_of_left hCdeg
    obtain ⟨ψ, hψ_m, -, hψ_coeff⟩ :=
      exists_monic_map_sub_coeff_mem φ (hφ (2 * n)) hT_monic
    obtain ⟨hPψ_ne, hPψ_val⟩ :=
      addVal_resultant_pow_mul_of_sub_add_C_pow_mem hπ hR₀_m hS₁_m e₁
        (by rw [← hk₁]; exact Nat.cast_lt.mpr hn₁) hψ_coeff
    obtain ⟨hQψ_ne, hQψ_val⟩ :=
      addVal_resultant_pow_mul_of_sub_add_C_pow_mem hπ hR₀_m hS₂_m e₂
        (by rw [← hk₂]; exact Nat.cast_lt.mpr hn₂) hψ_coeff
    have heq := h ψ hψ_m hPψ_ne hQψ_ne
    rw [hPψ_val, hQψ_val, ← hk₁, ← hk₂, ← Nat.cast_add, ← Nat.cast_add] at heq
    exact Nat.cast_injective heq
  let N := max k₁ k₂ + 1
  have h1 := hslope N (by lia) (by lia)
  have h2 := hslope (N + 1) (by lia) (by lia)
  have hmul : R₀.natDegree * e₁ = R₀.natDegree * e₂ := by nlinarith
  exact he (Nat.eq_of_mul_eq_mul_left hd_pos hmul)

end Recognition

end Polynomial
