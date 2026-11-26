/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation

/-!
# Selecting primes by a factor of an unramified uniformizer

Suppose `a * σ a` is the product of a base prime generator and an element prime to it,
where `σ` is a base-algebra automorphism. At an unramified prime over the generator,
exactly one factor belongs to the prime and the multiplicity of that factor is one.
When all primes over the generator are unramified, the primes containing `a` and the
primes containing `σ a` are complementary. The automorphism pairs the two sets, so each
has half the primes in the fiber. For complex conjugation this selects one prime from
each conjugate pair, as needed to define the support of residue characters.

The number-field application is the prime selection in `New.Parameters.star_mem_iff_notMem`
and `New.Parameters.intValuation_eq_of_mul_star` in `New/Derivatives/Field/WeilData.lean`
of lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open IsDedekindDomain WithZero

namespace IsDedekindDomain.HeightOneSpectrum

open Ideal in
/-- At a prime with ramification index one over `(r)`, the image of `r * c` has multiplicity
one when `c` is outside `(r)`. -/
theorem intValuation_algebraMap_mul_eq_exp_neg_one {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [IsDedekindDomain S]
    (w : HeightOneSpectrum S) {r c : R} [w.asIdeal.LiesOver (span {r})]
    (hr : algebraMap R S r ≠ 0) (hc : c ∉ span {r}) (he : w.asIdeal.ramificationIdx R = 1) :
    w.intValuation (algebraMap R S (r * c)) = exp (-1 : ℤ) := by
  have hmap : (span {r}).map (algebraMap R S) = span {algebraMap R S r} := by
    rw [map_span, Set.image_singleton]
  have hrmap : (span {r}).map (algebraMap R S) ≠ ⊥ := by
    rw [hmap]
    exact mt span_singleton_eq_bot.mp hr
  have hm := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (span {r}) w.asIdeal hrmap
  have hvc : w.intValuation (algebraMap R S c) = 1 :=
    intValuation_eq_one_iff.2 (mt (w.asIdeal.mem_of_liesOver (span {r}) c).2 hc)
  rw [hmap, he] at hm
  simp [map_mul, hvc, w.intValuation_eq_exp_neg_multiplicity hr, ← hm]

open Ideal in
/-- At a prime of ramification index one over `(r)`, if `x * y` is the image of `r * c`
with `c` outside `(r)`, then one factor has multiplicity one and the other is a local unit. -/
theorem intValuation_factors_of_mul_eq_algebraMap {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [IsDedekindDomain S]
    (w : HeightOneSpectrum S) {r c : R} [w.asIdeal.LiesOver (span {r})] {x y : S}
    (hr : algebraMap R S r ≠ 0) (hc : c ∉ span {r}) (he : w.asIdeal.ramificationIdx R = 1)
    (hxy : x * y = algebraMap R S (r * c)) :
    (w.intValuation x = exp (-1 : ℤ) ∧ w.intValuation y = 1) ∨
      (w.intValuation x = 1 ∧ w.intValuation y = exp (-1 : ℤ)) := by
  have h : w.intValuation (x * y) = exp (-1 : ℤ) :=
    hxy.symm ▸ w.intValuation_algebraMap_mul_eq_exp_neg_one hr hc he
  by_cases hx : x ∈ w.asIdeal
  · have hy : y ∉ w.asIdeal := by
      intro hy
      have hsq : x * y ∈ w.asIdeal ^ 2 := by simpa [pow_two] using Ideal.mul_mem_mul hx hy
      have hle := (w.intValuation_le_pow_iff_mem _ 2).2 hsq
      rw [h, exp_le_exp] at hle
      norm_num at hle
    have hvy := intValuation_eq_one_iff.2 hy
    exact Or.inl ⟨by simpa only [map_mul, hvy, mul_one] using h, hvy⟩
  · have hvx := intValuation_eq_one_iff.2 hx
    exact Or.inr ⟨hvx, by simpa only [map_mul, hvx, one_mul] using h⟩

end IsDedekindDomain.HeightOneSpectrum

namespace Ideal

open scoped Pointwise

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The image of `r * c` lies in a prime over `(r)` but not in its square when the
ramification index is one and `c` lies outside `(r)`. This formulation is convenient in
families indexed by `Ideal.primesOver`, without bundling each prime as a height-one prime. -/
theorem mem_and_notMem_sq_algebraMap_mul [IsDedekindDomain S] (P : Ideal S)
    {r c : R} [P.LiesOver (span {r})] (hr : algebraMap R S r ≠ 0)
    (hc : c ∉ span {r}) (he : P.ramificationIdx R = 1) :
    algebraMap R S (r * c) ∈ P ∧ algebraMap R S (r * c) ∉ P ^ 2 := by
  have hrP : algebraMap R S r ∈ P := (P.mem_of_liesOver (span {r}) r).1 (subset_span (by simp))
  have hP : P ≠ ⊥ := by
    intro h
    exact hr (Ideal.mem_bot.1 (h ▸ hrP))
  have hprime : P.IsPrime := by
    by_contra h
    simp [P.ramificationIdx_of_not_isPrime R h] at he
  let w : HeightOneSpectrum S := ⟨P, hprime, hP⟩
  have hw : w.asIdeal = P := rfl
  have : w.asIdeal.LiesOver (span {r}) := hw.symm ▸ inferInstanceAs (P.LiesOver (span {r}))
  have hval := w.intValuation_algebraMap_mul_eq_exp_neg_one hr hc (by simpa only [hw] using he)
  refine ⟨?_, ?_⟩
  · rw [map_mul]
    exact P.mul_mem_right _ hrP
  · rw [← hw, ← w.intValuation_le_pow_iff_mem, hval, exp_le_exp]
    norm_num

/-- If `a * σ a` belongs to every prime in the fiber but to none of their squares, then the
fiber is two copies of the primes containing `a`. The second copy is sent to the primes
containing `σ a` by `σ`. -/
noncomputable def primesOverEquivSumOfConjugateFactors (p : Ideal R)
    (σ : S ≃ₐ[R] S) (a : S)
    (hmul : ∀ P : p.primesOver S, a * σ a ∈ P.val ∧ a * σ a ∉ P.val ^ 2) :
    ({P : p.primesOver S // a ∈ P.val} ⊕ {P : p.primesOver S // a ∈ P.val}) ≃
      p.primesOver S := by
  classical
  refine (Equiv.sumCongr (Equiv.refl _) ((MulAction.toPerm σ).subtypeEquiv ?_)).trans
    (Equiv.sumCompl (fun P : p.primesOver S ↦ a ∈ P.val))
  intro P
  have hmem : σ a ∈ (σ • P).val ↔ a ∈ P.val := smul_mem_pointwise_smul_iff
  have hlocal := hmul (σ • P)
  have hprime : (σ • P).val.IsPrime := inferInstance
  exact ⟨fun hs ha ↦ hlocal.2 (by simpa [pow_two] using Ideal.mul_mem_mul ha (hmem.2 hs)),
    fun ha ↦ hmem.1 ((hprime.mul_mem_iff_mem_or_mem.1 hlocal.1).resolve_left ha)⟩

/-- The first copy of a selected prime is the prime itself. -/
@[simp]
theorem primesOverEquivSumOfConjugateFactors_apply_inl (p : Ideal R) (σ : S ≃ₐ[R] S) (a : S)
    (hmul : ∀ P : p.primesOver S, a * σ a ∈ P.val ∧ a * σ a ∉ P.val ^ 2)
    (P : {P : p.primesOver S // a ∈ P.val}) :
    primesOverEquivSumOfConjugateFactors p σ a hmul (.inl P) = P.val := by
  classical
  simp [primesOverEquivSumOfConjugateFactors]

/-- The second copy of a selected prime is its image under the automorphism. -/
@[simp]
theorem primesOverEquivSumOfConjugateFactors_apply_inr (p : Ideal R) (σ : S ≃ₐ[R] S) (a : S)
    (hmul : ∀ P : p.primesOver S, a * σ a ∈ P.val ∧ a * σ a ∉ P.val ^ 2)
    (P : {P : p.primesOver S // a ∈ P.val}) :
    primesOverEquivSumOfConjugateFactors p σ a hmul (.inr P) = σ • P.val := by
  classical
  simp [primesOverEquivSumOfConjugateFactors, MulAction.toPerm]

/-- If the product of `a` and its image under `σ` is the image of `r * c`, and every prime over
`(r)` has ramification index one, then exactly half the primes over `(r)` contain `a`.
The equality of extended cardinalities does not require a separate finiteness hypothesis. -/
theorem card_primesOver_eq_two_mul_of_mul_eq_algebraMap [IsDedekindDomain S]
    (σ : S ≃ₐ[R] S) {a : S} {r c : R} (hr : algebraMap R S r ≠ 0) (hc : c ∉ span {r})
    (he : ∀ P : (span {r}).primesOver S, P.val.ramificationIdx R = 1)
    (ha : a * σ a = algebraMap R S (r * c)) :
    ENat.card ((span {r}).primesOver S) =
      2 * ENat.card {P : (span {r}).primesOver S // a ∈ P.val} := by
  have hmul (P : (span {r}).primesOver S) : a * σ a ∈ P.val ∧ a * σ a ∉ P.val ^ 2 :=
    ha.symm ▸ P.val.mem_and_notMem_sq_algebraMap_mul hr hc (he P)
  rw [← ENat.card_congr (primesOverEquivSumOfConjugateFactors _ σ a hmul), ENat.card_sum, two_mul]

end Ideal
