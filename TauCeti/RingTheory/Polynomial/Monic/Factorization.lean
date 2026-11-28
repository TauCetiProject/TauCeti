/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff.Basic
public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import Mathlib.Algebra.Polynomial.BigOperators
import TauCeti.RingTheory.UniqueFactorizationDomain.SubsetProduct

/-!
# Squarefree monic polynomials are products of distinct monic irreducibles

Over a domain `R` with a normalization monoid, such as `ℤ`, whose polynomial ring has unique
factorization, a squarefree monic polynomial is the product of a finite set of monic irreducible
polynomials. The set is that of its normalized irreducible factors: a normalized divisor of a
monic polynomial is monic, because its leading coefficient is a normalized unit.

A nonzero discriminant gives squarefreeness (`Polynomial.Monic.squarefree_of_discr_ne_zero`).
For monic `f : ℤ[X]` with `disc f ≠ 0` this is the first step in reducing statements about a
reducible `f` to its irreducible factors. The factors are irreducible in `ℤ[X]`, and so, being
monic, also over `ℚ` by Gauss's lemma.

## Main results

* `Polynomial.Monic.exists_pow_mul_not_dvd`: extracting the highest power of a monic
  polynomial of positive degree dividing a monic polynomial over any semiring.
* `Polynomial.Monic.exists_factor_ne_multiplicity`: two distinct monic polynomials over an
  integrally closed domain differ in the multiplicity of some monic factor that is irreducible over
  the fraction field.
* `Polynomial.Monic.monic_of_mem_normalizedFactors`: a normalized irreducible factor of a monic
  polynomial is monic.
* `Polynomial.Monic.prod_toFinset_normalizedFactors_of_squarefree`: a squarefree monic
  polynomial is the product of its distinct normalized irreducible factors.
* `Polynomial.Monic.exists_finset_prod_eq_of_squarefree`: a squarefree monic polynomial is the
  product of a finite set of monic irreducible polynomials.
* `Polynomial.Monic.exists_finset_prod_eq_of_discr_ne_zero`: the same conclusion for a monic
  polynomial with nonzero discriminant.
* `Polynomial.natDegree_eq_sum_mul_count_normalizedFactors`: the degree of a polynomial is
  the sum of the degrees of its normalized factors, counted with multiplicity.
* `TauCeti.Polynomial.sum_finsuppAntidiag_eq_sum_monicsOfDegree`: over a finite field, the monic
  polynomials of degree `n` whose normalized factors lie in a finite set `S` of monic irreducibles
  are the products `∏_{P ∈ S} P ^ (l P / deg P)` for the exponent vectors `l` on `S` with
  `∑ l = n` and `deg P ∣ l P`, so a sum over these polynomials is a sum over such `l`.
-/

public section

open UniqueFactorizationMonoid

namespace Polynomial.Monic

/-- Over any semiring, a monic polynomial `f` factors as `g ^ e * s` with `s` monic and not
divisible by `g`, for any monic `g` of positive degree. -/
theorem exists_pow_mul_not_dvd {R : Type*} [Semiring R] {g f : R[X]}
    (hg : g.Monic) (hg_pos : 0 < g.natDegree) (hf : f.Monic) :
    ∃ e : ℕ, ∃ s : R[X], s.Monic ∧ ¬ g ∣ s ∧ f = g ^ e * s := by
  have : Nontrivial R :=
    Nontrivial.of_polynomial_ne (p := g) (q := 0) (by rintro rfl; simp at hg_pos)
  obtain ⟨s, hs_eq, hs_ndvd⟩ :=
    (finiteMultiplicity_of_degree_pos_of_monic (natDegree_pos_iff_degree_pos.mp hg_pos)
      hg hf.ne_zero).exists_eq_pow_mul_and_not_dvd
  exact ⟨multiplicity g f, s, (hg.pow _).of_mul_monic_left (hs_eq ▸ hf), hs_ndvd, hs_eq⟩

private theorem exists_factor_ne_multiplicity_aux {O K : Type*} [CommRing O]
    [IsIntegrallyClosed O] [Field K] [Algebra O K] [IsFractionRing O K]
    {X₁ X₂ : O[X]} (hX₁ : X₁.Monic) (hX₂ : X₂.Monic)
    {g A : K[X]} (hgA : X₁.map (algebraMap O K) = g * A)
    (hgcd : ∀ d : K[X],
      d ∣ X₁.map (algebraMap O K) → d ∣ X₂.map (algebraMap O K) → d ∣ g)
    (hA : ¬ IsUnit A) :
    ∃ R₀ : O[X], R₀.Monic ∧ Irreducible (R₀.map (algebraMap O K)) ∧
      ∃ e₁ e₂ : ℕ, ∃ S₁ S₂ : O[X], S₁.Monic ∧ S₂.Monic ∧
        ¬ (R₀.map (algebraMap O K) ∣ S₁.map (algebraMap O K)) ∧
        ¬ (R₀.map (algebraMap O K) ∣ S₂.map (algebraMap O K)) ∧
        X₁ = R₀ ^ e₁ * S₁ ∧ X₂ = R₀ ^ e₂ * S₂ ∧ e₁ ≠ e₂ := by
  classical
  let ι := algebraMap O K
  obtain ⟨R, hR_monic, hR_irr, hR_dvd_A⟩ := A.exists_monic_irreducible_factor hA
  have hR_dvd_X₁ : R ∣ X₁.map ι := hgA ▸ hR_dvd_A.mul_left g
  obtain ⟨R₀, hR₀_map⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hX₁ hR_dvd_X₁
  rw [hR_monic.leadingCoeff, C_1, mul_one] at hR₀_map
  have hR₀_monic : R₀.Monic :=
    monic_of_injective (IsFractionRing.injective O K) (hR₀_map ▸ hR_monic)
  have hR₀_irr : Irreducible (R₀.map ι) := hR₀_map ▸ hR_irr
  have hR₀_pos : 0 < R₀.natDegree := by
    rw [← natDegree_map_eq_of_injective (IsFractionRing.injective O K)]
    exact hR₀_irr.natDegree_pos
  obtain ⟨e₁, S₁, hS₁_m, hS₁_ndvd', hX₁_eq⟩ := hR₀_monic.exists_pow_mul_not_dvd hR₀_pos hX₁
  obtain ⟨e₂, S₂, hS₂_m, hS₂_ndvd', hX₂_eq⟩ := hR₀_monic.exists_pow_mul_not_dvd hR₀_pos hX₂
  have hS₁_ndvd : ¬ (R₀.map ι ∣ S₁.map ι) :=
    fun h ↦ hS₁_ndvd' (hS₁_m.dvd_of_fraction_map_dvd_fraction_map hR₀_monic h)
  have hS₂_ndvd : ¬ (R₀.map ι ∣ S₂.map ι) :=
    fun h ↦ hS₂_ndvd' (hS₂_m.dvd_of_fraction_map_dvd_fraction_map hR₀_monic h)
  refine ⟨R₀, hR₀_monic, hR₀_irr, e₁, e₂, S₁, S₂,
    hS₁_m, hS₂_m, hS₁_ndvd, hS₂_ndvd, hX₁_eq, hX₂_eq, ?_⟩
  rintro rfl
  have hpow_dvd_g : R ^ e₁ ∣ g := by
    have hd1 : R ^ e₁ ∣ X₁.map ι := by
      rw [hX₁_eq, Polynomial.map_mul, Polynomial.map_pow, hR₀_map]
      exact dvd_mul_right _ _
    have hd2 : R ^ e₁ ∣ X₂.map ι := by
      rw [hX₂_eq, Polynomial.map_mul, Polynomial.map_pow, hR₀_map]
      exact dvd_mul_right _ _
    exact hgcd (R ^ e₁) hd1 hd2
  obtain ⟨g', rfl⟩ := hpow_dvd_g
  have heq : R ^ e₁ * S₁.map ι = R ^ e₁ * (g' * A) := by
    calc
      R ^ e₁ * S₁.map ι = (R₀ ^ e₁ * S₁).map ι := by
        rw [Polynomial.map_mul, Polynomial.map_pow, hR₀_map]
      _ = X₁.map ι := by rw [← hX₁_eq]
      _ = R ^ e₁ * (g' * A) := by rw [hgA, mul_assoc]
  have hS₁_eq := mul_left_cancel₀ (pow_ne_zero e₁ hR_monic.ne_zero) heq
  apply hS₁_ndvd
  rw [hR₀_map, hS₁_eq]
  exact hR_dvd_A.mul_left g'

/-- Two distinct monic polynomials `P, Q : O[X]` over an integrally closed domain admit a monic
factor `R₀ : O[X]` irreducible over `K = Frac(O)` appearing with distinct multiplicities in `P`
and `Q`, with monic cofactors `S₁, S₂` not divisible by `R₀` over `K`. -/
theorem exists_factor_ne_multiplicity {O K : Type*} [CommRing O]
    [IsIntegrallyClosed O] [Field K] [Algebra O K] [IsFractionRing O K]
    {P Q : O[X]} (hP : P.Monic) (hQ : Q.Monic) (hne : P ≠ Q) :
    ∃ R₀ : O[X], R₀.Monic ∧ Irreducible (R₀.map (algebraMap O K)) ∧
      ∃ e₁ e₂ : ℕ, ∃ S₁ S₂ : O[X], S₁.Monic ∧ S₂.Monic ∧
        ¬ (R₀.map (algebraMap O K) ∣ S₁.map (algebraMap O K)) ∧
        ¬ (R₀.map (algebraMap O K) ∣ S₂.map (algebraMap O K)) ∧
        P = R₀ ^ e₁ * S₁ ∧ Q = R₀ ^ e₂ * S₂ ∧ e₁ ≠ e₂ := by
  classical
  let ι := algebraMap O K
  have hne_K : P.map ι ≠ Q.map ι :=
    fun h ↦ hne (map_injective ι (IsFractionRing.injective O K) h)
  let g := EuclideanDomain.gcd (P.map ι) (Q.map ι)
  obtain ⟨A, hA⟩ := EuclideanDomain.gcd_dvd_left (P.map ι) (Q.map ι)
  obtain ⟨B, hB⟩ := EuclideanDomain.gcd_dvd_right (P.map ι) (Q.map ι)
  have hnot : ¬ IsUnit A ∨ ¬ IsUnit B := by
    by_contra! h
    have h1 : Associated (P.map ι) g := hA ▸ (associated_mul_unit_right g A h.1).symm
    have h2 : Associated (Q.map ι) g := hB ▸ (associated_mul_unit_right g B h.2).symm
    exact hne_K (eq_of_monic_of_associated (hP.map ι) (hQ.map ι) (h1.trans h2.symm))
  rcases hnot with hAn | hBn
  · exact exists_factor_ne_multiplicity_aux hP hQ hA
      (fun _ h1 h2 ↦ EuclideanDomain.dvd_gcd h1 h2) hAn
  · obtain ⟨R₀, hR₀_m, hR₀_i, e₂, e₁, S₂, S₁,
        hS₂_m, hS₁_m, hS₂_nd, hS₁_nd, hQ_eq, hP_eq, hne'⟩ :=
      exists_factor_ne_multiplicity_aux hQ hP hB
        (fun _ h1 h2 ↦ EuclideanDomain.dvd_gcd h2 h1) hBn
    exact ⟨R₀, hR₀_m, hR₀_i, e₁, e₂, S₁, S₂,
      hS₁_m, hS₂_m, hS₁_nd, hS₂_nd, hP_eq, hQ_eq, hne'.symm⟩

variable {R : Type*} [CommRing R] [IsDomain R] [NormalizationMonoid R]
  [UniqueFactorizationMonoid R[X]] {f : R[X]}

/-- A normalized irreducible factor of a monic polynomial is monic: its leading coefficient is
a normalized unit. -/
theorem monic_of_mem_normalizedFactors (hf : f.Monic) {g : R[X]}
    (hg : g ∈ normalizedFactors f) : g.Monic := by
  have hu : IsUnit g.leadingCoeff := by
    obtain ⟨h, hh⟩ := dvd_of_mem_normalizedFactors hg
    exact IsUnit.of_mul_eq_one h.leadingCoeff
      (by rw [← leadingCoeff_mul, ← hh, hf.leadingCoeff])
  rw [Monic, ← normalize_normalized_factor g hg, leadingCoeff_normalize,
    normalize_eq_one.mpr hu]

/-- A squarefree monic polynomial is the product of its distinct normalized irreducible
factors. -/
theorem prod_toFinset_normalizedFactors_of_squarefree [DecidableEq R[X]] (hf : f.Monic)
    (hsq : Squarefree f) : ∏ g ∈ (normalizedFactors f).toFinset, g = f := by
  have hf0 : f ≠ 0 := hf.ne_zero
  -- Squarefreeness makes the factor multiset duplicate-free, so it is its own `toFinset`.
  rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    ((squarefree_iff_nodup_normalizedFactors hf0).mp hsq).dedup, Multiset.map_id']
  have hprod := monic_multiset_prod_of_monic (normalizedFactors f) id
    fun _ hg ↦ monic_of_mem_normalizedFactors hf hg
  rw [Multiset.map_id] at hprod
  exact eq_of_monic_of_associated hprod hf (prod_normalizedFactors hf0)

/-- A squarefree monic polynomial is the product of a finite set of monic irreducible
polynomials, namely its normalized irreducible factors. -/
theorem exists_finset_prod_eq_of_squarefree (hf : f.Monic) (hsq : Squarefree f) :
    ∃ s : Finset R[X], (∀ g ∈ s, g.Monic ∧ Irreducible g) ∧ ∏ g ∈ s, g = f := by
  classical
  refine ⟨(normalizedFactors f).toFinset, fun g hg ↦ ?_,
    hf.prod_toFinset_normalizedFactors_of_squarefree hsq⟩
  rw [Multiset.mem_toFinset] at hg
  exact ⟨monic_of_mem_normalizedFactors hf hg, irreducible_of_normalized_factor g hg⟩

/-- A monic polynomial with nonzero discriminant is the product of a finite set of monic
irreducible polynomials. Over `ℤ` this is the factorization of a monic `f` with `disc f ≠ 0`
into distinct monic irreducible factors. -/
theorem exists_finset_prod_eq_of_discr_ne_zero (hf : f.Monic) (hd : f.discr ≠ 0) :
    ∃ s : Finset R[X], (∀ g ∈ s, g.Monic ∧ Irreducible g) ∧ ∏ g ∈ s, g = f :=
  hf.exists_finset_prod_eq_of_squarefree (hf.squarefree_of_discr_ne_zero hd)

/-- A polynomial `f` whose normalized factors lie in a finite set `S` has degree
`∑ g ∈ S, deg g · m g`, where `m g` is the number of times that `g` occurs as a normalized
factor. -/
theorem _root_.Polynomial.natDegree_eq_sum_mul_count_normalizedFactors [DecidableEq R[X]]
    (f : R[X]) {S : Finset R[X]} (hS : (normalizedFactors f).toFinset ⊆ S) :
    f.natDegree = ∑ g ∈ S, g.natDegree * (normalizedFactors f).count g := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  conv_lhs => rw [← natDegree_eq_of_degree_eq
    (degree_eq_degree_of_associated (prod_normalizedFactors hf0)),
    natDegree_multiset_prod _ (zero_notMem_normalizedFactors f), Finset.sum_multiset_map_count]
  refine (Finset.sum_subset hS fun g _ hg ↦ ?_).trans (Finset.sum_congr rfl fun g _ ↦ ?_)
  · rw [Multiset.count_eq_zero.2 fun h ↦ hg (Multiset.mem_toFinset.2 h), zero_smul]
  · rw [smul_eq_mul, mul_comm]

/-- The integral case: a monic integral polynomial with nonzero discriminant is the product of
distinct monic irreducible integral polynomials. -/
example {f : ℤ[X]} (hf : f.Monic) (hd : f.discr ≠ 0) :
    ∃ s : Finset ℤ[X], (∀ g ∈ s, g.Monic ∧ Irreducible g) ∧ ∏ g ∈ s, g = f :=
  hf.exists_finset_prod_eq_of_discr_ne_zero hd

end Polynomial.Monic

namespace TauCeti.Polynomial

open _root_.Polynomial Finset

variable {F : Type*} [Field F] [Finite F] [DecidableEq F]

/-- **Factorization over a finite set of monic irreducibles.** Let `S` be a finite set of monic
irreducible polynomials over a finite field. Then `l ↦ ∏_{P ∈ S} P ^ (l P / deg P)` is a bijection
from the `l : F[X] →₀ ℕ` on `S` with `∑_{P ∈ S} l P = n` and `deg P ∣ l P` to the monic
polynomials of degree `n` whose normalized factors lie in `S`. So a sum of `w` over these
polynomials is a sum over such `l`. -/
theorem sum_finsuppAntidiag_eq_sum_monicsOfDegree {M : Type*} [AddCommMonoid M]
    {S : Finset F[X]} (hS : ∀ P ∈ S, P.Monic ∧ Irreducible P) (n : ℕ) (w : F[X] → M) :
    ∑ l ∈ (S.finsuppAntidiag n).filter (fun l ↦ ∀ P ∈ S, P.natDegree ∣ l P),
        w (∏ P ∈ S, P ^ (l P / P.natDegree)) =
      ∑ g ∈ (monicsOfDegree F n).filter (fun g ↦ (normalizedFactors g).toFinset ⊆ S), w g := by
  have hdeg : ∀ P ∈ S, 0 < P.natDegree := fun P hP ↦ (hS P hP).2.natDegree_pos
  have hnS : ∀ P ∈ S, normalize P = P ∧ Irreducible P := fun P hP ↦
    ⟨(hS P hP).1.normalize_eq_self, (hS P hP).2⟩
  -- The inverse sends `g` to the vector of `deg P` times the multiplicity of `P` in `g`.
  refine sum_nbij' (fun l ↦ ∏ P ∈ S, P ^ (l P / P.natDegree))
    (fun g ↦ Finsupp.onFinset S
      (fun P ↦ if P ∈ S then P.natDegree * (normalizedFactors g).count P else 0)
      (fun P hP ↦ by by_contra h; simp [h] at hP)) ?_ ?_ ?_ ?_ fun _ _ ↦ rfl
  · intro l hl
    simp only [mem_filter, mem_finsuppAntidiag] at hl
    simp only [mem_filter, mem_monicsOfDegree]
    refine ⟨⟨monic_prod_of_monic _ _ fun P hP ↦ (hS P hP).1.pow _, ?_⟩, ?_⟩
    · rw [natDegree_prod_of_monic _ _ fun P hP ↦ (hS P hP).1.pow _, ← hl.1.1]
      refine sum_congr rfl fun P hP ↦ ?_
      rw [(hS P hP).1.natDegree_pow, Nat.div_mul_cancel (hl.2 P hP)]
    · rw [TauCeti.normalizedFactors_finset_prod_pow hnS]
      intro Q hQ
      obtain ⟨R, hR, hQR⟩ := Multiset.mem_sum.1 (Multiset.mem_toFinset.1 hQ)
      rw [Multiset.mem_nsmul] at hQR
      rwa [Multiset.mem_singleton.1 hQR.2]
  · intro g hg
    simp only [mem_filter, mem_monicsOfDegree] at hg
    obtain ⟨⟨-, hgn⟩, hgS⟩ := hg
    simp only [mem_filter, mem_finsuppAntidiag, Finsupp.onFinset_apply]
    refine ⟨⟨?_, Finsupp.support_onFinset_subset⟩, fun P hP ↦ by simp [hP]⟩
    rw [← hgn, g.natDegree_eq_sum_mul_count_normalizedFactors hgS]
    exact sum_congr rfl fun P hP ↦ by simp [hP]
  · intro l hl
    simp only [mem_filter, mem_finsuppAntidiag] at hl
    ext P
    simp only [Finsupp.onFinset_apply]
    split_ifs with hP
    · rw [TauCeti.count_normalizedFactors_finset_prod_pow hnS _ hP,
        Nat.mul_div_cancel' (hl.2 P hP)]
    · exact (Finsupp.notMem_support_iff.1 fun h ↦ hP (hl.1.2 h)).symm
  · intro g hg
    simp only [mem_filter, mem_monicsOfDegree] at hg
    obtain ⟨⟨hgm, -⟩, hgS⟩ := hg
    simp only [Finsupp.onFinset_apply]
    refine (prod_congr rfl fun P hP ↦ ?_).trans
      (TauCeti.finset_prod_pow_count_normalizedFactors hgm.ne_zero hgm.normalize_eq_self hgS)
    simp only [hP, ↓reduceIte, Nat.mul_div_cancel_left _ (hdeg P hP)]

end TauCeti.Polynomial
