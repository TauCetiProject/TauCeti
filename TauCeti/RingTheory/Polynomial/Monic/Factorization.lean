/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import Mathlib.Algebra.Polynomial.BigOperators

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

/-- The integral case: a monic integral polynomial with nonzero discriminant is the product of
distinct monic irreducible integral polynomials. -/
example {f : ℤ[X]} (hf : f.Monic) (hd : f.discr ≠ 0) :
    ∃ s : Finset ℤ[X], (∀ g ∈ s, g.Monic ∧ Irreducible g) ∧ ∏ g ∈ s, g = f :=
  hf.exists_finset_prod_eq_of_discr_ne_zero hd

end Polynomial.Monic
