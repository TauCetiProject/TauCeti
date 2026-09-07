/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Degrees of factors modulo a prime

For an integral polynomial `f` and a prime `p`, `TauCeti.factorDegrees f p` is the multiset of
degrees of the monic irreducible factors of the reduction of `f` modulo `p`. Multiplicities are
retained: a repeated irreducible factor contributes its degree repeatedly.

This is the polynomial-side factorization datum compared with cycle types in Dedekind's
factorization theorem. The API here records its total degree, its behaviour on irreducible
reductions, and the fact that a prime not dividing the discriminant of a monic polynomial gives a
squarefree factorization.

## Main declarations

* `TauCeti.factorDegrees`: the multiset of factor degrees of `f` modulo `p`.
* `TauCeti.factorDegrees_sum_eq_natDegree_map`: the factor degrees sum to the degree after
  reduction.
* `TauCeti.factorDegrees_sum`: for monic `f`, this sum is `f.natDegree`.
* `TauCeti.factorDegrees_eq_singleton`: an irreducible reduction has its degree as its sole
  factor degree.
* `TauCeti.separable_map_zmod_of_not_dvd_discr`: a monic polynomial has separable reduction at a
  prime not dividing its discriminant.

## References

* R. Dedekind, the factorization theorem for prime ideals, in its polynomial factorization form.
-/

public section
noncomputable section

open Polynomial UniqueFactorizationMonoid

namespace TauCeti

/-- The multiset of degrees of the monic irreducible factors of the reduction of an integral
polynomial modulo a prime. Repeated factors occur with their multiplicities. -/
@[expose] noncomputable def factorDegrees (f : ℤ[X]) (p : ℕ) [Fact p.Prime] : Multiset ℕ :=
  Multiset.map Polynomial.natDegree
    (normalizedFactors (f.map (Int.castRingHom (ZMod p))))

/-- The defining equation for `factorDegrees`. -/
theorem factorDegrees_def (f : ℤ[X]) (p : ℕ) [Fact p.Prime] :
    factorDegrees f p = Multiset.map Polynomial.natDegree
      (normalizedFactors (f.map (Int.castRingHom (ZMod p)))) :=
  rfl

/-- A natural number occurs in `factorDegrees f p` exactly when it is the degree of a normalized
irreducible factor of the reduction of `f` modulo `p`. -/
theorem mem_factorDegrees_iff {f : ℤ[X]} {p d : ℕ} [Fact p.Prime] :
    d ∈ factorDegrees f p ↔ ∃ q ∈ normalizedFactors (f.map (Int.castRingHom (ZMod p))),
      q.natDegree = d := by
  simp [factorDegrees]

/-- Every degree occurring in `factorDegrees` is positive. -/
theorem factorDegrees_pos_of_mem {f : ℤ[X]} {p d : ℕ} [Fact p.Prime]
    (hd : d ∈ factorDegrees f p) : 0 < d := by
  obtain ⟨q, hq, rfl⟩ := mem_factorDegrees_iff.mp hd
  exact (irreducible_of_normalized_factor q hq).natDegree_pos

/-- The number of factor degrees is the number of normalized irreducible factors, counted with
multiplicity. -/
@[simp]
theorem factorDegrees_card (f : ℤ[X]) (p : ℕ) [Fact p.Prime] :
    (factorDegrees f p).card =
      (normalizedFactors (f.map (Int.castRingHom (ZMod p)))).card := by
  simp [factorDegrees]

/-- The zero polynomial has no factor degrees. -/
@[simp]
theorem factorDegrees_zero (p : ℕ) [Fact p.Prime] : factorDegrees 0 p = 0 := by
  simp [factorDegrees]

/-- The constant polynomial one has no factor degrees. -/
@[simp]
theorem factorDegrees_one (p : ℕ) [Fact p.Prime] : factorDegrees 1 p = 0 := by
  simp [factorDegrees]

/-- Factor degrees turn a product whose reductions are nonzero into multiset addition. -/
theorem factorDegrees_mul (f g : ℤ[X]) (p : ℕ) [Fact p.Prime]
    (hf : f.map (Int.castRingHom (ZMod p)) ≠ 0)
    (hg : g.map (Int.castRingHom (ZMod p)) ≠ 0) :
    factorDegrees (f * g) p = factorDegrees f p + factorDegrees g p := by
  simp [factorDegrees, normalizedFactors_mul hf hg]

/-- The sum of the factor degrees is the degree of the polynomial after reduction. -/
@[simp]
theorem factorDegrees_sum_eq_natDegree_map (f : ℤ[X]) (p : ℕ) [Fact p.Prime] :
    (factorDegrees f p).sum = (f.map (Int.castRingHom (ZMod p))).natDegree := by
  let g : (ZMod p)[X] := f.map (Int.castRingHom (ZMod p))
  change (Multiset.map Polynomial.natDegree (normalizedFactors g)).sum = g.natDegree
  by_cases hg : g = 0
  · simp [hg]
  · have hprod := prod_normalizedFactors hg
    rw [← Polynomial.natDegree_multiset_prod]
    · exact Polynomial.natDegree_eq_of_degree_eq
        (Polynomial.degree_eq_degree_of_associated hprod)
    · exact zero_notMem_normalizedFactors g

/-- For a monic polynomial, the degrees of all irreducible factors of its reduction modulo a
prime, counted with multiplicity, sum to the degree of the original polynomial. -/
theorem factorDegrees_sum (f : ℤ[X]) (hf : f.Monic) (p : ℕ) [Fact p.Prime] :
    (factorDegrees f p).sum = f.natDegree := by
  rw [factorDegrees_sum_eq_natDegree_map, hf.natDegree_map]

/-- If the reduction of `f` modulo `p` is irreducible, its only factor degree is its degree. -/
@[simp]
theorem factorDegrees_eq_singleton (f : ℤ[X]) (p : ℕ) [Fact p.Prime]
    (h : Irreducible (f.map (Int.castRingHom (ZMod p)))) :
    factorDegrees f p = {(f.map (Int.castRingHom (ZMod p))).natDegree} := by
  rw [factorDegrees, normalizedFactors_irreducible h, Multiset.map_singleton,
    Polynomial.natDegree_normalize]

/-- For a monic integral polynomial, having one factor degree is equivalent to its reduction
being irreducible. -/
theorem factorDegrees_eq_singleton_iff_irreducible (f : ℤ[X]) (hf : f.Monic) (p : ℕ)
    [Fact p.Prime] :
    factorDegrees f p = {f.natDegree} ↔
      Irreducible (f.map (Int.castRingHom (ZMod p))) := by
  let g : (ZMod p)[X] := f.map (Int.castRingHom (ZMod p))
  have hg : g.Monic := hf.map _
  constructor
  · intro h
    obtain ⟨q, hq, -⟩ := Multiset.map_eq_singleton.mp h
    have hqmem : q ∈ normalizedFactors g := by
      change q ∈ normalizedFactors (f.map (Int.castRingHom (ZMod p)))
      rw [hq]
      simp
    have hprod := prod_normalizedFactors hg.ne_zero
    rw [hq, Multiset.prod_singleton] at hprod
    exact hprod.irreducible (irreducible_of_normalized_factor q hqmem)
  · intro h
    rw [factorDegrees_eq_singleton f p h, hf.natDegree_map]

/-- A prime not dividing the discriminant of a monic integral polynomial gives a separable
reduction modulo that prime. -/
theorem separable_map_zmod_of_not_dvd_discr (f : ℤ[X]) (hf : f.Monic) (p : ℕ)
    [Fact p.Prime] (hp : ¬ (p : ℤ) ∣ f.discr) :
    (f.map (Int.castRingHom (ZMod p))).Separable := by
  apply (hf.map (Int.castRingHom (ZMod p))).discr_ne_zero_iff.mp
  rw [hf.discr_map, Int.coe_castRingHom, ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact hp

/-- At a prime not dividing the discriminant of a monic integral polynomial, its normalized
irreducible factors modulo that prime have no repetitions. -/
theorem normalizedFactors_map_zmod_nodup_of_not_dvd_discr (f : ℤ[X]) (hf : f.Monic)
    (p : ℕ) [Fact p.Prime] (hp : ¬ (p : ℤ) ∣ f.discr) :
    (normalizedFactors (f.map (Int.castRingHom (ZMod p)))).Nodup := by
  rw [← squarefree_iff_nodup_normalizedFactors (hf.map _).ne_zero]
  exact (separable_map_zmod_of_not_dvd_discr f hf p hp).squarefree

private theorem irreducible_X_sq_add_X_add_one_zmod_two :
    Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
    rw [hdeg]
    decide
  · intro x
    rw [Polynomial.IsRoot.def]
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    fin_cases x <;> decide

private theorem irreducible_X_cube_add_X_sq_add_one_zmod_two :
    Irreducible (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]).natDegree = 3 := by compute_degree!
    rw [hdeg]
    decide
  · intro x
    rw [Polynomial.IsRoot.def]
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    fin_cases x <;> decide

/-- The polynomial `X⁵ - X - 1` has factor degrees `3` and `2` modulo `2`. -/
example : factorDegrees (X ^ 5 - X - 1) 2 = {3, 2} := by
  have hmap :
      (X ^ 5 - X - 1 : ℤ[X]).map (Int.castRingHom (ZMod 2)) =
        (X ^ 3 + X ^ 2 + 1) * (X ^ 2 + X + 1) := by
    have hneg (a : (ZMod 2)[X]) : -a = a := by
      ext n
      simp only [Polynomial.coeff_neg, ZMod.neg_eq_self_mod_two]
    have htwo : (2 : (ZMod 2)[X]) = 0 := by
      ext n
      cases n
      · rw [Polynomial.coeff_ofNat_zero, Polynomial.coeff_zero]
        exact show (2 : ZMod 2) = 0 by decide
      · simp
    norm_num
    ring_nf
    rw [htwo]
    simp only [mul_zero, add_zero]
    simp only [sub_eq_add_neg, hneg]
  have hdeg_three : (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]).natDegree = 3 := by
    compute_degree!
  have hdeg_two : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by
    compute_degree!
  rw [factorDegrees, hmap,
    normalizedFactors_mul irreducible_X_cube_add_X_sq_add_one_zmod_two.ne_zero
      irreducible_X_sq_add_X_add_one_zmod_two.ne_zero,
    normalizedFactors_irreducible irreducible_X_cube_add_X_sq_add_one_zmod_two,
    normalizedFactors_irreducible irreducible_X_sq_add_X_add_one_zmod_two]
  simp [Polynomial.natDegree_normalize, hdeg_three, hdeg_two]

end TauCeti
