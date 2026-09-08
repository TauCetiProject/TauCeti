/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Factors
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination

/-!
# Degrees of factors modulo a prime

For an integral polynomial `f` and a prime `p`, `Polynomial.factorDegrees f p` is the multiset of
degrees of the monic irreducible factors of the reduction of `f` modulo `p`. Multiplicities are
retained: a repeated irreducible factor contributes its degree repeatedly.

This is the polynomial-side factorization datum compared with cycle types in Dedekind's
factorization theorem. The API here records its total degree, computes it from any factorization
of the reduction into irreducibles, and characterizes the polynomials whose reduction is
irreducible. The underlying facts about `normalizedFactors` over a field are proved in
`TauCeti/RingTheory/Polynomial/Factors.lean`, and the separability of the reduction at a prime
not dividing the discriminant in `TauCeti/RingTheory/Polynomial/Resultant/Discriminant.lean`.

## Main declarations

* `Polynomial.factorDegrees`: the multiset of factor degrees of `f` modulo `p`.
* `Polynomial.factorDegrees_eq_map_natDegree_of_map_eq_prod`: the factor degrees are read off
  from any factorization of the reduction into irreducibles.
* `Polynomial.sum_factorDegrees_eq_natDegree_map`, `Polynomial.Monic.sum_factorDegrees`: the
  factor degrees sum to the degree after reduction, which for monic `f` is `f.natDegree`.
* `Polynomial.factorDegrees_eq_singleton_of_irreducible`,
  `Polynomial.irreducible_map_of_card_factorDegrees_eq_one`,
  `Polynomial.Monic.factorDegrees_eq_singleton_iff_irreducible`: a single factor degree is the
  same thing as an irreducible reduction.
* `Polynomial.factorDegrees_X_pow_five_sub_X_sub_one_two`: the worked example
  `factorDegrees (X ^ 5 - X - 1) 2 = {3, 2}`, with the two irreducibility facts over `ZMod 2`
  that it rests on.

## References

* D. A. Marcus, *Number Fields*, 2nd edition, Springer 2018, Chapter 4, where the factorization
  of `f mod p` is matched with the splitting of `p`.
* J. Neukirch, *Algebraic Number Theory*, Springer 1999, Chapter I, §8.
-/

public section
noncomputable section

open Polynomial UniqueFactorizationMonoid

namespace TauCeti

/-- The multiset of degrees of the monic irreducible factors of the reduction of an integral
polynomial modulo a prime. Repeated factors occur with their multiplicities. -/
noncomputable def _root_.Polynomial.factorDegrees (f : ℤ[X]) (p : ℕ) [Fact p.Prime] :
    Multiset ℕ :=
  Multiset.map Polynomial.natDegree
    (normalizedFactors (f.map (Int.castRingHom (ZMod p))))

/-- The defining equation for `Polynomial.factorDegrees`. -/
theorem _root_.Polynomial.factorDegrees_def (f : ℤ[X]) (p : ℕ) [Fact p.Prime] :
    f.factorDegrees p = Multiset.map Polynomial.natDegree
      (normalizedFactors (f.map (Int.castRingHom (ZMod p)))) :=
  (rfl)

/-- A natural number occurs in `f.factorDegrees p` exactly when it is the degree of a normalized
irreducible factor of the reduction of `f` modulo `p`. -/
theorem _root_.Polynomial.mem_factorDegrees_iff {f : ℤ[X]} {p d : ℕ} [Fact p.Prime] :
    d ∈ f.factorDegrees p ↔ ∃ q ∈ normalizedFactors (f.map (Int.castRingHom (ZMod p))),
      q.natDegree = d := by
  simp [factorDegrees_def]

/-- Every degree occurring in `f.factorDegrees p` is positive. -/
theorem _root_.Polynomial.pos_of_mem_factorDegrees {f : ℤ[X]} {p d : ℕ} [Fact p.Prime]
    (hd : d ∈ f.factorDegrees p) : 0 < d := by
  obtain ⟨q, hq, rfl⟩ := mem_factorDegrees_iff.mp hd
  exact (irreducible_of_normalized_factor q hq).natDegree_pos

/-- The number of factor degrees is the number of normalized irreducible factors, counted with
multiplicity. -/
@[simp]
theorem _root_.Polynomial.card_factorDegrees (f : ℤ[X]) (p : ℕ) [Fact p.Prime] :
    (f.factorDegrees p).card =
      (normalizedFactors (f.map (Int.castRingHom (ZMod p)))).card := by
  simp [factorDegrees_def]

/-- The zero polynomial has no factor degrees. -/
@[simp]
theorem _root_.Polynomial.factorDegrees_zero (p : ℕ) [Fact p.Prime] :
    (0 : ℤ[X]).factorDegrees p = 0 := by
  simp [factorDegrees_def]

/-- The constant polynomial one has no factor degrees. -/
@[simp]
theorem _root_.Polynomial.factorDegrees_one (p : ℕ) [Fact p.Prime] :
    (1 : ℤ[X]).factorDegrees p = 0 := by
  simp [factorDegrees_def]

/-- Factor degrees turn a product whose reductions are nonzero into multiset addition. -/
theorem _root_.Polynomial.factorDegrees_mul (f g : ℤ[X]) (p : ℕ) [Fact p.Prime]
    (hf : f.map (Int.castRingHom (ZMod p)) ≠ 0)
    (hg : g.map (Int.castRingHom (ZMod p)) ≠ 0) :
    (f * g).factorDegrees p = f.factorDegrees p + g.factorDegrees p := by
  simp [factorDegrees_def, normalizedFactors_mul hf hg]

/-- The factor degrees are read off from any factorization of the reduction into irreducibles,
without normalizing the factors first. This is how the multiset is computed in practice: a
factorization of `f mod p` need not come from a factorization over `ℤ`. -/
theorem _root_.Polynomial.factorDegrees_eq_map_natDegree_of_map_eq_prod {f : ℤ[X]} {p : ℕ}
    [Fact p.Prime] {s : Multiset (ZMod p)[X]} (hs : ∀ q ∈ s, Irreducible q)
    (hfs : f.map (Int.castRingHom (ZMod p)) = s.prod) :
    f.factorDegrees p = s.map Polynomial.natDegree := by
  rw [factorDegrees_def, hfs, normalizedFactors_prod_eq s hs, Multiset.map_map]
  exact Multiset.map_congr rfl fun q _ ↦ Polynomial.natDegree_normalize

/-- The sum of the factor degrees is the degree of the polynomial after reduction. -/
@[simp]
theorem _root_.Polynomial.sum_factorDegrees_eq_natDegree_map (f : ℤ[X]) (p : ℕ) [Fact p.Prime] :
    (f.factorDegrees p).sum = (f.map (Int.castRingHom (ZMod p))).natDegree := by
  rw [factorDegrees_def]
  exact Polynomial.sum_natDegree_normalizedFactors _

/-- For a monic polynomial, the degrees of all irreducible factors of its reduction modulo a
prime, counted with multiplicity, sum to the degree of the original polynomial. -/
theorem _root_.Polynomial.Monic.sum_factorDegrees {f : ℤ[X]} (hf : f.Monic) (p : ℕ)
    [Fact p.Prime] : (f.factorDegrees p).sum = f.natDegree := by
  rw [sum_factorDegrees_eq_natDegree_map, hf.natDegree_map]

/-- If the reduction of `f` modulo `p` is irreducible, its only factor degree is its degree. -/
theorem _root_.Polynomial.factorDegrees_eq_singleton_of_irreducible (f : ℤ[X]) (p : ℕ)
    [Fact p.Prime] (h : Irreducible (f.map (Int.castRingHom (ZMod p)))) :
    f.factorDegrees p = {(f.map (Int.castRingHom (ZMod p))).natDegree} := by
  rw [factorDegrees_def]
  exact Polynomial.map_natDegree_normalizedFactors_eq_singleton_iff.mpr h

/-- A single factor degree, whatever it is, forces the reduction to be irreducible. -/
theorem _root_.Polynomial.irreducible_map_of_card_factorDegrees_eq_one {f : ℤ[X]} {p : ℕ}
    [Fact p.Prime] (h : (f.factorDegrees p).card = 1) :
    Irreducible (f.map (Int.castRingHom (ZMod p))) :=
  Polynomial.irreducible_of_card_normalizedFactors_eq_one (by simpa using h)

/-- For a monic integral polynomial, having its own degree as sole factor degree is equivalent to
its reduction being irreducible. -/
theorem _root_.Polynomial.Monic.factorDegrees_eq_singleton_iff_irreducible {f : ℤ[X]}
    (hf : f.Monic) (p : ℕ) [Fact p.Prime] :
    f.factorDegrees p = {f.natDegree} ↔ Irreducible (f.map (Int.castRingHom (ZMod p))) := by
  refine ⟨fun h ↦ irreducible_map_of_card_factorDegrees_eq_one ?_, fun h ↦ ?_⟩
  · rw [h, Multiset.card_singleton]
  · rw [factorDegrees_eq_singleton_of_irreducible f p h, hf.natDegree_map]

/-! ### The factorization of `X ^ 5 - X - 1` modulo `2` -/

private theorem natDegree_X_pow_three_add_X_sq_add_one :
    (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]).natDegree = 3 := by compute_degree!

private theorem natDegree_X_sq_add_X_add_one :
    (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!

/-- `X ^ 2 + X + 1` is irreducible over `ZMod 2`: it is quadratic and has no root there. -/
theorem _root_.Polynomial.irreducible_X_sq_add_X_add_one_zmod_two :
    Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_X_sq_add_X_add_one]
    decide
  · intro x
    rw [Polynomial.IsRoot.def]
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    fin_cases x <;> decide

/-- `X ^ 3 + X ^ 2 + 1` is irreducible over `ZMod 2`: it is cubic and has no root there. -/
theorem _root_.Polynomial.irreducible_X_pow_three_add_X_sq_add_one_zmod_two :
    Irreducible (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_X_pow_three_add_X_sq_add_one]
    decide
  · intro x
    rw [Polynomial.IsRoot.def]
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    fin_cases x <;> decide

/-- The polynomial `X ^ 5 - X - 1` has factor degrees `3` and `2` modulo `2`: its reduction is
the product of the irreducibles `X ^ 3 + X ^ 2 + 1` and `X ^ 2 + X + 1`. -/
theorem _root_.Polynomial.factorDegrees_X_pow_five_sub_X_sub_one_two :
    (X ^ 5 - X - 1 : ℤ[X]).factorDegrees 2 = {3, 2} := by
  have hirr : ∀ q ∈ ({X ^ 3 + X ^ 2 + 1, X ^ 2 + X + 1} : Multiset (ZMod 2)[X]),
      Irreducible q := by
    intro q hq
    rcases Multiset.mem_cons.mp hq with rfl | hq
    · exact Polynomial.irreducible_X_pow_three_add_X_sq_add_one_zmod_two
    · rw [Multiset.mem_singleton.mp hq]
      exact Polynomial.irreducible_X_sq_add_X_add_one_zmod_two
  have hmap : (X ^ 5 - X - 1 : ℤ[X]).map (Int.castRingHom (ZMod 2)) =
      ({X ^ 3 + X ^ 2 + 1, X ^ 2 + X + 1} : Multiset (ZMod 2)[X]).prod := by
    rw [Multiset.insert_eq_cons, Multiset.prod_cons, Multiset.prod_singleton]
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
    linear_combination (-(X ^ 4 + X ^ 3 + X ^ 2 + X + 1) : (ZMod 2)[X]) *
      (CharTwo.two_eq_zero : (2 : (ZMod 2)[X]) = 0)
  rw [factorDegrees_eq_map_natDegree_of_map_eq_prod hirr hmap]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    natDegree_X_pow_three_add_X_sq_add_one, natDegree_X_sq_add_X_add_one]

end TauCeti
