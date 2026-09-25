/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.GroupTheory.GroupAction.Jordan
public import TauCeti.NumberTheory.NumberField.Frobenius.CycleType
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Tactic.ComputeDegree
import TauCeti.FieldTheory.GaloisGroups.FactorDegrees
import TauCeti.FieldTheory.GaloisGroups.Orbits
import TauCeti.GroupTheory.Perm.MultipleTransitivity
import TauCeti.GroupTheory.Perm.Recognition

/-!
# Galois groups over `ℚ` from factorizations modulo primes

Let `f` be a monic integral polynomial and `p` a prime not dividing `disc f`. Dedekind's theorem,
`TauCeti.NumberField.exists_gal_fullCycleType_eq_factorizationType`, says that the degrees of the
irreducible factors of `f mod p` are the cycle lengths, fixed points included, of some element of
the Galois group of `f` over `ℚ` acting on the complex roots of `f`. This file reads that theorem
as membership of the factorization type in the set of full cycle types of the Galois image, and
draws the consequences for the Galois group.

A factorization type exhibits an element of the Galois image, so it only ever bounds the image
from below. The shapes read off here are:

* an irreducible reduction exhibits a cycle through all the roots;
* a reduction with exactly one quadratic factor, all its other factors being of odd degree,
  exhibits a transposition, as an odd power of the element it produces;
* a reduction whose only factor of degree at least two is a cubic exhibits a `3`-cycle.

Combined with the recognition theorems for permutation groups, these give the classical
criteria for a large Galois group. In prime degree, irreducibility over `ℚ` and a transposition
force the full symmetric group. In any degree, irreducibility over `ℚ`, a reduction of type
`(1, n - 1)` and a reduction with a single quadratic factor and odd other factors force the full
symmetric group: the first two make the Galois image doubly transitive, hence primitive, and a
primitive group containing a transposition is everything. This is the criterion behind van der
Waerden's construction of integral polynomials of every degree with Galois group `Sₙ`, where the
three reductions are prescribed modulo `2`, `3` and `5`.

## Main results

* `TauCeti.exists_mem_range_galActionHom_fullCycleType_eq_factorDegrees`: the factor degrees of
  `f` modulo a prime not dividing `disc f` are the full cycle type of an element of the Galois
  image.
* `TauCeti.exists_isCycle_mem_range_galActionHom_of_irreducible_map`: an irreducible reduction
  exhibits a cycle moving every root.
* `TauCeti.exists_isSwap_mem_range_galActionHom`: a reduction with one quadratic factor and odd
  other factors exhibits a transposition.
* `TauCeti.exists_isThreeCycle_mem_range_galActionHom`: a reduction whose only nonlinear factor
  is cubic exhibits a `3`-cycle.
* `TauCeti.alternatingGroup_le_range_galActionHom`: a primitive Galois image with a reduction
  whose only nonlinear factor is a cubic contains the alternating group.
* `TauCeti.surjective_galActionHom_of_prime_natDegree`: in prime degree, irreducibility and a
  reduction exhibiting a transposition give the full symmetric group.
* `TauCeti.surjective_galActionHom_of_factorDegrees`: irreducibility, a reduction of type
  `(1, n - 1)` and a reduction exhibiting a transposition give the full symmetric group.
* `TauCeti.surjective_galActionHom_X_pow_five_sub_X_sub_one`: the Galois group of
  `X ^ 5 - X - 1` over `ℚ` is the full symmetric group on its five roots.

## References

* B. L. van der Waerden, *Algebra* I, Springer, §61.
* H. Cohen, *A Course in Computational Algebraic Number Theory*, Springer 1993, §6.3.
-/

public section

open Polynomial Equiv Equiv.Perm MulAction

namespace TauCeti

attribute [local instance] Gal.splits_ℚ_ℂ

variable {f : ℤ[X]}

/-- A prime candidate is good for an integral polynomial when it does not divide the polynomial
discriminant. -/
def IsGoodPrime (f : ℤ[X]) (p : ℕ) : Prop :=
  ¬ (p : ℤ) ∣ f.discr

/-- The defining characterization of a good prime. -/
@[simp]
theorem isGoodPrime_iff (f : ℤ[X]) (p : ℕ) : IsGoodPrime f p ↔ ¬ (p : ℤ) ∣ f.discr :=
  Iff.rfl

open scoped Classical in
/-- **Factor degrees are a full cycle type of the Galois image.** Let `f` be a monic integral
polynomial and `p` a prime not dividing `disc f`. Some permutation of the complex roots of `f`
induced by the Galois group of `f` over `ℚ` has as its cycle lengths, one part for each fixed
root, the degrees of the irreducible factors of `f` modulo `p`.

The polynomial `f` need not be irreducible. -/
theorem exists_mem_range_galActionHom_fullCycleType_eq_factorDegrees (hf : f.Monic) (p : ℕ)
    [Fact p.Prime] (hp : ¬ (p : ℤ) ∣ f.discr) :
    ∃ σ ∈ (Gal.galActionHom (f.map (Int.castRingHom ℚ)) ℂ).range,
      σ.fullCycleType = f.factorDegrees p := by
  obtain ⟨σ, hσ⟩ := NumberField.exists_gal_fullCycleType_eq_factorizationType f hf p hp
  exact ⟨_, ⟨σ, rfl⟩, hσ⟩

open scoped Classical in
/-- **An irreducible reduction exhibits a full cycle.** If a monic integral polynomial `f` of
degree at least two is irreducible modulo a prime `p`, then the Galois image of `f` over `ℚ`
contains a cycle moving every complex root of `f`.

No hypothesis on the discriminant is needed: an irreducible polynomial over the perfect field
`ZMod p` is separable, so `p` does not divide `disc f`. -/
theorem exists_isCycle_mem_range_galActionHom_of_irreducible_map (hf : f.Monic)
    (hdeg : 2 ≤ f.natDegree) (p : ℕ) [Fact p.Prime]
    (hirr : Irreducible (f.map (Int.castRingHom (ZMod p)))) :
    ∃ σ ∈ (Gal.galActionHom (f.map (Int.castRingHom ℚ)) ℂ).range,
      σ.IsCycle ∧ σ.support = Finset.univ := by
  have hp : ¬ (p : ℤ) ∣ f.discr :=
    (hf.separable_map_zmod_iff_not_dvd_discr p).mp (PerfectField.separable_of_irreducible hirr)
  obtain ⟨σ, hσG, hσ⟩ := exists_mem_range_galActionHom_fullCycleType_eq_factorDegrees hf p hp
  rw [(hf.factorDegrees_eq_singleton_iff_irreducible p).mpr hirr] at hσ
  have hcyc : σ.cycleType = {f.natDegree} := by
    rw [← filter_fullCycleType_eq_cycleType, hσ]
    simp [hdeg]
  obtain ⟨hcyc, hsupp⟩ := cycleType_eq_singleton_iff.mp hcyc
  refine ⟨σ, hσG, hcyc, Finset.eq_univ_of_card _ ?_⟩
  rw [hsupp, ← Nat.card_eq_fintype_card,
    natCard_rootSet_complex_eq_natDegree fun h => hp (h ▸ dvd_zero _)]

open scoped Classical in
/-- **A single quadratic factor exhibits a transposition.** Let `f` be a monic integral
polynomial and `p` a prime not dividing `disc f`. If exactly one irreducible factor of `f`
modulo `p` is quadratic and all the others have odd degree, then the Galois image of `f` over
`ℚ` contains a transposition of the complex roots of `f`. -/
theorem exists_isSwap_mem_range_galActionHom (hf : f.Monic) (p : ℕ) [Fact p.Prime]
    (hp : ¬ (p : ℤ) ∣ f.discr) (htwo : (f.factorDegrees p).count 2 = 1)
    (hodd : ∀ k ∈ f.factorDegrees p, k ≠ 2 → Odd k) :
    ∃ τ ∈ (Gal.galActionHom (f.map (Int.castRingHom ℚ)) ℂ).range, τ.IsSwap := by
  obtain ⟨σ, hσG, hσ⟩ := exists_mem_range_galActionHom_fullCycleType_eq_factorDegrees hf p hp
  rw [← hσ] at htwo hodd
  obtain ⟨k, -, hk⟩ := σ.exists_odd_isSwap_pow
    (by rwa [← count_fullCycleType_of_ne_one σ (by decide)])
    fun n hn hn2 => hodd n (Multiset.mem_of_mem_filter
      (filter_fullCycleType_eq_cycleType (σ := σ) ▸ hn)) hn2
  exact ⟨σ ^ k, pow_mem hσG k, hk⟩

open scoped Classical in
/-- **A single cubic factor exhibits a `3`-cycle.** Let `f` be a monic integral polynomial and
let `p` be a prime not dividing `disc f`. If the only irreducible factor of `f` modulo `p` of
degree at least two is a cubic, then the Galois image contains a `3`-cycle. -/
theorem exists_isThreeCycle_mem_range_galActionHom (hf : f.Monic)
    (p : ℕ) [Fact p.Prime] (hp : ¬ (p : ℤ) ∣ f.discr)
    (hthree : (f.factorDegrees p).filter (2 ≤ ·) = {3}) :
    ∃ σ ∈ (Gal.galActionHom (f.map (Int.castRingHom ℚ)) ℂ).range, σ.IsThreeCycle := by
  obtain ⟨σ, hσG, hσ⟩ := exists_mem_range_galActionHom_fullCycleType_eq_factorDegrees hf p hp
  refine ⟨σ, hσG, ?_⟩
  rw [IsThreeCycle, ← filter_fullCycleType_eq_cycleType, hσ, hthree]

open scoped Classical in
/-- **A cubic factor forces the alternating group.** Let `f` be a monic integral polynomial whose
Galois image over `ℚ` acts primitively on the complex roots of `f`, and let `p` be a prime not
dividing `disc f`. If the only irreducible factor of `f` modulo `p` of degree at least two is a
cubic, then the Galois image contains the alternating group of the roots. -/
theorem alternatingGroup_le_range_galActionHom (hf : f.Monic)
    (hprim : IsPreprimitive (Gal.galActionHom (f.map (Int.castRingHom ℚ)) ℂ).range
      ((f.map (Int.castRingHom ℚ)).rootSet ℂ))
    (p : ℕ) [Fact p.Prime] (hp : ¬ (p : ℤ) ∣ f.discr)
    (hthree : (f.factorDegrees p).filter (2 ≤ ·) = {3}) :
    alternatingGroup ((f.map (Int.castRingHom ℚ)).rootSet ℂ) ≤
      (Gal.galActionHom (f.map (Int.castRingHom ℚ)) ℂ).range := by
  obtain ⟨σ, hσG, hσ⟩ := exists_isThreeCycle_mem_range_galActionHom hf p hp hthree
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim hσ hσG

open scoped Classical in
/-- **The full symmetric group in prime degree.** Let `f` be a monic integral polynomial of
prime degree, irreducible over `ℚ`, and let `p` be a prime not dividing `disc f`. If exactly one
irreducible factor of `f` modulo `p` is quadratic and all the others have odd degree, then the
Galois group of `f` over `ℚ` induces every permutation of the complex roots of `f`. -/
theorem surjective_galActionHom_of_prime_natDegree (hf : f.Monic)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hprime : f.natDegree.Prime)
    (p : ℕ) [Fact p.Prime] (hp : ¬ (p : ℤ) ∣ f.discr) (htwo : (f.factorDegrees p).count 2 = 1)
    (hodd : ∀ k ∈ f.factorDegrees p, k ≠ 2 → Odd k) :
    Function.Surjective (Gal.galActionHom (f.map (Int.castRingHom ℚ)) ℂ) := by
  obtain ⟨τ, hτG, hτ⟩ := exists_isSwap_mem_range_galActionHom hf p hp htwo hodd
  rw [← MonoidHom.range_eq_top]
  refine subgroup_eq_top_of_isPretransitive_of_prime_card_of_isSwap_mem
    (isPretransitive_range_galActionHom ℂ hirr) ?_ τ hτ hτG
  rwa [natCard_rootSet_complex_eq_natDegree fun h => hp (h ▸ dvd_zero _)]

open scoped Classical in
/-- **The full symmetric group from two reductions.** Let `f` be a monic integral polynomial of
degree `n`, irreducible over `ℚ`, and let `q` and `r` be primes. Suppose that `f` modulo `q` is the
product of an irreducible factor of degree `n - 1` and a linear factor, and that `r` does not
divide `disc f`, with exactly one irreducible factor of `f` modulo `r` quadratic and all the
others of odd degree. Then the Galois group of `f` over `ℚ` induces every permutation of the
complex roots of `f`.

Irreducibility over `ℚ` may itself come from a third prime, modulo which `f` is irreducible. -/
theorem surjective_galActionHom_of_factorDegrees (hf : f.Monic)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (q : ℕ) [Fact q.Prime] (hqdeg : f.factorDegrees q = {1, f.natDegree - 1})
    (r : ℕ) [Fact r.Prime] (hr : ¬ (r : ℤ) ∣ f.discr) (htwo : (f.factorDegrees r).count 2 = 1)
    (hodd : ∀ k ∈ f.factorDegrees r, k ≠ 2 → Odd k) :
    Function.Surjective (Gal.galActionHom (f.map (Int.castRingHom ℚ)) ℂ) := by
  have hcard := natCard_rootSet_complex_eq_natDegree fun h => hr (h ▸ dvd_zero _)
  obtain ⟨τ, hτG, hτ⟩ := exists_isSwap_mem_range_galActionHom hf r hr htwo hodd
  -- A transposition moves two roots, so the degree is at least two; degree two is prime.
  have h2 : 2 ≤ f.natDegree := by
    rw [← hcard, Nat.card_eq_fintype_card, ← card_support_eq_two.mpr hτ]
    exact Finset.card_le_univ _
  rcases h2.eq_or_lt with h2 | h3
  · exact surjective_galActionHom_of_prime_natDegree hf hirr (h2 ▸ Nat.prime_two) r hr htwo hodd
  -- In degree at least three, the type `(1, n - 1)` exhibits a cycle fixing exactly one root,
  -- which makes the transitive Galois image primitive.
  have hq : ¬ (q : ℤ) ∣ f.discr := (hf.separable_map_zmod_iff_not_dvd_discr q).mp <| by
    rw [PerfectField.separable_iff_squarefree]
    apply squarefree_map_of_nodup_factorDegrees (hf.map _).ne_zero
    rw [hqdeg]
    have hne : 1 ≠ f.natDegree - 1 := by omega
    simpa using hne
  obtain ⟨σ, hσG, hσ⟩ := exists_mem_range_galActionHom_fullCycleType_eq_factorDegrees hf q hq
  have hcyc : σ.cycleType = {f.natDegree - 1} := by
    rw [← filter_fullCycleType_eq_cycleType, hσ, hqdeg]
    have hn : 2 ≤ f.natDegree - 1 := by omega
    simp [hn, Multiset.filter_singleton]
  obtain ⟨hcyc, hsupp⟩ := cycleType_eq_singleton_iff.mp hcyc
  have := isPretransitive_range_galActionHom ℂ hirr
  have hprim := isPreprimitive_of_isCycle_mem_of_card_support_add_one_eq_card _ hcyc hσG
    (by rw [hsupp, ← Nat.card_eq_fintype_card, hcard]; omega)
  rw [← MonoidHom.range_eq_top]
  exact subgroup_eq_top_of_isPreprimitive_of_isSwap_mem hprim τ hτ hτG

/-! ### The quintic `X ^ 5 - X - 1` -/

/-- The polynomial `X ^ 5 - X - 1` is monic. -/
theorem monic_X_pow_five_sub_X_sub_one : (X ^ 5 - X - 1 : ℤ[X]).Monic := by
  rw [sub_sub]
  exact monic_X_pow_sub (by compute_degree!)

/-- Modulo `2`, the irreducible factors of `X ^ 5 - X - 1` have the distinct degrees `3` and `2`,
so the reduction is squarefree, hence separable, and `2` does not divide the discriminant. -/
theorem not_two_dvd_discr_X_pow_five_sub_X_sub_one :
    ¬ ((2 : ℕ) : ℤ) ∣ (X ^ 5 - X - 1 : ℤ[X]).discr := by
  have hf := monic_X_pow_five_sub_X_sub_one
  rw [← hf.separable_map_zmod_iff_not_dvd_discr, PerfectField.separable_iff_squarefree]
  exact squarefree_map_of_nodup_factorDegrees (hf.map _).ne_zero
    (by rw [factorDegrees_X_pow_five_sub_X_sub_one_two]; decide)

/-- **The Galois group of `X ^ 5 - X - 1` over `ℚ` is `S₅`.** -/
theorem surjective_galActionHom_X_pow_five_sub_X_sub_one :
    Function.Surjective
      (Gal.galActionHom ((X ^ 5 - X - 1 : ℤ[X]).map (Int.castRingHom ℚ)) ℂ) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hf := monic_X_pow_five_sub_X_sub_one
  have hirr : Irreducible ((X ^ 5 - X - 1 : ℤ[X]).map (Int.castRingHom ℚ)) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hf.isPrimitive).mp
      (Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 5)) _ hf
        (factorDegrees_eq_singleton_iff.mp factorDegrees_X_pow_five_sub_X_sub_one_five).1)
  have hdeg : (X ^ 5 - X - 1 : ℤ[X]).natDegree = 5 := by
    rw [sub_sub]
    compute_degree!
  refine surjective_galActionHom_of_prime_natDegree hf hirr (by rw [hdeg]; exact Nat.prime_five) 2
    not_two_dvd_discr_X_pow_five_sub_X_sub_one ?_ ?_ <;>
    rw [factorDegrees_X_pow_five_sub_X_sub_one_two]
  · decide
  · simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
    rintro k (rfl | rfl) hk
    exacts [by decide, absurd rfl hk]

end TauCeti
