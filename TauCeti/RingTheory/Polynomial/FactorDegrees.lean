/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Factors
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Degrees of polynomial factors modulo a prime

For an integral polynomial `f` and a prime `p`, `Polynomial.factorDegrees f p` is the multiset of
degrees of the monic irreducible factors of the reduction of `f` modulo `p`. Multiplicities are
retained: a repeated irreducible factor contributes its degree repeatedly.

This file gives the generic polynomial API for the carrier: membership, products, total degree,
and its relationship with irreducibility. Worked examples for `X ^ 5 - X - 1` are in
`TauCeti/FieldTheory/GaloisGroups/FactorDegrees.lean`.

## Main declarations

* `Polynomial.factorDegrees`: the multiset of factor degrees of `f` modulo `p`.
* `Polynomial.factorDegrees_def`: a convenient defining equation for the carrier.
* `Polynomial.mem_factorDegrees_iff`: a number occurs as a factor degree exactly when it is the
  degree of a normalized irreducible factor of the reduction.
* `Polynomial.factorDegrees_mul`: the factor degrees of a product with nonzero reductions are the
  sum of the factor degrees.
* `Polynomial.factorDegrees_eq_map_natDegree_of_map_eq_prod`: compute the factor degrees from any
  factorization of the reduction into irreducibles.
* `Polynomial.sum_factorDegrees_eq_natDegree_map`, `Polynomial.Monic.sum_factorDegrees`: the
  factor degrees sum to the degree after reduction, which for monic `f` is `f.natDegree`.
* `Polynomial.factorDegrees_eq_singleton_iff`: the factor degrees are `{n}` exactly when the
  reduction is irreducible of degree `n`.
* `Polynomial.squarefree_map_of_nodup_factorDegrees`: pairwise distinct factor degrees force the
  reduction to be squarefree.
* `Polynomial.nodup_normalizedFactors_map_of_not_dvd_discr`: at a prime dividing neither the
  leading coefficient nor the discriminant, every irreducible factor of the reduction occurs once,
  so the factor degrees are the degrees of the distinct factors.
* `Polynomial.count_one_factorDegrees_eq_card_roots`, `Polynomial.count_one_factorDegrees_le`: at
  such a prime the number of linear factors is the number of distinct roots of the reduction in
  `ZMod p`, hence at most `p`.

Away from such primes nothing of this kind holds: a factor of the reduction can repeat, and when
`p` divides the leading coefficient the degree drops. Worked instances of both are in
`TauCeti/FieldTheory/GaloisGroups/FactorDegrees.lean`.

## References

* D. A. Marcus, *Number Fields*, 2nd edition, Springer 2018, Chapter 4.
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

/-- A convenient defining equation for `Polynomial.factorDegrees`. -/
theorem _root_.Polynomial.factorDegrees_def (f : ℤ[X]) (p : ℕ) [Fact p.Prime] :
    f.factorDegrees p = Multiset.map Polynomial.natDegree
      (normalizedFactors (f.map (Int.castRingHom (ZMod p)))) :=
  (rfl)

/-- A natural number occurs in `f.factorDegrees p` exactly when it is the degree of a normalized
irreducible factor of the reduction of `f` modulo `p`. -/
@[simp]
theorem _root_.Polynomial.mem_factorDegrees_iff {f : ℤ[X]} {p d : ℕ} [Fact p.Prime] :
    d ∈ f.factorDegrees p ↔ ∃ q ∈ normalizedFactors (f.map (Int.castRingHom (ZMod p))),
      q.natDegree = d := by
  simp [factorDegrees_def]

/-- Every degree occurring in `f.factorDegrees p` is positive. -/
@[grind →]
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
without normalizing the factors first. -/
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

/-- The factor degrees of `f` modulo `p` are the singleton `{n}` exactly when the reduction is
irreducible of degree `n`. -/
@[simp]
theorem _root_.Polynomial.factorDegrees_eq_singleton_iff {f : ℤ[X]} {p n : ℕ}
    [Fact p.Prime] :
    f.factorDegrees p = {n} ↔
      Irreducible (f.map (Int.castRingHom (ZMod p))) ∧
        (f.map (Int.castRingHom (ZMod p))).natDegree = n := by
  constructor
  · intro h
    refine ⟨irreducible_map_of_card_factorDegrees_eq_one ?_, ?_⟩
    · simp [h]
    · simpa using congrArg Multiset.sum h
  · rintro ⟨hirr, hdeg⟩
    rw [factorDegrees_eq_singleton_of_irreducible f p hirr, hdeg]

/-- For a monic integral polynomial, having its own degree as sole factor degree is equivalent to
its reduction being irreducible. -/
theorem _root_.Polynomial.Monic.factorDegrees_eq_singleton_iff_irreducible {f : ℤ[X]}
    (hf : f.Monic) (p : ℕ) [Fact p.Prime] :
    f.factorDegrees p = {f.natDegree} ↔ Irreducible (f.map (Int.castRingHom (ZMod p))) := by
  rw [factorDegrees_eq_singleton_iff, hf.natDegree_map, and_iff_left rfl]

/-- A nonzero reduction whose irreducible factors have pairwise distinct degrees is squarefree:
no irreducible factor can then occur twice. -/
theorem _root_.Polynomial.squarefree_map_of_nodup_factorDegrees {f : ℤ[X]} {p : ℕ}
    [Fact p.Prime] (hf : f.map (Int.castRingHom (ZMod p)) ≠ 0)
    (h : (f.factorDegrees p).Nodup) : Squarefree (f.map (Int.castRingHom (ZMod p))) := by
  rw [factorDegrees_def] at h
  exact (squarefree_iff_nodup_normalizedFactors hf).mpr (h.of_map _)

/-! ### Multiplicity one at primes not dividing the discriminant -/

/-- **Multiplicity one.** If the prime `p` divides neither the leading coefficient nor the
discriminant of `f`, then each normalized irreducible factor of the reduction of `f` modulo `p`
occurs exactly once: the factor degrees are the degrees of the distinct irreducible factors of
the reduction. -/
theorem _root_.Polynomial.nodup_normalizedFactors_map_of_not_dvd_discr {f : ℤ[X]} {p : ℕ}
    [Fact p.Prime] (hlc : ¬ (p : ℤ) ∣ f.leadingCoeff) (hd : ¬ (p : ℤ) ∣ f.discr) :
    (normalizedFactors (f.map (Int.castRingHom (ZMod p)))).Nodup := by
  have hsep := (f.separable_map_zmod_iff_not_dvd_discr p hlc).mpr hd
  exact (squarefree_iff_nodup_normalizedFactors hsep.ne_zero).mp hsep.squarefree

/-- If the prime `p` divides neither the leading coefficient nor the discriminant of `f`, the
number of factor degrees equal to `1` is the number of distinct roots of the reduction of `f` in
`ZMod p`. -/
theorem _root_.Polynomial.count_one_factorDegrees_eq_card_roots {f : ℤ[X]} {p : ℕ}
    [Fact p.Prime] (hlc : ¬ (p : ℤ) ∣ f.leadingCoeff) (hd : ¬ (p : ℤ) ∣ f.discr) :
    (f.factorDegrees p).count 1 = (f.map (Int.castRingHom (ZMod p))).roots.toFinset.card := by
  have hsep := (f.separable_map_zmod_iff_not_dvd_discr p hlc).mpr hd
  rw [factorDegrees_def, count_one_map_natDegree_normalizedFactors hsep.ne_zero hsep.squarefree]

/-- If the prime `p` divides neither the leading coefficient nor the discriminant of `f`, then at
most `p` factor degrees equal `1`: the reduction is squarefree, so its linear factors are distinct
and each has its own root in `ZMod p`. For instance, no monic integral cubic with odd discriminant
has three linear factors modulo `2`. -/
theorem _root_.Polynomial.count_one_factorDegrees_le {f : ℤ[X]} {p : ℕ} [Fact p.Prime]
    (hlc : ¬ (p : ℤ) ∣ f.leadingCoeff) (hd : ¬ (p : ℤ) ∣ f.discr) :
    (f.factorDegrees p).count 1 ≤ p := by
  rw [count_one_factorDegrees_eq_card_roots hlc hd]
  exact (Finset.card_le_univ _).trans (ZMod.card p).le

end TauCeti
