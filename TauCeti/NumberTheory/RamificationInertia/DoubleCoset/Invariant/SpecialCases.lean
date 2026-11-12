/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.RamificationInertia.DoubleCoset.Invariant.Basic

/-!
# The double coset law for special subgroups

Let a finite group `G` act on a commutative ring `B` with invariant ring `A`, let `Q` be a prime
of `B` above a prime `p` of `A`, with decomposition group `D = stabilizer G Q`, and let `C` be an
intermediate ring of invariants for a subgroup `H` of `G`. The double coset law
(`Ideal.doubleCosetQuotientEquivPrimesOverOfIsInvariant`) indexes the primes of `C` above `p` by
`H \ G / D`, the class of `σ` naming `σ Q ∩ C`. This file reads the law off at the subgroups
where the double cosets are explicit.

The setting covers integral closures over an arbitrary Dedekind base, through
`IsGaloisGroup.of_isIntegralClosure` and `IsGaloisGroup.of_isIntegralClosure_fixedField`, and,
through instances, the rings of integers `𝓞 K`, `𝓞 M` and `𝓞 (M ^ H)` of a Galois extension of
number fields. No hypothesis on the residue fields is made: they need be neither finite nor
perfect, and the residue extensions need not be separable.

* **One prime.** `p` has a single prime above it in `C`, namely `Q ∩ C`, exactly when
  `H D = G`, since then `H \ G / D` is the identity class alone. This covers `H = G`, where `C`
  is identified with the image of `A` in `B`, and the case `D = G` of a prime `p` with a single
  prime above it in `B`, for instance an inert prime: then `p` has a single prime above it in
  every intermediate ring.
* **`H = 1`.** Then `1 \ G / D` is `G / D`, and the law recovers the Galois count `g = [G : D]`
  of the primes of `B` above `p` (`Ideal.card_primesOver_eq_index_stabilizer`).
* **`H = D`.** Then `C` is the decomposition ring of `Q`. The double cosets `D \ G / D` are not
  a singleton in general, and only the identity double coset is special: it names `Q ∩ C`,
  which has ramification index `1` and residue degree `1` over `p`, and `Q` is the only prime of
  `B` above it. The two facts extend in opposite directions: the local degree
  `e · f = [D : H ∩ D]` is `1` as soon as `D ≤ H`
  (`Ideal.ramificationIdx_under_eq_one_of_stabilizer_le` and
  `Ideal.inertiaDeg_under_eq_one_of_stabilizer_le`), and the primes of `B` with the same
  contraction to `C` as `Q` form the `H`-orbit of `Q`, which is `{Q}` as soon as `H ≤ D`
  (`Ideal.primesOver_under_eq_singleton_of_le_stabilizer`). Both hold at `H = D`. These are
  the invariant-ring counterparts of the Hilbert-theory statements for an abstract
  decomposition field, Tau Ceti's `TauCeti.IsDecompositionField.ramificationIdx_under_eq_one` and
  `TauCeti.IsDecompositionField.inertiaDeg_under_eq_one`, and Mathlib's
  `IsDecompositionField.primesOver_eq_singleton`.

## Main results

* `Ideal.doubleCosetQuotientEquivPrimesOverOfIsInvariant_mk_one`: the identity double coset
  names `Q ∩ C`.
* `Ideal.primesOver_eq_singleton_of_mul_eq_univ`: if `H D = G`, then `Q ∩ C` is the only prime
  of `C` above `p`.
* `Ideal.card_primesOver_eq_one_iff`: a single prime above `p` in `C` exactly when `H D = G`.
* `Ideal.primesOver_eq_singleton_of_eq_top` and
  `Ideal.primesOver_eq_singleton_of_stabilizer_eq_top`: the cases `H = G` and `D = G`.
* `Ideal.ramificationIdx_doubleCosetQuotientEquivPrimesOverOfIsInvariant_stabilizer_mk_one_eq_one`,
  `Ideal.inertiaDeg_doubleCosetQuotientEquivPrimesOverOfIsInvariant_stabilizer_mk_one_eq_one`
  and
  `Ideal.primesOver_doubleCosetQuotientEquivPrimesOverOfIsInvariant_stabilizer_mk_one_eq_singleton`:
  for `H = D`, the prime named by the identity double coset has `e = f = 1` over `p`, and `Q` is the
  only prime above it.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9.
* G. J. Janusz, *Algebraic Number Fields*, Chapter I.
* X. Roblot, the decomposition-field section of
  `Mathlib/NumberTheory/RamificationInertia/HilbertTheory.lean`, for the abstract
  decomposition-field statements recovered here at `H = D`.
-/

public section

open MulAction

open scoped Pointwise

namespace Ideal

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Group G] [MulSemiringAction G B]

section Equivalence

variable [Finite G] [Algebra.IsInvariant A B G] [SMulCommClass G A B]
  (p : Ideal A) (Q : Ideal B) [Q.IsPrime] [Q.LiesOver p]

section Subgroup

variable (H : Subgroup G) (C : Type*) [CommRing C] [Algebra A C] [Algebra C B]
  [IsScalarTower A C B] [FaithfulSMul C B]
  [Algebra.IsInvariant C B H] [SMulCommClass H C B]

/-- The double coset law sends the identity double coset of `H \ G / D` to the contraction
`Q ∩ C`. -/
theorem doubleCosetQuotientEquivPrimesOverOfIsInvariant_mk_one :
    (Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H C (DoubleCoset.mk H _ 1) : Ideal C) =
      Q.under C := by
  rw [doubleCosetQuotientEquivPrimesOverOfIsInvariant_mk, one_smul]

variable {H} in
/-- **A single prime above `p` in an intermediate ring.** For a subgroup `H` of `G` and the
decomposition group `D` of a prime `Q` of `B` above `p`, if `H D = G` then `Q ∩ C` is the only
prime of the `H`-invariant ring `C` above `p`. -/
theorem primesOver_eq_singleton_of_mul_eq_univ
    (h : (H : Set G) * (stabilizer G Q : Set G) = Set.univ) :
    p.primesOver C = {Q.under C} := by
  have := (TauCeti.subsingleton_doubleCosetQuotient_iff _ _).2 h
  have := (Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H C).symm.subsingleton
  rw [← doubleCosetQuotientEquivPrimesOverOfIsInvariant_mk_one p Q H C]
  exact Set.eq_singleton_iff_unique_mem.2 ⟨Subtype.prop _, fun 𝔮 h𝔮 ↦
    Subtype.ext_iff.1 (Subsingleton.elim (⟨𝔮, h𝔮⟩ : p.primesOver C) _)⟩

/-- **A single prime above `p` in an intermediate ring, counted.** For a subgroup `H` of `G`
and the decomposition group `D` of a prime `Q` of `B` above `p`, there is exactly one prime of
the `H`-invariant ring `C` above `p` if and only if `H D = G`. -/
theorem card_primesOver_eq_one_iff :
    Nat.card (p.primesOver C) = 1 ↔
      (H : Set G) * (stabilizer G Q : Set G) = Set.univ := by
  rw [← Nat.card_congr (Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H C),
    Nat.card_eq_one_iff_unique, TauCeti.subsingleton_doubleCosetQuotient_iff]
  exact and_iff_left ⟨DoubleCoset.mk H _ 1⟩

/-- **The double coset law for `H = G`.** If `C` is the invariant ring of the whole group, so
that it is identified with the image of `A` in `B`, then `Q ∩ C` is the only prime of `C` above
`p`. -/
theorem primesOver_eq_singleton_of_eq_top (hH : H = ⊤) :
    p.primesOver C = {Q.under C} :=
  primesOver_eq_singleton_of_mul_eq_univ p Q C <| Set.eq_univ_of_forall fun σ ↦
    Set.mem_mul.2 ⟨σ, hH ▸ Subgroup.mem_top σ, 1, one_mem _, mul_one σ⟩

include H in
/-- **A prime with a single prime above it in `B` has a single prime above it in every
intermediate ring.** If the decomposition group of `Q` is the whole group, as for an inert
prime, then for every subgroup `H` the only prime of the `H`-invariant ring `C` above `p` is
`Q ∩ C`. -/
theorem primesOver_eq_singleton_of_stabilizer_eq_top (hD : stabilizer G Q = ⊤) :
    p.primesOver C = {Q.under C} :=
  primesOver_eq_singleton_of_mul_eq_univ p Q C <| Set.eq_univ_of_forall fun σ ↦
    Set.mem_mul.2 ⟨1, one_mem H, σ, hD ▸ Subgroup.mem_top σ, one_mul σ⟩

end Subgroup

/-- **`Q` is the only prime above the prime named by the identity double coset of
`D \ G / D`.** For `D` the decomposition group of `Q` and `C` its invariant ring, the only prime
of `B` above `Q ∩ C` is `Q` itself. -/
theorem primesOver_doubleCosetQuotientEquivPrimesOverOfIsInvariant_stabilizer_mk_one_eq_singleton
    (C : Type*) [CommRing C] [Algebra A C] [Algebra C B]
    [IsScalarTower A C B] [FaithfulSMul C B]
    [Algebra.IsInvariant C B (stabilizer G Q)] [SMulCommClass (stabilizer G Q) C B] :
    (Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p (stabilizer G Q) C
      (DoubleCoset.mk _ _ 1) : Ideal C).primesOver B = {Q} := by
  rw [doubleCosetQuotientEquivPrimesOverOfIsInvariant_mk_one]
  exact primesOver_under_eq_singleton_of_le_stabilizer Q (H := stabilizer G Q) C le_rfl

end Equivalence

section LocalDegree

variable [Finite G] [IsDomain A] [IsDomain B] [Module.Finite A B] [Module.Flat A B]
  [IsGaloisGroup G A B] (Q : Ideal B) [Q.IsMaximal]
  (p : Ideal A) [Q.LiesOver p] (C : Type*) [CommRing C] [IsDomain C]
  [Algebra A C] [Algebra C B] [IsScalarTower A C B] [FaithfulSMul C B] [Module.Flat C B]
  [IsGaloisGroup (stabilizer G Q) C B]

/-- **The identity double coset of `D \ G / D` names an unramified prime.** For `D` the
decomposition group of `Q` and `C` its invariant ring, the prime named by the identity double
coset, namely `Q ∩ C`, has ramification index `1` over `A`. -/
theorem ramificationIdx_doubleCosetQuotientEquivPrimesOverOfIsInvariant_stabilizer_mk_one_eq_one :
    (Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p (stabilizer G Q) C
      (DoubleCoset.mk _ _ 1) : Ideal C).ramificationIdx A = 1 := by
  rw [doubleCosetQuotientEquivPrimesOverOfIsInvariant_mk_one]
  exact Q.ramificationIdx_under_eq_one_of_stabilizer_le (H := stabilizer G Q) C le_rfl

/-- **The identity double coset of `D \ G / D` names a prime of residue degree one.** For `D`
the decomposition group of `Q` and `C` its invariant ring, the prime named by the identity
double coset, namely `Q ∩ C`, has residue degree `1` over `A`. -/
theorem inertiaDeg_doubleCosetQuotientEquivPrimesOverOfIsInvariant_stabilizer_mk_one_eq_one :
    (Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p (stabilizer G Q) C
      (DoubleCoset.mk _ _ 1) : Ideal C).inertiaDeg A = 1 := by
  rw [doubleCosetQuotientEquivPrimesOverOfIsInvariant_mk_one]
  exact Q.inertiaDeg_under_eq_one_of_stabilizer_le (H := stabilizer G Q) C le_rfl

end LocalDegree

end Ideal
