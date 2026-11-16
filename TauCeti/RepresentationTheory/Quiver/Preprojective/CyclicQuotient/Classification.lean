/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.SimpleGraph
public import TauCeti.RepresentationTheory.Quiver.Preprojective.CyclicQuotient.Basic
import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.CyclicQuotient
import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.BadCharacteristic
import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.CyclicQuotient
import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.BadCharacteristic
import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CharacteristicFive
import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CharacteristicThree
import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CyclicQuotient
import TauCeti.RepresentationTheory.Quiver.Preprojective.CyclicQuotient.Cycle
import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.Tree

/-!
# Classification of vanishing for positive-degree preprojective cyclic quotients

Let `G` be a finite connected simple graph, `o` an orientation of `G`, and `k` a field. Both the
signless preprojective algebra `Π⁺(G)` and the additive preprojective algebra `Π_k(Q_o)` are graded
by path length, and their cyclic quotients `Π / [Π, Π]` compute zeroth Hochschild homology
`HH₀(Π)`. For a quiver whose underlying graph is a tree, Liu and Wang identify the degree-`(q + 2)`
piece `(Π / [Π, Π])_{q + 2}` with the second Hochschild cohomology `HH^{2, q}(Π₂(Q))` of the
two-dimensional Ginzburg DG algebra, which controls the `A∞` deformations of the zigzag algebra
of `G`.

This file assembles the complete vanishing classification for the positive-degree cyclic quotient:

* **Dynkin graphs in good characteristic**: for `Aₙ` over every commutative ring, `Dₙ` when `2` is
  a unit, `E₆` and `E₇` when `2` and `3` are units, and `E₈` when `2`, `3`, and `5` are units,
  every graded piece of positive degree lies in the commutator submodule.
* **Dynkin graphs in bad characteristic**: over every nontrivial commutative ring of a bad
  characteristic (`2` for `Dₙ` with `n ≥ 4`, `2` or `3` for `E₆` and `E₇`, and `2`, `3`, or `5`
  for `E₈`), a nonzero homogeneous cyclic class survives in degree `4`, `6`, or `10`.
* **Connected non-Dynkin graphs**: over every nontrivial commutative ring, a connected non-Dynkin
  graph either contains a cycle of length `m ≥ 3` (producing a degree-`m` class via
  `TauCeti.RepresentationTheory.Quiver.Preprojective.CyclicQuotient.Cycle`) or is a non-Dynkin tree
  (producing a class of degree `4`, `6`, `8`, or `12` via
  `TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.Tree`).

Consequently, over a field `k`, the positive-degree cyclic quotient vanishes in all degrees `d ≥ 3`
(equivalently, in all degrees `d > 0`) if and only if `G` is isomorphic to a valid simply-laced
Dynkin diagram `t` and `ringChar k` is not a bad prime for `t`.

## Main definitions

* `TauCeti.IsBadPrime`: the bad primes for each finite Dynkin type (`2` for `Dₙ`; `2, 3` for `E₆`
  and `E₇`; `2, 3, 5` for `E₈`; none for `Aₙ` or the non-simply-laced types).

## Main results

* `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso` and
  `TauCeti.preprojectiveGrade_le_commutatorSubmodule_of_iso`: positive-degree vanishing on graphs
  isomorphic to a simply-laced Dynkin diagram outside bad characteristic.
* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime` and
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime`: nonzero cyclic
  classes in bad characteristic over any nontrivial commutative ring.
* `SimpleGraph.Connected.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule` and
  `SimpleGraph.Connected.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule`: nonzero cyclic
  classes for every connected non-Dynkin graph over any nontrivial commutative ring.
* `TauCeti.signlessPreprojective_cyclicQuotient_vanishes_iff`,
  `TauCeti.signlessPreprojective_cyclicQuotient_vanishes_pos_iff`,
  `TauCeti.preprojective_cyclicQuotient_vanishes_iff`, and
  `TauCeti.preprojective_cyclicQuotient_vanishes_pos_iff`: the full vanishing classification over a
  field.
* `TauCeti.preprojective_cyclicQuotient_vanishes_iff_of_charZero`: in characteristic zero, the
  positive-degree cyclic quotient vanishes if and only if the graph is a finite simply-laced Dynkin
  diagram.

## References

* P. Etingof and C.-H. Eu, *Hochschild and cyclic homology of preprojective algebras of ADE
  quivers*, Mosc. Math. J. 7 (2007), https://arxiv.org/abs/math/0609006.
* T. Schedler, *Hochschild homology of preprojective algebras over the integers*, Theorem 13.1.1,
  https://arxiv.org/abs/0704.3278.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  Theorem 1.1 and Corollary 3.4, https://arxiv.org/abs/2301.06757.
* J.-L. Loday, *Cyclic Homology*, Section 1.1.
-/

public section

namespace TauCeti

open DoubledQuiver

universe u w

/-! ### Bad primes for finite Dynkin types -/

/-- The primes that are bad for the preprojective cyclic quotient of a finite Dynkin type (in the
sense of Schedler, Theorem 13.1.1, and Liu--Wang, Theorem 1.1): `2` for `Dₙ`, `2` and `3` for `E₆`
and `E₇`, and `2`, `3`, and `5` for `E₈`. Type `A` and the non-simply-laced types have no bad
primes, and `0` (characteristic zero) is never bad. -/
def IsBadPrime : DynkinType → ℕ → Prop
  | .D _, p => p = 2
  | .E6, p => p = 2 ∨ p = 3
  | .E7, p => p = 2 ∨ p = 3
  | .E8, p => p = 2 ∨ p = 3 ∨ p = 5
  | .A _, _ => False
  | .B _, _ => False
  | .C _, _ => False
  | .F4, _ => False
  | .G2, _ => False

@[simp] theorem not_isBadPrime_A (n p : ℕ) : ¬ IsBadPrime (.A n) p := not_false
@[simp] theorem not_isBadPrime_B (n p : ℕ) : ¬ IsBadPrime (.B n) p := not_false
@[simp] theorem not_isBadPrime_C (n p : ℕ) : ¬ IsBadPrime (.C n) p := not_false
@[simp] theorem isBadPrime_D_iff (n p : ℕ) : IsBadPrime (.D n) p ↔ p = 2 := Iff.rfl
@[simp] theorem isBadPrime_E6_iff (p : ℕ) : IsBadPrime .E6 p ↔ p = 2 ∨ p = 3 := Iff.rfl
@[simp] theorem isBadPrime_E7_iff (p : ℕ) : IsBadPrime .E7 p ↔ p = 2 ∨ p = 3 := Iff.rfl
@[simp] theorem isBadPrime_E8_iff (p : ℕ) : IsBadPrime .E8 p ↔ p = 2 ∨ p = 3 ∨ p = 5 := Iff.rfl
@[simp] theorem not_isBadPrime_F4 (p : ℕ) : ¬ IsBadPrime .F4 p := not_false
@[simp] theorem not_isBadPrime_G2 (p : ℕ) : ¬ IsBadPrime .G2 p := not_false

instance (t : DynkinType) (p : ℕ) : Decidable (IsBadPrime t p) :=
  match t with
  | .D _ => decidable_of_iff (p = 2) (isBadPrime_D_iff _ p).symm
  | .E6 => decidable_of_iff (p = 2 ∨ p = 3) (isBadPrime_E6_iff p).symm
  | .E7 => decidable_of_iff (p = 2 ∨ p = 3) (isBadPrime_E7_iff p).symm
  | .E8 => decidable_of_iff (p = 2 ∨ p = 3 ∨ p = 5) (isBadPrime_E8_iff p).symm
  | .A _ => isFalse (not_isBadPrime_A _ p)
  | .B _ => isFalse (not_isBadPrime_B _ p)
  | .C _ => isFalse (not_isBadPrime_C _ p)
  | .F4 => isFalse (not_isBadPrime_F4 p)
  | .G2 => isFalse (not_isBadPrime_G2 p)

/-- Characteristic zero is never a bad prime. -/
@[simp]
theorem not_isBadPrime_zero (t : DynkinType) : ¬ IsBadPrime t 0 := by
  cases t <;> simp

/-- Every bad prime is at most `5`; in particular no number strictly greater than `5` is bad. -/
theorem not_isBadPrime_of_five_lt (t : DynkinType) {p : ℕ} (hp : 5 < p) : ¬ IsBadPrime t p := by
  cases t <;> simp <;> omega

/-- Every bad prime is a prime number. -/
theorem IsBadPrime.prime {t : DynkinType} {p : ℕ} (h : IsBadPrime t p) : p.Prime := by
  cases t <;> simp only [isBadPrime_D_iff, isBadPrime_E6_iff, isBadPrime_E7_iff, isBadPrime_E8_iff,
    not_isBadPrime_A, not_isBadPrime_B, not_isBadPrime_C, not_isBadPrime_F4,
    not_isBadPrime_G2] at h
  · rw [h]; exact Nat.prime_two
  · rcases h with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · rcases h with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · rcases h with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five

/-- Only simply-laced Dynkin types have bad primes. -/
theorem IsBadPrime.isSimplyLaced {t : DynkinType} {p : ℕ} (h : IsBadPrime t p) :
    t.IsSimplyLaced := by
  cases t <;> simp_all

/-- The characteristic of a characteristic-zero semiring is never a bad prime. -/
theorem not_isBadPrime_ringChar_of_charZero (k : Type*) [Semiring k] [CharZero k]
    (t : DynkinType) : ¬ IsBadPrime t (ringChar k) := by
  rw [ringChar.eq_zero]
  exact not_isBadPrime_zero t

/-! ### Vanishing on Dynkin graphs in good characteristic -/

section GoodCharacteristic

private theorem isUnit_natCast_of_ringChar_ne {k : Type w} [Field k] {p : ℕ} (hp : p.Prime)
    (h : ringChar k ≠ p) : IsUnit (p : k) :=
  isUnit_iff_ne_zero.2 fun h0 => h (CharP.ringChar_of_prime_eq_zero hp h0)

variable (k : Type w) [Field k]

/-- **Positive-degree vanishing on a simply-laced Dynkin diagram in good characteristic** for the
signless preprojective algebra. -/
theorem signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso {V : Type u} [Finite V]
    {G : SimpleGraph V} [∀ v, Fintype (G.neighborSet v)] {t : DynkinType} (ht : t.IsSimplyLaced)
    (e : G ≃g diagramGraph t.cartanMatrix) (hp : ¬ IsBadPrime t (ringChar k)) {d : ℕ}
    (hd : 0 < d) :
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  let _ : ∀ v, Fintype ((diagramGraph t.cartanMatrix).neighborSet v) :=
    SimpleGraph.neighborSetFintypeOfFinite (diagramGraph t.cartanMatrix)
  rw [signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso k e]
  cases t with
  | A n =>
    exact signlessPreprojectiveGrade_A_le_commutatorSubmodule k hd
  | D n =>
    have h2 : IsUnit (2 : k) :=
      isUnit_natCast_of_ringChar_ne Nat.prime_two (by simpa using hp)
    exact signlessPreprojectiveGrade_D_le_commutatorSubmodule k h2 hd
  | E6 =>
    have h2 : IsUnit (2 : k) :=
      isUnit_natCast_of_ringChar_ne Nat.prime_two (fun h => hp (Or.inl h))
    have h3 : IsUnit (3 : k) :=
      isUnit_natCast_of_ringChar_ne Nat.prime_three (fun h => hp (Or.inr h))
    exact signlessPreprojectiveGrade_E6_le_commutatorSubmodule k h2 h3 hd
  | E7 =>
    have h2 : IsUnit (2 : k) :=
      isUnit_natCast_of_ringChar_ne Nat.prime_two (fun h => hp (Or.inl h))
    have h3 : IsUnit (3 : k) :=
      isUnit_natCast_of_ringChar_ne Nat.prime_three (fun h => hp (Or.inr h))
    exact signlessPreprojectiveGrade_E7_le_commutatorSubmodule k h2 h3 hd
  | E8 =>
    have h2 : IsUnit (2 : k) :=
      isUnit_natCast_of_ringChar_ne Nat.prime_two (fun h => hp (Or.inl h))
    have h3 : IsUnit (3 : k) :=
      isUnit_natCast_of_ringChar_ne Nat.prime_three (fun h => hp (Or.inr (Or.inl h)))
    have h5 : IsUnit (5 : k) :=
      isUnit_natCast_of_ringChar_ne Nat.prime_five (fun h => hp (Or.inr (Or.inr h)))
    have key : ∀ H : SimpleGraph (Fin 8), zigzagE8Graph = H →
        let _ : ∀ v, Fintype (H.neighborSet v) := SimpleGraph.neighborSetFintypeOfFinite H
        signlessPreprojectiveGrade k (DoubledQuiver H) d ≤
          commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) := by
      rintro H rfl
      exact signlessPreprojectiveGrade_E8_le_commutatorSubmodule k h2 h3 h5 hd
    exact key _ zigzagE8Graph_eq_diagramGraph
  | B n | C n | F4 | G2 => simp at ht

/-- **Positive-degree vanishing on a simply-laced Dynkin diagram in good characteristic** for the
additive preprojective algebra of every orientation. -/
theorem preprojectiveGrade_le_commutatorSubmodule_of_iso {V : Type u} [Finite V]
    {G : SimpleGraph V} {t : DynkinType} (ht : t.IsSimplyLaced)
    (e : G ≃g diagramGraph t.cartanMatrix) (hp : ¬ IsBadPrime t (ringChar k))
    (o : Orientation G) {d : ℕ} (hd : 0 < d) :
    preprojectiveGrade k (OrientedQuiver G o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  let _ : ∀ v, Fintype (G.neighborSet v) := SimpleGraph.neighborSetFintypeOfFinite G
  have hbip : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  rw [hbip.preprojectiveGrade_le_commutatorSubmodule_iff k o]
  exact signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k ht e hp hd

end GoodCharacteristic

/-! ### Nonvanishing in bad characteristic and on non-Dynkin graphs -/

section Nonvanishing

private theorem natCast_eq_zero_of_ringChar_eq (k : Type w) [CommRing k] {p : ℕ}
    (h : ringChar k = p) : (p : k) = 0 := by
  rw [← h]
  exact CharP.cast_eq_zero k (ringChar k)

private theorem exists_signless_of_graph_eq (k : Type w) [CommRing k] {V : Type u} [Finite V]
    {G H : SimpleGraph V} {instG : ∀ v, Fintype (G.neighborSet v)}
    {instH : ∀ v, Fintype (H.neighborSet v)} (hGH : G = H) {d : ℕ}
    (h : let _ := instG
      ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
        x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) :
    let _ := instH
    ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver H) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) := by
  subst hGH
  obtain rfl : instG = instH := funext fun _ => Subsingleton.elim _ _
  exact h

variable (k : Type w) [CommRing k] [Nontrivial k]

/-- **Nonzero cyclic classes in bad characteristic for the signless preprojective algebra.** Over
any nontrivial commutative ring whose characteristic is a bad prime for a valid Dynkin type `t`,
every graph isomorphic to the diagram of `t` has a nonzero homogeneous cyclic class in degree
`4`, `6`, or `10` (in particular of degree at least three). -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
    {V : Type u} [Finite V] {G : SimpleGraph V} [∀ v, Fintype (G.neighborSet v)]
    {t : DynkinType} (ht : t.Valid) (e : G ≃g diagramGraph t.cartanMatrix)
    (hp : IsBadPrime t (ringChar k)) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  let _ : ∀ v, Fintype ((diagramGraph t.cartanMatrix).neighborSet v) :=
    SimpleGraph.neighborSetFintypeOfFinite (diagramGraph t.cartanMatrix)
  suffices ∃ d, 3 ≤ d ∧
      ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver (diagramGraph t.cartanMatrix)) d,
        x ∉ commutatorSubmodule k
          (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph t.cartanMatrix))) by
    obtain ⟨d, hd, x, hxgrade, hx⟩ := this
    have hnot : ¬ signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
      rw [signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso k e]
      exact fun hle => hx (hle hxgrade)
    exact ⟨d, hd, IsConcreteLE.not_le_iff_exists.mp hnot⟩
  cases t with
  | D n =>
    have h2 : (2 : k) = 0 := natCast_eq_zero_of_ringChar_eq k (by simpa using hp)
    exact ⟨4, by omega, exists_signless_of_graph_eq k rfl
      (exists_mem_signlessPreprojectiveGrade_D_four_notMem_commutatorSubmodule k
        (DynkinType.valid_D.mp ht) h2)⟩
  | E6 =>
    have hG := congrArg diagramGraph DynkinType.cartanMatrix_E6.symm
    rcases (isBadPrime_E6_iff _).1 hp with h2 | h3
    · exact ⟨4, by omega, exists_signless_of_graph_eq k hG
        (exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule k (n := 6)
          (by omega) (natCast_eq_zero_of_ringChar_eq k h2))⟩
    · exact ⟨6, by omega, exists_signless_of_graph_eq k hG
        (exists_mem_signlessPreprojectiveGrade_E_six_notMem_commutatorSubmodule k (n := 6)
          (by omega) (natCast_eq_zero_of_ringChar_eq k h3))⟩
  | E7 =>
    have hG := congrArg diagramGraph DynkinType.cartanMatrix_E7.symm
    rcases (isBadPrime_E7_iff _).1 hp with h2 | h3
    · exact ⟨4, by omega, exists_signless_of_graph_eq k hG
        (exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule k (n := 7)
          (by omega) (natCast_eq_zero_of_ringChar_eq k h2))⟩
    · exact ⟨6, by omega, exists_signless_of_graph_eq k hG
        (exists_mem_signlessPreprojectiveGrade_E_six_notMem_commutatorSubmodule k (n := 7)
          (by omega) (natCast_eq_zero_of_ringChar_eq k h3))⟩
  | E8 =>
    have hG := congrArg diagramGraph DynkinType.cartanMatrix_E8.symm
    rcases (isBadPrime_E8_iff _).1 hp with h2 | h3 | h5
    · exact ⟨4, by omega, exists_signless_of_graph_eq k hG
        (exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule k (n := 8)
          (by omega) (natCast_eq_zero_of_ringChar_eq k h2))⟩
    · exact ⟨6, by omega, exists_signless_of_graph_eq k hG
        (exists_mem_signlessPreprojectiveGrade_E_six_notMem_commutatorSubmodule k (n := 8)
          (by omega) (natCast_eq_zero_of_ringChar_eq k h3))⟩
    · have h5' : (5 : k) = 0 := natCast_eq_zero_of_ringChar_eq k h5
      exact ⟨10, by omega, exists_signless_of_graph_eq k zigzagE8Graph_eq_diagramGraph
        ⟨_, signlessWord_E8_cyclicWord_mem_grade_ten k,
          signlessWord_E8_cyclicWord_notMem_commutatorSubmodule k h5'⟩⟩
  | A n | B n | C n | F4 | G2 => simp at hp

/-- **Nonzero cyclic classes in bad characteristic for every orientation.** Over any nontrivial
commutative ring whose characteristic is a bad prime for a valid Dynkin type `t`, the additive
preprojective algebra of every orientation of a graph isomorphic to the diagram of `t` has a
nonzero homogeneous cyclic class of degree at least three. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
    {V : Type u} [Finite V] {G : SimpleGraph V} {t : DynkinType} (ht : t.Valid)
    (e : G ≃g diagramGraph t.cartanMatrix) (hp : IsBadPrime t (ringChar k))
    (o : Orientation G) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  let _ : ∀ v, Fintype (G.neighborSet v) := SimpleGraph.neighborSetFintypeOfFinite G
  obtain ⟨d, hd, x, hxgrade, hx⟩ :=
    exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k ht e hp
  have hbip : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  have hnot : ¬ preprojectiveGrade k (OrientedQuiver G o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
    rw [hbip.preprojectiveGrade_le_commutatorSubmodule_iff k o]
    exact fun hle => hx (hle hxgrade)
  exact ⟨d, hd, IsConcreteLE.not_le_iff_exists.mp hnot⟩

end Nonvanishing

end TauCeti

namespace SimpleGraph.Connected

open TauCeti DoubledQuiver

universe u w

variable {k : Type w} [CommRing k] [Nontrivial k]

/-- **Connected non-Dynkin graphs have nonzero cyclic classes in degree at least three** in their
signless preprojective algebra, over every nontrivial commutative ring. -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule
    {V : Type u} [Finite V] {G : SimpleGraph V} [∀ v, Fintype (G.neighborSet v)]
    (hG : G.Connected)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  by_cases hacyc : G.IsAcyclic
  · classical
    let _ : Fintype V := Fintype.ofFinite V
    obtain ⟨d, hdmem, x, hxgrade, hx⟩ :=
      SimpleGraph.IsTree.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule
        (k := k) ⟨hG, hacyc⟩ hD
    refine ⟨d, ?_, exists_signless_of_graph_eq k rfl ⟨x, hxgrade, hx⟩⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdmem
    omega
  · exact exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic k hacyc

/-- **Connected non-Dynkin graphs have nonzero cyclic classes in degree at least three** in the
additive preprojective algebra of every orientation, over every nontrivial commutative ring. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule
    {V : Type u} [Finite V] {G : SimpleGraph V} (hG : G.Connected)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix))
    (o : Orientation G) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  by_cases hacyc : G.IsAcyclic
  · let _ : ∀ v, Fintype (G.neighborSet v) := SimpleGraph.neighborSetFintypeOfFinite G
    obtain ⟨d, hd, x, hxgrade, hx⟩ :=
      hG.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule (k := k) hD
    have hnot : ¬ preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
      rw [hacyc.isBipartite.preprojectiveGrade_le_commutatorSubmodule_iff k o]
      exact fun hle => hx (hle hxgrade)
    exact ⟨d, hd, IsConcreteLE.not_le_iff_exists.mp hnot⟩
  · exact exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic k hacyc o

end SimpleGraph.Connected

/-! ### The vanishing classification over a field -/

namespace TauCeti

open DoubledQuiver

section Classification

variable (k : Type w) [Field k] {V : Type u} [Finite V] (G : SimpleGraph V)

/-- **The positive-degree cyclic quotient of a signless preprojective algebra.** For a finite
connected simple graph `G` over a field `k`, every graded piece of `Π⁺(G)` in degree `d ≥ 3` lies
in the commutator submodule if and only if `G` is isomorphic to the diagram of a valid simply-laced
Dynkin type `t` and `ringChar k` is not a bad prime for `t`. -/
theorem signlessPreprojective_cyclicQuotient_vanishes_iff [∀ v, Fintype (G.neighborSet v)]
    (hG : G.Connected) :
    (∀ d : ℕ, 3 ≤ d →
      signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
    ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
      Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) := by
  constructor
  · intro hvan
    have hD : ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) := by
      by_contra hnot
      obtain ⟨d, hd, x, hxgrade, hx⟩ :=
        hG.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule (k := k) hnot
      exact hx (hvan d hd hxgrade)
    obtain ⟨t, htvalid, htsl, ⟨e⟩⟩ :=
      (SimpleGraph.exists_valid_isSimplyLaced_dynkinType_iso_iff G).2 hD
    refine ⟨t, htvalid, htsl, ⟨e⟩, fun hbad => ?_⟩
    obtain ⟨d, hd, x, hxgrade, hx⟩ :=
      exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
        k htvalid e hbad
    exact hx (hvan d hd hxgrade)
  · rintro ⟨t, -, htsl, ⟨e⟩, hgood⟩ d hd
    exact signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k htsl e hgood (by omega)

/-- Every positive-degree piece of `Π⁺(G)` lies in the commutator submodule if and only if `G` is
a valid simply-laced Dynkin diagram and `ringChar k` is not a bad prime for its type. -/
theorem signlessPreprojective_cyclicQuotient_vanishes_pos_iff [∀ v, Fintype (G.neighborSet v)]
    (hG : G.Connected) :
    (∀ d : ℕ, 0 < d →
      signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
    ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
      Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) :=
  ⟨fun h => (signlessPreprojective_cyclicQuotient_vanishes_iff k G hG).1
      fun d hd => h d (by omega),
   fun ⟨_, _, htsl, ⟨e⟩, hgood⟩ _ hd =>
      signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k htsl e hgood hd⟩

/-- **The positive-degree cyclic quotient of a preprojective algebra** (Schedler, Theorem 13.1.1;
Liu--Wang, Corollary 3.4). For any orientation `o` of a finite connected simple graph `G` over a
field `k`, every graded piece of `Π_k(Q_o)` in degree `d ≥ 3` lies in the commutator submodule
`[Π_k(Q_o), Π_k(Q_o)]` if and only if `G` is isomorphic to the diagram of a valid simply-laced
Dynkin type `t` and `ringChar k` is not a bad prime for `t`. -/
theorem preprojective_cyclicQuotient_vanishes_iff (hG : G.Connected) (o : Orientation G) :
    (∀ d : ℕ, 3 ≤ d →
      preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
    ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
      Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) := by
  constructor
  · intro hvan
    have hD : ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) := by
      by_contra hnot
      obtain ⟨d, hd, x, hxgrade, hx⟩ :=
        hG.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule (k := k) hnot o
      exact hx (hvan d hd hxgrade)
    obtain ⟨t, htvalid, htsl, ⟨e⟩⟩ :=
      (SimpleGraph.exists_valid_isSimplyLaced_dynkinType_iso_iff G).2 hD
    refine ⟨t, htvalid, htsl, ⟨e⟩, fun hbad => ?_⟩
    obtain ⟨d, hd, x, hxgrade, hx⟩ :=
      exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k htvalid e hbad o
    exact hx (hvan d hd hxgrade)
  · rintro ⟨t, -, htsl, ⟨e⟩, hgood⟩ d hd
    exact preprojectiveGrade_le_commutatorSubmodule_of_iso k htsl e hgood o (by omega)

/-- Every positive-degree piece of `Π_k(Q_o)` lies in the commutator submodule if and only if `G`
is a valid simply-laced Dynkin diagram and `ringChar k` is not a bad prime for its type. -/
theorem preprojective_cyclicQuotient_vanishes_pos_iff (hG : G.Connected) (o : Orientation G) :
    (∀ d : ℕ, 0 < d →
      preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
    ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
      Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) :=
  ⟨fun h => (preprojective_cyclicQuotient_vanishes_iff k G hG o).1 fun d hd => h d (by omega),
   fun ⟨_, _, htsl, ⟨e⟩, hgood⟩ _ hd =>
      preprojectiveGrade_le_commutatorSubmodule_of_iso k htsl e hgood o hd⟩

/-- Over a field of characteristic zero, the positive-degree cyclic quotient of `Π⁺(G)` vanishes
if and only if `G` is isomorphic to a valid simply-laced Dynkin diagram. -/
theorem signlessPreprojective_cyclicQuotient_vanishes_iff_of_charZero [CharZero k]
    [∀ v, Fintype (G.neighborSet v)] (hG : G.Connected) :
    (∀ d : ℕ, 3 ≤ d →
      signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
    ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) := by
  rw [signlessPreprojective_cyclicQuotient_vanishes_iff k G hG]
  simp

/-- Over a field of characteristic zero, the positive-degree cyclic quotient of `Π_k(Q_o)` vanishes
if and only if `G` is isomorphic to a valid simply-laced Dynkin diagram. -/
theorem preprojective_cyclicQuotient_vanishes_iff_of_charZero [CharZero k] (hG : G.Connected)
    (o : Orientation G) :
    (∀ d : ℕ, 3 ≤ d →
      preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
    ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) := by
  rw [preprojective_cyclicQuotient_vanishes_iff k G hG o]
  simp

end Classification

end TauCeti
