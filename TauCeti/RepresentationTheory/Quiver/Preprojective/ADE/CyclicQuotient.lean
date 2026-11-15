/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Basic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.SimpleGraph
public import TauCeti.RepresentationTheory.Quiver.Preprojective.CyclicQuotient
import Mathlib.RingTheory.Ideal.Quotient.Basic
import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.CyclicQuotient
import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.BadCharacteristic
import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.CyclicQuotient
import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.BadCharacteristic
import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CharacteristicFive
import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CharacteristicThree
import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CyclicQuotient
import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.Tree

/-!
# Positive-degree cyclic quotients of preprojective algebras

The cyclic quotient `Π / [Π, Π]` of an algebra is its zeroth Hochschild homology `HH_0(Π)`. For the
additive preprojective algebra `Π_k(Q_o)` of an oriented finite connected simple graph `(G, o)`,
graded by path length, positive-degree cyclic classes govern minimal `A∞` deformations of the
zigzag algebra of `G` through the bigraded Hochschild comparison
`HH^{2,q}(Π₂(Q_o)) ≅ (Π/[Π,Π])_{q+2}` for `q > 0` (`d = q + 2 ≥ 3`).

This file defines the bad primes `TauCeti.DynkinType.IsBadPrime` of a finite Dynkin type (`2` in
type `D`, `2` and `3` in types `E₆` and `E₇`, `2`, `3`, and `5` in type `E₈`, and none in type `A`)
and assembles the complete vanishing criterion for positive-degree cyclic quotients of connected
finite simple graphs:

1. **Good characteristic (`_of_dynkinType_iso`).** Over any commutative ring `k` in which every bad
   prime of `t` is invertible, every homogeneous piece of positive path degree (`d > 0`) in both
   `Π⁺_k(G)` and `Π_k(OrientedQuiver G o)` lies in the commutator submodule whenever
   `G ≃g diagramGraph t.cartanMatrix`.
2. **Bad characteristic (`_of_isBadPrime`).** Over any nontrivial commutative ring `k` in which a
   bad prime `p` of a valid type `t` vanishes (`(p : k) = 0`), both `Π⁺_k(G)` and
   `Π_k(OrientedQuiver G o)` carry a homogeneous element outside the commutator submodule in path
   degree `4`, `6`, or `10`.
3. **Connected-graph dichotomy.** Over any nontrivial commutative ring `k`, for a connected finite
   simple graph `G` and any orientation `o`, every graded piece of degree `d ≥ 3` (equivalently, of
   degree `d > 0`) lies in the commutator submodule if and only if `G` is isomorphic to the diagram
   of a valid simply-laced Dynkin type `t` whose bad primes are all units in `k`. Over a field `k`,
   the unit condition is equivalent to `¬ t.IsBadPrime (ringChar k)`.

In the converse direction over a general nontrivial commutative ring `k`, non-acyclic graphs are
excluded by simple cycles (`d ≥ 3`), non-Dynkin trees are excluded by embedded affine `D` or `E`
subdiagrams (`d ∈ {4, 6, 8, 12}`), and non-invertible bad primes `p` are excluded by base change
along `k →+* k ⧸ Ideal.span {(p : k)}` to a nontrivial ring in which `(p : k ⧸ _) = 0`.

## Main definitions and results

* `TauCeti.DynkinType.IsBadPrime`: bad primes of a finite Dynkin type (`2` for `D`, `2, 3` for
  `E₆, E₇`, `2, 3, 5` for `E₈`, none otherwise), with `DecidableRel` and characteristic lemmas.
* `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_of_dynkinType_iso` and
  `TauCeti.preprojectiveGrade_le_commutatorSubmodule_of_dynkinType_iso`: positive-degree vanishing
  when bad primes are units.
* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime` and
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime`: degree-`4`,
  `6`, or `10` cyclic classes when a bad prime vanishes in `k`.
* `TauCeti.forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff`,
  `TauCeti.forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff`,
  `TauCeti.forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff`, and
  `TauCeti.forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff`: the connected-graph
  dichotomies over any nontrivial commutative ring.
* `TauCeti.forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff_not_isBadPrime`,
  `TauCeti.forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff_not_isBadPrime`, and
  `TauCeti.forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff_not_isBadPrime`:
  the `ringChar k` specialization over a field.

## References

* T. Schedler, *Hochschild homology of preprojective algebras over the integers*, Adv. Math. 299
  (2016), Theorem 13.1.1, https://arxiv.org/abs/0704.3278.
* P. Etingof and C.-H. Eu, *Hochschild and cyclic homology of preprojective algebras of ADE
  quivers*, Mosc. Math. J. 7 (2007), https://arxiv.org/abs/math/0609006.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  Theorem 1.1, Proposition 3.2, and Corollary 3.4, https://arxiv.org/abs/2301.06757.
-/

public section

namespace TauCeti

namespace DynkinType

/-- The primes at which the positive-degree cyclic quotient of the additive preprojective algebra of
a simply-laced finite Dynkin diagram fails to vanish (Schedler, Theorem 13.1.1; Liu--Wang,
Theorem 1.1): `2` for type `D`, `2` and `3` for `E₆` and `E₇`, `2`, `3`, and `5` for `E₈`, and none
for type `A`. On the non-simply-laced constructors `B`, `C`, `F₄`, and `G₂` (whose underlying simple
graphs `diagramGraph t.cartanMatrix` are type-`A` path graphs) this predicate is `False`. Note that
`0` is never a bad prime, so characteristic zero is never bad when tested via `ringChar`. -/
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

@[simp]
theorem isBadPrime_D (n p : ℕ) : (DynkinType.D n).IsBadPrime p ↔ p = 2 :=
  (Iff.rfl)

@[simp]
theorem isBadPrime_E6 (p : ℕ) : DynkinType.E6.IsBadPrime p ↔ p = 2 ∨ p = 3 :=
  (Iff.rfl)

@[simp]
theorem isBadPrime_E7 (p : ℕ) : DynkinType.E7.IsBadPrime p ↔ p = 2 ∨ p = 3 :=
  (Iff.rfl)

@[simp]
theorem isBadPrime_E8 (p : ℕ) : DynkinType.E8.IsBadPrime p ↔ p = 2 ∨ p = 3 ∨ p = 5 :=
  (Iff.rfl)

@[simp]
theorem not_isBadPrime_A (n p : ℕ) : ¬ (DynkinType.A n).IsBadPrime p :=
  not_false

@[simp]
theorem not_isBadPrime_B (n p : ℕ) : ¬ (DynkinType.B n).IsBadPrime p :=
  not_false

@[simp]
theorem not_isBadPrime_C (n p : ℕ) : ¬ (DynkinType.C n).IsBadPrime p :=
  not_false

@[simp]
theorem not_isBadPrime_F4 (p : ℕ) : ¬ DynkinType.F4.IsBadPrime p :=
  not_false

@[simp]
theorem not_isBadPrime_G2 (p : ℕ) : ¬ DynkinType.G2.IsBadPrime p :=
  not_false

instance instDecidableRelIsBadPrime : DecidableRel IsBadPrime := fun t p =>
  match t with
  | .D n => decidable_of_iff' (p = 2) (isBadPrime_D n p)
  | .E6 => decidable_of_iff' (p = 2 ∨ p = 3) (isBadPrime_E6 p)
  | .E7 => decidable_of_iff' (p = 2 ∨ p = 3) (isBadPrime_E7 p)
  | .E8 => decidable_of_iff' (p = 2 ∨ p = 3 ∨ p = 5) (isBadPrime_E8 p)
  | .A n => isFalse (not_isBadPrime_A n p)
  | .B n => isFalse (not_isBadPrime_B n p)
  | .C n => isFalse (not_isBadPrime_C n p)
  | .F4 => isFalse (not_isBadPrime_F4 p)
  | .G2 => isFalse (not_isBadPrime_G2 p)

/-- Every bad prime is `2`, `3`, or `5`. -/
theorem IsBadPrime.eq_two_or_three_or_five {t : DynkinType} {p : ℕ} (h : t.IsBadPrime p) :
    p = 2 ∨ p = 3 ∨ p = 5 := by
  cases t <;> simp [IsBadPrime] at h <;> omega

/-- Every bad prime of a Dynkin type is a prime number. -/
theorem IsBadPrime.prime {t : DynkinType} {p : ℕ} (h : t.IsBadPrime p) : p.Prime := by
  rcases h.eq_two_or_three_or_five with rfl | rfl | rfl <;> decide

/-- Only simply-laced Dynkin types admit bad primes. -/
theorem IsBadPrime.isSimplyLaced {t : DynkinType} {p : ℕ} (h : t.IsBadPrime p) :
    t.IsSimplyLaced := by
  cases t <;> simp [IsBadPrime] at h ⊢

/-- No integer `p ≥ 7` (in particular, no prime `p ≥ 7`) is bad for any finite Dynkin type. -/
theorem not_isBadPrime_of_seven_le (t : DynkinType) {p : ℕ} (hp : 7 ≤ p) : ¬ t.IsBadPrime p :=
  fun h => by rcases h.eq_two_or_three_or_five with rfl | rfl | rfl <;> omega

@[simp]
theorem not_isBadPrime_zero (t : DynkinType) : ¬ t.IsBadPrime 0 :=
  fun h => Nat.not_prime_zero h.prime

@[simp]
theorem not_isBadPrime_one (t : DynkinType) : ¬ t.IsBadPrime 1 :=
  fun h => Nat.not_prime_one h.prime

/-- Over a division ring (in particular, a field), every bad prime of `t` is invertible if and only
if `ringChar k` is not a bad prime of `t`. -/
theorem forall_isBadPrime_isUnit_iff {k : Type*} [DivisionRing k] (t : DynkinType) :
    (∀ p, t.IsBadPrime p → IsUnit (p : k)) ↔ ¬ t.IsBadPrime (ringChar k) := by
  constructor
  · intro h hbad
    exact (isUnit_iff_ne_zero.mp (h (ringChar k) hbad)) (CharP.cast_eq_zero k (ringChar k))
  · intro hnot p hp
    rw [isUnit_iff_ne_zero]
    intro hp0
    have : CharP k p := (CharP.charP_iff_prime_eq_zero hp.prime).mpr hp0
    exact hnot (ringChar.eq_iff.mpr this ▸ hp)

end DynkinType

/-! ### Good-characteristic vanishing and bad-characteristic cyclic classes -/

open DoubledQuiver

section GoodCharacteristic

attribute [local instance] SimpleGraph.neighborSetFintypeOfFinite

private theorem signlessPreprojectiveGrade_diagramGraph_le_commutatorSubmodule
    (k : Type*) [CommRing k] (t : DynkinType)
    (hunit : ∀ p, t.IsBadPrime p → IsUnit (p : k)) {d : ℕ} (hd : 0 < d) :
    signlessPreprojectiveGrade k (DoubledQuiver (diagramGraph t.cartanMatrix)) d ≤
      commutatorSubmodule k
        (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph t.cartanMatrix))) := by
  by_cases hsl : t.IsSimplyLaced
  · cases t with
    | A n => exact signlessPreprojectiveGrade_A_le_commutatorSubmodule k hd
    | D n => exact signlessPreprojectiveGrade_D_le_commutatorSubmodule k (hunit 2 (by simp)) hd
    | E6 =>
        exact signlessPreprojectiveGrade_E6_le_commutatorSubmodule k
          (hunit 2 (by simp)) (hunit 3 (by simp)) hd
    | E7 =>
        exact signlessPreprojectiveGrade_E7_le_commutatorSubmodule k
          (hunit 2 (by simp)) (hunit 3 (by simp)) hd
    | E8 =>
        have key : ∀ H : SimpleGraph (Fin 8), zigzagE8Graph = H →
            signlessPreprojectiveGrade k (DoubledQuiver H) d ≤
              commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) := by
          rintro H rfl
          exact signlessPreprojectiveGrade_E8_le_commutatorSubmodule k
            (hunit 2 (by simp)) (hunit 3 (by simp)) (hunit 5 (by simp)) hd
        exact key _ zigzagE8Graph_eq_diagramGraph
    | B _ | C _ | F4 | G2 => simp at hsl
  · obtain ⟨f⟩ := t.nonempty_diagramGraph_iso_A_of_not_isSimplyLaced hsl
    exact (signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso k f d).mpr
      (signlessPreprojectiveGrade_A_le_commutatorSubmodule k hd)

end GoodCharacteristic

/-- **Positive-degree cyclic vanishing for signless Dynkin preprojective algebras in good
characteristic.** If `G` is isomorphic to the diagram of a Dynkin type `t` whose bad primes are all
invertible in `k`, then every graded piece of positive path degree in `Π⁺_k(G)` lies in the
commutator submodule, independently of the chosen neighbourhood enumerations. -/
theorem signlessPreprojectiveGrade_le_commutatorSubmodule_of_dynkinType_iso
    (k : Type*) [CommRing k] {V : Type*} [Finite V] {G : SimpleGraph V}
    [instG : ∀ i, Fintype (G.neighborSet i)] {t : DynkinType}
    (e : G ≃g diagramGraph t.cartanMatrix)
    (hunit : ∀ p, t.IsBadPrime p → IsUnit (p : k)) {d : ℕ} (hd : 0 < d) :
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) :=
  (@signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso k _ V _ _ _ G
    (diagramGraph t.cartanMatrix) instG
    (SimpleGraph.neighborSetFintypeOfFinite (diagramGraph t.cartanMatrix)) e d).mpr
    (signlessPreprojectiveGrade_diagramGraph_le_commutatorSubmodule k t hunit hd)

/-- **Positive-degree cyclic vanishing for Dynkin preprojective algebras in good characteristic.**
If `G` is isomorphic to the diagram of a Dynkin type `t` whose bad primes are all invertible in `k`,
then for every orientation `o` of `G` and every `d > 0`, the degree-`d` piece of
`Π_k(OrientedQuiver G o)` lies in the commutator submodule. -/
theorem preprojectiveGrade_le_commutatorSubmodule_of_dynkinType_iso
    (k : Type*) [CommRing k] {V : Type*} [Finite V] {G : SimpleGraph V}
    {t : DynkinType} (e : G ≃g diagramGraph t.cartanMatrix) (o : Orientation G)
    (hunit : ∀ p, t.IsBadPrime p → IsUnit (p : k)) {d : ℕ} (hd : 0 < d) :
    preprojectiveGrade k (OrientedQuiver G o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  let _ := SimpleGraph.neighborSetFintypeOfFinite G
  have hbip : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  exact (SimpleGraph.IsBipartite.preprojectiveGrade_le_commutatorSubmodule_iff k hbip o d).mpr
    (signlessPreprojectiveGrade_le_commutatorSubmodule_of_dynkinType_iso k e hunit hd)

section BadCharacteristic

attribute [local instance] SimpleGraph.neighborSetFintypeOfFinite

private theorem exists_mem_signlessPreprojectiveGrade_E_of_eq
    (k : Type*) [CommRing k] [Nontrivial k] {n : ℕ} (hn : 6 ≤ n)
    {C : Matrix (Fin n) (Fin n) ℤ} (hC : C = CartanMatrix.E n)
    {p : ℕ} (hbad : p = 2 ∨ p = 3) (hp : (p : k) = 0) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ),
      ∃ z ∈ signlessPreprojectiveGrade k (DoubledQuiver (diagramGraph C)) d,
        z ∉ commutatorSubmodule k
          (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph C))) := by
  subst hC
  rcases hbad with rfl | rfl
  · exact ⟨4, by simp,
      exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule k (by omega) hp⟩
  · exact ⟨6, by simp,
      exists_mem_signlessPreprojectiveGrade_E_six_notMem_commutatorSubmodule k hn hp⟩

private theorem exists_mem_signlessPreprojectiveGrade_diagramGraph_of_isBadPrime
    (k : Type*) [CommRing k] [Nontrivial k] {t : DynkinType} (ht : t.Valid)
    {p : ℕ} (hbad : t.IsBadPrime p) (hp : (p : k) = 0) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ),
      ∃ z ∈ signlessPreprojectiveGrade k (DoubledQuiver (diagramGraph t.cartanMatrix)) d,
        z ∉ commutatorSubmodule k
          (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph t.cartanMatrix))) := by
  cases t with
  | A _ | B _ | C _ | F4 | G2 => simp at hbad
  | D n =>
      rw [DynkinType.isBadPrime_D] at hbad
      subst p
      exact ⟨4, by simp,
        exists_mem_signlessPreprojectiveGrade_D_four_notMem_commutatorSubmodule k
          (DynkinType.valid_D.mp ht) hp⟩
  | E6 =>
      rw [DynkinType.isBadPrime_E6] at hbad
      exact exists_mem_signlessPreprojectiveGrade_E_of_eq (n := 6) k (by decide)
        DynkinType.cartanMatrix_E6 hbad hp
  | E7 =>
      rw [DynkinType.isBadPrime_E7] at hbad
      exact exists_mem_signlessPreprojectiveGrade_E_of_eq (n := 7) k (by decide)
        DynkinType.cartanMatrix_E7 hbad hp
  | E8 =>
      rw [DynkinType.isBadPrime_E8] at hbad
      rcases hbad with rfl | rfl | rfl
      · exact exists_mem_signlessPreprojectiveGrade_E_of_eq (n := 8) k (by decide)
          DynkinType.cartanMatrix_E8 (.inl rfl) hp
      · exact exists_mem_signlessPreprojectiveGrade_E_of_eq (n := 8) k (by decide)
          DynkinType.cartanMatrix_E8 (.inr rfl) hp
      · have key : ∀ H : SimpleGraph (Fin 8), zigzagE8Graph = H →
            ∃ z ∈ signlessPreprojectiveGrade k (DoubledQuiver H) 10,
              z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) := by
          rintro H rfl
          exact ⟨signlessWord k zigzagE8Graph [3, 2, 3, 4, 3, 4, 3, 4, 3, 4, 3],
            signlessWord_E8_cyclicWord_mem_grade_ten k,
            signlessWord_E8_cyclicWord_notMem_commutatorSubmodule k hp⟩
        exact ⟨10, by simp, key _ zigzagE8Graph_eq_diagramGraph⟩

end BadCharacteristic

/-- **Nonzero cyclic classes in bad characteristic (signless presentation).** Over any nontrivial
commutative ring `k` in which a bad prime `p` of a valid Dynkin type `t` vanishes (`(p : k) = 0`),
any graph isomorphic to `diagramGraph t.cartanMatrix` carries a homogeneous element in path degree
`4`, `6`, or `10` outside the commutator submodule of `Π⁺_k(G)`. -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
    (k : Type*) [CommRing k] [Nontrivial k] {V : Type*} [Finite V] {G : SimpleGraph V}
    [instG : ∀ i, Fintype (G.neighborSet i)] {t : DynkinType} (ht : t.Valid)
    (e : G ≃g diagramGraph t.cartanMatrix) {p : ℕ} (hbad : t.IsBadPrime p) (hp : (p : k) = 0) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ), ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain ⟨d, hd, z, hz, hz0⟩ :=
    exists_mem_signlessPreprojectiveGrade_diagramGraph_of_isBadPrime k ht hbad hp
  refine ⟨d, hd, ?_⟩
  by_contra! hle
  exact hz0 ((@signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso k _ V _ _ _ G
    (diagramGraph t.cartanMatrix) instG
    (SimpleGraph.neighborSetFintypeOfFinite (diagramGraph t.cartanMatrix)) e d).mp hle hz)

/-- **Nonzero cyclic classes in bad characteristic (oriented presentation).** Over any nontrivial
commutative ring `k` in which a bad prime `p` of a valid Dynkin type `t` vanishes (`(p : k) = 0`),
every orientation `o` of any graph isomorphic to `diagramGraph t.cartanMatrix` carries a homogeneous
element in path degree `4`, `6`, or `10` outside the commutator submodule of
`Π_k(OrientedQuiver G o)`. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
    (k : Type*) [CommRing k] [Nontrivial k] {V : Type*} [Finite V] {G : SimpleGraph V}
    {t : DynkinType} (ht : t.Valid) (e : G ≃g diagramGraph t.cartanMatrix) (o : Orientation G)
    {p : ℕ} (hbad : t.IsBadPrime p) (hp : (p : k) = 0) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ), ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  let _ := SimpleGraph.neighborSetFintypeOfFinite G
  have hbip : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  obtain ⟨d, hd, x, hx, hx0⟩ :=
    exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
      k ht e hbad hp
  refine ⟨d, hd, ?_⟩
  by_contra! hle
  exact hx0 ((SimpleGraph.IsBipartite.preprojectiveGrade_le_commutatorSubmodule_iff k hbip o d).mp
    hle hx)

/-! ### The positive-degree cyclic quotient dichotomy for connected graphs -/

/-- **Positive-degree cyclic quotient dichotomy for oriented connected graphs (over a nontrivial
commutative ring).** For a finite connected simple graph `G` and any orientation `o` of `G`, every
graded piece of path degree `d ≥ 3` in `Π_k(OrientedQuiver G o)` lies in the commutator submodule if
and only if `G` is isomorphic to the diagram of a valid simply-laced Dynkin type `t` whose bad
primes are all units in `k`. -/
theorem forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff
    (k : Type*) [CommRing k] [Nontrivial k] {V : Type*} [Finite V] {G : SimpleGraph V}
    (hG : G.Connected) (o : Orientation G) :
    (∀ d ≥ 3, preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧
        ∀ p, t.IsBadPrime p → IsUnit (p : k) := by
  constructor
  · intro hall
    -- Step 1: Any simple cycle produces a surviving cyclic class in path degree ≥ 3.
    have hacyc : G.IsAcyclic := by
      by_contra hnot
      obtain ⟨d, hd, x, hx, hx0⟩ :=
        exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic (k := k) o hnot
      exact hx0 (hall d hd hx)
    have htree : G.IsTree := ⟨hG, hacyc⟩
    have hbip : G.IsBipartite := hacyc.isBipartite
    -- Step 2: Any non-Dynkin tree contains an affine D or E diagram with a class in {4, 6, 8, 12}.
    have hdyn : ∃ s : DynkinType, s.Valid ∧ Nonempty (G ≃g diagramGraph s.cartanMatrix) := by
      classical
      let _ : Fintype V := Fintype.ofFinite V
      by_contra hnot
      obtain ⟨d, hd, x, hx, hx0⟩ :=
        htree.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule (k := k) hnot
      have hd3 : 3 ≤ d := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        omega
      exact hx0
        ((SimpleGraph.IsBipartite.preprojectiveGrade_le_commutatorSubmodule_iff k hbip o d).mp
          (hall d hd3) hx)
    obtain ⟨t, ht, hsl, ⟨e⟩⟩ :=
      (SimpleGraph.exists_valid_isSimplyLaced_dynkinType_iso_iff G).mpr hdyn
    -- Step 3: If a bad prime p is not a unit, k / (p) is nontrivial with p = 0 and detects a class.
    refine ⟨t, ht, hsl, ⟨e⟩, fun p hbad => ?_⟩
    by_contra hnu
    let I : Ideal k := Ideal.span {(p : k)}
    have hItop : I ≠ ⊤ := mt Ideal.span_singleton_eq_top.mp hnu
    have : Nontrivial (k ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
    let f : k →+* k ⧸ I := Ideal.Quotient.mk I
    have hp0 : (p : k ⧸ I) = 0 := by
      rw [← map_natCast f p]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    obtain ⟨d, hd, x, hx, hx0⟩ :=
      exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime (k ⧸ I) ht e o hbad hp0
    have hd3 : 3 ≤ d := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      omega
    exact hx0 (f.preprojectiveGrade_le_commutatorSubmodule (hall d hd3) hx)
  · rintro ⟨t, -, -, ⟨e⟩, hunit⟩ d hd
    exact preprojectiveGrade_le_commutatorSubmodule_of_dynkinType_iso k e o hunit (by omega)

/-- For a finite connected simple graph `G` and any orientation `o` of `G`, vanishing of the cyclic
quotient of `Π_k(OrientedQuiver G o)` in all positive degrees (`d > 0`) is equivalent to the same
simply-laced Dynkin and bad-prime unit criterion as vanishing in degrees `d ≥ 3`. -/
theorem forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff
    (k : Type*) [CommRing k] [Nontrivial k] {V : Type*} [Finite V] {G : SimpleGraph V}
    (hG : G.Connected) (o : Orientation G) :
    (∀ d > 0, preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧
        ∀ p, t.IsBadPrime p → IsUnit (p : k) := by
  refine ⟨fun hall => (forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff k hG o).mp
    fun d hd => hall d (by omega), ?_⟩
  rintro ⟨t, -, -, ⟨e⟩, hunit⟩ d hd
  exact preprojectiveGrade_le_commutatorSubmodule_of_dynkinType_iso k e o hunit hd

/-- **Positive-degree cyclic quotient dichotomy for signless preprojective algebras
(degrees `≥ 3`).** For a finite connected simple graph `G`, every graded piece of path degree
`d ≥ 3` in `Π⁺_k(G)` lies in the commutator submodule if and only if `G` is isomorphic to the
diagram of a valid simply-laced Dynkin type `t` whose bad primes are all units in `k`. -/
theorem forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff
    (k : Type*) [CommRing k] [Nontrivial k] {V : Type*} [Finite V] {G : SimpleGraph V}
    [∀ i, Fintype (G.neighborSet i)] (hG : G.Connected) :
    (∀ d ≥ 3, signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧
        ∀ p, t.IsBadPrime p → IsUnit (p : k) := by
  constructor
  · intro hall
    have hacyc : G.IsAcyclic := by
      by_contra hnot
      obtain ⟨d, hd, x, hx, hx0⟩ :=
        exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic
          (k := k) hnot
      exact hx0 (hall d hd hx)
    have hbip : G.IsBipartite := hacyc.isBipartite
    let o : Orientation G := (SimpleGraph.IsBipartite.coloringBool hbip).sourceSink
    refine (forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff k hG o).mp fun d hd => ?_
    exact (SimpleGraph.IsBipartite.preprojectiveGrade_le_commutatorSubmodule_iff k hbip o d).mpr
      (hall d hd)
  · rintro ⟨t, -, -, ⟨e⟩, hunit⟩ d hd
    exact signlessPreprojectiveGrade_le_commutatorSubmodule_of_dynkinType_iso k e hunit (by omega)

/-- For a finite connected simple graph `G`, vanishing of the cyclic quotient of `Π⁺_k(G)` in all
positive degrees (`d > 0`) is equivalent to the same simply-laced Dynkin and bad-prime unit
criterion as vanishing in degrees `d ≥ 3`. -/
theorem forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff
    (k : Type*) [CommRing k] [Nontrivial k] {V : Type*} [Finite V] {G : SimpleGraph V}
    [∀ i, Fintype (G.neighborSet i)] (hG : G.Connected) :
    (∀ d > 0, signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧
        ∀ p, t.IsBadPrime p → IsUnit (p : k) := by
  refine ⟨fun hall => (forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff
    k hG).mp fun d hd => hall d (by omega), ?_⟩
  rintro ⟨t, -, -, ⟨e⟩, hunit⟩ d hd
  exact signlessPreprojectiveGrade_le_commutatorSubmodule_of_dynkinType_iso k e hunit hd

/-! ### Specialization over fields via `ringChar` -/

/-- **The positive-degree cyclic quotient criterion over a field (degrees `≥ 3`).** Let `o` orient a
finite connected simple graph `G` and let `Π = Π_k(OrientedQuiver G o)` over a field `k`. Every
homogeneous piece of path degree `d ≥ 3` lies in `[Π, Π]` if and only if `G` is isomorphic to the
diagram of a valid simply-laced Dynkin type `t` and `ringChar k` is not a bad prime of `t`
(Schedler, Theorem 13.1.1; Liu--Wang, Corollary 3.4). -/
theorem forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff_not_isBadPrime
    (k : Type*) [Field k] {V : Type*} [Finite V] {G : SimpleGraph V}
    (hG : G.Connected) (o : Orientation G) :
    (∀ d ≥ 3, preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ t.IsBadPrime (ringChar k) := by
  rw [forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff k hG o]
  simp_rw [DynkinType.forall_isBadPrime_isUnit_iff]

/-- Over a field `k`, every graded piece of positive path degree (`d > 0`) in
`Π_k(OrientedQuiver G o)` lies in the commutator submodule if and only if `G` is isomorphic to the
diagram of a valid simply-laced Dynkin type `t` and `ringChar k` is not a bad prime of `t`. -/
theorem forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff_not_isBadPrime
    (k : Type*) [Field k] {V : Type*} [Finite V] {G : SimpleGraph V}
    (hG : G.Connected) (o : Orientation G) :
    (∀ d > 0, preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ t.IsBadPrime (ringChar k) := by
  rw [forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff k hG o]
  simp_rw [DynkinType.forall_isBadPrime_isUnit_iff]

/-- Over a field `k`, every graded piece of path degree `d ≥ 3` in the signless preprojective
algebra `Π⁺_k(G)` of a finite connected simple graph `G` lies in the commutator submodule if and
only if `G` is isomorphic to the diagram of a valid simply-laced Dynkin type `t` and `ringChar k` is
not a bad prime of `t`. -/
theorem forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff_not_isBadPrime
    (k : Type*) [Field k] {V : Type*} [Finite V] {G : SimpleGraph V}
    [∀ i, Fintype (G.neighborSet i)] (hG : G.Connected) :
    (∀ d ≥ 3, signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ t.IsBadPrime (ringChar k) := by
  rw [forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff k hG]
  simp_rw [DynkinType.forall_isBadPrime_isUnit_iff]

end TauCeti
