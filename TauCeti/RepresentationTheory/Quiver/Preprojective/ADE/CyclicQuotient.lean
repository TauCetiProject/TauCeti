/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import TauCeti.LinearAlgebra.RootSystem.BadPrime
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
public import TauCeti.RepresentationTheory.Quiver.Preprojective.CyclicQuotient
import Mathlib.Algebra.CharP.Basic
import TauCeti.LinearAlgebra.RootSystem.FiniteType.SimpleGraph
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

This file combines the good-characteristic vanishing theorems for types `A`, `D` and `E`, the
bad-characteristic cyclic classes in types `D` and `E`, the affine-tree cyclic classes, and the
cycle matrix representation into the complete positive-degree cyclic quotient dichotomy for
connected finite simple graphs.

Over a field `k`, for a connected finite simple graph `G`, the graded piece of degree `d` of the
cyclic quotient `Π⁺(G) / [Π⁺(G), Π⁺(G)]` vanishes for all `d ≥ 3` (equivalently, for all `d > 0`)
if and only if `G` is isomorphic to the diagram of a valid simply-laced Dynkin type `t` whose bad
primes (`TauCeti.DynkinType.IsBadPrime`) do not include `ringChar k`:

* no bad primes for `Aₙ`;
* `2` for `Dₙ` (`n ≥ 4`);
* `2` and `3` for `E₆` and `E₇`;
* `2`, `3` and `5` for `E₈`.

The same characterization holds for the additive preprojective algebra `Π_k(OrientedQuiver G o)` of
every orientation `o` of `G`.

The nonvanishing directions do not require a field: for a bad characteristic of a valid
simply-laced Dynkin diagram the statement holds over every commutative ring (since a bad prime is
not `1`), and for any connected non-Dynkin graph it holds over every nontrivial commutative ring,
in both cases producing a nonzero cyclic class in some path degree `d ≥ 3`.

## Main results

* `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso` and
  `TauCeti.preprojectiveGrade_le_commutatorSubmodule_of_iso`: in good characteristic, every
  positive-degree graded piece of the preprojective algebra of a simply-laced Dynkin diagram lies
  in the commutator submodule.
* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime` and
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime`: in a bad
  characteristic of a valid simply-laced Dynkin diagram, there is a nonzero cyclic class of degree
  at least `3` (`4`, `6` or `10`).
* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_dynkinType_iso`
  and `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_dynkinType_iso`:
  every connected finite non-Dynkin graph has a nonzero cyclic class of degree at least `3`.
* `TauCeti.forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff`,
  `TauCeti.forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff`,
  `TauCeti.forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff`, and
  `TauCeti.forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff`: **the complete
  positive-degree cyclic quotient dichotomy for connected finite simple graphs.**

## References

* P. Etingof and C.-H. Eu, *Hochschild and cyclic homology of preprojective algebras of ADE
  quivers*, Mosc. Math. J. 7 (2007), https://arxiv.org/abs/math/0609006.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, Theorem 1.1 and Proposition 3.2.
* T. Schedler, *Hochschild homology of preprojective algebras over the integers*,
  https://arxiv.org/abs/0704.3278.
-/

public section

namespace TauCeti

open DoubledQuiver

attribute [local instance] SimpleGraph.neighborSetFintypeOfFinite

/-! ### Characteristic helpers -/

private theorem isUnit_of_ringChar_ne {k : Type*} [Field k] {p : ℕ}
    (hp : p.Prime) (h : ringChar k ≠ p) : IsUnit (p : k) :=
  isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime k (p := ringChar k) hp h)

private theorem natCast_eq_zero_of_ringChar_eq {k : Type*} [CommRing k] {p : ℕ}
    (h : ringChar k = p) : (p : k) = 0 := by
  rw [← h]
  exact ringChar.Nat.cast_ringChar

private theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_eq
    (k : Type*) [CommRing k] {V : Type*} [Finite V] {G H : SimpleGraph V} (hGH : G = H) {d : ℕ}
    (h : ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) :
    ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver H) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) := by
  subst hGH
  exact h

private theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_iso
    (k : Type*) [CommRing k] {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [∀ i, Fintype (G.neighborSet i)] [∀ j, Fintype (H.neighborSet j)]
    (e : G ≃g H) {d : ℕ}
    (h : ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver H) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H))) :
    ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain ⟨y, hy, hy0⟩ := h
  let φ := signlessPreprojectiveAlgebraEquiv k e
  refine ⟨φ.symm y, ?_, fun hx => hy0 ?_⟩
  · simpa only [φ, signlessPreprojectiveAlgebraEquiv_symm] using
      (signlessPreprojectiveAlgebraEquiv_mem_signlessPreprojectiveGrade_iff k e.symm).mpr hy
  · simpa only [AlgEquiv.apply_symm_apply] using map_mem_commutatorSubmodule φ hx

/-! ### Good-characteristic vanishing for simply-laced Dynkin diagrams -/

section GoodCharacteristic

variable (k : Type*) [Field k]

/-- **In good characteristic, the positive-degree cyclic quotient of the signless preprojective
algebra of a simply-laced Dynkin diagram vanishes.** -/
theorem signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso {V : Type*} [Finite V]
    {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] {t : DynkinType}
    (hs : t.IsSimplyLaced) (hgood : ¬ t.IsBadPrime (ringChar k))
    (e : G ≃g diagramGraph t.cartanMatrix) {d : ℕ} (hd : 0 < d) :
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  refine (signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso k e d).mpr ?_
  cases t with
  | A n =>
    exact signlessPreprojectiveGrade_A_le_commutatorSubmodule k hd
  | D n =>
    have h2 : IsUnit (2 : k) :=
      isUnit_of_ringChar_ne Nat.prime_two (by simpa using hgood)
    exact signlessPreprojectiveGrade_D_le_commutatorSubmodule k h2 hd
  | E6 =>
    simp only [DynkinType.isBadPrime_E6_iff, not_or] at hgood
    have h2 : IsUnit (2 : k) := isUnit_of_ringChar_ne Nat.prime_two hgood.1
    have h3 : IsUnit (3 : k) := isUnit_of_ringChar_ne Nat.prime_three hgood.2
    exact signlessPreprojectiveGrade_E6_le_commutatorSubmodule k h2 h3 hd
  | E7 =>
    simp only [DynkinType.isBadPrime_E7_iff, not_or] at hgood
    have h2 : IsUnit (2 : k) := isUnit_of_ringChar_ne Nat.prime_two hgood.1
    have h3 : IsUnit (3 : k) := isUnit_of_ringChar_ne Nat.prime_three hgood.2
    exact signlessPreprojectiveGrade_E7_le_commutatorSubmodule k h2 h3 hd
  | E8 =>
    simp only [DynkinType.isBadPrime_E8_iff, not_or] at hgood
    have h2 : IsUnit (2 : k) := isUnit_of_ringChar_ne Nat.prime_two hgood.1
    have h3 : IsUnit (3 : k) := isUnit_of_ringChar_ne Nat.prime_three hgood.2.1
    have h5 : IsUnit (5 : k) := isUnit_of_ringChar_ne Nat.prime_five hgood.2.2
    have key : ∀ H : SimpleGraph (Fin 8), zigzagE8Graph = H →
        signlessPreprojectiveGrade k (DoubledQuiver H) d ≤
          commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) := by
      rintro H rfl
      exact signlessPreprojectiveGrade_E8_le_commutatorSubmodule k h2 h3 h5 hd
    exact key _ zigzagE8Graph_eq_diagramGraph
  | B n | C n | F4 | G2 => simp at hs

/-- **In good characteristic, the positive-degree cyclic quotient of the preprojective algebra of
every orientation of a simply-laced Dynkin diagram vanishes.** -/
theorem preprojectiveGrade_le_commutatorSubmodule_of_iso {V : Type*} [Finite V]
    {G : SimpleGraph V} {t : DynkinType}
    (hs : t.IsSimplyLaced) (hgood : ¬ t.IsBadPrime (ringChar k))
    (e : G ≃g diagramGraph t.cartanMatrix) (o : Orientation G) {d : ℕ} (hd : 0 < d) :
    preprojectiveGrade k (OrientedQuiver G o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  have hb : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  exact (hb.preprojectiveGrade_le_commutatorSubmodule_iff k o d).mpr
    (signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k hs hgood e hd)

end GoodCharacteristic

/-! ### Bad-characteristic nonvanishing for simply-laced Dynkin diagrams -/

section BadCharacteristic

variable (k : Type*) [CommRing k]

private theorem exists_mem_signlessPreprojectiveGrade_E_notMem_commutatorSubmodule_of_two_or_three
    [Nontrivial k] {n : ℕ} (hn : 6 ≤ n) (h : ringChar k = 2 ∨ ringChar k = 3) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ signlessPreprojectiveGrade k
        (DoubledQuiver (diagramGraph (CartanMatrix.E n))) d,
      x ∉ commutatorSubmodule k
        (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph (CartanMatrix.E n)))) := by
  rcases h with h2 | h3
  · exact ⟨4, by omega, exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule
      k (by omega) (by simpa using natCast_eq_zero_of_ringChar_eq (k := k) h2)⟩
  · exact ⟨6, by omega, exists_mem_signlessPreprojectiveGrade_E_six_notMem_commutatorSubmodule
      k hn (by simpa using natCast_eq_zero_of_ringChar_eq (k := k) h3)⟩

/-- **In a bad characteristic of a valid simply-laced Dynkin diagram, the signless preprojective
algebra has a nonzero cyclic class of degree at least three** (`4`, `6` or `10`), over every
commutative ring (the bad-prime hypothesis forces `ringChar k ≠ 1` and hence `Nontrivial k`). -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    {t : DynkinType} (ht : t.Valid) (hs : t.IsSimplyLaced)
    (hbad : t.IsBadPrime (ringChar k)) (e : G ≃g diagramGraph t.cartanMatrix) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  have : Nontrivial k := CharP.nontrivial_of_char_ne_one (v := ringChar k) hbad.prime.ne_one
  suffices ∃ d, 3 ≤ d ∧
      ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver (diagramGraph t.cartanMatrix)) d,
        x ∉ commutatorSubmodule k
          (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph t.cartanMatrix))) by
    obtain ⟨d, hd, hx⟩ := this
    exact ⟨d, hd,
      exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_iso k e hx⟩
  cases t with
  | A n => exact absurd hbad (DynkinType.not_isBadPrime_A n _)
  | D n =>
    rw [DynkinType.isBadPrime_D_iff] at hbad
    have h2 : (2 : k) = 0 := by simpa using natCast_eq_zero_of_ringChar_eq (k := k) hbad
    exact ⟨4, by omega,
      exists_mem_signlessPreprojectiveGrade_D_four_notMem_commutatorSubmodule k
        (DynkinType.valid_D.mp ht) h2⟩
  | E6 =>
    rw [DynkinType.isBadPrime_E6_iff] at hbad
    obtain ⟨d, hd, hx⟩ :=
      exists_mem_signlessPreprojectiveGrade_E_notMem_commutatorSubmodule_of_two_or_three k
        (n := 6) (by omega) hbad
    exact ⟨d, hd, exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_eq k
      (congrArg diagramGraph DynkinType.cartanMatrix_E6.symm) hx⟩
  | E7 =>
    rw [DynkinType.isBadPrime_E7_iff] at hbad
    obtain ⟨d, hd, hx⟩ :=
      exists_mem_signlessPreprojectiveGrade_E_notMem_commutatorSubmodule_of_two_or_three k
        (n := 7) (by omega) hbad
    exact ⟨d, hd, exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_eq k
      (congrArg diagramGraph DynkinType.cartanMatrix_E7.symm) hx⟩
  | E8 =>
    rw [DynkinType.isBadPrime_E8_iff] at hbad
    rcases or_assoc.mpr hbad with h23 | h5
    · obtain ⟨d, hd, hx⟩ :=
        exists_mem_signlessPreprojectiveGrade_E_notMem_commutatorSubmodule_of_two_or_three k
          (n := 8) (by omega) h23
      exact ⟨d, hd, exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_eq k
        (congrArg diagramGraph DynkinType.cartanMatrix_E8.symm) hx⟩
    · have h5' : (5 : k) = 0 := by simpa using natCast_eq_zero_of_ringChar_eq (k := k) h5
      exact ⟨10, by omega,
        exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_eq k
          zigzagE8Graph_eq_diagramGraph
          ⟨_, signlessWord_E8_cyclicWord_mem_grade_ten k,
            signlessWord_E8_cyclicWord_notMem_commutatorSubmodule k h5'⟩⟩
  | B n | C n | F4 | G2 => simp at hs

/-- **In a bad characteristic of a valid simply-laced Dynkin diagram, the preprojective algebra of
every orientation has a nonzero cyclic class of degree at least three**, over every commutative
ring. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
    {V : Type*} [Finite V] {G : SimpleGraph V}
    {t : DynkinType} (ht : t.Valid) (hs : t.IsSimplyLaced)
    (hbad : t.IsBadPrime (ringChar k)) (e : G ≃g diagramGraph t.cartanMatrix)
    (o : Orientation G) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  have hb : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  obtain ⟨d, hd, x, hx, hx0⟩ :=
    exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k ht hs hbad e
  let φ := hb.signlessPreprojectiveAlgebraEquiv k o
  refine ⟨d, hd, φ x, hb.signlessPreprojectiveAlgebraEquiv_mem_preprojectiveGrade k o hx, ?_⟩
  intro hmem
  exact hx0 (by
    simpa only [AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule φ.symm hmem)

end BadCharacteristic

/-! ### Non-Dynkin connected finite graphs -/

section NonDynkin

variable (k : Type*) [CommRing k] [Nontrivial k]

/-- **Every connected finite non-Dynkin graph has a nonzero cyclic class of degree at least three**
in its signless preprojective algebra, over every nontrivial commutative ring: a cycle gives a
class in its length, while a non-Dynkin tree contains an affine `D` or `E` subdiagram giving a
class in degree `4`, `6`, `8` or `12`. -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_dynkinType_iso
    {V : Type*} [Finite V] {G : SimpleGraph V} [inst : ∀ i, Fintype (G.neighborSet i)]
    (hG : G.Connected)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  by_cases hacyc : G.IsAcyclic
  · classical
    have : Fintype V := Fintype.ofFinite V
    obtain rfl : inst = fun v => Subtype.fintype (Membership.mem (G.neighborSet v)) :=
      Subsingleton.elim _ _
    have htree : G.IsTree := ⟨hG, hacyc⟩
    obtain ⟨d, hd, hx⟩ :=
      htree.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule (k := k) hD
    have hd3 : 3 ≤ d := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      omega
    exact ⟨d, hd3, hx⟩
  · exact exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic k hacyc

/-- **Every connected finite non-Dynkin graph has a nonzero cyclic class of degree at least three**
in the preprojective algebra of every orientation, over every nontrivial commutative ring. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_dynkinType_iso
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.Connected)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix))
    (o : Orientation G) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  by_cases hacyc : G.IsAcyclic
  · have hb : G.IsBipartite := hacyc.isBipartite
    obtain ⟨d, hd, x, hx, hx0⟩ :=
      exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_dynkinType_iso
        k hG hD
    let φ := hb.signlessPreprojectiveAlgebraEquiv k o
    refine ⟨d, hd, φ x, hb.signlessPreprojectiveAlgebraEquiv_mem_preprojectiveGrade k o hx, ?_⟩
    intro hmem
    exact hx0 (by
      simpa only [AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule φ.symm hmem)
  · exact exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic k hacyc o

end NonDynkin

/-! ### The complete positive-degree cyclic quotient dichotomy -/

section Dichotomy

variable (k : Type*) [Field k]

/-- **The cyclic quotient dichotomy in degrees at least three for signless preprojective algebras**:
for a connected finite simple graph `G` and a field `k`, every graded piece of degree `d ≥ 3` of
`Π⁺(G)` lies in the commutator submodule if and only if `G` is isomorphic to the diagram of a valid
simply-laced Dynkin type for which `ringChar k` is not a bad prime. -/
theorem forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    (hG : G.Connected) :
    (∀ d, 3 ≤ d → signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ t.IsBadPrime (ringChar k) := by
  constructor
  · intro hvan
    have hD : ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) :=
      by_contra fun hnot => by
        obtain ⟨d, hd, x, hx, hx0⟩ :=
          exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_dynkinType_iso
            k hG hnot
        exact hx0 (hvan d hd hx)
    obtain ⟨t, ht, hs, ⟨e⟩⟩ := (SimpleGraph.exists_valid_isSimplyLaced_dynkinType_iso_iff G).mpr hD
    refine ⟨t, ht, hs, ⟨e⟩, fun hbad => ?_⟩
    obtain ⟨d, hd, x, hx, hx0⟩ :=
      exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
        k ht hs hbad e
    exact hx0 (hvan d hd hx)
  · rintro ⟨t, -, hs, ⟨e⟩, hgood⟩ d hd
    exact signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k hs hgood e (by omega)

/-- **The positive-degree cyclic quotient dichotomy for signless preprojective algebras**: for a
connected finite simple graph `G` and a field `k`, every positive-degree graded piece of `Π⁺(G)`
lies in the commutator submodule if and only if `G` is isomorphic to the diagram of a valid
simply-laced Dynkin type for which `ringChar k` is not a bad prime. -/
theorem forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    (hG : G.Connected) :
    (∀ d, 0 < d → signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ t.IsBadPrime (ringChar k) :=
  ⟨fun h =>
    (forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff k hG).mp
      fun d hd => h d (by omega),
   fun ⟨_, _, hs, ⟨e⟩, hgood⟩ _ hd =>
    signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k hs hgood e hd⟩

/-- **The cyclic quotient dichotomy in degrees at least three for preprojective algebras of oriented
graphs**: for a connected finite simple graph `G`, an orientation `o` of `G`, and a field `k`,
every graded piece of degree `d ≥ 3` of `Π_k(OrientedQuiver G o)` lies in the commutator submodule
if and only if `G` is isomorphic to the diagram of a valid simply-laced Dynkin type for which
`ringChar k` is not a bad prime. -/
theorem forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.Connected) (o : Orientation G) :
    (∀ d, 3 ≤ d → preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ t.IsBadPrime (ringChar k) := by
  constructor
  · intro hvan
    have hD : ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) :=
      by_contra fun hnot => by
        obtain ⟨d, hd, x, hx, hx0⟩ :=
          exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_dynkinType_iso
            k hG hnot o
        exact hx0 (hvan d hd hx)
    obtain ⟨t, ht, hs, ⟨e⟩⟩ := (SimpleGraph.exists_valid_isSimplyLaced_dynkinType_iso_iff G).mpr hD
    refine ⟨t, ht, hs, ⟨e⟩, fun hbad => ?_⟩
    obtain ⟨d, hd, x, hx, hx0⟩ :=
      exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k ht hs hbad e o
    exact hx0 (hvan d hd hx)
  · rintro ⟨t, -, hs, ⟨e⟩, hgood⟩ d hd
    exact preprojectiveGrade_le_commutatorSubmodule_of_iso k hs hgood e o (by omega)

/-- **The positive-degree cyclic quotient dichotomy for preprojective algebras of oriented graphs**:
for a connected finite simple graph `G`, an orientation `o` of `G`, and a field `k`, every
positive-degree graded piece of `Π_k(OrientedQuiver G o)` lies in the commutator submodule if and
only if `G` is isomorphic to the diagram of a valid simply-laced Dynkin type for which `ringChar k`
is not a bad prime. -/
theorem forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.Connected) (o : Orientation G) :
    (∀ d, 0 < d → preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ t.IsBadPrime (ringChar k) :=
  ⟨fun h =>
    (forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff k hG o).mp
      fun d hd => h d (by omega),
   fun ⟨_, _, hs, ⟨e⟩, hgood⟩ _ hd =>
    preprojectiveGrade_le_commutatorSubmodule_of_iso k hs hgood e o hd⟩

end Dichotomy

end TauCeti
