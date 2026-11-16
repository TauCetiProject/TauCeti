/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BadPrime
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
public import TauCeti.RepresentationTheory.Quiver.Preprojective.CyclicQuotient
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Span
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

Over a nontrivial commutative ring `k`, for a connected finite simple graph `G`, the graded piece
of degree `d` of the cyclic quotient `Π⁺(G) / [Π⁺(G), Π⁺(G)]` vanishes for all `d ≥ 3`
(equivalently, for all `d > 0`) if and only if `G` is isomorphic to the diagram of a valid
simply-laced Dynkin type `t` whose bad primes (`TauCeti.DynkinType.IsBadPrime`) are all invertible
in `k`:

* no bad primes for `Aₙ`;
* `2` for `Dₙ` (`n ≥ 4`);
* `2` and `3` for `E₆` and `E₇`;
* `2`, `3` and `5` for `E₈`.

Over a field `k`, invertibility of every bad prime of `t` is equivalent to `¬ t.IsBadPrime
(ringChar k)` (`TauCeti.DynkinType.forall_isBadPrime_isUnit_iff_not_isBadPrime_ringChar`). The
same characterization holds for the additive preprojective algebra `Π_k(OrientedQuiver G o)` of
every orientation `o` of `G`.

The threshold `d ≥ 3` is singled out alongside `d > 0` because in zigzag deformation theory,
path degree `d = q + 2 ≥ 3` of the cyclic quotient feeds the Hochschild cohomology group
`HH^{2, q}` of the 2-Calabi--Yau Ginzburg dg algebra for `q > 0`, governing intrinsic formality of
the corresponding zigzag algebra.

## Main results

* `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso` and
  `TauCeti.preprojectiveGrade_le_commutatorSubmodule_of_iso`: when every bad prime of a
  simply-laced Dynkin diagram is invertible in `k`, every positive-degree graded piece of its
  preprojective algebra lies in the commutator submodule.
* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime` and
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime`: when a bad
  prime of a valid simply-laced Dynkin diagram is not invertible in `k`, there is a nonzero cyclic
  class of degree at least `3`.
* `exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_exists_dynkinType_iso`
  and `exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_exists_dynkinType_iso`:
  every connected finite non-Dynkin graph has a nonzero cyclic class of degree at least `3`.
* `TauCeti.forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff`,
  `TauCeti.forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff`,
  `TauCeti.forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff`, and
  `TauCeti.forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff`: **the complete
  positive-degree cyclic quotient dichotomy for connected finite simple graphs over a nontrivial
  commutative ring**, together with their field specializations
  `TauCeti.forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_field`,
  `TauCeti.forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_field`,
  `TauCeti.forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff_of_field`, and
  `TauCeti.forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff_of_field`.

## References

* P. Etingof and C.-H. Eu, *Hochschild and cyclic homology of preprojective algebras of ADE
  quivers*, Mosc. Math. J. 7 (2007), https://arxiv.org/abs/math/0609006.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, Corollary 3.4 (with Theorem 1.1 and Proposition 3.2 for the
  intrinsic formality context).
* T. Schedler, *Zeroth Hochschild homology of preprojective algebras over the integers*,
  https://arxiv.org/abs/0704.3278, Theorem 13.1.1.
-/

public section

namespace TauCeti

open DoubledQuiver

attribute [local instance] SimpleGraph.neighborSetFintypeOfFinite

/-! ### Good-characteristic vanishing for simply-laced Dynkin diagrams -/

section GoodCharacteristic

variable (k : Type*) [CommRing k]

/-- **When every bad prime is invertible, the positive-degree cyclic quotient of the signless
preprojective algebra of a simply-laced Dynkin diagram vanishes.** -/
theorem signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso {V : Type*} [Finite V]
    {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] {t : DynkinType}
    (hs : t.IsSimplyLaced) (hgood : ∀ p, t.IsBadPrime p → IsUnit (p : k))
    (e : G ≃g diagramGraph t.cartanMatrix) {d : ℕ} (hd : 0 < d) :
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  cases t with
  | A n =>
    exact (signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso k e d).mpr
      (signlessPreprojectiveGrade_A_le_commutatorSubmodule k hd)
  | D n =>
    have h2 : IsUnit (2 : k) := by simpa using hgood 2 (by simp)
    exact (signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso k e d).mpr
      (signlessPreprojectiveGrade_D_le_commutatorSubmodule k h2 hd)
  | E6 =>
    have h2 : IsUnit (2 : k) := by simpa using hgood 2 (by simp)
    have h3 : IsUnit (3 : k) := by simpa using hgood 3 (by simp)
    exact (signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso k e d).mpr
      (signlessPreprojectiveGrade_E6_le_commutatorSubmodule k h2 h3 hd)
  | E7 =>
    have h2 : IsUnit (2 : k) := by simpa using hgood 2 (by simp)
    have h3 : IsUnit (3 : k) := by simpa using hgood 3 (by simp)
    exact (signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso k e d).mpr
      (signlessPreprojectiveGrade_E7_le_commutatorSubmodule k h2 h3 hd)
  | E8 =>
    have h2 : IsUnit (2 : k) := by simpa using hgood 2 (by simp)
    have h3 : IsUnit (3 : k) := by simpa using hgood 3 (by simp)
    have h5 : IsUnit (5 : k) := by simpa using hgood 5 (by simp)
    rw [← zigzagE8Graph_eq_diagramGraph] at e
    change G ≃g zigzagE8Graph at e
    exact (signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso k e d).mpr
      (signlessPreprojectiveGrade_E8_le_commutatorSubmodule k h2 h3 h5 hd)
  | B n | C n | F4 | G2 => simp at hs

/-- **When every bad prime is invertible, the positive-degree cyclic quotient of the preprojective
algebra of every orientation of a simply-laced Dynkin diagram vanishes.** -/
theorem preprojectiveGrade_le_commutatorSubmodule_of_iso {V : Type*} [Finite V]
    {G : SimpleGraph V} {t : DynkinType}
    (hs : t.IsSimplyLaced) (hgood : ∀ p, t.IsBadPrime p → IsUnit (p : k))
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

private theorem exists_not_le_signlessPreprojectiveGrade_E_of_two_or_three
    [Nontrivial k] {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    {n p : ℕ} (hn : 6 ≤ n) (hp : p = 2 ∨ p = 3) (hp0 : (p : k) = 0)
    (e : G ≃g diagramGraph (CartanMatrix.E n)) :
    ∃ d, 3 ≤ d ∧ ¬ (signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) := by
  rcases hp with rfl | rfl
  · exact ⟨4, by omega,
      (signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso k e 4).not.mpr
        (IsConcreteLE.not_le_iff_exists.mpr
          (exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule
            k (by omega) (by simpa using hp0)))⟩
  · exact ⟨6, by omega,
      (signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso k e 6).not.mpr
        (IsConcreteLE.not_le_iff_exists.mpr
          (exists_mem_signlessPreprojectiveGrade_E_six_notMem_commutatorSubmodule
            k hn (by simpa using hp0)))⟩

private theorem exists_not_le_signlessPreprojectiveGrade_of_isBadPrime_of_eq_zero
    [Nontrivial k] {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    {t : DynkinType} (ht : t.Valid) (hs : t.IsSimplyLaced)
    {p : ℕ} (hp : t.IsBadPrime p) (hp0 : (p : k) = 0)
    (e : G ≃g diagramGraph t.cartanMatrix) :
    ∃ d, 3 ≤ d ∧ ¬ (signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) := by
  cases t with
  | A n => exact absurd hp (DynkinType.not_isBadPrime_A n p)
  | D n =>
    obtain rfl : p = 2 := (DynkinType.isBadPrime_D_iff n p).mp hp
    exact ⟨4, by omega,
      (signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso k e 4).not.mpr
        (IsConcreteLE.not_le_iff_exists.mpr
          (exists_mem_signlessPreprojectiveGrade_D_four_notMem_commutatorSubmodule k
            (DynkinType.valid_D.mp ht) (by simpa using hp0)))⟩
  | E6 =>
    rw [DynkinType.cartanMatrix_E6] at e
    exact exists_not_le_signlessPreprojectiveGrade_E_of_two_or_three k (n := 6) (by omega)
      ((DynkinType.isBadPrime_E6_iff p).mp hp) hp0 e
  | E7 =>
    rw [DynkinType.cartanMatrix_E7] at e
    exact exists_not_le_signlessPreprojectiveGrade_E_of_two_or_three k (n := 7) (by omega)
      ((DynkinType.isBadPrime_E7_iff p).mp hp) hp0 e
  | E8 =>
    rcases or_assoc.mpr ((DynkinType.isBadPrime_E8_iff p).mp hp) with h23 | rfl
    · rw [DynkinType.cartanMatrix_E8] at e
      exact exists_not_le_signlessPreprojectiveGrade_E_of_two_or_three k (n := 8) (by omega)
        h23 hp0 e
    · rw [← zigzagE8Graph_eq_diagramGraph] at e
      change G ≃g zigzagE8Graph at e
      refine ⟨10, by omega,
        (signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso k e 10).not.mpr fun h =>
          signlessWord_E8_cyclicWord_notMem_commutatorSubmodule k (by simpa using hp0)
            (h (signlessWord_E8_cyclicWord_mem_grade_ten k))⟩
  | B n | C n | F4 | G2 => simp at hs

/-- **When a bad prime of a valid simply-laced Dynkin diagram is not invertible, the preprojective
algebra of every orientation has a nonzero cyclic class of degree at least three**, over every
commutative ring. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
    {V : Type*} [Finite V] {G : SimpleGraph V}
    {t : DynkinType} (ht : t.Valid) (hs : t.IsSimplyLaced)
    {p : ℕ} (hp : t.IsBadPrime p) (hpu : ¬ IsUnit (p : k))
    (e : G ≃g diagramGraph t.cartanMatrix) (o : Orientation G) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  let I : Ideal k := Ideal.span {(p : k)}
  have hI : I ≠ ⊤ := mt Ideal.span_singleton_eq_top.mp hpu
  have : Nontrivial (k ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hp0 : (p : k ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  obtain ⟨d, hd, hnot⟩ :=
    exists_not_le_signlessPreprojectiveGrade_of_isBadPrime_of_eq_zero (k ⧸ I) ht hs hp hp0 e
  have hb : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  have hnotO : ¬ (preprojectiveGrade (k ⧸ I) (OrientedQuiver G o) d ≤
      commutatorSubmodule (k ⧸ I) (preprojectiveAlgebra (k ⧸ I) (OrientedQuiver G o))) :=
    (hb.preprojectiveGrade_le_commutatorSubmodule_iff (k ⧸ I) o d).not.mpr hnot
  refine ⟨d, hd, IsConcreteLE.not_le_iff_exists.mp fun hk => hnotO ?_⟩
  let _ : Fintype (OrientedQuiver G o) := OrientedQuiver.instFintypeOfFinite G o
  exact preprojectiveGrade_le_commutatorSubmodule_of_ringHom k (Ideal.Quotient.mk I) d hk

/-- **When a bad prime of a valid simply-laced Dynkin diagram is not invertible, the signless
preprojective algebra has a nonzero cyclic class of degree at least three**, over every commutative
ring. -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    {t : DynkinType} (ht : t.Valid) (hs : t.IsSimplyLaced)
    {p : ℕ} (hp : t.IsBadPrime p) (hpu : ¬ IsUnit (p : k))
    (e : G ≃g diagramGraph t.cartanMatrix) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  have hb : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  let o : Orientation G := hb.coloringBool.sourceSink
  obtain ⟨d, hd, hx⟩ :=
    exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k ht hs hp hpu e o
  exact ⟨d, hd, IsConcreteLE.not_le_iff_exists.mp
    ((hb.preprojectiveGrade_le_commutatorSubmodule_iff k o d).not.mp
      (IsConcreteLE.not_le_iff_exists.mpr hx))⟩

end BadCharacteristic

/-! ### Non-Dynkin connected finite graphs -/

section NonDynkin

variable (k : Type*) [CommRing k] [Nontrivial k]

/-- **Every connected finite non-Dynkin graph has a nonzero cyclic class of degree at least three**
in its signless preprojective algebra, over every nontrivial commutative ring. -/
theorem
exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_exists_dynkinType_iso
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
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_exists_dynkinType_iso
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.Connected)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix))
    (o : Orientation G) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  by_cases hacyc : G.IsAcyclic
  · have hb : G.IsBipartite := hacyc.isBipartite
    obtain ⟨d, hd, hx⟩ :=
      exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_exists_dynkinType_iso
        k hG hD
    exact ⟨d, hd, IsConcreteLE.not_le_iff_exists.mp
      ((hb.preprojectiveGrade_le_commutatorSubmodule_iff k o d).not.mpr
        (IsConcreteLE.not_le_iff_exists.mpr hx))⟩
  · exact exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic k hacyc o

end NonDynkin

/-! ### The complete positive-degree cyclic quotient dichotomy -/

section Dichotomy

section CommRing

variable (k : Type*) [CommRing k] [Nontrivial k]

/-- **The cyclic quotient dichotomy in degrees at least three for signless preprojective algebras**:
for a connected finite simple graph `G` and a nontrivial commutative ring `k`, every graded piece
of degree `d ≥ 3` of `Π⁺(G)` lies in the commutator submodule if and only if `G` is isomorphic to
the diagram of a valid simply-laced Dynkin type whose bad primes are all invertible in `k`. -/
theorem forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    (hG : G.Connected) :
    (∀ d, 3 ≤ d → signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ∀ p, t.IsBadPrime p → IsUnit (p : k) := by
  refine ⟨fun hvan => ?_, fun ⟨t, _, hs, ⟨e⟩, hgood⟩ d hd =>
    signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k hs hgood e (by omega)⟩
  by_cases hD : ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)
  · obtain ⟨t, ht, hs, ⟨e⟩⟩ := (SimpleGraph.exists_valid_isSimplyLaced_dynkinType_iso_iff G).mpr hD
    refine ⟨t, ht, hs, ⟨e⟩, fun p hp => by_contra fun hpu => ?_⟩
    obtain ⟨d, hd, x, hx, hx0⟩ :=
      exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
        k ht hs hp hpu e
    exact hx0 (hvan d hd hx)
  · obtain ⟨d, hd, x, hx, hx0⟩ :=
      exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_exists_dynkinType_iso
        k hG hD
    exact absurd (hvan d hd hx) hx0

/-- **The positive-degree cyclic quotient dichotomy for signless preprojective algebras**: for a
connected finite simple graph `G` and a nontrivial commutative ring `k`, every positive-degree
graded piece of `Π⁺(G)` lies in the commutator submodule if and only if `G` is isomorphic to the
diagram of a valid simply-laced Dynkin type whose bad primes are all invertible in `k`. -/
theorem forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    (hG : G.Connected) :
    (∀ d, 0 < d → signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ∀ p, t.IsBadPrime p → IsUnit (p : k) :=
  ⟨fun h =>
    (forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff k hG).mp
      fun d hd => h d (by omega),
   fun ⟨_, _, hs, ⟨e⟩, hgood⟩ _ hd =>
    signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k hs hgood e hd⟩

/-- **The cyclic quotient dichotomy in degrees at least three for preprojective algebras of oriented
graphs**: for a connected finite simple graph `G`, an orientation `o` of `G`, and a nontrivial
commutative ring `k`, every graded piece of degree `d ≥ 3` of `Π_k(OrientedQuiver G o)` lies in
the commutator submodule if and only if `G` is isomorphic to the diagram of a valid simply-laced
Dynkin type whose bad primes are all invertible in `k`. -/
theorem forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.Connected) (o : Orientation G) :
    (∀ d, 3 ≤ d → preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ∀ p, t.IsBadPrime p → IsUnit (p : k) := by
  constructor
  · intro hvan
    have hD : ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) :=
      by_contra fun hnot => by
        obtain ⟨d, hd, x, hx, hx0⟩ :=
          exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_exists_dynkinType_iso
            k hG hnot o
        exact hx0 (hvan d hd hx)
    obtain ⟨t, ht, hs, ⟨e⟩⟩ := (SimpleGraph.exists_valid_isSimplyLaced_dynkinType_iso_iff G).mpr hD
    refine ⟨t, ht, hs, ⟨e⟩, fun p hp => by_contra fun hpu => ?_⟩
    obtain ⟨d, hd, x, hx, hx0⟩ :=
      exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k ht hs hp hpu e o
    exact hx0 (hvan d hd hx)
  · rintro ⟨t, -, hs, ⟨e⟩, hgood⟩ d hd
    exact preprojectiveGrade_le_commutatorSubmodule_of_iso k hs hgood e o (by omega)

/-- **The positive-degree cyclic quotient dichotomy for preprojective algebras of oriented graphs**:
for a connected finite simple graph `G`, an orientation `o` of `G`, and a nontrivial commutative
ring `k`, every positive-degree graded piece of `Π_k(OrientedQuiver G o)` lies in the commutator
submodule if and only if `G` is isomorphic to the diagram of a valid simply-laced Dynkin type whose
bad primes are all invertible in `k`. -/
theorem forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.Connected) (o : Orientation G) :
    (∀ d, 0 < d → preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ∀ p, t.IsBadPrime p → IsUnit (p : k) :=
  ⟨fun h =>
    (forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff k hG o).mp
      fun d hd => h d (by omega),
   fun ⟨_, _, hs, ⟨e⟩, hgood⟩ _ hd =>
    preprojectiveGrade_le_commutatorSubmodule_of_iso k hs hgood e o hd⟩

end CommRing

section Field

variable (k : Type*) [Field k]

/-- **The cyclic quotient dichotomy in degrees at least three for signless preprojective algebras
over a field**: every graded piece of degree `d ≥ 3` of `Π⁺(G)` lies in the commutator submodule if
and only if `G` is isomorphic to the diagram of a valid simply-laced Dynkin type for which
`ringChar k` is not a bad prime. -/
theorem forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_field
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    (hG : G.Connected) :
    (∀ d, 3 ≤ d → signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ t.IsBadPrime (ringChar k) := by
  rw [forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff k hG]
  simp only [DynkinType.forall_isBadPrime_isUnit_iff_not_isBadPrime_ringChar]

/-- **The positive-degree cyclic quotient dichotomy for signless preprojective algebras over a
field**: every positive-degree graded piece of `Π⁺(G)` lies in the commutator submodule if and only
if `G` is isomorphic to the diagram of a valid simply-laced Dynkin type for which `ringChar k` is
not a bad prime. -/
theorem forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_field
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    (hG : G.Connected) :
    (∀ d, 0 < d → signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ t.IsBadPrime (ringChar k) := by
  rw [forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff k hG]
  simp only [DynkinType.forall_isBadPrime_isUnit_iff_not_isBadPrime_ringChar]

/-- **The cyclic quotient dichotomy in degrees at least three for preprojective algebras of oriented
graphs over a field**: every graded piece of degree `d ≥ 3` of `Π_k(OrientedQuiver G o)` lies in
the commutator submodule if and only if `G` is isomorphic to the diagram of a valid simply-laced
Dynkin type for which `ringChar k` is not a bad prime. -/
theorem forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff_of_field
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.Connected) (o : Orientation G) :
    (∀ d, 3 ≤ d → preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ t.IsBadPrime (ringChar k) := by
  rw [forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff k hG o]
  simp only [DynkinType.forall_isBadPrime_isUnit_iff_not_isBadPrime_ringChar]

/-- **The positive-degree cyclic quotient dichotomy for preprojective algebras of oriented graphs
over a field**: every positive-degree graded piece of `Π_k(OrientedQuiver G o)` lies in the
commutator submodule if and only if `G` is isomorphic to the diagram of a valid simply-laced Dynkin
type for which `ringChar k` is not a bad prime. -/
theorem forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff_of_field
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.Connected) (o : Orientation G) :
    (∀ d, 0 < d → preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ t.IsBadPrime (ringChar k) := by
  rw [forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff k hG o]
  simp only [DynkinType.forall_isBadPrime_isUnit_iff_not_isBadPrime_ringChar]

end Field

end Dichotomy

end TauCeti
