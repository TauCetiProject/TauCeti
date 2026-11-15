/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.BadCharacteristic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.BadCharacteristic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CharacteristicFive
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CharacteristicThree
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Preprojective.PathAlgebra
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.Tree

/-!
# Classification of positive-degree cyclic quotients of preprojective algebras

For a finite connected simple graph `G` oriented by `o`, let `Π = Π_k(OrientedQuiver G o)` be its
additive preprojective algebra over a field `k`, graded by path length. Its cyclic quotient
`Π / [Π, Π]` is zeroth Hochschild homology; when `G` is a tree, Liu and Wang identify its
degree-`(q + 2)` piece with the second Hochschild cohomology `HH^{2,q}` of the two-dimensional
Ginzburg dg algebra, which governs minimal `A∞` deformations of the zigzag algebra of `G`.

This file assembles the type-by-type calculations for `A`, `D` and `E`, the bad-characteristic
obstruction classes in degrees `4`, `6` and `10`, the affine-subgraph trace classes on non-Dynkin
trees, and the closed-path trace on non-acyclic graphs into a complete characterization: the
cyclic quotient vanishes in all degrees `d ≥ 3` — equivalently, in all positive degrees `d > 0` —
if and only if `G` is isomorphic to the diagram of a valid simply-laced Dynkin type `t` and
`ringChar k` is not a bad prime for `t` (`TauCeti.IsBadPrime`): `2` for `Dₙ`, `2` or `3` for `E₆`
and `E₇`, `2`, `3` or `5` for `E₈`, and none for `Aₙ`. For finite trees the same equivalence holds
for the signless preprojective algebra `Π⁺_k(DoubledQuiver G)`.

## Main definitions

* `TauCeti.IsBadPrime`: the bad primes of a simply-laced Dynkin type (`2` for `Dₙ`, `2, 3` for
  `E₆, E₇`, `2, 3, 5` for `E₈`, and none otherwise).

## Main results

* `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso` and
  `TauCeti.preprojectiveGrade_le_commutatorSubmodule_of_iso`: over a field whose characteristic is
  not bad for a simply-laced Dynkin type `t`, every positive-degree piece of the signless or
  additive preprojective algebra of a graph isomorphic to `diagramGraph t.cartanMatrix` lies in the
  commutator submodule.
* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime` and
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime`: over any
  nontrivial commutative ring whose characteristic is bad for a valid Dynkin type `t`, a nonzero
  cyclic class exists in path degree `4`, `6` or `10`.
* `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_exists_dynkinType_iso`:
  for any connected finite simple graph not isomorphic to a valid Dynkin diagram, every orientation
  has a nonzero cyclic class of degree at least `3` over every nontrivial commutative ring.
* `TauCeti.forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff` and
  `TauCeti.forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff`: **the complete vanishing
  characterization for connected finite simple graphs.**
* `TauCeti.forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff` and
  `TauCeti.forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff`: **the corresponding
  characterization for the signless preprojective algebra of a finite tree.**

## References

* P. Etingof and C.-H. Eu, *Hochschild and cyclic homology of preprojective algebras of ADE
  quivers*, Mosc. Math. J. 7 (2007), https://arxiv.org/abs/math/0609006.
* T. Schedler, *Deformations of algebras in noncommutative geometry*, Section 13.1, Theorem 13.1.1,
  https://arxiv.org/abs/1212.0914.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  Theorem 1.1 and Corollary 3.4, https://arxiv.org/abs/2301.06757.
-/

public section

namespace TauCeti

open DoubledQuiver PathAlgebra

/-! ### Bad primes of simply-laced Dynkin types -/

/-- The primes that are **bad** for a simply-laced finite Dynkin type in the sense of Schedler,
Theorem 13.1.1, and Liu--Wang, Theorem 1.1: `2` for `Dₙ`, `2` and `3` for `E₆` and `E₇`, `2`, `3`
and `5` for `E₈`, and none for `Aₙ`. On the non-simply-laced constructors `B`, `C`, `F₄` and `G₂`
(which are excluded by `DynkinType.IsSimplyLaced` in the classification statements) the predicate
is `False`. Characteristic `0` is never bad. -/
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

/-- In type `Dₙ`, only `2` is a bad prime. -/
@[simp]
theorem isBadPrime_D (n p : ℕ) : IsBadPrime (.D n) p ↔ p = 2 :=
  (Iff.rfl)

/-- In type `E₆`, the bad primes are `2` and `3`. -/
@[simp]
theorem isBadPrime_E6 (p : ℕ) : IsBadPrime .E6 p ↔ p = 2 ∨ p = 3 :=
  (Iff.rfl)

/-- In type `E₇`, the bad primes are `2` and `3`. -/
@[simp]
theorem isBadPrime_E7 (p : ℕ) : IsBadPrime .E7 p ↔ p = 2 ∨ p = 3 :=
  (Iff.rfl)

/-- In type `E₈`, the bad primes are `2`, `3` and `5`. -/
@[simp]
theorem isBadPrime_E8 (p : ℕ) : IsBadPrime .E8 p ↔ p = 2 ∨ p = 3 ∨ p = 5 :=
  (Iff.rfl)

/-- Type `Aₙ` has no bad primes. -/
@[simp]
theorem not_isBadPrime_A (n p : ℕ) : ¬ IsBadPrime (.A n) p :=
  id

/-- `IsBadPrime` is `False` on `Bₙ`. -/
@[simp]
theorem not_isBadPrime_B (n p : ℕ) : ¬ IsBadPrime (.B n) p :=
  id

/-- `IsBadPrime` is `False` on `Cₙ`. -/
@[simp]
theorem not_isBadPrime_C (n p : ℕ) : ¬ IsBadPrime (.C n) p :=
  id

/-- `IsBadPrime` is `False` on `F₄`. -/
@[simp]
theorem not_isBadPrime_F4 (p : ℕ) : ¬ IsBadPrime .F4 p :=
  id

/-- `IsBadPrime` is `False` on `G₂`. -/
@[simp]
theorem not_isBadPrime_G2 (p : ℕ) : ¬ IsBadPrime .G2 p :=
  id

instance instDecidableRelIsBadPrime : DecidableRel IsBadPrime
  | .D n, p => decidable_of_iff (p = 2) (isBadPrime_D n p).symm
  | .E6, p => decidable_of_iff (p = 2 ∨ p = 3) (isBadPrime_E6 p).symm
  | .E7, p => decidable_of_iff (p = 2 ∨ p = 3) (isBadPrime_E7 p).symm
  | .E8, p => decidable_of_iff (p = 2 ∨ p = 3 ∨ p = 5) (isBadPrime_E8 p).symm
  | .A n, p => isFalse (not_isBadPrime_A n p)
  | .B n, p => isFalse (not_isBadPrime_B n p)
  | .C n, p => isFalse (not_isBadPrime_C n p)
  | .F4, p => isFalse (not_isBadPrime_F4 p)
  | .G2, p => isFalse (not_isBadPrime_G2 p)

/-- Characteristic `0` is never bad for any Dynkin type. -/
@[simp]
theorem not_isBadPrime_zero (t : DynkinType) : ¬ IsBadPrime t 0 := by
  cases t <;> simp

/-- `1` is never a bad prime for any Dynkin type. -/
@[simp]
theorem not_isBadPrime_one (t : DynkinType) : ¬ IsBadPrime t 1 := by
  cases t <;> simp

/-- Every number strictly greater than `5` (in particular every prime `p ≥ 7`) is good for every
Dynkin type. -/
theorem not_isBadPrime_of_gt_five (t : DynkinType) {p : ℕ} (hp : 5 < p) : ¬ IsBadPrime t p := by
  cases t <;> simp <;> omega

/-- Every Dynkin type admitting a bad prime is simply laced. -/
theorem IsBadPrime.isSimplyLaced {t : DynkinType} {p : ℕ} (h : IsBadPrime t p) :
    t.IsSimplyLaced := by
  cases t <;> simp_all

/-- Every bad prime is indeed a prime number (`2`, `3` or `5`). -/
theorem IsBadPrime.prime {t : DynkinType} {p : ℕ} (h : IsBadPrime t p) : p.Prime := by
  cases t <;> simp only [isBadPrime_D, isBadPrime_E6, isBadPrime_E7, isBadPrime_E8,
    not_isBadPrime_A, not_isBadPrime_B, not_isBadPrime_C, not_isBadPrime_F4,
    not_isBadPrime_G2] at h
  · exact h ▸ Nat.prime_two
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

/-! ### Auxiliary characteristic and isomorphism lemmas -/

private theorem natCast_eq_zero_iff_ringChar_eq (k : Type*) [NonAssocSemiring k] [Nontrivial k]
    {p : ℕ} (hp : p.Prime) : (p : k) = 0 ↔ ringChar k = p := by
  rw [ringChar.spec, hp.dvd_iff_eq (CharP.char_ne_one k (ringChar k)), eq_comm]

private theorem isUnit_of_ringChar_ne (k : Type*) [Field k] {p : ℕ} (hp : p.Prime)
    (hne : ringChar k ≠ p) : IsUnit (p : k) :=
  isUnit_iff_ne_zero.mpr fun h => hne ((natCast_eq_zero_iff_ringChar_eq k hp).mp h)

private theorem exists_signless_notMem_commutator_of_iso (k : Type*) [CommRing k] {V W : Type*}
    [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    [∀ i, Fintype (G.neighborSet i)] [∀ j, Fintype (H.neighborSet j)] (e : G ≃g H) {d : ℕ}
    (hH : ∃ z ∈ signlessPreprojectiveGrade k (DoubledQuiver H) d,
      z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H))) :
    ∃ z ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain ⟨z, hz, hz0⟩ := hH
  by_contra! hall
  exact hz0 ((signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso k e d).mp hall hz)

/-! ### Good-characteristic vanishing on ADE diagrams -/

section GoodCharacteristic

attribute [local instance] SimpleGraph.neighborSetFintypeOfFinite

/-- **Over a field whose characteristic is not bad for a simply-laced Dynkin type `t`, the cyclic
quotient of the signless preprojective algebra of any graph isomorphic to
`diagramGraph t.cartanMatrix` vanishes in all positive degrees.** -/
theorem signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso (k : Type*) [Field k]
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    {t : DynkinType} (hsl : t.IsSimplyLaced) (e : G ≃g diagramGraph t.cartanMatrix)
    (ht : ¬ IsBadPrime t (ringChar k)) {d : ℕ} (hd : 0 < d) :
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  refine (signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso k e d).mpr ?_
  cases t with
  | A n => exact signlessPreprojectiveGrade_A_le_commutatorSubmodule k hd
  | D n =>
    have h2 : IsUnit (2 : k) := by
      exact_mod_cast isUnit_of_ringChar_ne k Nat.prime_two ((isBadPrime_D n _).not.mp ht)
    exact signlessPreprojectiveGrade_D_le_commutatorSubmodule k h2 hd
  | E6 =>
    simp only [isBadPrime_E6, not_or] at ht
    have h2 : IsUnit (2 : k) := by exact_mod_cast isUnit_of_ringChar_ne k Nat.prime_two ht.1
    have h3 : IsUnit (3 : k) := by exact_mod_cast isUnit_of_ringChar_ne k Nat.prime_three ht.2
    exact signlessPreprojectiveGrade_E6_le_commutatorSubmodule k h2 h3 hd
  | E7 =>
    simp only [isBadPrime_E7, not_or] at ht
    have h2 : IsUnit (2 : k) := by exact_mod_cast isUnit_of_ringChar_ne k Nat.prime_two ht.1
    have h3 : IsUnit (3 : k) := by exact_mod_cast isUnit_of_ringChar_ne k Nat.prime_three ht.2
    exact signlessPreprojectiveGrade_E7_le_commutatorSubmodule k h2 h3 hd
  | E8 =>
    simp only [isBadPrime_E8, not_or] at ht
    have h2 : IsUnit (2 : k) := by exact_mod_cast isUnit_of_ringChar_ne k Nat.prime_two ht.1
    have h3 : IsUnit (3 : k) := by exact_mod_cast isUnit_of_ringChar_ne k Nat.prime_three ht.2.1
    have h5 : IsUnit (5 : k) := by exact_mod_cast isUnit_of_ringChar_ne k Nat.prime_five ht.2.2
    have key : ∀ H : SimpleGraph (Fin 8), zigzagE8Graph = H →
        signlessPreprojectiveGrade k (DoubledQuiver H) d ≤
          commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) := by
      rintro H rfl
      exact signlessPreprojectiveGrade_E8_le_commutatorSubmodule k h2 h3 h5 hd
    exact key _ zigzagE8Graph_eq_diagramGraph
  | B _ | C _ | F4 | G2 => simp at hsl

/-- **Over a field whose characteristic is not bad for a simply-laced Dynkin type `t`, the cyclic
quotient of the additive preprojective algebra of every orientation of a graph isomorphic to
`diagramGraph t.cartanMatrix` vanishes in all positive degrees.** -/
theorem preprojectiveGrade_le_commutatorSubmodule_of_iso (k : Type*) [Field k]
    {V : Type*} [Finite V] {G : SimpleGraph V} {t : DynkinType}
    (hsl : t.IsSimplyLaced) (e : G ≃g diagramGraph t.cartanMatrix)
    (ht : ¬ IsBadPrime t (ringChar k)) (o : Orientation G) {d : ℕ} (hd : 0 < d) :
    preprojectiveGrade k (OrientedQuiver G o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  have hb : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  exact (hb.preprojectiveGrade_le_commutatorSubmodule_iff k o d).mpr
    (signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k hsl e ht hd)

end GoodCharacteristic

/-! ### Bad-characteristic cyclic classes on ADE diagrams -/

section BadCharacteristic

attribute [local instance] SimpleGraph.neighborSetFintypeOfFinite

private theorem exists_signless_E_of_char_two_or_three (k : Type*) [CommRing k] [Nontrivial k]
    {n : ℕ} (hn : 6 ≤ n) {C : Matrix (Fin n) (Fin n) ℤ} (hC : C = CartanMatrix.E n)
    (hchar : ringChar k = 2 ∨ ringChar k = 3) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ),
      ∃ z ∈ signlessPreprojectiveGrade k (DoubledQuiver (diagramGraph C)) d,
        z ∉ commutatorSubmodule k
          (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph C))) := by
  subst hC
  rcases hchar with h2 | h3
  · have h2' : (2 : k) = 0 := by
      exact_mod_cast (natCast_eq_zero_iff_ringChar_eq k Nat.prime_two).mpr h2
    exact ⟨4, by simp,
      exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule k (by omega) h2'⟩
  · have h3' : (3 : k) = 0 := by
      exact_mod_cast (natCast_eq_zero_iff_ringChar_eq k Nat.prime_three).mpr h3
    exact ⟨6, by simp,
      exists_mem_signlessPreprojectiveGrade_E_six_notMem_commutatorSubmodule k hn h3'⟩

/-- **Over any nontrivial commutative ring whose characteristic is bad for a valid Dynkin type `t`,
the signless preprojective algebra of any graph isomorphic to `diagramGraph t.cartanMatrix` has a
homogeneous element of degree `4`, `6` or `10` outside the commutator submodule.** -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
    (k : Type*) [CommRing k] [Nontrivial k] {V : Type*} [Finite V] {G : SimpleGraph V}
    [∀ i, Fintype (G.neighborSet i)] {t : DynkinType} (ht : t.Valid)
    (e : G ≃g diagramGraph t.cartanMatrix) (hbad : IsBadPrime t (ringChar k)) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ),
      ∃ z ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
        z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  suffices ∃ d ∈ ({4, 6, 10} : Finset ℕ),
      ∃ z ∈ signlessPreprojectiveGrade k (DoubledQuiver (diagramGraph t.cartanMatrix)) d,
        z ∉ commutatorSubmodule k
          (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph t.cartanMatrix))) by
    obtain ⟨d, hd, hH⟩ := this
    exact ⟨d, hd, exists_signless_notMem_commutator_of_iso k e hH⟩
  cases t with
  | A _ | B _ | C _ | F4 | G2 => simp at hbad
  | D n =>
    have hn : 4 ≤ n := DynkinType.valid_D.mp ht
    have h2 : (2 : k) = 0 := by
      exact_mod_cast
        (natCast_eq_zero_iff_ringChar_eq k Nat.prime_two).mpr ((isBadPrime_D n _).mp hbad)
    exact ⟨4, by simp,
      exists_mem_signlessPreprojectiveGrade_D_four_notMem_commutatorSubmodule k hn h2⟩
  | E6 =>
    exact exists_signless_E_of_char_two_or_three k (n := 6) (by decide)
      DynkinType.cartanMatrix_E6 ((isBadPrime_E6 _).mp hbad)
  | E7 =>
    exact exists_signless_E_of_char_two_or_three k (n := 7) (by decide)
      DynkinType.cartanMatrix_E7 ((isBadPrime_E7 _).mp hbad)
  | E8 =>
    rcases (isBadPrime_E8 _).mp hbad with h2 | h3 | h5
    · exact exists_signless_E_of_char_two_or_three k (n := 8) (by decide)
        DynkinType.cartanMatrix_E8 (.inl h2)
    · exact exists_signless_E_of_char_two_or_three k (n := 8) (by decide)
        DynkinType.cartanMatrix_E8 (.inr h3)
    · have h5' : (5 : k) = 0 := by
        exact_mod_cast (natCast_eq_zero_iff_ringChar_eq k Nat.prime_five).mpr h5
      refine ⟨10, by simp, ?_⟩
      have key : ∀ H : SimpleGraph (Fin 8), zigzagE8Graph = H →
          ∃ z ∈ signlessPreprojectiveGrade k (DoubledQuiver H) 10,
            z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) := by
        rintro H rfl
        exact ⟨_, signlessWord_E8_cyclicWord_mem_grade_ten k,
          signlessWord_E8_cyclicWord_notMem_commutatorSubmodule k h5'⟩
      exact key _ zigzagE8Graph_eq_diagramGraph

/-- **Over any nontrivial commutative ring whose characteristic is bad for a valid Dynkin type `t`,
the additive preprojective algebra of every orientation of a graph isomorphic to
`diagramGraph t.cartanMatrix` has a homogeneous element of degree `4`, `6` or `10` outside the
commutator submodule.** -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
    (k : Type*) [CommRing k] [Nontrivial k] {V : Type*} [Finite V] {G : SimpleGraph V}
    {t : DynkinType} (ht : t.Valid) (e : G ≃g diagramGraph t.cartanMatrix)
    (hbad : IsBadPrime t (ringChar k)) (o : Orientation G) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ),
      ∃ z ∈ preprojectiveGrade k (OrientedQuiver G o) d,
        z ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  have hb : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  obtain ⟨d, hd, z, hz, hz0⟩ :=
    exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k ht e hbad
  refine ⟨d, hd, ?_⟩
  by_contra! hall
  exact hz0 ((hb.preprojectiveGrade_le_commutatorSubmodule_iff k o d).mp hall hz)

end BadCharacteristic

/-! ### Non-Dynkin connected graphs and the complete classification -/

/-- **Every connected finite non-Dynkin simple graph has a nonzero cyclic class of degree at least
three** in the additive preprojective algebra of every orientation, over every nontrivial
commutative ring. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_exists_dynkinType_iso
    (k : Type*) [CommRing k] [Nontrivial k] {V : Type*} [Finite V] {G : SimpleGraph V}
    (hG : G.Connected)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix))
    (o : Orientation G) :
    ∃ d : ℕ, 3 ≤ d ∧ ∃ z ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      z ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  by_cases hac : G.IsAcyclic
  · classical
    have : Fintype V := Fintype.ofFinite V
    have htree : G.IsTree := ⟨hG, hac⟩
    obtain ⟨d, hd, z, hz, hz0⟩ :=
      htree.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule (k := k) hD
    have hd3 : 3 ≤ d := by simp at hd; omega
    refine ⟨d, hd3, ?_⟩
    by_contra! hall
    exact hz0 ((hac.isBipartite.preprojectiveGrade_le_commutatorSubmodule_iff k o d).mp hall hz)
  · exact exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic k hac o

/-- **Classification of preprojective cyclic quotients vanishing in degrees `d ≥ 3`** (Schedler,
Theorem 13.1.1; Liu--Wang, Corollary 3.4). For a connected finite simple graph `G`, an orientation
`o` of `G`, and a field `k`, every graded piece `Π_d` of path degree `d ≥ 3` lies in the commutator
submodule `[Π, Π]` if and only if `G` is isomorphic to the diagram of a valid simply-laced Dynkin
type `t` and `ringChar k` is not a bad prime for `t`. -/
theorem forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff
    (k : Type*) [Field k] {V : Type*} [Finite V] {G : SimpleGraph V}
    (hG : G.Connected) (o : Orientation G) :
    (∀ d : ℕ, 3 ≤ d →
      preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
    ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
      Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) := by
  constructor
  · intro hvan
    have hDyn : ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) := by
      by_contra hD
      obtain ⟨d, hd, z, hz, hz0⟩ :=
        exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_exists_dynkinType_iso
          k hG hD o
      exact hz0 (hvan d hd hz)
    obtain ⟨t, ht, hsl, ⟨e⟩⟩ :=
      (SimpleGraph.exists_valid_isSimplyLaced_dynkinType_iso_iff G).mpr hDyn
    refine ⟨t, ht, hsl, ⟨e⟩, fun hbad => ?_⟩
    obtain ⟨d, hd, z, hz, hz0⟩ :=
      exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k ht e hbad o
    have hd3 : 3 ≤ d := by simp at hd; omega
    exact hz0 (hvan d hd3 hz)
  · rintro ⟨t, -, hsl, ⟨e⟩, hgood⟩ d hd
    exact preprojectiveGrade_le_commutatorSubmodule_of_iso k hsl e hgood o (by omega)

/-- **Classification of preprojective cyclic quotients vanishing in all positive degrees.** For a
connected finite simple graph `G`, an orientation `o` of `G`, and a field `k`, every graded piece
`Π_d` of path degree `d > 0` lies in the commutator submodule `[Π, Π]` if and only if `G` is
isomorphic to the diagram of a valid simply-laced Dynkin type `t` and `ringChar k` is not a bad
prime for `t`. -/
theorem forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff
    (k : Type*) [Field k] {V : Type*} [Finite V] {G : SimpleGraph V}
    (hG : G.Connected) (o : Orientation G) :
    (∀ d : ℕ, 0 < d →
      preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
    ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
      Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) := by
  refine ⟨fun hvan => (forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff k hG o).mp
    fun d hd => hvan d (by omega), ?_⟩
  rintro ⟨t, -, hsl, ⟨e⟩, hgood⟩ d hd
  exact preprojectiveGrade_le_commutatorSubmodule_of_iso k hsl e hgood o hd

/-- **Classification of signless preprojective cyclic quotients of finite trees in degrees
`d ≥ 3`.** -/
theorem forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff
    (k : Type*) [Field k] {V : Type*} [Finite V] {G : SimpleGraph V}
    [∀ i, Fintype (G.neighborSet i)] (hG : G.IsTree) :
    (∀ d : ℕ, 3 ≤ d →
      signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
    ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
      Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) := by
  let hb : G.IsBipartite := hG.isAcyclic.isBipartite
  let o := hb.coloringBool.sourceSink
  rw [← forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff k hG.connected o]
  exact forall₂_congr fun d _ => (hb.preprojectiveGrade_le_commutatorSubmodule_iff k o d).symm

/-- **Classification of signless preprojective cyclic quotients of finite trees in all positive
degrees.** -/
theorem forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff
    (k : Type*) [Field k] {V : Type*} [Finite V] {G : SimpleGraph V}
    [∀ i, Fintype (G.neighborSet i)] (hG : G.IsTree) :
    (∀ d : ℕ, 0 < d →
      signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
    ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
      Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) := by
  let hb : G.IsBipartite := hG.isAcyclic.isBipartite
  let o := hb.coloringBool.sourceSink
  rw [← forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff k hG.connected o]
  exact forall₂_congr fun d _ => (hb.preprojectiveGrade_le_commutatorSubmodule_iff k o d).symm

end TauCeti
