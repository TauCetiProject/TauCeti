/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Basic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.SimpleGraph
public import TauCeti.RepresentationTheory.Quiver.Preprojective.CyclicQuotient
import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.CyclicQuotient
import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.BadCharacteristic
import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.BadCharacteristic
import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CharacteristicFive
import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CharacteristicThree
import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CyclicQuotient
import TauCeti.RepresentationTheory.Quiver.Preprojective.Cycle
import TauCeti.RepresentationTheory.Quiver.Preprojective.Isomorphism
import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.Tree

/-!
# The positive-degree cyclic quotient of preprojective algebras

For a finite connected simple graph `G`, an orientation `o` of `G`, and a field `k`, this file
determines when the positive-degree part of the cyclic quotient `Π / [Π, Π]` of the additive
preprojective algebra `Π = Π_k(OrientedQuiver G o)` (and of the signless preprojective algebra
`Π⁺(G)`) vanishes: every homogeneous piece of path degree `d ≥ 3` — equivalently every homogeneous
piece of positive path degree `d > 0` — lies in the commutator submodule `[Π, Π]` if and only if
`G` is isomorphic to the diagram `TauCeti.diagramGraph t.cartanMatrix` of a valid simply-laced
Dynkin type `t` and `ringChar k` is not a bad prime for `t` (`TauCeti.DynkinType.IsBadPrime`).

Through the Hochschild cohomology comparison `HH^{2, q}(Π₂(Q)) ≅ (Π / [Π, Π])_{q + 2}` for `q > 0`
(Liu--Wang, Proposition 3.2), the degree range `d ≥ 3` is the vanishing criterion for
obstruction-free minimal `A∞` deformations of the zigzag algebra of `G`. Both `[Field k]` and
`G.Connected` are sharp: over `ℤ` (`ringChar ℤ = 0`), the degree-four cyclic quotient on `D₄` has
`2`-torsion (`ℤ / 2ℤ ≠ 0`) because `2` is non-invertible, while a disconnected disjoint union of
ADE diagrams has vanishing positive-degree cyclic quotient without being isomorphic to a single
`diagramGraph t.cartanMatrix`.

## Proof architecture

* **Good characteristics on simply-laced Dynkin diagrams**
  (`TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso` and
  `TauCeti.preprojectiveGrade_le_commutatorSubmodule_of_iso`): when `t.IsSimplyLaced` and
  `¬ t.IsBadPrime (ringChar k)`, the primes listed for `t` are nonzero and hence invertible in `k`,
  so the normal-form calculations for types `A`, `D`, `E₆`, `E₇` and `E₈` show that every
  positive-degree graded piece lies in `[Π, Π]`.
* **Bad characteristics on valid ADE diagrams**
  (`TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime` and
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime`): when `t.Valid`
  and `t.IsBadPrime (ringChar k)`, the explicit cyclic classes constructed in types `Dₙ` (`n ≥ 4`,
  characteristic `2`, degree `4`), `Eₙ` (`n ≥ 5`, characteristic `2`, degree `4`), `Eₙ` (`n ≥ 6`,
  characteristic `3`, degree `6`), and `E₈` (characteristic `5`, degree `10`) transport along
  `G ≃g diagramGraph t.cartanMatrix`.
* **Connected non-Dynkin graphs**: if `G` is not acyclic,
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic` produces a
  nonzero cyclic class of degree `d ≥ 3` from a cycle copy; if `G` is acyclic, it is a non-Dynkin
  tree, and `SimpleGraph.IsTree.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule`
  produces a nonzero cyclic class in degree `4`, `6`, `8` or `12`, which transfers across
  bipartite sign rescaling to every orientation.

## Main definitions

* `TauCeti.DynkinType.IsBadPrime`: the bad primes for a simply-laced finite Dynkin type (`2` for
  `Dₙ`, `2` and `3` for `E₆` and `E₇`, `2`, `3` and `5` for `E₈`, and none otherwise).

## Main results

* `SimpleGraph.IsBipartite.preprojectiveGrade_le_commutatorSubmodule_iff`: for a bipartite finite
  simple graph, degree-`d` cyclic quotient vanishing for `Π_k(OrientedQuiver G o)` is equivalent to
  that for `Π⁺(G)`.
* `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso`,
  `TauCeti.preprojectiveGrade_le_commutatorSubmodule_of_iso`,
  `TauCeti.commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker_of_iso`,
  `TauCeti.finrank_cyclicQuotient_signlessPreprojectiveAlgebra_of_iso` and
  `TauCeti.finrank_cyclicQuotient_preprojectiveAlgebra_of_iso`: positive-degree vanishing,
  augmentation-kernel identification, and cyclic-quotient dimension `Nat.card V` on any graph
  isomorphic to a simply-laced Dynkin diagram outside bad characteristics.
* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime` and
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime`: nonzero cyclic
  classes in degree `4`, `6` or `10` at bad characteristics of valid Dynkin diagrams.
* `TauCeti.preprojective_cyclicQuotient_vanishes_iff` and
  `TauCeti.forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff`: **the complete
  characterization of positive-degree cyclic quotient vanishing for oriented connected finite simple
  graphs** (`d ≥ 3` and `d > 0`).
* `TauCeti.signlessPreprojective_cyclicQuotient_vanishes_iff` and
  `TauCeti.forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff`: the signless
  counterparts.

## References

* P. Etingof and C.-H. Eu, *Hochschild and cyclic homology of preprojective algebras of ADE
  quivers*, Mosc. Math. J. 7 (2007), https://arxiv.org/abs/math/0609006.
* T. Schedler, *Hochschild homology of preprojective algebras over the integers*, Adv. Math. 225
  (2010), Theorem 13.1.1, https://arxiv.org/abs/0704.3278.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  Theorem 1.1 and Corollary 3.4, https://arxiv.org/abs/2301.06757.
-/

public section

namespace SimpleGraph.IsBipartite

open TauCeti TauCeti.DoubledQuiver

/-- **For a bipartite finite simple graph, degree-`d` cyclic quotient vanishing is independent of
orientation and agrees with the signless presentation.** -/
theorem preprojectiveGrade_le_commutatorSubmodule_iff {V : Type*} [Finite V] {G : SimpleGraph V}
    (hb : G.IsBipartite) (k : Type*) [CommRing k] [inst : ∀ i, Fintype (G.neighborSet i)]
    (o : Orientation G) (d : ℕ) :
    preprojectiveGrade k (OrientedQuiver G o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) ↔
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  have hinst : inst = SimpleGraph.neighborSetFintypeOfFinite G := Subsingleton.elim _ _
  subst hinst
  let E := hb.signlessPreprojectiveAlgebraEquiv k o
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · have hEx := h (hb.signlessPreprojectiveAlgebraEquiv_mem_preprojectiveGrade k o hx)
    simpa only [E, AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule E.symm hEx
  · have hEx := h (hb.signlessPreprojectiveAlgebraEquiv_symm_mem_signlessPreprojectiveGrade k o hx)
    simpa only [E, AlgEquiv.apply_symm_apply] using map_mem_commutatorSubmodule E hEx

end SimpleGraph.IsBipartite

namespace TauCeti

namespace DynkinType

/-- The primes that are bad for the preprojective cyclic quotient and zigzag deformation theory of
a simply-laced finite Dynkin type (Schedler, Theorem 13.1.1; Liu--Wang, Theorem 1.1): `2` for `Dₙ`,
`2` and `3` for `E₆` and `E₇`, and `2`, `3` and `5` for `E₈`; type `A` (and the non-simply-laced
constructors, which do not occur in the simply-laced classification statements) have none.

On valid simply-laced types (`t.Valid ∧ t.IsSimplyLaced`, namely `Aₙ` for `n ≥ 1`, `Dₙ` for
`n ≥ 4`, `E₆`, `E₇`, `E₈`) these agree with the bad primes of the root system, while `0`
(characteristic zero) is never bad. -/
def IsBadPrime : DynkinType → ℕ → Prop
  | .D _, p => p = 2
  | .E6, p | .E7, p => p = 2 ∨ p = 3
  | .E8, p => p = 2 ∨ p = 3 ∨ p = 5
  | .A _, _ | .B _, _ | .C _, _ | .F4, _ | .G2, _ => False

instance instDecidableIsBadPrime (t : DynkinType) (p : ℕ) : Decidable (t.IsBadPrime p) :=
  match t with
  | .D _ => inferInstanceAs (Decidable (p = 2))
  | .E6 | .E7 => inferInstanceAs (Decidable (p = 2 ∨ p = 3))
  | .E8 => inferInstanceAs (Decidable (p = 2 ∨ p = 3 ∨ p = 5))
  | .A _ | .B _ | .C _ | .F4 | .G2 => inferInstanceAs (Decidable False)

/-- Type `Aₙ` has no bad primes. -/
@[simp]
theorem not_isBadPrime_A (n p : ℕ) : ¬ (A n).IsBadPrime p := id

/-- The non-simply-laced constructor `Bₙ` has `IsBadPrime = False`. -/
@[simp]
theorem not_isBadPrime_B (n p : ℕ) : ¬ (B n).IsBadPrime p := id

/-- The non-simply-laced constructor `Cₙ` has `IsBadPrime = False`. -/
@[simp]
theorem not_isBadPrime_C (n p : ℕ) : ¬ (C n).IsBadPrime p := id

/-- `2` is the unique bad prime for type `Dₙ`. -/
@[simp]
theorem isBadPrime_D_iff {n p : ℕ} : (D n).IsBadPrime p ↔ p = 2 := Iff.rfl

/-- `2` and `3` are the bad primes for `E₆`. -/
@[simp]
theorem isBadPrime_E6_iff {p : ℕ} : E6.IsBadPrime p ↔ p = 2 ∨ p = 3 := Iff.rfl

/-- `2` and `3` are the bad primes for `E₇`. -/
@[simp]
theorem isBadPrime_E7_iff {p : ℕ} : E7.IsBadPrime p ↔ p = 2 ∨ p = 3 := Iff.rfl

/-- `2`, `3` and `5` are the bad primes for `E₈`. -/
@[simp]
theorem isBadPrime_E8_iff {p : ℕ} : E8.IsBadPrime p ↔ p = 2 ∨ p = 3 ∨ p = 5 := Iff.rfl

/-- The non-simply-laced constructor `F₄` has `IsBadPrime = False`. -/
@[simp]
theorem not_isBadPrime_F4 (p : ℕ) : ¬ F4.IsBadPrime p := id

/-- The non-simply-laced constructor `G₂` has `IsBadPrime = False`. -/
@[simp]
theorem not_isBadPrime_G2 (p : ℕ) : ¬ G2.IsBadPrime p := id

/-- Characteristic zero (`p = 0`) is never bad for any Dynkin type. -/
@[simp]
theorem not_isBadPrime_zero (t : DynkinType) : ¬ t.IsBadPrime 0 := by
  cases t <;> simp

/-- `1` is never a bad prime for any Dynkin type. -/
@[simp]
theorem not_isBadPrime_one (t : DynkinType) : ¬ t.IsBadPrime 1 := by
  cases t <;> simp

/-- Only simply-laced Dynkin types satisfy `IsBadPrime`. -/
theorem IsBadPrime.isSimplyLaced {t : DynkinType} {p : ℕ} (h : t.IsBadPrime p) :
    t.IsSimplyLaced := by
  cases t <;> simp_all

/-- Every number satisfying `IsBadPrime` is prime (`2`, `3` or `5`). -/
theorem IsBadPrime.prime {t : DynkinType} {p : ℕ} (h : t.IsBadPrime p) : Nat.Prime p := by
  cases t <;> simp only [isBadPrime_D_iff, isBadPrime_E6_iff, isBadPrime_E7_iff, isBadPrime_E8_iff,
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

/-- Every bad prime of a Dynkin type is at most `5`. -/
theorem IsBadPrime.le_five {t : DynkinType} {p : ℕ} (h : t.IsBadPrime p) : p ≤ 5 := by
  cases t <;> simp_all <;> omega

/-- No number `p ≥ 6` is a bad prime for any Dynkin type. -/
theorem not_isBadPrime_of_six_le (t : DynkinType) {p : ℕ} (hp : 6 ≤ p) : ¬ t.IsBadPrime p :=
  fun h => by have := h.le_five; omega

/-- No prime (or natural number) `p ≥ 7` is a bad prime for any Dynkin type. -/
theorem not_isBadPrime_of_seven_le (t : DynkinType) {p : ℕ} (hp : 7 ≤ p) : ¬ t.IsBadPrime p :=
  t.not_isBadPrime_of_six_le (by omega)

end DynkinType

/-! ### Transport and characteristic helpers -/

open DoubledQuiver

attribute [local instance] SimpleGraph.neighborSetFintypeOfFinite

private theorem isUnit_natCast_of_prime_of_ringChar_ne (k : Type*) [Field k] {p : ℕ}
    (hp : Nat.Prime p) (hchar : ringChar k ≠ p) : IsUnit (p : k) := by
  refine isUnit_iff_ne_zero.mpr fun h0 => hchar ?_
  rcases (Nat.dvd_prime hp).mp ((ringChar.spec k p).mp h0) with h1 | hp'
  · exact absurd h1 (CharP.char_ne_one k (ringChar k))
  · exact hp'

private theorem signlessPreprojectiveGrade_le_commutatorSubmodule_of_graphIso
    (k : Type*) [CommRing k] {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [∀ i, Fintype (G.neighborSet i)] [∀ j, Fintype (H.neighborSet j)]
    (e : G ≃g H) {d : ℕ}
    (hH : signlessPreprojectiveGrade k (DoubledQuiver H) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H))) :
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  intro x hx
  let E := signlessPreprojectiveAlgebraEquiv k e
  have hEx := hH (signlessPreprojectiveAlgebraEquiv_mem_signlessPreprojectiveGrade k e hx)
  simpa only [E, AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule E.symm hEx

private theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_graphIso
    (k : Type*) [CommRing k] {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [∀ i, Fintype (G.neighborSet i)] [∀ j, Fintype (H.neighborSet j)]
    (e : G ≃g H) {d : ℕ}
    (hH : ∃ z : signlessPreprojectiveAlgebra k (DoubledQuiver H),
      z ∈ signlessPreprojectiveGrade k (DoubledQuiver H) d ∧
        z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H))) :
    ∃ z : signlessPreprojectiveAlgebra k (DoubledQuiver G),
      z ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d ∧
        z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain ⟨z, hz, hz0⟩ := hH
  let E := signlessPreprojectiveAlgebraEquiv k e
  refine ⟨E.symm z, ?_, fun h => hz0 ?_⟩
  · simpa only [E, signlessPreprojectiveAlgebraEquiv_symm] using
      signlessPreprojectiveAlgebraEquiv_mem_signlessPreprojectiveGrade k e.symm hz
  · simpa only [E, AlgEquiv.apply_symm_apply] using map_mem_commutatorSubmodule E h

private theorem exists_mem_signlessPreprojectiveGrade_of_graphEq
    (k : Type*) [CommRing k] {W : Type*} [Finite W] {H H' : SimpleGraph W} (hEq : H = H') {d : ℕ}
    (hH : ∃ z : signlessPreprojectiveAlgebra k (DoubledQuiver H),
      z ∈ signlessPreprojectiveGrade k (DoubledQuiver H) d ∧
        z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H))) :
    ∃ z : signlessPreprojectiveAlgebra k (DoubledQuiver H'),
      z ∈ signlessPreprojectiveGrade k (DoubledQuiver H') d ∧
        z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H')) := by
  subst hEq
  exact hH

/-! ### Good and bad characteristics on ADE diagrams -/

variable (k : Type*) [Field k]

/-- **Outside bad characteristics, the signless preprojective algebra of any graph isomorphic to a
simply-laced Dynkin diagram has vanishing cyclic quotient in positive degrees.** -/
theorem signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso {V : Type*} [Finite V]
    {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] {t : DynkinType}
    (ht : t.IsSimplyLaced) (e : G ≃g diagramGraph t.cartanMatrix)
    (hp : ¬ t.IsBadPrime (ringChar k)) {d : ℕ} (hd : 0 < d) :
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  refine signlessPreprojectiveGrade_le_commutatorSubmodule_of_graphIso k e ?_
  cases t with
  | A n => exact signlessPreprojectiveGrade_A_le_commutatorSubmodule k hd
  | D n =>
    have h2 : IsUnit (2 : k) := isUnit_natCast_of_prime_of_ringChar_ne k Nat.prime_two
      (by simpa using hp)
    exact signlessPreprojectiveGrade_D_le_commutatorSubmodule k h2 hd
  | E6 =>
    simp only [DynkinType.isBadPrime_E6_iff, not_or] at hp
    exact signlessPreprojectiveGrade_E6_le_commutatorSubmodule k
      (isUnit_natCast_of_prime_of_ringChar_ne k Nat.prime_two hp.1)
      (isUnit_natCast_of_prime_of_ringChar_ne k Nat.prime_three hp.2) hd
  | E7 =>
    simp only [DynkinType.isBadPrime_E7_iff, not_or] at hp
    exact signlessPreprojectiveGrade_E7_le_commutatorSubmodule k
      (isUnit_natCast_of_prime_of_ringChar_ne k Nat.prime_two hp.1)
      (isUnit_natCast_of_prime_of_ringChar_ne k Nat.prime_three hp.2) hd
  | E8 =>
    simp only [DynkinType.isBadPrime_E8_iff, not_or] at hp
    have key : ∀ H : SimpleGraph (Fin 8), zigzagE8Graph = H →
        signlessPreprojectiveGrade k (DoubledQuiver H) d ≤
          commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) := by
      rintro H rfl
      exact signlessPreprojectiveGrade_E8_le_commutatorSubmodule k
        (isUnit_natCast_of_prime_of_ringChar_ne k Nat.prime_two hp.1)
        (isUnit_natCast_of_prime_of_ringChar_ne k Nat.prime_three hp.2.1)
        (isUnit_natCast_of_prime_of_ringChar_ne k Nat.prime_five hp.2.2) hd
    exact key _ zigzagE8Graph_eq_diagramGraph
  | B _ | C _ | F4 | G2 => simp at ht

/-- **Outside bad characteristics, the additive preprojective algebra of every orientation of a
graph isomorphic to a simply-laced Dynkin diagram has vanishing cyclic quotient in positive
degrees.** -/
theorem preprojectiveGrade_le_commutatorSubmodule_of_iso {V : Type*} [Finite V]
    {G : SimpleGraph V} {t : DynkinType} (ht : t.IsSimplyLaced)
    (e : G ≃g diagramGraph t.cartanMatrix) (hp : ¬ t.IsBadPrime (ringChar k))
    (o : Orientation G) {d : ℕ} (hd : 0 < d) :
    preprojectiveGrade k (OrientedQuiver G o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  have hb : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  rw [hb.preprojectiveGrade_le_commutatorSubmodule_iff k o d]
  exact signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k ht e hp hd

/-- **Outside bad characteristics, the commutator submodule of the signless preprojective algebra
of any graph isomorphic to a simply-laced Dynkin diagram is the augmentation kernel.** -/
theorem commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker_of_iso {V : Type*} [Finite V]
    {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] {t : DynkinType}
    (ht : t.IsSimplyLaced) (e : G ≃g diagramGraph t.cartanMatrix)
    (hp : ¬ t.IsBadPrime (ringChar k)) :
    commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) =
      LinearMap.ker (signlessPreprojectiveAugmentation (R := DoubledQuiver G) k).toLinearMap :=
  commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker k fun x hx =>
    signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k ht e hp hx
      (signlessPreprojectiveMk_mem_grade k _ (PathAlgebra.ofPath_mem_grade x))

/-- **Outside bad characteristics, the cyclic quotient of the signless preprojective algebra of any
graph isomorphic to a simply-laced Dynkin diagram has dimension `Nat.card V`.** -/
theorem finrank_cyclicQuotient_signlessPreprojectiveAlgebra_of_iso {V : Type*} [Finite V]
    {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] {t : DynkinType}
    (ht : t.IsSimplyLaced) (e : G ≃g diagramGraph t.cartanMatrix)
    (hp : ¬ t.IsBadPrime (ringChar k)) :
    Module.finrank k (cyclicQuotient k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) =
      Nat.card V := by
  rw [finrank_cyclicQuotient_signlessPreprojectiveAlgebra k fun x hx =>
      signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k ht e hp hx
        (signlessPreprojectiveMk_mem_grade k _ (PathAlgebra.ofPath_mem_grade x)),
    ← Nat.card_congr (vertexEquiv G)]

/-- **Outside bad characteristics, the cyclic quotient of the additive preprojective algebra of
every orientation of a graph isomorphic to a simply-laced Dynkin diagram has dimension
`Nat.card V`.** -/
theorem finrank_cyclicQuotient_preprojectiveAlgebra_of_iso {V : Type*} [Finite V]
    {G : SimpleGraph V} {t : DynkinType} (ht : t.IsSimplyLaced)
    (e : G ≃g diagramGraph t.cartanMatrix) (hp : ¬ t.IsBadPrime (ringChar k))
    (o : Orientation G) :
    Module.finrank k (cyclicQuotient k (preprojectiveAlgebra k (OrientedQuiver G o))) =
      Nat.card V := by
  have hb : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  let E := hb.signlessPreprojectiveAlgebraEquiv k o
  have hcomm : (commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))).map
      E.toLinearEquiv.toLinearMap =
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) :=
    le_antisymm
      (Submodule.map_le_iff_le_comap.mpr fun _ hx => map_mem_commutatorSubmodule E hx)
      fun y hy => ⟨E.symm y, map_mem_commutatorSubmodule E.symm hy, E.apply_symm_apply y⟩
  rw [← (Submodule.Quotient.equiv _ _ E.toLinearEquiv hcomm).finrank_eq,
    finrank_cyclicQuotient_signlessPreprojectiveAlgebra_of_iso k ht e hp]

private theorem exists_badPrime_typeE_two_or_three {n : ℕ} (hn5 : 5 ≤ n) (hn6 : 6 ≤ n)
    {C : Matrix (Fin n) (Fin n) ℤ} (hC : CartanMatrix.E n = C)
    (hp : ringChar k = 2 ∨ ringChar k = 3) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ),
      ∃ z : signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph C)),
        z ∈ signlessPreprojectiveGrade k (DoubledQuiver (diagramGraph C)) d ∧
          z ∉ commutatorSubmodule k
            (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph C))) := by
  rcases hp with hp2 | hp3
  · have : CharP k 2 := ringChar.of_eq hp2
    exact ⟨4, by simp, exists_mem_signlessPreprojectiveGrade_of_graphEq k (congrArg diagramGraph hC)
      (exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule k hn5
        (CharP.cast_eq_zero k 2))⟩
  · have : CharP k 3 := ringChar.of_eq hp3
    exact ⟨6, by simp, exists_mem_signlessPreprojectiveGrade_of_graphEq k (congrArg diagramGraph hC)
      (exists_mem_signlessPreprojectiveGrade_E_six_notMem_commutatorSubmodule k hn6)⟩

/-- **At a bad characteristic of a valid Dynkin diagram, the signless preprojective algebra has a
nonzero cyclic class in degree `4`, `6` or `10`.** -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] {t : DynkinType}
    (ht : t.Valid) (e : G ≃g diagramGraph t.cartanMatrix) (hp : t.IsBadPrime (ringChar k)) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ), ∃ z : signlessPreprojectiveAlgebra k (DoubledQuiver G),
      z ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d ∧
        z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  suffices ∃ d ∈ ({4, 6, 10} : Finset ℕ),
      ∃ z : signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph t.cartanMatrix)),
        z ∈ signlessPreprojectiveGrade k (DoubledQuiver (diagramGraph t.cartanMatrix)) d ∧
          z ∉ commutatorSubmodule k
            (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph t.cartanMatrix))) by
    obtain ⟨d, hd, hH⟩ := this
    exact ⟨d, hd,
      exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_graphIso k e hH⟩
  cases t with
  | D n =>
    have : CharP k 2 := ringChar.of_eq (DynkinType.isBadPrime_D_iff.mp hp)
    exact ⟨4, by simp, exists_mem_signlessPreprojectiveGrade_D_four_notMem_commutatorSubmodule k
      (DynkinType.valid_D.mp ht) (CharP.cast_eq_zero k 2)⟩
  | E6 =>
    exact exists_badPrime_typeE_two_or_three k (by decide) (by decide)
      DynkinType.cartanMatrix_E6.symm (DynkinType.isBadPrime_E6_iff.mp hp)
  | E7 =>
    exact exists_badPrime_typeE_two_or_three k (by decide) (by decide)
      DynkinType.cartanMatrix_E7.symm (DynkinType.isBadPrime_E7_iff.mp hp)
  | E8 =>
    rcases DynkinType.isBadPrime_E8_iff.mp hp with hp2 | hp3 | hp5
    · exact exists_badPrime_typeE_two_or_three k (by decide) (by decide)
        DynkinType.cartanMatrix_E8.symm (Or.inl hp2)
    · exact exists_badPrime_typeE_two_or_three k (by decide) (by decide)
        DynkinType.cartanMatrix_E8.symm (Or.inr hp3)
    · have : CharP k 5 := ringChar.of_eq hp5
      refine ⟨10, by simp,
        exists_mem_signlessPreprojectiveGrade_of_graphEq k zigzagE8Graph_eq_diagramGraph ?_⟩
      exact ⟨_, signlessWord_E8_cyclicWord_mem_grade_ten k,
        signlessWord_E8_cyclicWord_notMem_commutatorSubmodule k (CharP.cast_eq_zero k 5)⟩
  | A _ | B _ | C _ | F4 | G2 => simp at hp

/-- **At a bad characteristic of a valid Dynkin diagram, the additive preprojective algebra of
every orientation has a nonzero cyclic class in degree `4`, `6` or `10`.** -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
    {V : Type*} [Finite V] {G : SimpleGraph V} {t : DynkinType} (ht : t.Valid)
    (e : G ≃g diagramGraph t.cartanMatrix) (hp : t.IsBadPrime (ringChar k)) (o : Orientation G) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ), ∃ z : preprojectiveAlgebra k (OrientedQuiver G o),
      z ∈ preprojectiveGrade k (OrientedQuiver G o) d ∧
        z ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  obtain ⟨d, hd, z, hz, hz0⟩ :=
    exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k ht e hp
  have hb : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  refine ⟨d, hd, ?_⟩
  by_contra! hall
  exact hz0 (((hb.preprojectiveGrade_le_commutatorSubmodule_iff k o d).mp hall) hz)

/-! ### The complete positive-degree cyclic quotient classification -/

/-- **The positive-degree cyclic quotient vanishing theorem for signless preprojective algebras.**
For a connected finite simple graph `G` over a field `k`, every graded piece of `Π⁺(G)` of path
degree `d ≥ 3` lies in `[Π⁺(G), Π⁺(G)]` if and only if `G` is isomorphic to the diagram of a valid
simply-laced Dynkin type `t` and `ringChar k` is not a bad prime for `t`. -/
theorem signlessPreprojective_cyclicQuotient_vanishes_iff {V : Type*} [Finite V]
    {G : SimpleGraph V} [inst : ∀ i, Fintype (G.neighborSet i)] (hG : G.Connected) :
    (∀ d : ℕ, 3 ≤ d →
      signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
    ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
      Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ t.IsBadPrime (ringChar k) := by
  refine ⟨fun hall => ?_, fun ⟨t, _, hsl, ⟨e⟩, hp⟩ d hd =>
    signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k hsl e hp (by omega)⟩
  have hacyc : G.IsAcyclic := by
    by_contra hnot
    obtain ⟨d, hd, _, hz, hz0⟩ :=
      exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic k hnot
    exact hz0 (hall d hd hz)
  have htree : G.IsTree := ⟨hG, hacyc⟩
  have hdyn : ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) := by
    classical
    have : Fintype V := Fintype.ofFinite V
    have hinst : inst = fun i => Subtype.fintype (· ∈ G.neighborSet i) := Subsingleton.elim _ _
    subst hinst
    by_contra hnot
    obtain ⟨d, hd, _, hz, hz0⟩ :=
      htree.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule (k := k) hnot
    exact hz0 (hall d (by simp at hd; omega) hz)
  obtain ⟨t, ht, hsl, ⟨e⟩⟩ := (G.exists_valid_isSimplyLaced_dynkinType_iso_iff).mpr hdyn
  refine ⟨t, ht, hsl, ⟨e⟩, fun hp => ?_⟩
  obtain ⟨d, hd, _, hz, hz0⟩ :=
    exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k ht e hp
  exact hz0 (hall d (by simp at hd; omega) hz)

/-- **Positive-degree (`d > 0`) signless cyclic quotient vanishing**: equivalent to vanishing in all
degrees `d ≥ 3`. -/
theorem forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff {V : Type*} [Finite V]
    {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] (hG : G.Connected) :
    (∀ d : ℕ, 0 < d →
      signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
    ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
      Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ t.IsBadPrime (ringChar k) :=
  ⟨fun hall => (signlessPreprojective_cyclicQuotient_vanishes_iff k hG).mp
    fun d hd => hall d (by omega),
   fun ⟨_, _, hsl, ⟨e⟩, hp⟩ _ hd =>
    signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k hsl e hp hd⟩

/-- **The positive-degree cyclic quotient of a preprojective algebra** (Schedler, Theorem 13.1.1;
Liu--Wang, Theorem 1.1 and Corollary 3.4). Let `o` orient a finite connected simple graph `G` and
let `Π = Π_k(OrientedQuiver G o)` over a field `k`, graded by path length. Every graded piece of
degree `d ≥ 3` lies in the commutator submodule `[Π, Π]`, that is `(Π / [Π, Π])_d = 0` for all
`d ≥ 3`, if and only if `G` is isomorphic to `diagramGraph t.cartanMatrix` for a valid simply-laced
Dynkin type `t` and `ringChar k` is not a bad prime for `t`. -/
theorem preprojective_cyclicQuotient_vanishes_iff {V : Type*} [Finite V] (G : SimpleGraph V)
    (hG : G.Connected) (o : Orientation G) :
    (∀ d : ℕ, 3 ≤ d →
      preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
    ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
      Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ t.IsBadPrime (ringChar k) := by
  refine ⟨fun hall => ?_, fun ⟨_, _, hsl, ⟨e⟩, hp⟩ d hd =>
    preprojectiveGrade_le_commutatorSubmodule_of_iso k hsl e hp o (by omega)⟩
  have hacyc : G.IsAcyclic := by
    by_contra hnot
    obtain ⟨d, hd, _, hz, hz0⟩ :=
      exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic k o hnot
    exact hz0 (hall d hd hz)
  refine (signlessPreprojective_cyclicQuotient_vanishes_iff k hG).mp fun d hd => ?_
  rw [← hacyc.isBipartite.preprojectiveGrade_le_commutatorSubmodule_iff k o d]
  exact hall d hd

/-- **Positive-degree (`d > 0`) preprojective cyclic quotient vanishing**: equivalent to vanishing
in all degrees `d ≥ 3`. -/
theorem forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff {V : Type*} [Finite V]
    (G : SimpleGraph V) (hG : G.Connected) (o : Orientation G) :
    (∀ d : ℕ, 0 < d →
      preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
    ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
      Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ t.IsBadPrime (ringChar k) :=
  ⟨fun hall => (preprojective_cyclicQuotient_vanishes_iff k G hG o).mp
    fun d hd => hall d (by omega),
   fun ⟨_, _, hsl, ⟨e⟩, hp⟩ _ hd =>
    preprojectiveGrade_le_commutatorSubmodule_of_iso k hsl e hp o hd⟩

end TauCeti
