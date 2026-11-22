/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BadPrime
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.BadCharacteristic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.BadCharacteristic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CharacteristicFive
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CharacteristicThree
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Affine
import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.GraphGrading
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Span
import TauCeti.RepresentationTheory.Quiver.Preprojective.Cycle

/-!
# Positive-degree cyclic quotients of preprojective algebras

For a finite quiver `Q` over a commutative ring `k`, the cyclic quotient `Π / [Π, Π]` of the
preprojective algebra inherits a grading from path length. This file assembles the type-by-type
results for `Aₙ`, `Dₙ`, `E₆`, `E₇`, and `E₈`, the bad-characteristic cyclic classes in types `D`
and `E`, the affine-tree cyclic classes, and the cycle matrix representation into the complete
positive-degree cyclic quotient dichotomy for connected finite simple graphs.

Over a nontrivial commutative ring `k`, for a connected finite simple graph `G`, the graded piece
of degree `d` of the cyclic quotient `Π⁺(G) / [Π⁺(G), Π⁺(G)]` vanishes for all `d ≥ 3`
(equivalently, for all `d > 0`) if and only if `G` is isomorphic to the diagram of a valid
simply-laced Dynkin type `t` whose bad primes (`TauCeti.IsBadPrime`) are all invertible in `k`.
The same characterization holds for the additive preprojective algebra `Π_k(OrientedQuiver G o)` of
every orientation `o` of `G`. Over a field `k`, invertibility of every bad prime of `t` is
equivalent to `¬ IsBadPrime t (ringChar k)` (`TauCeti.forall_isBadPrime_isUnit_iff`).

The threshold `d ≥ 3` is singled out alongside `d > 0` because in zigzag deformation theory,
path degree `d = q + 2 ≥ 3` of the cyclic quotient feeds the Hochschild cohomology group
`HH^{2, q}` of the 2-Calabi--Yau Ginzburg dg algebra for `q > 0`, governing intrinsic formality of
the corresponding zigzag algebra.

## Bad primes of preprojective cyclic quotients

For a valid Dynkin type `t`, `TauCeti.IsBadPrime t p` records the primes `p` at which the
positive-degree cyclic quotient of the preprojective algebra of `diagramGraph t.cartanMatrix` fails
to vanish:

* `p = 2` for `Dₙ` (`n ≥ 4`), `E₆`, `E₇`, `E₈`;
* `p = 3` for `E₆`, `E₇`, `E₈`;
* `p = 5` for `E₈`;
* none for `Aₙ` (nor for `Bₙ`, `Cₙ`, `F₄`, `G₂`, whose unweighted `diagramGraph`s are path graphs of
  type `A`).

On valid simply-laced Dynkin types (`A`, `D`, `E`), these coincide with the bad primes of the root
system (`TauCeti.isBadPrime_iff_dynkinType_isBadPrime_of_isSimplyLaced`) and with the bad
characteristics in Schedler, Theorem 13.1.1, Etingof--Eu, and Liu--Wang, Theorem 1.1. Because
`diagramGraph` forgets bond multiplicities, the root-system bad primes of the multiply-laced types
(`Bₙ`, `Cₙ`, `F₄`, `G₂`) do not obstruct the unweighted preprojective algebra here, so
`TauCeti.IsBadPrime` is defined in this preprojective module rather than on root systems.

## Main definitions and results

* `TauCeti.IsBadPrime`: the bad primes of `t : DynkinType` for the unweighted preprojective cyclic
  quotient, `TauCeti.isBadPrime_iff_dynkinType_isBadPrime_of_isSimplyLaced`, and
  `TauCeti.forall_isBadPrime_isUnit_iff` relating invertibility of bad primes over a field `k` to
  `¬ IsBadPrime t (ringChar k)`.
* `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso`,
  `TauCeti.preprojectiveGrade_le_commutatorSubmodule_of_iso`, and
  `TauCeti.finrank_cyclicQuotient_preprojectiveAlgebra_of_iso`: when every bad prime of `t` is a
  unit in `k`, every positive-degree piece of the signless or oriented preprojective algebra of a
  graph isomorphic to `diagramGraph t.cartanMatrix` lies in the commutator submodule, the signless
  commutator submodule equals the augmentation kernel, and both cyclic quotients have dimension
  `t.rank`.
* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime`,
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime`, and their
  non-unit generalizations
  `exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime_of_not_isUnit`
  and `exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime_of_not_isUnit`:
  when `t` is valid and a bad prime `p` of `t` is not a unit in a commutative ring `k` (or
  `(p : k) = 0` in a nontrivial one), a nonzero cyclic class appears in path degree `4`, `6`,
  or `10`.
* `exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_exists_dynkinType_iso`:
  every connected finite non-Dynkin graph has a nonzero signless cyclic class of degree at
  least `3`.
* `TauCeti.forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff`,
  `TauCeti.forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff`,
  `TauCeti.forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff_of_commRing`, and
  `TauCeti.forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff_of_commRing`: **the complete
  positive-degree cyclic quotient dichotomy for connected finite simple graphs over a nontrivial
  commutative ring**.
* `TauCeti.forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_field`,
  `TauCeti.forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_field`,
  `TauCeti.forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff`, and
  `TauCeti.forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff`: **the complete
  positive-degree cyclic quotient dichotomy over a field `k`**.

## References

* P. Etingof and C.-H. Eu, *Hochschild and cyclic homology of preprojective algebras of ADE
  quivers*, Mosc. Math. J. 7 (2007), https://arxiv.org/abs/math/0609006.
* T. Schedler, *Zeroth Hochschild homology of preprojective algebras over the integers*, Theorem
  13.1.1, https://arxiv.org/abs/0704.3278.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  Theorem 1.1, Proposition 3.2, and Corollary 3.4, https://arxiv.org/abs/2301.06757.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

/-! ### Bad primes -/

/-- The bad primes of a valid Dynkin type `t` for the cyclic quotient of the unweighted
preprojective algebra of `diagramGraph t.cartanMatrix`: `2` in types `D` and `E`, `3` in type `E`,
and `5` in type `E₈`. Non-simply-laced constructors have path-graph diagrams and therefore have no
bad primes for the unweighted preprojective algebra. -/
def IsBadPrime : DynkinType → ℕ → Prop
  | .D _, p => p = 2
  | .E6, p | .E7, p => p = 2 ∨ p = 3
  | .E8, p => p = 2 ∨ p = 3 ∨ p = 5
  | .A _, _ | .B _, _ | .C _, _ | .F4, _ | .G2, _ => False

instance : DecidableRel IsBadPrime := fun t p =>
  match t with
  | .D _ => inferInstanceAs (Decidable (p = 2))
  | .E6 | .E7 => inferInstanceAs (Decidable (p = 2 ∨ p = 3))
  | .E8 => inferInstanceAs (Decidable (p = 2 ∨ p = 3 ∨ p = 5))
  | .A _ | .B _ | .C _ | .F4 | .G2 => inferInstanceAs (Decidable False)

@[simp] theorem not_isBadPrime_A (n p : ℕ) : ¬ IsBadPrime (.A n) p := not_false
@[simp] theorem not_isBadPrime_B (n p : ℕ) : ¬ IsBadPrime (.B n) p := not_false
@[simp] theorem not_isBadPrime_C (n p : ℕ) : ¬ IsBadPrime (.C n) p := not_false
@[simp] theorem isBadPrime_D (n p : ℕ) : IsBadPrime (.D n) p ↔ p = 2 := (Iff.rfl)
@[simp] theorem isBadPrime_E6 (p : ℕ) : IsBadPrime .E6 p ↔ p = 2 ∨ p = 3 := (Iff.rfl)
@[simp] theorem isBadPrime_E7 (p : ℕ) : IsBadPrime .E7 p ↔ p = 2 ∨ p = 3 := (Iff.rfl)
@[simp] theorem isBadPrime_E8 (p : ℕ) : IsBadPrime .E8 p ↔ p = 2 ∨ p = 3 ∨ p = 5 := (Iff.rfl)
@[simp] theorem not_isBadPrime_F4 (p : ℕ) : ¬ IsBadPrime .F4 p := not_false
@[simp] theorem not_isBadPrime_G2 (p : ℕ) : ¬ IsBadPrime .G2 p := not_false

/-- On simply-laced Dynkin types, the unweighted preprojective bad primes `TauCeti.IsBadPrime`
agree with the root-system bad primes `TauCeti.DynkinType.IsBadPrime`. -/
theorem isBadPrime_iff_dynkinType_isBadPrime_of_isSimplyLaced {t : DynkinType}
    (hs : t.IsSimplyLaced) (p : ℕ) :
    IsBadPrime t p ↔ t.IsBadPrime p := by
  cases t <;> simp_all

/-- Every bad prime of a Dynkin type is a prime number (`2`, `3`, or `5`). -/
theorem IsBadPrime.prime {t : DynkinType} {p : ℕ} (h : IsBadPrime t p) : p.Prime := by
  cases t with
  | D _ =>
    rcases h with rfl
    exact Nat.prime_two
  | E6 | E7 =>
    rcases h with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  | E8 =>
    rcases h with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · decide
  | A _ | B _ | C _ | F4 | G2 => cases h

/-- Zero (the `ringChar` of a field of characteristic zero) is never a bad prime. -/
@[simp]
theorem not_isBadPrime_zero (t : DynkinType) : ¬ IsBadPrime t 0 :=
  fun h => Nat.not_prime_zero h.prime

/-- One is never a bad prime. -/
@[simp]
theorem not_isBadPrime_one (t : DynkinType) : ¬ IsBadPrime t 1 :=
  fun h => Nat.not_prime_one h.prime

/-- No integer `p ≥ 6` (in particular, no prime `p ≥ 7`) is a bad prime of any Dynkin type. -/
theorem not_isBadPrime_of_six_le {t : DynkinType} {p : ℕ} (hp : 6 ≤ p) : ¬ IsBadPrime t p := by
  cases t <;> simp <;> omega

/-! ### Vanishing in good characteristic -/

section GoodCharacteristic

attribute [local instance] SimpleGraph.neighborSetFintypeOfFinite

variable (k : Type*) [CommRing k]

/-- **When every bad prime of `t` is invertible in `k`, every positive-length path in the signless
preprojective algebra of a graph isomorphic to `diagramGraph t.cartanMatrix` lies in the commutator
submodule.** -/
theorem signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_iso
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] {t : DynkinType}
    (e : G ≃g diagramGraph t.cartanMatrix) (hbad : ∀ p, IsBadPrime t p → IsUnit (p : k))
    (x : Quiver.TotalPath (DoubledQuiver G)) (hx : 0 < x.2.2.length) :
    signlessPreprojectiveMk k (DoubledQuiver G) (ofPath x) ∈
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  by_cases hsl : t.IsSimplyLaced
  · cases t with
    | A n =>
      exact (forall_pos_length_signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_iff_of_iso
        k e).mpr (signlessPreprojectiveMk_A_ofPath_mem_commutatorSubmodule k) x hx
    | D n =>
      exact (forall_pos_length_signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_iff_of_iso
        k e).mpr (signlessPreprojectiveMk_D_ofPath_mem_commutatorSubmodule k (hbad 2 rfl)) x hx
    | E6 =>
      exact (forall_pos_length_signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_iff_of_iso
        k e).mpr (signlessPreprojectiveMk_E6_ofPath_mem_commutatorSubmodule k
          (hbad 2 (Or.inl rfl)) (hbad 3 (Or.inr rfl))) x hx
    | E7 =>
      exact (forall_pos_length_signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_iff_of_iso
        k e).mpr (signlessPreprojectiveMk_E7_ofPath_mem_commutatorSubmodule k
          (hbad 2 (Or.inl rfl)) (hbad 3 (Or.inr rfl))) x hx
    | E8 =>
      have e' : G ≃g zigzagE8Graph := by rwa [zigzagE8Graph_eq_diagramGraph]
      exact (forall_pos_length_signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_iff_of_iso
        k e').mpr (signlessPreprojectiveMk_E8_ofPath_mem_commutatorSubmodule k
          (hbad 2 (Or.inl rfl)) (hbad 3 (Or.inr (Or.inl rfl)))
          (hbad 5 (Or.inr (Or.inr rfl)))) x hx
    | B _ | C _ | F4 | G2 => simp at hsl
  · have e' : G ≃g diagramGraph (DynkinType.A t.rank).cartanMatrix := by
      simp only [DynkinType.rank_A, DynkinType.cartanMatrix_A,
        DynkinType.diagramGraph_cartanMatrix_A]
      rwa [t.diagramGraph_cartanMatrix_of_not_isSimplyLaced hsl] at e
    exact (forall_pos_length_signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_iff_of_iso
      k e').mpr (signlessPreprojectiveMk_A_ofPath_mem_commutatorSubmodule k) x hx

/-- **When every bad prime of `t` is invertible in `k`, the cyclic quotient of the signless
preprojective algebra of a graph isomorphic to `diagramGraph t.cartanMatrix` vanishes in positive
path degrees.** -/
theorem signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] {t : DynkinType}
    (e : G ≃g diagramGraph t.cartanMatrix) (hbad : ∀ p, IsBadPrime t p → IsUnit (p : k))
    {d : ℕ} (hd : 0 < d) :
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) :=
  signlessPreprojectiveGrade_le_commutatorSubmodule k
    (signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_iso k e hbad) hd

/-- **When every bad prime of `t` is invertible in `k`, the commutator submodule of the signless
preprojective algebra of a graph isomorphic to `diagramGraph t.cartanMatrix` equals the augmentation
kernel.** -/
theorem commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker_of_iso
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] {t : DynkinType}
    (e : G ≃g diagramGraph t.cartanMatrix) (hbad : ∀ p, IsBadPrime t p → IsUnit (p : k)) :
    commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) =
      LinearMap.ker (signlessPreprojectiveAugmentation (R := DoubledQuiver G) k).toLinearMap :=
  commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker k
    (signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_iso k e hbad)

/-- **When every bad prime of `t` is invertible in a nontrivial commutative ring `k`, the cyclic
quotient of the signless preprojective algebra of a graph isomorphic to
`diagramGraph t.cartanMatrix` has dimension `t.rank`.** -/
theorem finrank_cyclicQuotient_signlessPreprojectiveAlgebra_of_iso [Nontrivial k]
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] {t : DynkinType}
    (e : G ≃g diagramGraph t.cartanMatrix) (hbad : ∀ p, IsBadPrime t p → IsUnit (p : k)) :
    Module.finrank k (cyclicQuotient k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) =
      t.rank := by
  rw [finrank_cyclicQuotient_signlessPreprojectiveAlgebra k
      (signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_iso k e hbad),
    ← Nat.card_congr (vertexEquiv G), Nat.card_congr e.toEquiv, Nat.card_fin]

/-- **When every bad prime of `t` is invertible in `k`, every positive-length path in the additive
preprojective algebra of any orientation of a graph isomorphic to `diagramGraph t.cartanMatrix` lies
in the commutator submodule.** -/
theorem preprojectiveMk_ofPath_mem_commutatorSubmodule_of_iso
    {V : Type*} [Finite V] {G : SimpleGraph V} {t : DynkinType}
    (e : G ≃g diagramGraph t.cartanMatrix) (o : Orientation G)
    (hbad : ∀ p, IsBadPrime t p → IsUnit (p : k))
    (x : Quiver.TotalPath (Symmetrify (OrientedQuiver G o))) (hx : 0 < x.2.2.length) :
    preprojectiveMk k (OrientedQuiver G o) (ofPath x) ∈
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  have hb : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  exact hb.coloringBool.preprojectiveMk_ofPath_mem_commutatorSubmodule k o
    (signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_iso k e hbad) x hx

/-- **When every bad prime of `t` is invertible in `k`, the cyclic quotient of the additive
preprojective algebra of any orientation of a graph isomorphic to `diagramGraph t.cartanMatrix`
vanishes in positive path degrees.** -/
theorem preprojectiveGrade_le_commutatorSubmodule_of_iso
    {V : Type*} [Finite V] {G : SimpleGraph V} {t : DynkinType}
    (e : G ≃g diagramGraph t.cartanMatrix) (o : Orientation G)
    (hbad : ∀ p, IsBadPrime t p → IsUnit (p : k)) {d : ℕ} (hd : 0 < d) :
    preprojectiveGrade k (OrientedQuiver G o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) :=
  preprojectiveGrade_le_commutatorSubmodule k
    (preprojectiveMk_ofPath_mem_commutatorSubmodule_of_iso k e o hbad) hd

/-- **When every bad prime of `t` is invertible in a nontrivial commutative ring `k`, the cyclic
quotient of the additive preprojective algebra of any orientation of a graph isomorphic to
`diagramGraph t.cartanMatrix` has dimension `t.rank`.** -/
theorem finrank_cyclicQuotient_preprojectiveAlgebra_of_iso [Nontrivial k]
    {V : Type*} [Finite V] {G : SimpleGraph V} {t : DynkinType}
    (e : G ≃g diagramGraph t.cartanMatrix) (o : Orientation G)
    (hbad : ∀ p, IsBadPrime t p → IsUnit (p : k)) :
    Module.finrank k (cyclicQuotient k (preprojectiveAlgebra k (OrientedQuiver G o))) =
      t.rank := by
  have hb : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  let E := hb.coloringBool.signlessPreprojectiveAlgebraEquiv k o
  have hmap : (commutatorSubmodule k
      (signlessPreprojectiveAlgebra k (DoubledQuiver G))).map
        (E.toLinearEquiv : _ →ₗ[k] _) =
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
    refine le_antisymm ?_ fun y hy =>
      ⟨E.symm y, map_mem_commutatorSubmodule E.symm hy, E.apply_symm_apply y⟩
    rintro _ ⟨x, hx, rfl⟩
    exact map_mem_commutatorSubmodule E hx
  rw [← (Submodule.Quotient.equiv _ _ E.toLinearEquiv hmap).finrank_eq,
    finrank_cyclicQuotient_signlessPreprojectiveAlgebra_of_iso k e hbad]

end GoodCharacteristic

/-! ### Nonzero cyclic classes in bad characteristic -/

section BadCharacteristic

attribute [local instance] SimpleGraph.neighborSetFintypeOfFinite

variable (k : Type*) [CommRing k]

/-- **At a bad prime `p` of a valid Dynkin type `t`, if `(p : k) = 0` in a nontrivial commutative
ring `k`, then the signless preprojective algebra of any graph isomorphic to
`diagramGraph t.cartanMatrix` has a nonzero cyclic class in path degree `4`, `6`, or `10`.** -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
    [Nontrivial k]
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    {t : DynkinType} (ht : t.Valid) (e : G ≃g diagramGraph t.cartanMatrix)
    {p : ℕ} (hp : IsBadPrime t p) (hp0 : (p : k) = 0) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ), ∃ z ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  cases t with
  | A _ | B _ | C _ | F4 | G2 => cases hp
  | D n =>
    rcases hp with rfl
    exact ⟨4, by simp,
      (exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_iff_of_iso k e).mpr
        (exists_mem_signlessPreprojectiveGrade_D_four_notMem_commutatorSubmodule k
          (DynkinType.valid_D.mp ht) hp0)⟩
  | E6 =>
    have e' : G ≃g diagramGraph (CartanMatrix.E 6) := by rwa [DynkinType.cartanMatrix_E6] at e
    rcases hp with rfl | rfl
    · exact ⟨4, by simp,
      (exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_iff_of_iso k e').mpr
        (exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule k
          (by decide) hp0)⟩
    · exact ⟨6, by simp,
      (exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_iff_of_iso k e').mpr
        (exists_mem_signlessPreprojectiveGrade_E_six_notMem_commutatorSubmodule k
          (by decide) hp0)⟩
  | E7 =>
    have e' : G ≃g diagramGraph (CartanMatrix.E 7) := by rwa [DynkinType.cartanMatrix_E7] at e
    rcases hp with rfl | rfl
    · exact ⟨4, by simp,
      (exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_iff_of_iso k e').mpr
        (exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule k
          (by decide) hp0)⟩
    · exact ⟨6, by simp,
      (exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_iff_of_iso k e').mpr
        (exists_mem_signlessPreprojectiveGrade_E_six_notMem_commutatorSubmodule k
          (by decide) hp0)⟩
  | E8 =>
    rcases hp with rfl | rfl | rfl
    · have e' : G ≃g diagramGraph (CartanMatrix.E 8) := by rwa [DynkinType.cartanMatrix_E8] at e
      exact ⟨4, by simp,
        (exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_iff_of_iso k e').mpr
          (exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule k
            (by decide) hp0)⟩
    · have e' : G ≃g diagramGraph (CartanMatrix.E 8) := by rwa [DynkinType.cartanMatrix_E8] at e
      exact ⟨6, by simp,
        (exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_iff_of_iso k e').mpr
          (exists_mem_signlessPreprojectiveGrade_E_six_notMem_commutatorSubmodule k
            (by decide) hp0)⟩
    · have e' : G ≃g zigzagE8Graph := by rwa [zigzagE8Graph_eq_diagramGraph]
      exact ⟨10, by simp,
        (exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_iff_of_iso k e').mpr
          ⟨signlessWord k zigzagE8Graph [3, 2, 3, 4, 3, 4, 3, 4, 3, 4, 3],
            signlessWord_mem_grade k zigzagE8Graph [3, 2, 3, 4, 3, 4, 3, 4, 3, 4, 3],
            signlessWord_E8_cyclicWord_notMem_commutatorSubmodule k hp0⟩⟩

/-- **At a bad prime `p` of a valid Dynkin type `t`, if `(p : k) = 0` in a nontrivial commutative
ring `k`, then the additive preprojective algebra of every orientation of any graph isomorphic to
`diagramGraph t.cartanMatrix` has a nonzero cyclic class in path degree `4`, `6`, or `10`.** -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime [Nontrivial k]
    {V : Type*} [Finite V] {G : SimpleGraph V}
    {t : DynkinType} (ht : t.Valid) (e : G ≃g diagramGraph t.cartanMatrix) (o : Orientation G)
    {p : ℕ} (hp : IsBadPrime t p) (hp0 : (p : k) = 0) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ), ∃ z ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      z ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  obtain ⟨d, hd, z, hz, hz0⟩ :=
    exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k ht e hp hp0
  have hb : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  exact ⟨d, hd, hb.coloringBool.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule k o
    ⟨z, hz, hz0⟩⟩

/-- **When a bad prime of a valid Dynkin diagram is not invertible in a commutative ring `k`, the
preprojective algebra of every orientation has a nonzero cyclic class in path degree `4`, `6`, or
`10`.** -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime_of_not_isUnit
    {V : Type*} [Finite V] {G : SimpleGraph V}
    {t : DynkinType} (ht : t.Valid) (e : G ≃g diagramGraph t.cartanMatrix) (o : Orientation G)
    {p : ℕ} (hp : IsBadPrime t p) (hpu : ¬ IsUnit (p : k)) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ), ∃ z ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      z ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  let I : Ideal k := Ideal.span {(p : k)}
  have hI : I ≠ ⊤ := mt Ideal.span_singleton_eq_top.mp hpu
  have : Nontrivial (k ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hp0 : (p : k ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  obtain ⟨d, hd, z, hz, hz0⟩ :=
    exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime (k ⧸ I) ht e o hp hp0
  refine ⟨d, hd, IsConcreteLE.not_le_iff_exists.mp fun hk => hz0 ?_⟩
  let _ : Fintype (OrientedQuiver G o) := OrientedQuiver.instFintypeOfFinite G o
  exact preprojectiveGrade_le_commutatorSubmodule_of_ringHom k (Ideal.Quotient.mk I) d hk hz

/-- **When a bad prime of a valid Dynkin diagram is not invertible in a commutative ring `k`, the
signless preprojective algebra has a nonzero cyclic class in path degree `4`, `6`, or `10`.** -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime_of_not_isUnit
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    {t : DynkinType} (ht : t.Valid) (e : G ≃g diagramGraph t.cartanMatrix)
    {p : ℕ} (hp : IsBadPrime t p) (hpu : ¬ IsUnit (p : k)) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ), ∃ z ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  have hb : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  let o : Orientation G := hb.coloringBool.sourceSink
  obtain ⟨d, hd, hx⟩ :=
    exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime_of_not_isUnit
      k ht e o hp hpu
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
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ∀ p, IsBadPrime t p → IsUnit (p : k) := by
  refine ⟨fun hvan => ?_, fun ⟨t, _, _, ⟨e⟩, hgood⟩ d hd =>
    signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k e hgood (by omega)⟩
  by_cases hD : ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)
  · obtain ⟨t, ht, hs, ⟨e⟩⟩ := (SimpleGraph.exists_valid_isSimplyLaced_dynkinType_iso_iff G).mpr hD
    refine ⟨t, ht, hs, ⟨e⟩, fun p hp => by_contra fun hpu => ?_⟩
    obtain ⟨d, hd, x, hx, hx0⟩ :=
      exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime_of_not_isUnit
        k ht e hp hpu
    have hd3 : 3 ≤ d := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      omega
    exact hx0 (hvan d hd3 hx)
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
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ∀ p, IsBadPrime t p → IsUnit (p : k) :=
  ⟨fun h =>
    (forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff k hG).mp
      fun d hd => h d (by omega),
   fun ⟨_, _, _, ⟨e⟩, hgood⟩ _ hd =>
    signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k e hgood hd⟩

/-- **The cyclic quotient dichotomy in degrees at least three for preprojective algebras of oriented
graphs**: for a connected finite simple graph `G`, an orientation `o` of `G`, and a nontrivial
commutative ring `k`, every graded piece of degree `d ≥ 3` of `Π_k(OrientedQuiver G o)` lies in
the commutator submodule if and only if `G` is isomorphic to the diagram of a valid simply-laced
Dynkin type whose bad primes are all invertible in `k`. -/
theorem forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff_of_commRing
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.Connected) (o : Orientation G) :
    (∀ d, 3 ≤ d → preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ∀ p, IsBadPrime t p → IsUnit (p : k) := by
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
      exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime_of_not_isUnit
        k ht e o hp hpu
    have hd3 : 3 ≤ d := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      omega
    exact hx0 (hvan d hd3 hx)
  · rintro ⟨t, -, -, ⟨e⟩, hgood⟩ d hd
    exact preprojectiveGrade_le_commutatorSubmodule_of_iso k e o hgood (by omega)

/-- **The positive-degree cyclic quotient dichotomy for preprojective algebras of oriented graphs**:
for a connected finite simple graph `G`, an orientation `o` of `G`, and a nontrivial commutative
ring `k`, every positive-degree graded piece of `Π_k(OrientedQuiver G o)` lies in the commutator
submodule if and only if `G` is isomorphic to the diagram of a valid simply-laced Dynkin type whose
bad primes are all invertible in `k`. -/
theorem forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff_of_commRing
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.Connected) (o : Orientation G) :
    (∀ d, 0 < d → preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ∀ p, IsBadPrime t p → IsUnit (p : k) :=
  ⟨fun h =>
    (forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff_of_commRing k hG o).mp
      fun d hd => h d (by omega),
   fun ⟨_, _, _, ⟨e⟩, hgood⟩ _ hd =>
    preprojectiveGrade_le_commutatorSubmodule_of_iso k e o hgood hd⟩

end CommRing

/-! ### Complete characterization over a field -/

section Field

variable (k : Type*) [Field k]

/-- Over a field `k`, every bad prime of `t` is invertible in `k` if and only if `ringChar k` is
not a bad prime of `t`. -/
theorem forall_isBadPrime_isUnit_iff {t : DynkinType} :
    (∀ p : ℕ, IsBadPrime t p → IsUnit (p : k)) ↔ ¬ IsBadPrime t (ringChar k) := by
  refine ⟨fun h hbad => ?_, fun hnotbad p hp => ?_⟩
  · exact not_isUnit_zero (CharP.cast_eq_zero k (ringChar k) ▸ h (ringChar k) hbad)
  · refine isUnit_iff_ne_zero.mpr fun hp0 => hnotbad ?_
    rwa [CharP.ringChar_of_prime_eq_zero hp.prime hp0]

/-- Over a field `k`, for a graph `G` isomorphic to the standard diagram of a valid Dynkin type `t`,
every graded piece of path degree `d ≥ 3` of the signless preprojective algebra of `G` lies in the
commutator submodule if and only if `ringChar k` is not a bad prime of `t`. -/
theorem forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    {t : DynkinType} (ht : t.Valid) (e : G ≃g diagramGraph t.cartanMatrix) :
    (∀ d : ℕ, 3 ≤ d → signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
      ¬ IsBadPrime t (ringChar k) := by
  refine ⟨fun h hbad => ?_, fun hnotbad d hd3 =>
    signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k e
      ((forall_isBadPrime_isUnit_iff k).mpr hnotbad) (by omega)⟩
  obtain ⟨d, hd, z, hz, hz0⟩ :=
    exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k ht e hbad
      (CharP.cast_eq_zero k (ringChar k))
  have hd3 : 3 ≤ d := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    omega
  exact hz0 (h d hd3 hz)

/-- Over a field `k`, for a graph `G` isomorphic to the standard diagram of a valid Dynkin type `t`,
the positive-degree pieces of the signless preprojective algebra of `G` lie in the commutator
submodule if and only if `ringChar k` is not a bad prime of `t`. -/
theorem forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    {t : DynkinType} (ht : t.Valid) (e : G ≃g diagramGraph t.cartanMatrix) :
    (∀ d : ℕ, 0 < d → signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
      ¬ IsBadPrime t (ringChar k) :=
  ⟨fun h =>
    (forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso k ht e).mp
      fun d hd3 => h d (by omega),
   fun hnotbad d hd =>
    signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k e
      ((forall_isBadPrime_isUnit_iff k).mpr hnotbad) hd⟩

/-- Over a field `k`, for any orientation `o` of a graph `G` isomorphic to the standard diagram of
a valid Dynkin type `t`, every graded piece of path degree `d ≥ 3` of `Π_k(OrientedQuiver G o)` lies
in the commutator submodule if and only if `ringChar k` is not a bad prime of `t`. -/
theorem forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff_of_iso
    {V : Type*} [Finite V] {G : SimpleGraph V}
    {t : DynkinType} (ht : t.Valid) (e : G ≃g diagramGraph t.cartanMatrix) (o : Orientation G) :
    (∀ d : ℕ, 3 ≤ d → preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
      ¬ IsBadPrime t (ringChar k) := by
  refine ⟨fun h hbad => ?_, fun hnotbad d hd3 =>
    preprojectiveGrade_le_commutatorSubmodule_of_iso k e o
      ((forall_isBadPrime_isUnit_iff k).mpr hnotbad) (by omega)⟩
  obtain ⟨d, hd, z, hz, hz0⟩ :=
    exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k ht e o hbad
      (CharP.cast_eq_zero k (ringChar k))
  have hd3 : 3 ≤ d := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    omega
  exact hz0 (h d hd3 hz)

/-- Over a field `k`, for any orientation `o` of a graph `G` isomorphic to the standard diagram of
a valid Dynkin type `t`, the positive-degree pieces of `Π_k(OrientedQuiver G o)` lie in the
commutator submodule if and only if `ringChar k` is not a bad prime of `t`. -/
theorem forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff_of_iso
    {V : Type*} [Finite V] {G : SimpleGraph V}
    {t : DynkinType} (ht : t.Valid) (e : G ≃g diagramGraph t.cartanMatrix) (o : Orientation G) :
    (∀ d : ℕ, 0 < d → preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
      ¬ IsBadPrime t (ringChar k) :=
  ⟨fun h =>
    (forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff_of_iso k ht e o).mp
      fun d hd3 => h d (by omega),
   fun hnotbad d hd =>
    preprojectiveGrade_le_commutatorSubmodule_of_iso k e o
      ((forall_isBadPrime_isUnit_iff k).mpr hnotbad) hd⟩

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
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) := by
  rw [forall_three_le_signlessPreprojectiveGrade_le_commutatorSubmodule_iff k hG]
  simp only [forall_isBadPrime_isUnit_iff]

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
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) := by
  rw [forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff k hG]
  simp only [forall_isBadPrime_isUnit_iff]

/-- **Characterization of vanishing in path degrees `d ≥ 3` of the cyclic quotient of a
preprojective algebra.** Over a field `k`, for any connected finite simple graph `G` and any
orientation `o` of `G`, every graded piece of `Π_k(OrientedQuiver G o)` of path degree `d ≥ 3` lies
in the commutator submodule if and only if `G` is isomorphic to a valid simply-laced Dynkin diagram
and `ringChar k` is not a bad prime of its type. -/
theorem forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.Connected) (o : Orientation G) :
    (∀ d : ℕ, 3 ≤ d → preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) := by
  rw [forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff_of_commRing k hG o]
  simp only [forall_isBadPrime_isUnit_iff]

/-- **Characterization of positive-degree vanishing of the cyclic quotient of a preprojective
algebra.** Over a field `k`, for any connected finite simple graph `G` and any orientation `o` of
`G`, every positive-degree piece of `Π_k(OrientedQuiver G o)` lies in the commutator submodule if
and only if `G` is isomorphic to a valid simply-laced Dynkin diagram and `ringChar k` is not a bad
prime of its type. -/
theorem forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.Connected) (o : Orientation G) :
    (∀ d : ℕ, 0 < d → preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) := by
  rw [forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff_of_commRing k hG o]
  simp only [forall_isBadPrime_isUnit_iff]

end Field

end Dichotomy

end TauCeti
