/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.BadCharacteristic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.BadCharacteristic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CharacteristicFive
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CharacteristicThree
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Cycle
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.Tree

/-!
# Vanishing of positive-degree cyclic quotients of preprojective algebras

The cyclic quotient `Π / [Π, Π]` of a preprojective algebra is its zeroth Hochschild homology,
graded by path length. For a quiver whose underlying graph is a tree, Liu and Wang identify the
degree-`(q + 2)` piece of `(Π(Q) / [Π(Q), Π(Q)])` with the second Hochschild cohomology `HH^{2,q}`
of the two-dimensional Ginzburg dg algebra `Π₂(Q)`, which by Koszul duality governs minimal `A∞`
deformations of the zigzag algebra in arity `q + 2 ≥ 3`.

This file assembles the type-by-type calculations, bad-characteristic witnesses, affine-tree
representations, and closed-trail trace representations into the complete classification of
connected finite simple graphs whose preprojective cyclic quotient vanishes in positive path
degrees (equivalently, in path degrees `d ≥ 3`):

* Over any commutative ring `k`, if `G` is isomorphic to the diagram of a simply-laced Dynkin type
  `t` whose bad primes (`TauCeti.IsBadPrime`) are invertible in `k` — none for `Aₙ`, `2` for `Dₙ`,
  `2, 3` for `E₆` and `E₇`, and `2, 3, 5` for `E₈` — then every path of positive length in `Π⁺(G)`
  and in `Π_k(OrientedQuiver G o)` lies in the commutator submodule, the commutator submodule of
  `Π⁺(G)` equals the augmentation kernel, and over a nontrivial commutative ring the cyclic
  quotient has rank `|V|`.
* Over any nontrivial commutative ring `k`, if `G` is isomorphic to the diagram of a valid Dynkin
  type `t` and `(p : k) = 0` for a bad prime `p` of `t`, then both `Π⁺(G)` and
  `Π_k(OrientedQuiver G o)` have a nonzero homogeneous cyclic class in path degree `4`, `6`, or
  `10`.
* Over any nontrivial commutative ring `k`, if `G` is a connected finite simple graph not
  isomorphic to any valid Dynkin diagram, then either `G` is a non-Dynkin tree (carrying a nonzero
  cyclic class in degree `4`, `6`, `8`, or `12`) or `G` contains a cycle of length `d ≥ 3`
  (carrying a nonzero cyclic class in degree `d`, even when `G` is not bipartite).
* Consequently, over a field `k`, for any connected finite simple graph `G` and any orientation `o`
  of `G`, the cyclic quotient of `Π_k(OrientedQuiver G o)` (and likewise of `Π⁺(G)`) vanishes in
  all path degrees `d ≥ 3` — equivalently, in all path degrees `d > 0` — if and only if `G` is
  isomorphic to the diagram of a valid simply-laced Dynkin type `t` and `ringChar k` is not a bad
  prime for `t`.

## Main definitions

* `TauCeti.IsBadPrime`: the bad primes of a Dynkin type (`2` for `Dₙ`, `2` and `3` for `E₆` and
  `E₇`, `2`, `3` and `5` for `E₈`, and none otherwise).

## Main results

* `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso` and
  `TauCeti.preprojectiveGrade_le_commutatorSubmodule_of_iso`: positive-degree vanishing for graphs
  isomorphic to a simply-laced Dynkin diagram away from its bad primes.
* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime` and
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime`: nonzero cyclic
  classes in degree `4`, `6`, or `10` when a bad prime vanishes in `k`.
* `SimpleGraph.Connected.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule` and
  `SimpleGraph.Connected.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule`: every connected
  non-Dynkin finite simple graph has a nonzero cyclic class in some degree `d ≥ 3`.
* `TauCeti.preprojective_cyclicQuotient_vanishes_iff` and
  `TauCeti.signlessPreprojective_cyclicQuotient_vanishes_iff`: **the complete `iff`
  characterization over a field for degrees `d ≥ 3`** (with `d > 0` counterparts
  `TauCeti.forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff` and
  `TauCeti.forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff`).

## References

* T. Schedler, *Hochschild homology of preprojective algebras over the integers*, Adv. Math. 229
  (2012), Theorem 13.1.1, https://arxiv.org/abs/0704.3278.
* P. Etingof and C.-H. Eu, *Hochschild and cyclic homology of preprojective algebras of ADE
  quivers*, Mosc. Math. J. 7 (2007), https://arxiv.org/abs/math/0609006.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  Theorem 1.1 and Corollary 3.4, https://arxiv.org/abs/2301.06757.
* J.-L. Loday, *Cyclic Homology*, Section 1.1.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

/-! ### Bad primes of a Dynkin type -/

/-- The **bad primes** of a Dynkin type for the positive-degree cyclic quotient of its
preprojective algebra: `2` in type `D`, `2` and `3` in types `E₆` and `E₇`, `2`, `3` and `5` in
type `E₈`, and none in type `A` or the non-simply-laced types. In particular `0` (characteristic
zero) is never bad. -/
def IsBadPrime : DynkinType → ℕ → Prop
  | .D _, p => p = 2
  | .E6, p => p = 2 ∨ p = 3
  | .E7, p => p = 2 ∨ p = 3
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
@[simp] theorem isBadPrime_D (n p : ℕ) : IsBadPrime (.D n) p ↔ p = 2 := Iff.rfl
@[simp] theorem isBadPrime_E6 (p : ℕ) : IsBadPrime .E6 p ↔ p = 2 ∨ p = 3 := Iff.rfl
@[simp] theorem isBadPrime_E7 (p : ℕ) : IsBadPrime .E7 p ↔ p = 2 ∨ p = 3 := Iff.rfl
@[simp] theorem isBadPrime_E8 (p : ℕ) : IsBadPrime .E8 p ↔ p = 2 ∨ p = 3 ∨ p = 5 := Iff.rfl
@[simp] theorem not_isBadPrime_F4 (p : ℕ) : ¬ IsBadPrime .F4 p := not_false
@[simp] theorem not_isBadPrime_G2 (p : ℕ) : ¬ IsBadPrime .G2 p := not_false

/-- Only simply-laced Dynkin types have bad primes. -/
theorem IsBadPrime.isSimplyLaced {t : DynkinType} {p : ℕ} (h : IsBadPrime t p) :
    t.IsSimplyLaced := by
  cases t <;> simp_all

/-- Every bad prime of a Dynkin type is a prime number. -/
theorem IsBadPrime.prime : ∀ {t : DynkinType} {p : ℕ}, IsBadPrime t p → p.Prime
  | .D _, _, rfl | .E6, _, .inl rfl | .E7, _, .inl rfl | .E8, _, .inl rfl => Nat.prime_two
  | .E6, _, .inr rfl | .E7, _, .inr rfl | .E8, _, .inr (.inl rfl) => Nat.prime_three
  | .E8, _, .inr (.inr rfl) => Nat.prime_five

/-- Every bad prime of a Dynkin type is at most `5`. -/
theorem IsBadPrime.le_five : ∀ {t : DynkinType} {p : ℕ}, IsBadPrime t p → p ≤ 5
  | .D _, _, rfl | .E6, _, .inl rfl | .E7, _, .inl rfl | .E8, _, .inl rfl => by decide
  | .E6, _, .inr rfl | .E7, _, .inr rfl | .E8, _, .inr (.inl rfl) => by decide
  | .E8, _, .inr (.inr rfl) => le_rfl

/-- Characteristic zero (`p = 0`) is never a bad prime. -/
@[simp]
theorem not_isBadPrime_zero (t : DynkinType) : ¬ IsBadPrime t 0 :=
  fun h => h.prime.ne_zero rfl

/-- `1` is never a bad prime. -/
@[simp]
theorem not_isBadPrime_one (t : DynkinType) : ¬ IsBadPrime t 1 :=
  fun h => h.prime.ne_one rfl

/-- No integer strictly greater than `5` (in particular, no prime `p ≥ 7`) is bad for any Dynkin
type. -/
theorem not_isBadPrime_of_five_lt (t : DynkinType) {p : ℕ} (hp : 5 < p) : ¬ IsBadPrime t p :=
  fun h => hp.not_ge h.le_five

/-- Over a field `k`, every bad prime of `t` is invertible in `k` if and only if `ringChar k` is
not a bad prime of `t`. -/
theorem forall_isBadPrime_isUnit_iff {k : Type*} [Field k] (t : DynkinType) :
    (∀ p, IsBadPrime t p → IsUnit (p : k)) ↔ ¬ IsBadPrime t (ringChar k) := by
  refine ⟨fun hu hb => (hu _ hb).ne_zero ringChar.Nat.cast_ringChar,
    fun hnb p hp => isUnit_iff_ne_zero.mpr fun hp0 =>
      hnb (CharP.ringChar_of_prime_eq_zero hp.prime hp0 ▸ hp)⟩

/-! ### Vanishing away from bad primes -/

section GoodCharacteristic

attribute [local instance] SimpleGraph.neighborSetFintypeOfFinite

variable (k : Type*) [CommRing k]

private theorem signlessPreprojectiveMk_cartanMatrix_ofPath_mem_commutatorSubmodule
    {t : DynkinType} (hsl : t.IsSimplyLaced) (hu : ∀ p, IsBadPrime t p → IsUnit (p : k))
    (x : Quiver.TotalPath (DoubledQuiver (diagramGraph t.cartanMatrix)))
    (hx : 0 < x.2.2.length) :
    signlessPreprojectiveMk k (DoubledQuiver (diagramGraph t.cartanMatrix)) (ofPath x) ∈
      commutatorSubmodule k
        (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph t.cartanMatrix))) := by
  cases t with
  | A n => exact signlessPreprojectiveMk_A_ofPath_mem_commutatorSubmodule k x hx
  | D n =>
    exact signlessPreprojectiveMk_D_ofPath_mem_commutatorSubmodule k
      (by simpa using hu 2 (by simp)) x hx
  | E6 =>
    exact signlessPreprojectiveMk_E6_ofPath_mem_commutatorSubmodule k
      (by simpa using hu 2 (by simp)) (by simpa using hu 3 (by simp)) x hx
  | E7 =>
    exact signlessPreprojectiveMk_E7_ofPath_mem_commutatorSubmodule k
      (by simpa using hu 2 (by simp)) (by simpa using hu 3 (by simp)) x hx
  | E8 =>
    have key : ∀ H : SimpleGraph (Fin 8), zigzagE8Graph = H →
        ∀ y : Quiver.TotalPath (DoubledQuiver H), 0 < y.2.2.length →
          signlessPreprojectiveMk k (DoubledQuiver H) (ofPath y) ∈
            commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) := by
      rintro H rfl
      exact signlessPreprojectiveMk_E8_ofPath_mem_commutatorSubmodule k
        (by simpa using hu 2 (by simp)) (by simpa using hu 3 (by simp))
        (by simpa using hu 5 (by simp))
    exact key _ zigzagE8Graph_eq_diagramGraph x hx
  | B n | C n | F4 | G2 => simp at hsl

/-- **Every path of positive length in `Π⁺(G)` is a sum of commutators** when `G` is isomorphic to
the diagram of a simply-laced Dynkin type whose bad primes are invertible in `k`. -/
theorem signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_iso {V : Type*} [Finite V]
    {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] {t : DynkinType}
    (e : G ≃g diagramGraph t.cartanMatrix) (hsl : t.IsSimplyLaced)
    (hu : ∀ p, IsBadPrime t p → IsUnit (p : k))
    (x : Quiver.TotalPath (DoubledQuiver G)) (hx : 0 < x.2.2.length) :
    signlessPreprojectiveMk k (DoubledQuiver G) (ofPath x) ∈
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  let E := signlessPreprojectiveAlgebraEquiv k e
  have hE : E (signlessPreprojectiveMk k _ (ofPath x)) ∈
      commutatorSubmodule k
        (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph t.cartanMatrix))) := by
    rw [signlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk, pathAlgebraEquiv_ofPath]
    exact signlessPreprojectiveMk_cartanMatrix_ofPath_mem_commutatorSubmodule k hsl hu _
      (by rwa [Prefunctor.length_mapTotalPath])
  simpa only [AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule E.symm hE

/-- **The cyclic quotient of `Π⁺(G)` vanishes in positive degrees** when `G` is isomorphic to the
diagram of a simply-laced Dynkin type whose bad primes are invertible in `k`. -/
theorem signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso {V : Type*} [Finite V]
    {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] {t : DynkinType}
    (e : G ≃g diagramGraph t.cartanMatrix) (hsl : t.IsSimplyLaced)
    (hu : ∀ p, IsBadPrime t p → IsUnit (p : k)) {d : ℕ} (hd : 0 < d) :
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) :=
  signlessPreprojectiveGrade_le_commutatorSubmodule k
    (signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_iso k e hsl hu) hd

/-- **The commutator submodule of `Π⁺(G)` equals the augmentation kernel** when `G` is isomorphic
to the diagram of a simply-laced Dynkin type whose bad primes are invertible in `k`. -/
theorem commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker_of_iso {V : Type*} [Finite V]
    {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] {t : DynkinType}
    (e : G ≃g diagramGraph t.cartanMatrix) (hsl : t.IsSimplyLaced)
    (hu : ∀ p, IsBadPrime t p → IsUnit (p : k)) :
    commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) =
      LinearMap.ker (signlessPreprojectiveAugmentation (R := DoubledQuiver G) k).toLinearMap :=
  commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker k
    (signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_iso k e hsl hu)

/-- **The cyclic quotient of `Π⁺(G)` has rank `Nat.card V`** over a nontrivial commutative ring `k`
when `G` is isomorphic to the diagram of a simply-laced Dynkin type whose bad primes are invertible
in `k`. -/
theorem finrank_cyclicQuotient_signlessPreprojectiveAlgebra_of_iso [Nontrivial k] {V : Type*}
    [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] {t : DynkinType}
    (e : G ≃g diagramGraph t.cartanMatrix) (hsl : t.IsSimplyLaced)
    (hu : ∀ p, IsBadPrime t p → IsUnit (p : k)) :
    Module.finrank k (cyclicQuotient k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) =
      Nat.card V := by
  rw [finrank_cyclicQuotient_signlessPreprojectiveAlgebra k
      (signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_iso k e hsl hu),
    ← Nat.card_congr (vertexEquiv G)]

/-- **Every path of positive length in `Π_k(OrientedQuiver G o)` is a sum of commutators** when `G`
is isomorphic to the diagram of a simply-laced Dynkin type whose bad primes are invertible in
`k`. -/
theorem preprojectiveMk_ofPath_mem_commutatorSubmodule_of_iso {V : Type*} [Finite V]
    {G : SimpleGraph V} {t : DynkinType} (e : G ≃g diagramGraph t.cartanMatrix)
    (hsl : t.IsSimplyLaced) (hu : ∀ p, IsBadPrime t p → IsUnit (p : k)) (o : Orientation G)
    (x : Quiver.TotalPath (Symmetrify (OrientedQuiver G o))) (hx : 0 < x.2.2.length) :
    preprojectiveMk k (OrientedQuiver G o) (ofPath x) ∈
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  have hb : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  exact hb.coloringBool.preprojectiveMk_ofPath_mem_commutatorSubmodule k o
    (signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_iso k e hsl hu) x hx

/-- **The cyclic quotient of `Π_k(OrientedQuiver G o)` vanishes in positive degrees** when `G` is
isomorphic to the diagram of a simply-laced Dynkin type whose bad primes are invertible in `k`. -/
theorem preprojectiveGrade_le_commutatorSubmodule_of_iso {V : Type*} [Finite V]
    {G : SimpleGraph V} {t : DynkinType} (e : G ≃g diagramGraph t.cartanMatrix)
    (hsl : t.IsSimplyLaced) (hu : ∀ p, IsBadPrime t p → IsUnit (p : k)) (o : Orientation G)
    {d : ℕ} (hd : 0 < d) :
    preprojectiveGrade k (OrientedQuiver G o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) :=
  preprojectiveGrade_le_commutatorSubmodule k
    (preprojectiveMk_ofPath_mem_commutatorSubmodule_of_iso k e hsl hu o) hd

end GoodCharacteristic

/-! ### Nonvanishing in bad characteristic and for non-Dynkin graphs -/

section Nonvanishing

attribute [local instance] SimpleGraph.neighborSetFintypeOfFinite

variable (k : Type*) [CommRing k] [Nontrivial k]

private theorem exists_mem_signlessPreprojectiveGrade_cartanMatrix_notMem_of_isBadPrime
    {t : DynkinType} {p : ℕ} (ht : t.Valid) (hp : IsBadPrime t p) (hp0 : (p : k) = 0) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ),
      ∃ z ∈ signlessPreprojectiveGrade k (DoubledQuiver (diagramGraph t.cartanMatrix)) d,
        z ∉ commutatorSubmodule k
          (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph t.cartanMatrix))) := by
  have hE {n d : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} (hC : C = CartanMatrix.E n)
      (h : ∃ z ∈ signlessPreprojectiveGrade k (DoubledQuiver (diagramGraph (CartanMatrix.E n))) d,
        z ∉ commutatorSubmodule k
          (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph (CartanMatrix.E n))))) :
      ∃ z ∈ signlessPreprojectiveGrade k (DoubledQuiver (diagramGraph C)) d,
        z ∉ commutatorSubmodule k
          (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph C))) := by
    rwa [hC]
  cases t with
  | D n =>
    simp only [isBadPrime_D] at hp
    subst hp
    exact ⟨4, by simp, exists_mem_signlessPreprojectiveGrade_D_four_notMem_commutatorSubmodule k
      (DynkinType.valid_D.mp ht) (by simpa using hp0)⟩
  | E6 =>
    rcases (isBadPrime_E6 p).mp hp with rfl | rfl
    · exact ⟨4, by simp, hE DynkinType.cartanMatrix_E6 <|
        exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule k
          (n := 6) (by decide) (by simpa using hp0)⟩
    · exact ⟨6, by simp, hE DynkinType.cartanMatrix_E6 <|
        exists_mem_signlessPreprojectiveGrade_E_six_notMem_commutatorSubmodule k
          (n := 6) (by decide) (by simpa using hp0)⟩
  | E7 =>
    rcases (isBadPrime_E7 p).mp hp with rfl | rfl
    · exact ⟨4, by simp, hE DynkinType.cartanMatrix_E7 <|
        exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule k
          (n := 7) (by decide) (by simpa using hp0)⟩
    · exact ⟨6, by simp, hE DynkinType.cartanMatrix_E7 <|
        exists_mem_signlessPreprojectiveGrade_E_six_notMem_commutatorSubmodule k
          (n := 7) (by decide) (by simpa using hp0)⟩
  | E8 =>
    rcases (isBadPrime_E8 p).mp hp with rfl | rfl | rfl
    · exact ⟨4, by simp, hE DynkinType.cartanMatrix_E8 <|
        exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule k
          (n := 8) (by decide) (by simpa using hp0)⟩
    · exact ⟨6, by simp, hE DynkinType.cartanMatrix_E8 <|
        exists_mem_signlessPreprojectiveGrade_E_six_notMem_commutatorSubmodule k
          (n := 8) (by decide) (by simpa using hp0)⟩
    · have key : ∀ H : SimpleGraph (Fin 8), zigzagE8Graph = H →
          ∃ z ∈ signlessPreprojectiveGrade k (DoubledQuiver H) 10,
            z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) := by
        rintro H rfl
        exact ⟨_, signlessWord_E8_cyclicWord_mem_grade_ten k,
          signlessWord_E8_cyclicWord_notMem_commutatorSubmodule k (by simpa using hp0)⟩
      exact ⟨10, by simp, key _ zigzagE8Graph_eq_diagramGraph⟩
  | A _ | B _ | C _ | F4 | G2 => simp at hp

/-- **Nonzero positive-degree cyclic class in bad characteristic (signless).** If `G` is isomorphic
to the diagram of a valid Dynkin type `t` and `(p : k) = 0` for a bad prime `p` of `t`, then
`Π⁺(G)` has a homogeneous element in path degree `4`, `6`, or `10` outside the commutator
submodule. -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    {t : DynkinType} {p : ℕ} (e : G ≃g diagramGraph t.cartanMatrix) (ht : t.Valid)
    (hp : IsBadPrime t p) (hp0 : (p : k) = 0) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ), ∃ z ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain ⟨d, hd, z, hz, hz0⟩ :=
    exists_mem_signlessPreprojectiveGrade_cartanMatrix_notMem_of_isBadPrime k ht hp hp0
  let E := signlessPreprojectiveAlgebraEquiv k e
  refine ⟨d, hd, E.symm z, ?_, fun h => hz0 ?_⟩
  · rwa [signlessPreprojectiveAlgebraEquiv_symm,
      signlessPreprojectiveAlgebraEquiv_mem_signlessPreprojectiveGrade_iff]
  · simpa only [AlgEquiv.apply_symm_apply] using map_mem_commutatorSubmodule E h

/-- **Nonzero positive-degree cyclic class in bad characteristic (oriented).** If `G` is isomorphic
to the diagram of a valid Dynkin type `t` and `(p : k) = 0` for a bad prime `p` of `t`, then for
every orientation `o` of `G`, `Π_k(OrientedQuiver G o)` has a homogeneous element in path degree
`4`, `6`, or `10` outside the commutator submodule. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
    {V : Type*} [Finite V] {G : SimpleGraph V} {t : DynkinType} {p : ℕ}
    (e : G ≃g diagramGraph t.cartanMatrix) (ht : t.Valid) (hp : IsBadPrime t p)
    (hp0 : (p : k) = 0) (o : Orientation G) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ), ∃ z ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      z ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  obtain ⟨d, hd, z, hz, hz0⟩ :=
    exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k e ht hp hp0
  have hb : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  let F := hb.signlessPreprojectiveAlgebraEquiv k o
  refine ⟨d, hd, F z, hb.signlessPreprojectiveAlgebraEquiv_mem_preprojectiveGrade k o hz, ?_⟩
  intro h
  exact hz0 (by simpa only [AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule F.symm h)

end Nonvanishing

end TauCeti

namespace SimpleGraph.Connected

open TauCeti DoubledQuiver

attribute [local instance] SimpleGraph.neighborSetFintypeOfFinite

variable (k : Type*) [CommRing k] [Nontrivial k]

/-- **Every connected non-Dynkin finite simple graph has a nonzero cyclic class in path degree at
least three in `Π⁺(G)`**, over every nontrivial commutative ring. -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule
    {V : Type*} [Finite V] {G : SimpleGraph V} [instG : ∀ i, Fintype (G.neighborSet i)]
    (hG : G.Connected)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ∃ d : ℕ, 3 ≤ d ∧ ∃ z ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  by_cases hac : G.IsAcyclic
  · classical
    let fV : Fintype V := Fintype.ofFinite V
    let instSub : ∀ v, Fintype (G.neighborSet v) := fun v => Subtype.fintype _
    have htree : G.IsTree := ⟨hG, hac⟩
    obtain ⟨d, hd, z, hz, hz0⟩ :=
      @SimpleGraph.IsTree.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule
        k _ V fV G _ _ htree hD
    let E := @signlessPreprojectiveAlgebraEquiv V V _ _ G G k _ instSub instG
      SimpleGraph.Iso.refl
    refine ⟨d, by simp only [Finset.mem_insert, Finset.mem_singleton] at hd; omega, E z,
      (@signlessPreprojectiveAlgebraEquiv_mem_signlessPreprojectiveGrade_iff V V _ _ G G k _
        instSub instG SimpleGraph.Iso.refl d z).mpr hz, fun h => hz0 ?_⟩
    simpa only [AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule E.symm h
  · exact exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic k hac

/-- **Every orientation of a connected non-Dynkin finite simple graph has a nonzero cyclic class in
path degree at least three in `Π_k(OrientedQuiver G o)`**, over every nontrivial commutative
ring. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.Connected)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix))
    (o : Orientation G) :
    ∃ d : ℕ, 3 ≤ d ∧ ∃ z ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      z ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  by_cases hac : G.IsAcyclic
  · obtain ⟨d, hd, z, hz, hz0⟩ :=
      hG.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule k hD
    let F := hac.isBipartite.signlessPreprojectiveAlgebraEquiv k o
    refine ⟨d, hd, F z,
      hac.isBipartite.signlessPreprojectiveAlgebraEquiv_mem_preprojectiveGrade k o hz,
      fun h => hz0 ?_⟩
    simpa only [AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule F.symm h
  · exact exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic k hac o

end SimpleGraph.Connected

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

/-! ### Complete characterization over a field -/

section Field

variable (k : Type*) [Field k]

/-- **Signless characterization of vanishing of the cyclic quotient in path degrees at least
three.** For a connected finite simple graph `G` over a field `k`, every homogeneous piece of
`Π⁺(G)` of path degree `d ≥ 3` lies in the commutator submodule if and only if `G` is isomorphic to
the diagram of a valid simply-laced Dynkin type `t` and `ringChar k` is not a bad prime for `t`. -/
theorem signlessPreprojective_cyclicQuotient_vanishes_iff {V : Type*} [Finite V]
    {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] (hG : G.Connected) :
    (∀ d : ℕ, 3 ≤ d → signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
    ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
      Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) := by
  constructor
  · intro h
    have hDyn : ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) := by
      by_contra hD
      obtain ⟨d, hd, z, hz, hz0⟩ :=
        hG.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule k hD
      exact hz0 (h d hd hz)
    obtain ⟨t, ht, hsl, ⟨e⟩⟩ := G.exists_valid_isSimplyLaced_dynkinType_iso_iff.mpr hDyn
    refine ⟨t, ht, hsl, ⟨e⟩, fun hb => ?_⟩
    obtain ⟨d, hd, z, hz, hz0⟩ :=
      exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k e ht hb
        ringChar.Nat.cast_ringChar
    exact hz0 (h d (by simp only [Finset.mem_insert, Finset.mem_singleton] at hd; omega) hz)
  · rintro ⟨t, -, hsl, ⟨e⟩, hnb⟩ d hd
    exact signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k e hsl
      ((forall_isBadPrime_isUnit_iff t).mpr hnb) (by omega)

/-- For a connected finite simple graph `G` over a field `k`, the cyclic quotient of `Π⁺(G)`
vanishes in all positive path degrees (`d > 0`) under the same condition as in degrees `d ≥ 3`:
`G` is isomorphic to the diagram of a valid simply-laced Dynkin type `t` and `ringChar k` is not a
bad prime for `t`. -/
theorem forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff {V : Type*} [Finite V]
    {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] (hG : G.Connected) :
    (∀ d : ℕ, 0 < d → signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
    ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
      Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) := by
  refine ⟨fun h => (signlessPreprojective_cyclicQuotient_vanishes_iff k hG).mp
    fun d hd => h d (by omega), ?_⟩
  rintro ⟨t, -, hsl, ⟨e⟩, hnb⟩ d hd
  exact signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k e hsl
    ((forall_isBadPrime_isUnit_iff t).mpr hnb) hd

/-- **Characterization of vanishing of the cyclic quotient in path degrees at least three.** Let `o`
orient a connected finite simple graph `G` and let `k` be a field. Every homogeneous piece of
`Π_k(OrientedQuiver G o)` of path degree `d ≥ 3` lies in the commutator submodule if and only if
`G` is isomorphic to the diagram of a valid simply-laced Dynkin type `t` and `ringChar k` is not a
bad prime for `t`. -/
theorem preprojective_cyclicQuotient_vanishes_iff {V : Type*} [Finite V]
    {G : SimpleGraph V} (hG : G.Connected) (o : Orientation G) :
    (∀ d : ℕ, 3 ≤ d → preprojectiveGrade k (OrientedQuiver G o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
    ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
      Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) := by
  constructor
  · intro h
    have hDyn : ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) := by
      by_contra hD
      obtain ⟨d, hd, z, hz, hz0⟩ :=
        hG.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule k hD o
      exact hz0 (h d hd hz)
    obtain ⟨t, ht, hsl, ⟨e⟩⟩ := G.exists_valid_isSimplyLaced_dynkinType_iso_iff.mpr hDyn
    refine ⟨t, ht, hsl, ⟨e⟩, fun hb => ?_⟩
    obtain ⟨d, hd, z, hz, hz0⟩ :=
      exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k e ht hb
        ringChar.Nat.cast_ringChar o
    exact hz0 (h d (by simp only [Finset.mem_insert, Finset.mem_singleton] at hd; omega) hz)
  · rintro ⟨t, -, hsl, ⟨e⟩, hnb⟩ d hd
    exact preprojectiveGrade_le_commutatorSubmodule_of_iso k e hsl
      ((forall_isBadPrime_isUnit_iff t).mpr hnb) o (by omega)

/-- For a connected finite simple graph `G` and any orientation `o` over a field `k`, the cyclic
quotient of `Π_k(OrientedQuiver G o)` vanishes in all positive path degrees (`d > 0`) under the
same condition as in degrees `d ≥ 3`: `G` is isomorphic to the diagram of a valid simply-laced
Dynkin type `t` and `ringChar k` is not a bad prime for `t`. -/
theorem forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff {V : Type*} [Finite V]
    {G : SimpleGraph V} (hG : G.Connected) (o : Orientation G) :
    (∀ d : ℕ, 0 < d → preprojectiveGrade k (OrientedQuiver G o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
    ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
      Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) := by
  refine ⟨fun h => (preprojective_cyclicQuotient_vanishes_iff k hG o).mp
    fun d hd => h d (by omega), ?_⟩
  rintro ⟨t, -, hsl, ⟨e⟩, hnb⟩ d hd
  exact preprojectiveGrade_le_commutatorSubmodule_of_iso k e hsl
    ((forall_isBadPrime_isUnit_iff t).mpr hnb) o hd

end Field

end TauCeti
