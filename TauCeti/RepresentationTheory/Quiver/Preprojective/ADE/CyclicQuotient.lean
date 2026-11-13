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
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Affine
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.GraphGrading

/-!
# Positive-degree cyclic quotients of preprojective algebras

For a finite quiver `Q` over a commutative ring `k`, the cyclic quotient `Π / [Π, Π]` of the
preprojective algebra inherits a grading from path length. This file assembles the type-by-type
results for `Aₙ`, `Dₙ`, `E₆`, `E₇`, and `E₈` together with the non-Dynkin obstructions of
`TauCeti.RepresentationTheory.Quiver.Preprojective.Affine` into a uniform characterization for
connected finite simple graphs.

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
system (and with the bad characteristics in Schedler, Theorem 13.1.1, Etingof--Eu, and Liu--Wang,
Theorem 1.1). Because `diagramGraph` forgets bond multiplicities, the root-system bad primes of the
multiply-laced types (`Bₙ`, `Cₙ`, `F₄`, `G₂`) do not obstruct the unweighted preprojective algebra
here, so `TauCeti.IsBadPrime` is defined in this preprojective module rather than on root systems.

## Main definitions and results

* `TauCeti.IsBadPrime`: the bad primes of `t : DynkinType` for the unweighted preprojective cyclic
  quotient.
* `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso`,
  `TauCeti.preprojectiveGrade_le_commutatorSubmodule_of_iso`, and
  `TauCeti.finrank_cyclicQuotient_preprojectiveAlgebra_of_iso`: when every bad prime of `t` is a
  unit in `k`, every positive-degree piece of the signless or oriented preprojective algebra of a
  graph isomorphic to `diagramGraph t.cartanMatrix` lies in the commutator submodule, the signless
  commutator submodule equals the augmentation kernel, and both cyclic quotients have dimension
  `t.rank`.
* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime` and
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime`: when `t` is
  valid, `p` is a bad prime of `t`, and `(p : k) = 0` in a nontrivial commutative ring `k`, a
  nonzero cyclic class appears in path degree `4`, `6`, or `10`.
* `TauCeti.forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff` and
  `TauCeti.forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff`: **over a field `k`, for any
  connected finite simple graph `G` and any orientation `o` of `G`, the cyclic quotient of
  `Π_k(OrientedQuiver G o)` vanishes in all path degrees `d ≥ 3` (equivalently, all `d > 0`) if and
  only if `G` is isomorphic to a valid simply-laced Dynkin diagram and `ringChar k` is not a bad
  prime of its type.**

## References

* P. Etingof and C.-H. Eu, *Hochschild and cyclic homology of preprojective algebras of ADE
  quivers*, Mosc. Math. J. 7 (2007), https://arxiv.org/abs/math/0609006.
* T. Schedler, *Hochschild homology of preprojective algebras over the integers*, Adv. Math. 214
  (2007), Theorem 13.1.1, https://arxiv.org/abs/math/0703475.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  Theorem 1.1 and Section 3, https://arxiv.org/abs/2301.06757.
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

private theorem exists_isSimplyLaced_diagramGraph_iso_isBadPrime (t : DynkinType) :
    ∃ s : DynkinType, s.IsSimplyLaced ∧ (∀ p, IsBadPrime s p ↔ IsBadPrime t p) ∧
      Nonempty (diagramGraph t.cartanMatrix ≃g diagramGraph s.cartanMatrix) := by
  have hpath {n : ℕ} {G : SimpleGraph (Fin n)} (hG : G = SimpleGraph.pathGraph n) :
      Nonempty (G ≃g diagramGraph (CartanMatrix.A n)) := by
    rw [hG, DynkinType.diagramGraph_cartanMatrix_A]
    exact ⟨SimpleGraph.Iso.refl⟩
  cases t with
  | A n | D n | E6 | E7 | E8 => exact ⟨_, by simp, fun _ => Iff.rfl, ⟨SimpleGraph.Iso.refl⟩⟩
  | B n =>
    refine ⟨.A n, by simp, by simp, ?_⟩
    simpa only [DynkinType.rank_B, DynkinType.cartanMatrix_B, DynkinType.rank_A,
      DynkinType.cartanMatrix_A] using hpath (G := diagramGraph (CartanMatrix.B n)) <| by
      ext i j
      rw [diagramGraph_adj, SimpleGraph.pathGraph_adj]
      simp [CartanMatrix.B, Fin.ext_iff]
      omega
  | C n =>
    refine ⟨.A n, by simp, by simp, ?_⟩
    simpa only [DynkinType.rank_C, DynkinType.cartanMatrix_C, DynkinType.rank_A,
      DynkinType.cartanMatrix_A] using hpath (G := diagramGraph (CartanMatrix.C n)) <| by
      ext i j
      rw [diagramGraph_adj, SimpleGraph.pathGraph_adj]
      simp [CartanMatrix.C, Fin.ext_iff]
      omega
  | F4 =>
    refine ⟨.A 4, by simp, by simp, ?_⟩
    simpa only [DynkinType.rank_F4, DynkinType.cartanMatrix_F4, DynkinType.rank_A,
      DynkinType.cartanMatrix_A] using hpath (G := diagramGraph CartanMatrix.F₄) <| by
      ext i j
      rw [diagramGraph_adj, SimpleGraph.pathGraph_adj]
      fin_cases i <;> fin_cases j <;> decide
  | G2 =>
    refine ⟨.A 2, by simp, by simp, ?_⟩
    simpa only [DynkinType.rank_G2, DynkinType.cartanMatrix_G2, DynkinType.rank_A,
      DynkinType.cartanMatrix_A] using hpath (G := diagramGraph CartanMatrix.G₂.transpose) <| by
      ext i j
      rw [diagramGraph_adj, SimpleGraph.pathGraph_adj]
      fin_cases i <;> fin_cases j <;> decide

/-! ### Vanishing in good characteristic -/

section GoodCharacteristic

attribute [local instance] SimpleGraph.neighborSetFintypeOfFinite

variable (k : Type*) [CommRing k]

private theorem signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_transport
    {V W : Type*} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    [∀ i, Fintype (G.neighborSet i)] [∀ j, Fintype (H.neighborSet j)] (e : G ≃g H)
    (hH : ∀ y : Quiver.TotalPath (DoubledQuiver H), 0 < y.2.2.length →
      signlessPreprojectiveMk k (DoubledQuiver H) (ofPath y) ∈
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)))
    (x : Quiver.TotalPath (DoubledQuiver G)) (hx : 0 < x.2.2.length) :
    signlessPreprojectiveMk k (DoubledQuiver G) (ofPath x) ∈
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  let E := signlessPreprojectiveAlgebraEquiv k e
  have hmap : E (signlessPreprojectiveMk k (DoubledQuiver G) (ofPath x)) ∈
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) := by
    rw [signlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk, pathAlgebraEquiv_ofPath]
    exact hH _ (by rwa [Prefunctor.length_mapTotalPath])
  simpa only [AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule E.symm hmap

/-- **When every bad prime of `t` is invertible in `k`, every positive-length path in the signless
preprojective algebra of a graph isomorphic to `diagramGraph t.cartanMatrix` lies in the commutator
submodule.** -/
theorem signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_iso
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] {t : DynkinType}
    (e : G ≃g diagramGraph t.cartanMatrix) (hbad : ∀ p, IsBadPrime t p → IsUnit (p : k))
    (x : Quiver.TotalPath (DoubledQuiver G)) (hx : 0 < x.2.2.length) :
    signlessPreprojectiveMk k (DoubledQuiver G) (ofPath x) ∈
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain ⟨s, hs, hbs, ⟨f⟩⟩ := exists_isSimplyLaced_diagramGraph_iso_isBadPrime t
  have hbads : ∀ p, IsBadPrime s p → IsUnit (p : k) := fun p hp => hbad p ((hbs p).mp hp)
  have ef : G ≃g diagramGraph s.cartanMatrix := e.trans f
  cases s with
  | A n =>
    exact signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_transport k ef
      (signlessPreprojectiveMk_A_ofPath_mem_commutatorSubmodule k) x hx
  | D n =>
    exact signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_transport k ef
      (signlessPreprojectiveMk_D_ofPath_mem_commutatorSubmodule k (hbads 2 rfl)) x hx
  | E6 =>
    exact signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_transport k ef
      (signlessPreprojectiveMk_E6_ofPath_mem_commutatorSubmodule k
        (hbads 2 (Or.inl rfl)) (hbads 3 (Or.inr rfl))) x hx
  | E7 =>
    exact signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_transport k ef
      (signlessPreprojectiveMk_E7_ofPath_mem_commutatorSubmodule k
        (hbads 2 (Or.inl rfl)) (hbads 3 (Or.inr rfl))) x hx
  | E8 =>
    have ef' : G ≃g zigzagE8Graph := by rwa [zigzagE8Graph_eq_diagramGraph]
    exact signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_transport k ef'
      (signlessPreprojectiveMk_E8_ofPath_mem_commutatorSubmodule k
        (hbads 2 (Or.inl rfl)) (hbads 3 (Or.inr (Or.inl rfl)))
        (hbads 5 (Or.inr (Or.inr rfl)))) x hx
  | B _ | C _ | F4 | G2 => simp at hs

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

private theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_transport
    {V W : Type*} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    [∀ i, Fintype (G.neighborSet i)] [∀ j, Fintype (H.neighborSet j)]
    (e : G ≃g H) {d : ℕ}
    (hH : ∃ z ∈ signlessPreprojectiveGrade k (DoubledQuiver H) d,
      z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H))) :
    ∃ z ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain ⟨z, hz, hz0⟩ := hH
  let E := signlessPreprojectiveAlgebraEquiv k e
  refine ⟨E.symm z, ?_, fun h => hz0 ?_⟩
  · rw [signlessPreprojectiveAlgebraEquiv_symm,
      signlessPreprojectiveAlgebraEquiv_mem_signlessPreprojectiveGrade_iff]
    exact hz
  · simpa only [AlgEquiv.apply_symm_apply] using map_mem_commutatorSubmodule E h

variable [Nontrivial k]

/-- **At a bad prime `p` of a valid Dynkin type `t`, if `(p : k) = 0` in a nontrivial commutative
ring `k`, then the signless preprojective algebra of any graph isomorphic to
`diagramGraph t.cartanMatrix` has a nonzero cyclic class in path degree `4`, `6`, or `10`.** -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
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
      exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_transport k e
        (exists_mem_signlessPreprojectiveGrade_D_four_notMem_commutatorSubmodule k
          (DynkinType.valid_D.mp ht) hp0)⟩
  | E6 =>
    have e' : G ≃g diagramGraph (CartanMatrix.E 6) := by rwa [DynkinType.cartanMatrix_E6] at e
    rcases hp with rfl | rfl
    · exact ⟨4, by simp,
        exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_transport k e'
          (exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule k
            (by decide) hp0)⟩
    · exact ⟨6, by simp,
        exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_transport k e'
          (exists_mem_signlessPreprojectiveGrade_E_six_notMem_commutatorSubmodule k
            (by decide) hp0)⟩
  | E7 =>
    have e' : G ≃g diagramGraph (CartanMatrix.E 7) := by rwa [DynkinType.cartanMatrix_E7] at e
    rcases hp with rfl | rfl
    · exact ⟨4, by simp,
        exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_transport k e'
          (exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule k
            (by decide) hp0)⟩
    · exact ⟨6, by simp,
        exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_transport k e'
          (exists_mem_signlessPreprojectiveGrade_E_six_notMem_commutatorSubmodule k
            (by decide) hp0)⟩
  | E8 =>
    rcases hp with rfl | rfl | rfl
    · have e' : G ≃g diagramGraph (CartanMatrix.E 8) := by rwa [DynkinType.cartanMatrix_E8] at e
      exact ⟨4, by simp,
        exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_transport k e'
          (exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule k
            (by decide) hp0)⟩
    · have e' : G ≃g diagramGraph (CartanMatrix.E 8) := by rwa [DynkinType.cartanMatrix_E8] at e
      exact ⟨6, by simp,
        exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_transport k e'
          (exists_mem_signlessPreprojectiveGrade_E_six_notMem_commutatorSubmodule k
            (by decide) hp0)⟩
    · have e' : G ≃g zigzagE8Graph := by rwa [zigzagE8Graph_eq_diagramGraph]
      exact ⟨10, by simp,
        exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_transport k e'
          ⟨signlessWord k zigzagE8Graph [3, 2, 3, 4, 3, 4, 3, 4, 3, 4, 3],
            signlessWord_E8_cyclicWord_mem_grade_ten k,
            signlessWord_E8_cyclicWord_notMem_commutatorSubmodule k hp0⟩⟩

/-- **At a bad prime `p` of a valid Dynkin type `t`, if `(p : k) = 0` in a nontrivial commutative
ring `k`, then the additive preprojective algebra of every orientation of any graph isomorphic to
`diagramGraph t.cartanMatrix` has a nonzero cyclic class in path degree `4`, `6`, or `10`.** -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
    {V : Type*} [Finite V] {G : SimpleGraph V}
    {t : DynkinType} (ht : t.Valid) (e : G ≃g diagramGraph t.cartanMatrix) (o : Orientation G)
    {p : ℕ} (hp : IsBadPrime t p) (hp0 : (p : k) = 0) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ), ∃ z ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      z ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  obtain ⟨d, hd, z, hz, hz0⟩ :=
    exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k ht e hp hp0
  have hb : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  let C := hb.coloringBool
  let E := C.signlessPreprojectiveAlgebraEquiv k o
  refine ⟨d, hd, E z, C.signlessPreprojectiveAlgebraEquiv_mem_preprojectiveGrade k o hz,
    fun h => hz0 ?_⟩
  simpa only [AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule E.symm h

end BadCharacteristic

/-! ### Complete characterization over a field -/

section Field

variable (k : Type*) [Field k]

private theorem isUnit_of_not_isBadPrime_ringChar {t : DynkinType}
    (hnotbad : ¬ IsBadPrime t (ringChar k)) (p : ℕ) (hp : IsBadPrime t p) :
    IsUnit (p : k) := by
  refine isUnit_iff_ne_zero.mpr fun hp0 => hnotbad ?_
  rwa [CharP.ringChar_of_prime_eq_zero hp.prime hp0]

/-- Over a field `k`, for a graph `G` isomorphic to the standard diagram of a valid Dynkin type `t`,
the positive-degree pieces of the signless preprojective algebra of `G` lie in the commutator
submodule if and only if `ringChar k` is not a bad prime of `t`. -/
theorem forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    {t : DynkinType} (ht : t.Valid) (e : G ≃g diagramGraph t.cartanMatrix) :
    (∀ d : ℕ, 0 < d → signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
      ¬ IsBadPrime t (ringChar k) := by
  refine ⟨fun h hbad => ?_, fun hnotbad d hd =>
    signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k e
      (isUnit_of_not_isBadPrime_ringChar k hnotbad) hd⟩
  obtain ⟨d, hd, z, hz, hz0⟩ :=
    exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k ht e hbad
      (CharP.cast_eq_zero k (ringChar k))
  have hdpos : 0 < d := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    omega
  exact hz0 (h d hdpos hz)

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
  constructor
  · intro h
    have hD : ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) := by
      by_contra hnot
      obtain ⟨d, hd3, x, hx, hx0⟩ :=
        exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_exists_dynkinType_iso
          k hG hnot o
      exact hx0 (h d hd3 hx)
    obtain ⟨t, ht, hsl, ⟨e⟩⟩ := (SimpleGraph.exists_valid_isSimplyLaced_dynkinType_iso_iff G).mpr hD
    refine ⟨t, ht, hsl, ⟨e⟩, fun hbad => ?_⟩
    obtain ⟨d, hd, z, hz, hz0⟩ :=
      exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k ht e o hbad
        (CharP.cast_eq_zero k (ringChar k))
    have hd3 : 3 ≤ d := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      omega
    exact hz0 (h d hd3 hz)
  · rintro ⟨t, -, -, ⟨e⟩, hnotbad⟩ d hd3
    exact preprojectiveGrade_le_commutatorSubmodule_of_iso k e o
      (isUnit_of_not_isBadPrime_ringChar k hnotbad) (by omega)

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
  refine ⟨fun h => (forall_three_le_preprojectiveGrade_le_commutatorSubmodule_iff k hG o).mp
      fun d hd3 => h d (by omega),
    fun ⟨t, _, _, ⟨e⟩, hnotbad⟩ d hd =>
      preprojectiveGrade_le_commutatorSubmodule_of_iso k e o
        (isUnit_of_not_isBadPrime_ringChar k hnotbad) hd⟩

end Field

end TauCeti
