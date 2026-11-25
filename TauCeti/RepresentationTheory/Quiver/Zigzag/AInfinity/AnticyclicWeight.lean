/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.WordPairing
import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.AnticyclicWeight

/-!
# Anticyclic word weights on Dynkin graphs

Let `G` be a finite simple graph. The word pairings of `TauCeti.zigzagWordPairing` detect
Hochschild classes of the zigzag algebra of `G` through weights `a` on the words of `n + 2` darts
which are anticyclic and satisfy the signless relation. On a bipartite graph whose signless
preprojective algebra `Π⁺(G)` is spanned by commutators in degree `n + 2`, such weights vanish on
every closed walk of length `n + 2`
(`SimpleGraph.IsBipartite.eq_zero_of_le_commutatorSubmodule_of_anticyclic`).

For a graph isomorphic to the diagram `diagramGraph t.cartanMatrix` of a Dynkin type `t` whose bad
primes are invertible in `k`, every element of `Π⁺(G)` of positive degree is a sum of commutators
(`TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso`). Dynkin diagrams are trees,
hence bipartite, so every anticyclic weight satisfying the signless relation vanishes on the
closed walks, and every word pairing of this kind vanishes on the higher operations of the loop
deformations `TauCeti.zigzagLoopAInfinityAlgebra`. Thus these pairings cannot detect a nonzero
Hochschild class of a loop operation in good characteristic, in contrast with the non-Dynkin
trees of `TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.Tree`.

## Main results

* `TauCeti.eq_zero_of_iso_diagramGraph_of_anticyclic`: on a graph isomorphic to a Dynkin diagram
  whose bad primes are units, an anticyclic weight satisfying the signless relation vanishes on
  every closed walk of length `n + 2`.
* `TauCeti.zigzagWordPairing_obstruction_eq_zero_of_iso`: on such a graph, the word pairings of
  anticyclic weights satisfying the signless relation vanish on the higher operations of all loop
  deformations.

## References

* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, Sections 3 and 4, for the comparison of zigzag Hochschild
  cohomology with the cyclic quotient of the preprojective algebra.
* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 4, for the
  signless relation of the quadratic dual of the zigzag algebra.
-/

public section

namespace TauCeti

variable {k : Type*} [CommRing k] {V : Type*} [Finite V] {G : SimpleGraph V} [Fintype G.Dart]
  [DecidableEq V]

/-- **Anticyclic weights vanish on the closed walks of a Dynkin graph in good characteristic.** Let
`G` be isomorphic to the diagram of a Dynkin type `t` whose bad primes are all units in `k`. Then
every weight `a` on the words of `n + 2` darts which is anticyclic, `a (u, e) = -a (e, u)`, and
satisfies the signless relation in the first two positions vanishes on every closed walk of length
`n + 2`. -/
theorem eq_zero_of_iso_diagramGraph_of_anticyclic {t : DynkinType}
    (hbad : ∀ p, IsBadPrime t p → IsUnit (p : k)) (e : G ≃g diagramGraph t.cartanMatrix)
    {n : ℕ} {a : (Fin (n + 2) → G.Dart) → k}
    (hrot : ∀ (u : Fin (n + 1) → G.Dart) (e : G.Dart), a (Fin.snoc u e) = -a (Fin.cons e u))
    (hrel : ∀ (u : Fin n → G.Dart) (v : V),
      ∑ d : G.Dart with d.snd = v, a (Fin.cons d (Fin.cons d.symm u)) = 0)
    {w : Fin (n + 2) → G.Dart} (hw : ∀ i, (w i).fst = (w (i + 1)).snd) :
    a w = 0 :=
  have := fun v ↦ Fintype.ofFinite (G.neighborSet v)
  SimpleGraph.IsBipartite.eq_zero_of_le_commutatorSubmodule_of_anticyclic
    (SimpleGraph.Colorable.of_hom e.toHom t.isBipartite_diagramGraph_cartanMatrix)
    (signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k e hbad (by omega)) hrot hrel hw

/-- **Word pairings of anticyclic weights vanish on the loop operations of a Dynkin graph in good
characteristic.** Let `G` be isomorphic to the diagram of a Dynkin type `t` whose bad primes are
all units in `k`, and let `a` be a weight on the words of `n + 2` darts, `n ≥ 1`, which is
anticyclic and satisfies the signless relation in the first two positions. Then the word pairing
`Λ_a` vanishes on the operation of arity `n + 2` of every loop deformation of the strict zigzag
algebra of `G`. So no such pairing shows that this operation is not a Hochschild coboundary. -/
theorem zigzagWordPairing_obstruction_eq_zero_of_iso {hns : ∀ i : V, ∃ j, G.Adj i j}
    {t : DynkinType} (hbad : ∀ p, IsBadPrime t p → IsUnit (p : k))
    (e : G ≃g diagramGraph t.cartanMatrix) {n : ℕ} (hn : 1 ≤ n)
    {a : (Fin (n + 2) → G.Dart) → k}
    (hrot : ∀ (u : Fin (n + 1) → G.Dart) (e : G.Dart), a (Fin.snoc u e) = -a (Fin.cons e u))
    (hrel : ∀ (u : Fin n → G.Dart) (v : V),
      ∑ d : G.Dart with d.snd = v, a (Fin.cons d (Fin.cons d.symm u)) = 0)
    (c : (Fin (n + 2) → G.Dart) →₀ k)
    (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd) :
    zigzagWordPairing hns n a ((zigzagLoopAInfinityAlgebra hns c hc).obstruction
      (zigzagStrictAInfinityAlgebra k hns) ⟨n + 2, by omega⟩) = 0 := by
  rw [zigzagWordPairing_obstruction hn, Finset.sum_eq_zero fun w _ ↦ ?_, mul_zero]
  by_cases hw : w ∈ c.support
  · rw [eq_zero_of_iso_diagramGraph_of_anticyclic hbad e hrot hrel (hc w hw), zero_mul]
  · rw [Finsupp.notMem_support_iff.1 hw, mul_zero]

end TauCeti
