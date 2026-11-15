/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.CyclicQuotient.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.CyclicQuotient.Cycle
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.Tree

/-!
# Positive-degree cyclic classes of preprojective algebras of non-Dynkin graphs

Let `G` be a finite connected simple graph that is not isomorphic to the diagram of any valid
Dynkin type. Over every nontrivial commutative ring `k`, both the signless preprojective algebra
`Π⁺(G)` and the additive preprojective algebra `Π_k(Q)` of any orientation `Q` of `G` possess a
homogeneous element of path degree `d ≥ 3` outside the commutator submodule.

The proof splits according to whether `G` is acyclic:

* If `G` is acyclic, then `G` is a finite non-Dynkin tree. By
  `SimpleGraph.IsTree.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule`, an affine
  `Dₙ`, `E₆`, `E₇` or `E₈` subdiagram produces a nonzero cyclic class in `Π⁺(G)` in degree `4`,
  `6`, `8` or `12`, which transfers to every orientation via the bipartite comparison
  `SimpleGraph.Coloring.signlessPreprojectiveAlgebraEquiv`.
* If `G` is not acyclic, then a simple cycle of length `d ≥ 3` produces a degree-`d` cyclic class
  directly via `TauCeti.RepresentationTheory.Quiver.Preprojective.CyclicQuotient.Cycle`.

## Main results

* `SimpleGraph.Connected.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule`:
  positive-degree (`d ≥ 3`) cyclic nonvanishing for `Π⁺(G)` when `G` is connected and non-Dynkin.
* `SimpleGraph.Connected.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule`:
  positive-degree (`d ≥ 3`) cyclic nonvanishing for `Π_k(OrientedQuiver G o)` for every orientation
  `o` of a connected non-Dynkin graph `G`.

## References

* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math. Res.
  Lett. 14 (2007).
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757.
-/

public section

namespace SimpleGraph.Connected

open TauCeti DoubledQuiver

universe u w

variable {k : Type w} [CommRing k] [Nontrivial k] {V : Type u} [Finite V] {G : SimpleGraph V}

/-- Every finite connected non-Dynkin simple graph has a homogeneous element of path degree `d ≥ 3`
outside the commutator submodule of its signless preprojective algebra `Π⁺(G)` over any nontrivial
commutative ring `k`. -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule
    (hG : G.Connected)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix))
    [instN : ∀ i, Fintype (G.neighborSet i)] :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  by_cases hac : G.IsAcyclic
  · classical
    let _ : Fintype V := Fintype.ofFinite V
    have hinst : instN = fun v => Subtype.fintype (· ∈ G.neighborSet v) := Subsingleton.elim _ _
    cases hinst
    have htree : G.IsTree := ⟨hG, hac⟩
    obtain ⟨d, hd, x, hx_grade, hx_comm⟩ :=
      htree.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule (k := k) hD
    have hd3 : 3 ≤ d := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      omega
    exact ⟨d, hd3, x, hx_grade, hx_comm⟩
  · exact exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic k hac

/-- Every orientation of a finite connected non-Dynkin simple graph has a homogeneous element of
path degree `d ≥ 3` outside the commutator submodule of its preprojective algebra over any
nontrivial commutative ring `k`. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule
    (hG : G.Connected)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix))
    (o : Orientation G)
    [instV : Fintype (OrientedQuiver G o)]
    [instHom : ∀ i j : OrientedQuiver G o, Fintype (i ⟶ j)] :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  by_cases hac : G.IsAcyclic
  · have hv : instV = OrientedQuiver.instFintypeOfFinite G o := Subsingleton.elim _ _
    cases hv
    have hh : instHom = OrientedQuiver.instFintypeHom G o := Subsingleton.elim _ _
    cases hh
    let _ : ∀ i, Fintype (G.neighborSet i) := fun v => Fintype.ofFinite (G.neighborSet v)
    obtain ⟨d, hd3, x, hx_grade, hx_comm⟩ :=
      hG.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule (k := k) hD
    let C := hac.isBipartite.coloringBool
    let e := C.signlessPreprojectiveAlgebraEquiv k o
    refine ⟨d, hd3, e x, C.signlessPreprojectiveAlgebraEquiv_mem_preprojectiveGrade k o hx_grade,
      fun hmem => hx_comm ?_⟩
    simpa only [AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule e.symm hmem
  · exact exists_mem_preprojectiveGrade_orientedQuiver_notMem_commutatorSubmodule_of_not_isAcyclic
      k hac o

end SimpleGraph.Connected
