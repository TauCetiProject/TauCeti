/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.D4.InducedSubgraph
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.Basic
import all TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.Basic

/-!
# Characteristic two in the exceptional preprojective cyclic quotients

For every `n ≥ 5`, the Bourbaki-labelled graph of `CartanMatrix.E n` contains an induced `D₄`:
retain the branch vertex `3` and its neighbors `1`, `2`, `4`. Consequently its signless
preprojective algebra has a nonzero degree-four cyclic class over every nontrivial commutative
ring of characteristic two. Bipartite sign rescaling gives the same result for the additive
preprojective algebra of every orientation.

In particular, this detects characteristic two as a bad characteristic for each of `E₆`, `E₇`
and `E₈`. It concerns zeroth Hochschild homology; it does not assert intrinsic nonformality.
The other bad characteristics, three and (for `E₈`) five, require different cyclic classes.
The statements use the neighborhood enumerations `Fintype.ofFinite`, as in the type-`E`
finite-dimensionality results.

## References

* P. Etingof and C.-H. Eu, *Hochschild and cyclic homology of preprojective algebras of ADE
  quivers*, https://arxiv.org/abs/math/0609006.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, for the exceptional bad characteristics and their role in
  zigzag deformation theory.
-/

public section

namespace TauCeti

open DoubledQuiver

attribute [local instance] SimpleGraph.neighborSetFintypeOfFinite

private def eBranchNodes {n : ℕ} (hn : 5 ≤ n) : Fin 4 ↪ Fin n where
  toFun i := ⟨![1, 3, 2, 4] i, by fin_cases i <;> simp <;> omega⟩
  inj' := by
    intro i j h
    have hval := congrArg Fin.val h
    fin_cases i <;> fin_cases j <;> simp_all

private theorem eBranchNodes_val {n : ℕ} (hn : 5 ≤ n) (i : Fin 4) :
    (eBranchNodes hn i).val = ![1, 3, 2, 4] i := by
  rfl

private def eBranchEmbedding {n : ℕ} (hn : 5 ≤ n) :
    zigzagD4Graph ↪g diagramGraph (CartanMatrix.E n) where
  toEmbedding := eBranchNodes hn
  map_rel_iff' := by
    intro i j
    rw [diagramGraph_E_adj]
    simp only [eBranchNodes_val, EAdj]
    fin_cases i <;> fin_cases j <;> simp [zigzagD4Graph_adj]

variable (k : Type*) [CommRing k] [Nontrivial k] {n : ℕ}

/-- In characteristic two, the signless preprojective algebra of the Bourbaki-labelled `Eₙ`
graph, `n ≥ 5`, has a degree-four element which is not a sum of commutators. In particular this
applies to each exceptional finite Dynkin diagram. -/
theorem exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule
    (hn : 5 ≤ n) (h2 : (2 : k) = 0) :
    ∃ z : signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph (CartanMatrix.E n))),
      z ∈ signlessPreprojectiveGrade k (DoubledQuiver (diagramGraph (CartanMatrix.E n))) 4 ∧
        z ∉ commutatorSubmodule k
          (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph (CartanMatrix.E n)))) :=
  exists_mem_signlessPreprojectiveGrade_four_notMem_commutatorSubmodule_of_d4_embedding
    k (eBranchEmbedding hn) h2

/-- In characteristic two, the additive preprojective algebra of every orientation of the
Bourbaki-labelled `Eₙ` graph, `n ≥ 5`, has a nonzero degree-four cyclic class. -/
theorem exists_mem_preprojectiveGrade_E_four_notMem_commutatorSubmodule
    (hn : 5 ≤ n) (h2 : (2 : k) = 0) (o : Orientation (diagramGraph (CartanMatrix.E n))) :
    ∃ z : preprojectiveAlgebra k (OrientedQuiver (diagramGraph (CartanMatrix.E n)) o),
      z ∈ preprojectiveGrade k (OrientedQuiver (diagramGraph (CartanMatrix.E n)) o) 4 ∧
        z ∉ commutatorSubmodule k
          (preprojectiveAlgebra k (OrientedQuiver (diagramGraph (CartanMatrix.E n)) o)) := by
  obtain ⟨z, hz, hz0⟩ :=
    exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule k hn h2
  let C := eColoring _ (diagramGraph_E_adj (n := n))
  let E := C.signlessPreprojectiveAlgebraEquiv k o
  refine ⟨E z, C.signlessPreprojectiveAlgebraEquiv_mem_preprojectiveGrade k o hz, ?_⟩
  intro h
  apply hz0
  simpa only [AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule E.symm h

end TauCeti
