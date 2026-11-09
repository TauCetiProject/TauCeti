/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.D4.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Preprojective.InducedSubgraph
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Isomorphism
import all TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.D4.Basic
import all TauCeti.RepresentationTheory.Quiver.Preprojective.InducedSubgraph

/-!
# Characteristic-two cyclic classes from induced `D₄` subdiagrams

An induced copy of `D₄` in a finite graph gives a quotient of signless preprojective algebras.
In characteristic two, lift the degree-four cyclic class of `D₄` along this quotient. Its lift
cannot be a sum of commutators, since algebra homomorphisms preserve sums of commutators.
This applies in particular to the branching vertices of the finite `D` and `E` diagrams.
The copy must be induced: an arbitrary graph homomorphism does not give this quotient.

Products use later-factor-first order. The lifted class traverses two distinct backtracks at
the branch vertex. No field hypothesis is required, only a nontrivial commutative ring with
`2 = 0`. Quotient carriers use the neighborhood enumerations `Fintype.ofFinite`.

## References

* P. Etingof and C.-H. Eu, *Hochschild and cyclic homology of preprojective algebras of ADE
  quivers*, https://arxiv.org/abs/math/0609006.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, for the bad-characteristic cyclic classes.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

attribute [local instance] d4NeighborSetFintype inducedSubgraphNeighborSetFintype

variable (k : Type*) [CommRing k] {V : Type*} [Finite V] {G : SimpleGraph V}

private noncomputable def d4EmbeddingQuotient (f : zigzagD4Graph ↪g G) :
    signlessPreprojectiveAlgebra k (DoubledQuiver G) →ₐ[k]
      signlessPreprojectiveAlgebra k (DoubledQuiver zigzagD4Graph) :=
  (signlessPreprojectiveAlgebraEquiv k f.isoInduceRange.symm).toAlgHom.comp
    (signlessPreprojectiveInducedSubgraphHom k G (Set.range f))

private theorem d4EmbeddingQuotient_arrow (f : zigzagD4Graph ↪g G) {i j : Fin 4}
    (h : zigzagD4Graph.Adj i j) :
    d4EmbeddingQuotient k f
        (signlessPreprojectiveMk k _ (ofArrow (arrow G (f.map_adj_iff.mpr h)))) =
      signlessArrow k zigzagD4Graph i.val j.val := by
  classical
  have hi : f i ∈ Set.range f := ⟨i, rfl⟩
  have hj : f j ∈ Set.range f := ⟨j, rfl⟩
  rw [signlessArrow_of_adj k h]
  apply (signlessPreprojectiveAlgebraEquiv k f.isoInduceRange).injective
  simp only [d4EmbeddingQuotient, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    ← signlessPreprojectiveAlgebraEquiv_symm, AlgEquiv.apply_symm_apply,
    signlessPreprojectiveInducedSubgraphHom_ofArrow, dite_eq_left hi, dite_eq_left hj,
    signlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk, pathAlgebraEquiv_ofArrow]
  -- Both constructions identify i with the range vertex ⟨f i, ⟨i, rfl⟩⟩.
  rfl

/-- An induced `D₄` subdiagram detects a nonzero degree-four cyclic class in characteristic
two. This holds over every nontrivial commutative coefficient ring. -/
theorem exists_mem_signlessPreprojectiveGrade_four_notMem_commutatorSubmodule_of_d4_embedding
    [Nontrivial k] (f : zigzagD4Graph ↪g G) (h2 : (2 : k) = 0) :
    ∃ z : signlessPreprojectiveAlgebra k (DoubledQuiver G),
      z ∈ signlessPreprojectiveGrade k (DoubledQuiver G) 4 ∧
        z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  let a := fun {i j : Fin 4} (h : zigzagD4Graph.Adj i j) =>
    signlessPreprojectiveMk k _ (ofArrow (arrow G (f.map_adj_iff.mpr h)))
  let h21 : zigzagD4Graph.Adj 2 1 := by decide
  let h12 : zigzagD4Graph.Adj 1 2 := by decide
  let h01 : zigzagD4Graph.Adj 0 1 := by decide
  let h10 : zigzagD4Graph.Adj 1 0 := by decide
  let z := a h21 * (a h12 * (a h01 * a h10))
  have ha {i j : Fin 4} (h : zigzagD4Graph.Adj i j) :
      a h ∈ signlessPreprojectiveGrade k (DoubledQuiver G) 1 :=
    signlessPreprojectiveMk_mem_grade k _ (ofArrow_mem_grade_one _)
  refine ⟨z, mul_mem_signlessPreprojectiveGrade k _ (ha h21)
    (mul_mem_signlessPreprojectiveGrade k _ (ha h12)
      (mul_mem_signlessPreprojectiveGrade k _ (ha h01) (ha h10))), fun h => ?_⟩
  have hmap : d4EmbeddingQuotient k f z = signlessWord k zigzagD4Graph [1, 2, 1, 0, 1] := by
    simp only [z, a, map_mul, d4EmbeddingQuotient_arrow k f h21,
      d4EmbeddingQuotient_arrow k f h12, d4EmbeddingQuotient_arrow k f h01,
      d4EmbeddingQuotient_arrow k f h10,
      signlessWord_cons_cons, signlessWord_singleton,
      signlessArrow_mul_vertexIdempotent, ↓reduceIte]
  apply signlessWord_D4_cyclicWord_not_mem_commutatorSubmodule k h2
  rw [← hmap]
  exact map_mem_commutatorSubmodule (d4EmbeddingQuotient k f) h

end TauCeti
