/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.D4.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Preprojective.InducedSubgraph
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Isomorphism
import all TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.Basic
import all TauCeti.RepresentationTheory.Quiver.Preprojective.InducedSubgraph

/-!
# The bad characteristic of the type-`D` cyclic quotient

For every `n ≥ 4`, the degree-four cyclic quotient of the signless preprojective algebra of
`Dₙ` is nonzero in characteristic two. Retaining the final four Bourbaki nodes gives an induced
`D₄` subdiagram. The quotient killing the other nodes sends the closed walk through the fork,
its adjacent long-arm node, and one fork leaf to the detecting walk in `D₄`.

Over a field, combine this class with the positive-degree vanishing away from characteristic
two: the degree-four piece consists of commutators exactly when `2 ≠ 0`. The bipartite sign
rescaling gives both statements for the additive preprojective algebra of every orientation.
These are statements about zeroth Hochschild homology, not intrinsic formality itself.

Products are in later-factor-first order. The nonvanishing argument works over every nontrivial
commutative ring with `2 = 0`, without a field hypothesis. As in the neighboring type-`D`
modules, select `forkNeighborSetFintype` when writing signless quotient carriers.

## References

* P. Etingof and C.-H. Eu, *Hochschild and cyclic homology of preprojective algebras of ADE
  quivers*, https://arxiv.org/abs/math/0609006.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, for the role of these cyclic classes in bad characteristic.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

attribute [local instance] forkNeighborSetFintype

private def d4ForkNodes {n : ℕ} (hn : 4 ≤ n) : Fin 4 ↪ Fin (DynkinType.D n).rank where
  toFun i := Fin.cast (DynkinType.rank_D n).symm ⟨n - 4 + i.val, by have := i.isLt; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have he := congrArg Fin.val h
    simp only [Fin.val_cast] at he
    omega

private theorem d4ForkNodes_val {n : ℕ} (hn : 4 ≤ n) (i : Fin 4) :
    (d4ForkNodes hn i).val = n - 4 + i.val := by
  rfl

private def d4ForkEmbedding {n : ℕ} (hn : 4 ≤ n) :
    zigzagD4Graph ↪g diagramGraph (DynkinType.D n).cartanMatrix where
  toEmbedding := d4ForkNodes hn
  map_rel_iff' := by
    intro i j
    -- Apply the graph equality to adjacency, without rewriting the dependent vertex type.
    have h4 := (Iff.of_eq (congrArg (fun H : SimpleGraph (Fin 4) => H.Adj i j)
      zigzagD4Graph_eq_diagramGraph)).trans (diagramGraph_D_adj (n := 4) (by omega) i j)
    refine (diagramGraph_D_adj (n := n) (by omega)
      (d4ForkNodes hn i) (d4ForkNodes hn j)).trans (Iff.trans ?_ h4.symm)
    simp only [d4ForkNodes_val]
    have := i.isLt
    have := j.isLt
    omega

section CommRing

variable (k : Type*) [CommRing k] {n : ℕ}

local notation "G" => diagramGraph (DynkinType.cartanMatrix (DynkinType.D n))
local notation "Π" => signlessPreprojectiveAlgebra k (DoubledQuiver G)

-- Align the neighborhood enumerations of the two existing quotient constructions.
attribute [local instance] d4NeighborSetFintype

private noncomputable def d4ForkQuotient (hn : 4 ≤ n) :
    Π →ₐ[k] signlessPreprojectiveAlgebra k (DoubledQuiver zigzagD4Graph) :=
  (signlessPreprojectiveAlgebraEquiv k (d4ForkEmbedding hn).isoInduceRange.symm).toAlgHom.comp
    (signlessPreprojectiveInducedSubgraphHom k G (Set.range (d4ForkEmbedding hn)))

private theorem d4ForkQuotient_arrow (hn : 4 ≤ n) {i j : Fin 4}
    (h : zigzagD4Graph.Adj i j) :
    d4ForkQuotient k hn
        (signlessArrow k G (d4ForkEmbedding hn i).val (d4ForkEmbedding hn j).val) =
      signlessArrow k zigzagD4Graph i.val j.val := by
  classical
  have hi : d4ForkEmbedding hn i ∈ Set.range (d4ForkEmbedding hn) := ⟨i, rfl⟩
  have hj : d4ForkEmbedding hn j ∈ Set.range (d4ForkEmbedding hn) := ⟨j, rfl⟩
  rw [signlessArrow_of_adj k ((d4ForkEmbedding hn).map_adj_iff.mpr h),
    signlessArrow_of_adj k h]
  apply (signlessPreprojectiveAlgebraEquiv k (d4ForkEmbedding hn).isoInduceRange).injective
  simp only [d4ForkQuotient, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    ← signlessPreprojectiveAlgebraEquiv_symm, AlgEquiv.apply_symm_apply,
    signlessPreprojectiveInducedSubgraphHom_ofArrow, dite_eq_left hi, dite_eq_left hj,
    signlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk, pathAlgebraEquiv_ofArrow]
  -- Via Equiv.ofInjective, isoInduceRange sends each vertex i to ⟨f i, ⟨i, rfl⟩⟩;
  -- these are the same range vertices chosen by the induced-subgraph quotient above.
  rfl

/-- In characteristic two, the signless preprojective algebra of `Dₙ`, `n ≥ 4`, has a
homogeneous element of degree four which is not a sum of commutators. -/
theorem exists_mem_signlessPreprojectiveGrade_D_four_notMem_commutatorSubmodule
    [Nontrivial k] (hn : 4 ≤ n) (h2 : (2 : k) = 0) :
    ∃ z : Π, z ∈ signlessPreprojectiveGrade k (DoubledQuiver G) 4 ∧
      z ∉ commutatorSubmodule k Π := by
  let f := d4ForkEmbedding hn
  let a := fun i j : Fin 4 => signlessArrow k G (f i).val (f j).val
  let z := a 2 1 * (a 1 2 * (a 0 1 * a 1 0))
  have ha (i j : Fin 4) : a i j ∈ signlessPreprojectiveGrade k (DoubledQuiver G) 1 :=
    signlessArrow_mem_signlessPreprojectiveGrade_one k _ _
  have hz : z ∈ signlessPreprojectiveGrade k (DoubledQuiver G) 4 :=
    mul_mem_signlessPreprojectiveGrade k _ (ha 2 1)
      (mul_mem_signlessPreprojectiveGrade k _ (ha 1 2)
        (mul_mem_signlessPreprojectiveGrade k _ (ha 0 1) (ha 1 0)))
  refine ⟨z, hz, fun h => ?_⟩
  have hmap : d4ForkQuotient k hn z = signlessWord k zigzagD4Graph [1, 2, 1, 0, 1] := by
    simp only [z, a, f, map_mul, d4ForkQuotient_arrow k hn (by decide : zigzagD4Graph.Adj 2 1),
      d4ForkQuotient_arrow k hn (by decide : zigzagD4Graph.Adj 1 2),
      d4ForkQuotient_arrow k hn (by decide : zigzagD4Graph.Adj 0 1),
      d4ForkQuotient_arrow k hn (by decide : zigzagD4Graph.Adj 1 0),
      signlessWord_cons_cons, signlessWord_singleton,
      signlessArrow_mul_vertexIdempotent, ↓reduceIte]
  apply signlessWord_D4_cyclicWord_not_mem_commutatorSubmodule k h2
  rw [← hmap]
  exact map_mem_commutatorSubmodule (d4ForkQuotient k hn) h

/-- In characteristic two, the additive preprojective algebra of every orientation of `Dₙ`,
`n ≥ 4`, has a degree-four element which is not a sum of commutators. -/
theorem exists_mem_preprojectiveGrade_D_four_notMem_commutatorSubmodule
    [Nontrivial k] (hn : 4 ≤ n) (h2 : (2 : k) = 0) (o : Orientation G) :
    ∃ z : preprojectiveAlgebra k (OrientedQuiver G o),
      z ∈ preprojectiveGrade k (OrientedQuiver G o) 4 ∧
        z ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  obtain ⟨z, hz, hz0⟩ :=
    exists_mem_signlessPreprojectiveGrade_D_four_notMem_commutatorSubmodule k hn h2
  let C := dColoring n
  let E := C.signlessPreprojectiveAlgebraEquiv k o
  refine ⟨E z, C.signlessPreprojectiveAlgebraEquiv_mem_preprojectiveGrade k o hz, ?_⟩
  intro h
  apply hz0
  simpa only [AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule E.symm h

end CommRing

section Field

variable {k : Type*} [Field k] {n : ℕ}

local notation "G" => diagramGraph (DynkinType.cartanMatrix (DynkinType.D n))
local notation "Π" => signlessPreprojectiveAlgebra k (DoubledQuiver G)

/-- For `Dₙ`, `n ≥ 4`, the degree-four cyclic quotient vanishes exactly outside
characteristic two. -/
theorem signlessPreprojectiveGrade_D_four_le_commutatorSubmodule_iff (hn : 4 ≤ n) :
    signlessPreprojectiveGrade k (DoubledQuiver G) 4 ≤ commutatorSubmodule k Π ↔
      (2 : k) ≠ 0 := by
  refine ⟨fun h h2 => ?_, fun h2 => ?_⟩
  · obtain ⟨z, hz, hz0⟩ :=
      exists_mem_signlessPreprojectiveGrade_D_four_notMem_commutatorSubmodule k hn h2
    exact hz0 (h hz)
  · exact signlessPreprojectiveGrade_D_le_commutatorSubmodule k
      (isUnit_iff_ne_zero.mpr h2) (by decide)

/-- For every orientation of `Dₙ`, `n ≥ 4`, the degree-four cyclic quotient of the additive
preprojective algebra vanishes exactly outside characteristic two. -/
theorem preprojectiveGrade_D_four_le_commutatorSubmodule_iff (hn : 4 ≤ n)
    (o : Orientation G) :
    preprojectiveGrade k (OrientedQuiver G o) 4 ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) ↔ (2 : k) ≠ 0 := by
  refine ⟨fun h h2 => ?_, fun h2 => ?_⟩
  · obtain ⟨z, hz, hz0⟩ :=
      exists_mem_preprojectiveGrade_D_four_notMem_commutatorSubmodule k hn h2 o
    exact hz0 (h hz)
  · exact preprojectiveGrade_D_le_commutatorSubmodule k o
      (isUnit_iff_ne_zero.mpr h2) (by decide)

end Field

end TauCeti
