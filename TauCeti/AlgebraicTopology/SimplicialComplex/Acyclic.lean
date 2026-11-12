/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SingleHomology
public import TauCeti.AlgebraicTopology.SimplicialComplex.ChainComplex

/-!
# Coning off ordered simplicial chains

Let `K` be a simplicial complex with linearly ordered vertices, and let `v` be a vertex. A cell
`c` of `K` all of whose vertices are smaller than `v`, and such that adjoining `v` to `c` gives a
face of `K`, has a *cone* `c * v`, the cell with vertex set `c ∪ {v}`, in which `v` is the last
vertex. Extending linearly, and sending the cells that cannot be coned off to zero, gives the
cone operator `TauCeti.OrderedSimplicialChain.cone` over any coefficient semiring, built from the
cone on a cell `AbstractSimplicialComplex.RealizationCell.cone`. Over a coefficient ring, on chains
supported on cells that can be coned off it satisfies the cone identities

* `∂ (z * v) = ε(z) [v] - z` in degree `0`, where `ε` sums the coefficients;
* `∂ (z * v) = (∂ z) * v + (-1) ^ (n + 1) z` in degree `n ≥ 1`.

If every finite set of vertices admits such a cone vertex, every cycle is supported on finitely
many vertices and is therefore the boundary of a multiple of its cone: the augmented ordered
chain complex of `K` is exact. The cone vertex is allowed to depend on the cycle, so the argument
proves exactness without producing a chain contraction. The main example is Milnor's countable
join, where a vertex over an index larger than every index in sight is a cone vertex.

## Main definitions

* `TauCeti.OrderedSimplicialChain.cone`: the cone operator on ordered simplicial chains.

## Main results

* `TauCeti.OrderedSimplicialChain.boundary_cone_zero`,
  `TauCeti.OrderedSimplicialChain.boundary_cone_succ`: the cone identities.
* `TauCeti.exactAt_orderedSimplicialChainComplex_of_cone`: the ordered chain complex is exact in
  positive degrees when every finite set of vertices has a cone vertex.
* `TauCeti.exists_boundary_eq_of_boundary_eq_zero_of_cone`,
  `TauCeti.exists_boundary_eq_of_augmentation_eq_zero_of_cone`: the same statements for
  individual chains, in positive degrees and in degree `0`.
* `TauCeti.quasiIso_orderedSimplicialChainComplexAugmentation_of_cone`: the augmentation is a
  quasi-isomorphism, so the ordered chain complex is a resolution of the coefficient ring.

The proof that the augmentation is a quasi-isomorphism follows the proof of
`Rep.FiniteCyclicGroup.resolution_quasiIso` in
`Mathlib/RepresentationTheory/Homological/FiniteCyclic.lean`.

## References

* J. R. Munkres, *Elements of Algebraic Topology*, Addison-Wesley, 1984, Section 8, the bracket
  operation and the acyclicity of cones.
* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
-/

public section

noncomputable section

open CategoryTheory Finsupp

universe u v

open AbstractSimplicialComplex

namespace TauCeti

variable {ι : Type u} [LinearOrder ι] {K : AbstractSimplicialComplex ι}

namespace OrderedSimplicialChain

section Semiring

variable (R : Type v) [Semiring R]

/-- The **cone operator** with cone vertex `v` on ordered simplicial `n`-chains: a cell all of
whose vertices are smaller than `v`, and to which `v` can be adjoined, goes to its cone
`RealizationCell.cone`; every other cell goes to `0`. -/
def cone (v : ι) (n : ℕ) : OrderedSimplicialChain K R n →ₗ[R] OrderedSimplicialChain K R (n + 1) :=
  open Classical in
  linearCombination R fun c ↦
    if h : (∀ w ∈ c.1.1, w < v) ∧ insert v c.1.1 ∈ K then single (c.cone v h.1 h.2) 1 else 0

variable {R}

/-- The cone operator sends a multiple of a cell that can be coned off at `v` to the same
multiple of its cone. -/
@[simp]
theorem cone_single {v : ι} {n : ℕ} (c : RealizationCell K n) (hlt : ∀ w ∈ c.1.1, w < v)
    (hK : insert v c.1.1 ∈ K) (a : R) :
    cone R v n (single c a) = single (c.cone v hlt hK) a := by
  simp [cone, iff_true_intro hlt, hK]

/-- The cone operator sends a multiple of a cell that cannot be coned off at `v` to `0`. -/
@[simp]
theorem cone_single_of_not {v : ι} {n : ℕ} (c : RealizationCell K n)
    (h : ¬((∀ w ∈ c.1.1, w < v) ∧ insert v c.1.1 ∈ K)) (a : R) :
    cone R v n (single c a) = 0 := by
  simp [cone, h]

end Semiring

variable {R : Type v} [Ring R]

/-- **The cone identity in degree `0`.** For a `0`-chain supported on vertices smaller than `v`
and joined to `v` by an edge, the boundary of its cone is its augmentation times `[v]`, minus the
chain. -/
theorem boundary_cone_zero {v : ι} {z : OrderedSimplicialChain K R 0}
    (hz : ∀ c ∈ z.support, (∀ w ∈ c.1.1, w < v) ∧ insert v c.1.1 ∈ K) :
    boundary R 0 (cone R v 0 z) =
      single (RealizationCell.vertex K v) (linearCombination R (fun _ ↦ (1 : R)) z) - z := by
  classical
  conv_lhs => rw [← z.sum_single]
  conv_rhs => rw [← z.sum_single]
  simp only [Finsupp.sum, map_sum, linearCombination_single, smul_eq_mul, mul_one,
    Finsupp.single_finsetSum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  obtain ⟨hlt, hK⟩ := hz c hc
  -- Splitting off the last vertex puts the second face in the form of `face_cone_last`.
  rw [cone_single c hlt hK, boundary_single, Fin.sum_univ_castSucc,
    RealizationCell.face_cone_last]
  simp [sub_eq_add_neg]

/-- **The cone identity in positive degrees.** For an `(n + 1)`-chain supported on cells that can
be coned off at `v`, the boundary of its cone is the cone on its boundary plus
`(-1) ^ (n + 2)` times the chain. -/
theorem boundary_cone_succ {v : ι} {n : ℕ} {z : OrderedSimplicialChain K R (n + 1)}
    (hz : ∀ c ∈ z.support, (∀ w ∈ c.1.1, w < v) ∧ insert v c.1.1 ∈ K) :
    boundary R (n + 1) (cone R v (n + 1) z) =
      cone R v n (boundary R n z) + (-1 : R) ^ (n + 2) • z := by
  classical
  conv_lhs => rw [← z.sum_single]
  conv_rhs => rw [← z.sum_single]
  simp only [Finsupp.sum, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  obtain ⟨hlt, hK⟩ := hz c hc
  rw [cone_single c hlt hK, boundary_single, Fin.sum_univ_castSucc, Fin.val_last,
    RealizationCell.face_cone_last, boundary_single, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Fin.val_castSucc, RealizationCell.face_cone_castSucc, map_smul,
    cone_single (c.face j) _ (c.insert_face_mem j hK)]

end OrderedSimplicialChain

open OrderedSimplicialChain

section Exactness

variable (R : Type v) [Ring R]

/-- If every finite set of vertices has a cone vertex, every chain is supported on cells that can
be coned off at a common vertex. -/
private theorem exists_cone_vertex_of_cone
    (h : ∀ s : Finset ι, ∃ v, (∀ w ∈ s, w < v) ∧ ∀ σ ∈ K, σ ⊆ s → insert v σ ∈ K) {n : ℕ}
    (z : OrderedSimplicialChain K R n) :
    ∃ v, ∀ c ∈ z.support, (∀ w ∈ c.1.1, w < v) ∧ insert v c.1.1 ∈ K := by
  classical
  obtain ⟨v, hlt, hK⟩ := h (z.support.biUnion fun c ↦ c.1.1)
  exact ⟨v, fun c hc ↦ ⟨fun w hw ↦ hlt w (Finset.mem_biUnion.mpr ⟨c, hc, hw⟩),
    hK _ c.1.2 (Finset.subset_biUnion_of_mem (fun c ↦ c.1.1) hc)⟩⟩

variable {R}
variable (h : ∀ s : Finset ι, ∃ v, (∀ w ∈ s, w < v) ∧ ∀ σ ∈ K, σ ⊆ s → insert v σ ∈ K)
include h

/-- **Cycles are boundaries.** If every finite set of vertices `s` has a cone vertex, a vertex `v`
larger than every vertex of `s` that can be adjoined to every face of `K` on `s`, then every
ordered `(n + 1)`-cycle of `K` is a boundary. -/
theorem exists_boundary_eq_of_boundary_eq_zero_of_cone {n : ℕ}
    {z : OrderedSimplicialChain K R (n + 1)} (hz : boundary R n z = 0) :
    ∃ y, boundary R (n + 1) y = z := by
  obtain ⟨v, hv⟩ := exists_cone_vertex_of_cone R h z
  refine ⟨(-1 : R) ^ (n + 2) • cone R v (n + 1) z, ?_⟩
  simp [boundary_cone_succ hv, hz, smul_smul, ← pow_add, Even.neg_one_pow ⟨n + 2, rfl⟩]

/-- **Exactness in degree `0`.** If every finite set of vertices has a cone vertex, every ordered
`0`-chain of `K` whose coefficients sum to zero is a boundary. -/
theorem exists_boundary_eq_of_augmentation_eq_zero_of_cone
    {z : OrderedSimplicialChain K R 0} (hz : linearCombination R (fun _ ↦ (1 : R)) z = 0) :
    ∃ y, boundary R 0 y = z := by
  obtain ⟨v, hv⟩ := exists_cone_vertex_of_cone R h z
  exact ⟨-cone R v 0 z, by simp [boundary_cone_zero hv, hz]⟩

/-- The ordered chain complex of a complex in which every finite set of vertices has a cone
vertex is exact in every positive degree. -/
theorem exactAt_orderedSimplicialChainComplex_of_cone (n : ℕ) :
    (orderedSimplicialChainComplex K R).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  refine (exact_orderedSimplicialChainComplex_d_iff R _
    (eqToIso (orderedSimplicialChainComplex_X R n)) (g' := boundary R n) (by simp)).2 fun z hz ↦ ?_
  exact exists_boundary_eq_of_boundary_eq_zero_of_cone h hz

end Exactness

section Augmentation

variable {R : Type u} [Ring R]

/-- **The ordered chain complex is a resolution.** If every finite set of vertices of `K` has a
cone vertex, a vertex larger than all of them that can be adjoined to every face of `K` on them,
then the augmentation of the ordered chain complex of `K` is a quasi-isomorphism. -/
theorem quasiIso_orderedSimplicialChainComplexAugmentation_of_cone
    (h : ∀ s : Finset ι, ∃ v, (∀ w ∈ s, w < v) ∧ ∀ σ ∈ K, σ ⊆ s → insert v σ ∈ K) :
    QuasiIso (orderedSimplicialChainComplexAugmentation K R) where
  quasiIsoAt m := by
    cases m with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ (by simp) rfl rfl]
      let ε := linearCombination R fun _ : RealizationCell K 0 ↦ (1 : R)
      refine ⟨(exact_orderedSimplicialChainComplex_d_iff R _
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (ModuleCat.of R R))
        (g' := ε) (by simp [ε])).2 fun z hz ↦ ?_, ?_⟩
      · exact exists_boundary_eq_of_augmentation_eq_zero_of_cone h hz
      · have : Epi (ModuleCat.ofHom ε) := by
          rw [ModuleCat.epi_iff_surjective]
          intro r
          obtain ⟨v, -⟩ := h ∅
          exact ⟨single (RealizationCell.vertex K v) r, by simp [ε]⟩
        simp only [HomologicalComplex.shortComplexFunctor'_map_τ₂,
          orderedSimplicialChainComplexAugmentation_f_zero]
        infer_instance
    | succ m =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
      exact exactAt_orderedSimplicialChainComplex_of_cone h m

end Augmentation

end TauCeti
