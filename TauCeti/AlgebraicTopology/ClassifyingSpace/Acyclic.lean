/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.CWComplex
public import TauCeti.AlgebraicTopology.SimplicialComplex.Acyclic

/-!
# The ordered chains of Milnor's countable join are a resolution

Order the vertices of the countable join `indexedJoin fun _ : ℕ => G` by
`TauCeti.universalGSpaceVertexOrder`, so that vertices with smaller index come first; this is the
orientation of the cells of `universalGSpace G`. For any finite set of vertices, a vertex over an
index larger than all the indices that occur is larger than all of them, and it can be adjoined
to every face on them. So every finite set of vertices has a cone vertex, and the general cone
argument (`TauCeti.quasiIso_orderedSimplicialChainComplexAugmentation_of_cone`) shows that the
augmented ordered chain complex of the countable join is exact: the augmentation is a
quasi-isomorphism onto the coefficient ring in degree `0`
(`TauCeti.quasiIso_orderedSimplicialChainComplexAugmentation_indexedJoin`).

This is the exactness half of the statement that the ordered chains of the countable join are a
free resolution of the trivial module over the group ring, the source of the explicit
comparison `TauCeti.universalGSpaceToStandardComplex` with Mathlib's standard resolution. Only
`Nonempty G` is used: no group structure is needed for exactness.

## Main results

* `TauCeti.exists_forall_lt_insert_mem_indexedJoin`: every finite set of vertices of the
  countable join has a cone vertex.
* `TauCeti.exactAt_orderedSimplicialChainComplex_indexedJoin`: the ordered chain complex of the
  countable join is exact in positive degrees.
* `TauCeti.quasiIso_orderedSimplicialChainComplexAugmentation_indexedJoin`: its augmentation is a
  quasi-isomorphism.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Chapter I, Section 5.
-/

public section

noncomputable section

namespace TauCeti

universe u v

variable {G : Type u} [Nonempty G]

attribute [local instance] universalGSpaceVertexOrder

/-- **Every finite set of vertices of the countable join has a cone vertex.** A vertex over an
index larger than every index of a finite vertex set `s` is larger than every vertex of `s`, and
adjoining it to a face on `s` gives a face. -/
theorem exists_forall_lt_insert_mem_indexedJoin (s : Finset (Σ _ : ℕ, G)) :
    ∃ v, (∀ w ∈ s, w < v) ∧
      ∀ σ ∈ indexedJoin (fun _ : ℕ => G), σ ⊆ s → insert v σ ∈ indexedJoin fun _ : ℕ => G := by
  obtain ⟨g⟩ := ‹Nonempty G›
  have hlt : ∀ w ∈ s, w.1 < (s.sup Sigma.fst + 1) := fun w hw ↦
    Nat.lt_succ_of_le (Finset.le_sup (f := Sigma.fst) hw)
  refine ⟨⟨s.sup Sigma.fst + 1, g⟩, fun w hw ↦ universalGSpaceVertexOrder_lt_of_fst_lt (hlt w hw),
    fun σ hσ hσs ↦ ?_⟩
  rw [mem_indexedJoin_iff] at hσ ⊢
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  rw [Finset.coe_insert, Set.injOn_insert fun hv ↦ (hlt _ (hσs hv)).false]
  exact ⟨hσ.2, fun ⟨w, hw, hwv⟩ ↦ (hlt w (hσs hw)).ne hwv⟩

/-- The ordered chain complex of the countable join is exact in every positive degree. -/
theorem exactAt_orderedSimplicialChainComplex_indexedJoin (R : Type v) [Ring R] (n : ℕ) :
    (orderedSimplicialChainComplex (indexedJoin fun _ : ℕ => G) R).ExactAt (n + 1) :=
  exactAt_orderedSimplicialChainComplex_of_cone exists_forall_lt_insert_mem_indexedJoin n

/-- **The ordered chains of the countable join are a resolution.** The augmentation of the
ordered chain complex of the countable join, which sums the coefficients of a `0`-chain, is a
quasi-isomorphism onto the coefficient ring placed in degree `0`. -/
theorem quasiIso_orderedSimplicialChainComplexAugmentation_indexedJoin (R : Type u) [Ring R] :
    QuasiIso (orderedSimplicialChainComplexAugmentation (indexedJoin fun _ : ℕ => G) R) :=
  quasiIso_orderedSimplicialChainComplexAugmentation_of_cone
    exists_forall_lt_insert_mem_indexedJoin

end TauCeti
