/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Coset.Comparison
public import TauCeti.GroupTheory.FreeGroup.FiniteIndex

/-!
# Finite index subgroups of free groups and complete graphs

A subgroup `H` of a free group has finite index if and only if its subgroup graph `Γ(H)` has
finitely many vertices and is complete, and then the index of `H` is the number of vertices
of `Γ(H)`. More generally the same holds for every folded graph all of whose vertices are
reachable from its base vertex and the subgroup it accepts, and the index of the subgroup
accepted by a connected folded complete graph is its number of vertices, finite or not. A
complete graph with finitely many vertices accepts a subgroup of finite index.

The comparison is made in the coset graph. A based morphism from a complete graph to a coset
graph is surjective on vertices, so the vertices of a connected folded complete graph
correspond to the cosets of the subgroup it accepts. Conversely, in a connected folded complete
graph accepting a subgroup of finite index every reduced path from the base vertex extends
to a reduced closed path, so such a graph is a core; this applies to the coset graph of a
subgroup of finite index, which is therefore isomorphic to its subgroup graph. Hence the core
of a folded graph accepting a subgroup of finite index is complete, so every dart leaving a
core vertex is a core dart, and every vertex reachable from the base vertex is a core vertex.

No finiteness assumption on the alphabet is needed. Over a finite alphabet the subgroup graph
of a subgroup of finite index also has finitely many darts.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 8, Definition 8.1 and Proposition 8.3.
-/

public section

namespace TauCeti.StallingsGraph

variable {α : Type*} {S : StallingsGraph α} {H : Subgroup (FreeGroup α)}

/-- A based morphism from a complete graph to a coset graph is surjective on vertices. -/
theorem IsComplete.surjective_mapV_cosetGraph (hS : S.IsComplete) (f : S.Hom H.cosetGraph) :
    Function.Surjective f.graphHom.mapV := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨b, p, hp⟩ := hS.exists_path_read S.base x⁻¹
    exact ⟨b, by rw [f.mapV_eq_coset p, hp, inv_inv]⟩

/-- The vertices of a connected folded complete graph correspond to the cosets of the
subgroup it accepts: its number of vertices is the index of that subgroup. Both are zero when
there are infinitely many vertices. -/
theorem IsComplete.index_subgroup (hS : S.IsComplete) (hfold : S.IsFolded)
    (hreach : ∀ v : S.graph.V, Nonempty (S.graph.Path S.base v)) :
    (S.subgroup S.base).index = Nat.card S.graph.V := by
  obtain ⟨f⟩ := (nonempty_hom_cosetGraph_iff hreach).mpr (le_refl (S.subgroup S.base))
  rw [Subgroup.index_eq_card]
  exact (Nat.card_congr (Equiv.ofBijective _
    ⟨(f.injective_cosetGraph hfold hreach).1, hS.surjective_mapV_cosetGraph f⟩)).symm

/-- A complete graph with finitely many vertices accepts a subgroup of finite index, whether
or not all its vertices are reachable from the base vertex. -/
theorem IsComplete.finiteIndex_subgroup [Finite S.graph.V] (hS : S.IsComplete) :
    (S.subgroup S.base).FiniteIndex := by
  choose b p hp using hS.exists_path_read S.base
  have hread : ∀ g c (hc : b g = c), S.read (hc ▸ p g) = g := by
    rintro g c rfl
    exact hp g
  have key : ∀ g g', b g = b g' → g * g'⁻¹ ∈ S.subgroup S.base := by
    intro g g' h
    have := S.read_mem_subgroup ((h ▸ p g).comp (p g').reverse)
    rwa [read_comp, read_reverse, hread, hp] at this
  refine Subgroup.finiteIndex_iff_finite_quotient.mpr (Finite.of_injective
    (fun q : FreeGroup α ⧸ S.subgroup S.base => b q.out⁻¹) fun q r h => ?_)
  rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' r]
  exact QuotientGroup.eq.mpr (by simpa using key _ _ h)

/-- In a folded complete graph accepting a subgroup of finite index, every reduced path from
the base vertex extends to a reduced closed path, so all its darts are core darts. -/
private theorem IsComplete.mem_coreDarts_of_isReduced [(S.subgroup S.base).FiniteIndex]
    (hS : S.IsComplete) (hfold : S.IsFolded) {v : S.graph.V} (p : S.graph.Path S.base v)
    (hp : SerreGraph.Path.IsReduced S.graph p) {e : S.graph.E}
    (he : e ∈ SerreGraph.Path.darts S.graph p) : e ∈ S.graph.coreDarts S.base := by
  obtain ⟨w, hw, hmem⟩ := (hfold.isReduced_word S p hp).exists_append_mem (S.subgroup S.base)
  obtain ⟨c, r, rfl⟩ := hS.exists_path_word v w
  rw [← S.word_comp, ← S.read_eq_mk_word] at hmem
  rw [← S.word_comp] at hw
  obtain rfl : c = S.base :=
    (hfold.eq_tgt_iff_read_mul_inv_mem S (p.comp r) .nil).mpr (by simpa using hmem)
  exact (S.graph.mem_coreDarts_iff S.base e).mpr
    ⟨p.comp r, S.isReduced_of_isReduced_word _ hw, by simp [he]⟩

/-- In a folded complete graph accepting a subgroup of finite index, every dart leaving the
end of a reduced path from the base vertex is a core dart. -/
private theorem IsComplete.mem_coreDarts_of_src_eq [(S.subgroup S.base).FiniteIndex]
    (hS : S.IsComplete) (hfold : S.IsFolded) {v : S.graph.V} (q : S.graph.Path S.base v)
    (hq : SerreGraph.Path.IsReduced S.graph q) {e : S.graph.E} (he : S.graph.src e = v) :
    e ∈ S.graph.coreDarts S.base := by
  by_cases h : SerreGraph.Path.IsReduced S.graph
      (q.cons (⟨e, he, rfl⟩ : Quiver.Hom v (S.graph.tgt e)))
  · exact hS.mem_coreDarts_of_isReduced hfold _ h (by simp)
  · -- Otherwise `q` ends with the reverse of `e`, which is therefore a core dart.
    cases q with
    | nil => exact absurd (SerreGraph.Path.isReduced_toPath S.graph _) h
    | cons q f =>
      have hf : e = S.graph.rev f.1 := by
        by_contra hne
        exact h ((SerreGraph.Path.isReduced_cons_cons S.graph q f _).mpr ⟨hq, hne⟩)
      rw [← S.graph.rev_mem_coreDarts_iff, hf, S.graph.rev_rev]
      exact hS.mem_coreDarts_of_isReduced hfold _ hq (by simp)

/-- A connected folded complete graph accepting a subgroup of finite index is a core at its
base vertex. -/
private theorem IsComplete.isCore [(S.subgroup S.base).FiniteIndex] (hS : S.IsComplete)
    (hfold : S.IsFolded) (hreach : ∀ v : S.graph.V, Nonempty (S.graph.Path S.base v)) :
    S.graph.IsCore S.base := by
  refine (S.graph.isCore_iff S.base).mpr ⟨hreach, fun e => ?_⟩
  obtain ⟨p⟩ := hreach (S.graph.src e)
  obtain ⟨q, hq, -⟩ := S.exists_reduced_path_read_eq p
  exact (S.graph.mem_coreDarts_iff S.base e).mp (hS.mem_coreDarts_of_src_eq hfold q hq rfl)

end TauCeti.StallingsGraph

namespace Subgroup

open TauCeti TauCeti.StallingsGraph

variable {α : Type*} (H : Subgroup (FreeGroup α))

/-- The coset graph of a subgroup of finite index is a core at the coset of the identity. -/
theorem cosetGraph_isCore [H.FiniteIndex] : (cosetGraph H).graph.IsCore (cosetGraph H).base := by
  have : ((cosetGraph H).subgroup (cosetGraph H).base).FiniteIndex := by
    rwa [cosetGraph_subgroup]
  exact (cosetGraph_isComplete H).isCore (cosetGraph_isFolded H) (cosetGraph_base_reachable H)

end Subgroup

namespace TauCeti.StallingsGraph

variable {α : Type*} {S : StallingsGraph α}

/-- A folded based core graph accepting a subgroup of finite index is isomorphic to the coset
graph of that subgroup. -/
private theorem nonempty_iso_cosetGraph_of_isCore [(S.subgroup S.base).FiniteIndex]
    (hfold : S.IsFolded) (hcore : S.graph.IsCore S.base) :
    Nonempty (Iso S (S.subgroup S.base).cosetGraph) :=
  (nonempty_iso_iff_subgroup_eq hfold (S.subgroup S.base).cosetGraph_isFolded hcore
    (S.subgroup S.base).cosetGraph_isCore).mpr (S.subgroup S.base).cosetGraph_subgroup.symm

/-- In a folded graph accepting a subgroup of finite index, every dart leaving a core vertex is
a core dart. -/
private theorem IsFolded.mem_coreDarts_of_src_mem [(S.subgroup S.base).FiniteIndex]
    (hfold : S.IsFolded) {e : S.graph.E} (he : S.graph.src e ∈ S.graph.coreVertices S.base) :
    e ∈ S.graph.coreDarts S.base := by
  have : (S.core.subgroup S.core.base).FiniteIndex := by rwa [core_base, core_subgroup]
  obtain ⟨f⟩ := nonempty_iso_cosetGraph_of_isCore hfold.core S.core_isCore
  obtain ⟨e', hs, hl⟩ :=
    (f.isComplete_iff.mpr (Subgroup.cosetGraph_isComplete _)).exists_dart ⟨_, he⟩ (S.label e)
  obtain rfl : e'.1 = e := S.isFolded_def.mp hfold e'.1 e (congrArg Subtype.val hs) hl
  exact e'.2

/-- In a folded graph accepting a subgroup of finite index, every vertex reachable from the base
vertex is a core vertex. -/
private theorem IsFolded.mem_coreVertices [(S.subgroup S.base).FiniteIndex] (hfold : S.IsFolded)
    {v : S.graph.V} (p : S.graph.Path S.base v) : v ∈ S.graph.coreVertices S.base := by
  induction p with
  | nil => exact (S.graph.mem_coreVertices_iff _ _).mpr (Or.inl rfl)
  | cons q e ih =>
    obtain ⟨e, rfl, rfl⟩ := e
    exact S.graph.tgt_mem_coreVertices S.base (hfold.mem_coreDarts_of_src_mem ih)

/-- In a folded graph accepting a subgroup of finite index, every dart of a path from the base
vertex lies on a reduced closed path at the base vertex. -/
theorem IsFolded.mem_coreDarts_of_mem_darts [(S.subgroup S.base).FiniteIndex]
    (hfold : S.IsFolded) {v : S.graph.V} (p : S.graph.Path S.base v) {e : S.graph.E}
    (he : e ∈ SerreGraph.Path.darts S.graph p) : e ∈ S.graph.coreDarts S.base := by
  obtain ⟨q, r, rfl⟩ := SerreGraph.Path.exists_eq_cons_comp_of_mem_darts S.graph p he
  exact hfold.mem_coreDarts_of_src_mem (hfold.mem_coreVertices q)

/-- A folded graph accepting a subgroup of finite index, all of whose vertices are reachable
from the base vertex, is a core at its base vertex. -/
theorem IsFolded.isCore_of_finiteIndex [(S.subgroup S.base).FiniteIndex] (hfold : S.IsFolded)
    (hreach : ∀ v : S.graph.V, Nonempty (S.graph.Path S.base v)) : S.graph.IsCore S.base := by
  refine (S.graph.isCore_iff S.base).mpr ⟨hreach, fun e => ?_⟩
  obtain ⟨q⟩ := hreach (S.graph.src e)
  exact (S.graph.mem_coreDarts_iff S.base e).mp
    (hfold.mem_coreDarts_of_mem_darts (q.cons (S.graph.dart e)) (by simp))

/-- A folded graph accepting a subgroup of finite index, all of whose vertices are reachable
from the base vertex, is isomorphic to the coset graph of that subgroup. -/
theorem nonempty_iso_cosetGraph [(S.subgroup S.base).FiniteIndex] (hfold : S.IsFolded)
    (hreach : ∀ v : S.graph.V, Nonempty (S.graph.Path S.base v)) :
    Nonempty (Iso S (S.subgroup S.base).cosetGraph) :=
  nonempty_iso_cosetGraph_of_isCore hfold (hfold.isCore_of_finiteIndex hreach)

/-- The subgroup accepted by a folded graph all of whose vertices are reachable from the base
vertex has finite index if and only if the graph has finitely many vertices and is complete. -/
theorem finiteIndex_subgroup_iff (hfold : S.IsFolded)
    (hreach : ∀ v : S.graph.V, Nonempty (S.graph.Path S.base v)) :
    (S.subgroup S.base).FiniteIndex ↔ Finite S.graph.V ∧ S.IsComplete := by
  refine ⟨fun h => ?_, fun ⟨_, hS⟩ => hS.finiteIndex_subgroup⟩
  obtain ⟨f⟩ := nonempty_iso_cosetGraph hfold hreach
  have : Finite (FreeGroup α ⧸ S.subgroup S.base) := Subgroup.finiteIndex_iff_finite_quotient.mp h
  exact ⟨Finite.of_equiv _ f.vertexEquiv.symm,
    f.isComplete_iff.mpr (S.subgroup S.base).cosetGraph_isComplete⟩

/-- A folded graph with finitely many vertices, all reachable from the base vertex, is complete
if and only if the subgroup it accepts has finite index. -/
theorem isComplete_iff_finiteIndex_subgroup [Finite S.graph.V] (hfold : S.IsFolded)
    (hreach : ∀ v : S.graph.V, Nonempty (S.graph.Path S.base v)) :
    S.IsComplete ↔ (S.subgroup S.base).FiniteIndex := by
  rw [finiteIndex_subgroup_iff hfold hreach, and_iff_right ‹_›]

end TauCeti.StallingsGraph

namespace Subgroup

open TauCeti TauCeti.StallingsGraph

variable {α : Type*} (H : Subgroup (FreeGroup α))

/-- A subgroup of a free group has finite index if and only if its subgroup graph has finitely
many vertices and is complete. -/
theorem finiteIndex_iff_finite_and_isComplete_subgroupGraph :
    H.FiniteIndex ↔ Finite (subgroupGraph H).graph.V ∧ (subgroupGraph H).IsComplete := by
  rw [← finiteIndex_subgroup_iff (subgroupGraph_isFolded H)
    ((SerreGraph.isCore_iff _ _).mp (subgroupGraph_isCore H)).1, subgroupGraph_subgroup]

/-- The subgroup graph of a subgroup of finite index has finitely many vertices. -/
instance subgroupGraph_finite_vertex [H.FiniteIndex] : Finite (subgroupGraph H).graph.V :=
  ((finiteIndex_iff_finite_and_isComplete_subgroupGraph H).mp ‹_›).1

/-- Over a finite alphabet, the subgroup graph of a subgroup of finite index has finitely many
darts. -/
instance subgroupGraph_finite_dart [Finite α] [H.FiniteIndex] :
    Finite (subgroupGraph H).graph.E :=
  (subgroupGraph_isFolded H).finite_E

/-- The subgroup graph of a subgroup of finite index is complete. -/
theorem subgroupGraph_isComplete [H.FiniteIndex] : (subgroupGraph H).IsComplete :=
  ((finiteIndex_iff_finite_and_isComplete_subgroupGraph H).mp ‹_›).2

/-- The index of a subgroup of finite index of a free group is the number of vertices of its
subgroup graph. -/
theorem index_eq_natCard_subgroupGraph [H.FiniteIndex] :
    H.index = Nat.card (subgroupGraph H).graph.V := by
  have h := (subgroupGraph_isComplete H).index_subgroup (subgroupGraph_isFolded H)
    ((SerreGraph.isCore_iff _ _).mp (subgroupGraph_isCore H)).1
  rwa [subgroupGraph_subgroup] at h

/-- The subgroup graph of a subgroup of finite index is the whole coset graph. -/
theorem nonempty_iso_subgroupGraph_cosetGraph [H.FiniteIndex] :
    Nonempty (Iso (subgroupGraph H) (cosetGraph H)) :=
  (nonempty_iso_iff_subgroup_eq (subgroupGraph_isFolded H) (cosetGraph_isFolded H)
    (subgroupGraph_isCore H) (cosetGraph_isCore H)).mpr
    ((subgroupGraph_subgroup H).trans (cosetGraph_subgroup H).symm)

end Subgroup
