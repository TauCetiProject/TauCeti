/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Preprojective.GraphOrientation
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Augmentation
import TauCeti.RepresentationTheory.Quiver.Preprojective.InducedSubgraph
import TauCeti.RepresentationTheory.Quiver.Preprojective.Isomorphism

/-!
# Cyclic quotients of preprojective algebras from their paths

The cyclic quotient `Π / [Π, Π]` of a preprojective algebra is spanned by the classes of paths.
This file collects the steps of a vanishing argument for the cyclic quotient in positive degrees
which do not depend on the graph: once every path of positive length is known to be a sum of
commutators, the same holds for the graded pieces of positive degree, the commutator submodule is
the kernel of the augmentation, so that the cyclic quotient is the module of vertex coefficients,
and, for a two-coloured graph, the vanishing transfers to the additive preprojective algebra of
every orientation. Moreover, degree-`d` vanishing descends along induced-subgraph embeddings and is
invariant under graph isomorphisms and bipartite orientation changes. The only paths which need a
graph-specific argument are the closed ones: a path between distinct vertices is a commutator with
its target idempotent.

## Main results

* `TauCeti.signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_ne`: a path between distinct
  vertices is a sum of commutators.
* `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule` and
  `TauCeti.preprojectiveGrade_le_commutatorSubmodule`: if every path of positive length is a sum of
  commutators, then so is every graded piece of positive degree.
* `TauCeti.commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker`: if every path of positive
  length is a sum of commutators, the commutator submodule is the augmentation kernel.
* `TauCeti.signlessPreprojectiveCyclicQuotientEquiv` and
  `TauCeti.finrank_cyclicQuotient_signlessPreprojectiveAlgebra`: in that case the augmentation
  identifies the cyclic quotient with the module of vertex coefficients, of dimension the number of
  vertices over a nontrivial ring.
* `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_of_embedding`,
  `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_embedding` and
  `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso`: degree-`d` signless
  cyclic quotient vanishing descends to induced subgraphs and is invariant under graph
  isomorphisms.
* `SimpleGraph.Coloring.preprojectiveMk_ofPath_mem_commutatorSubmodule`,
  `SimpleGraph.Coloring.preprojectiveGrade_le_commutatorSubmodule_iff` and
  `SimpleGraph.IsBipartite.preprojectiveGrade_le_commutatorSubmodule_iff`: for a two-coloured or
  bipartite graph, degree-`d` cyclic quotient vanishing agrees between the signless algebra and the
  additive preprojective algebra of every orientation.

## References

* J.-L. Loday, *Cyclic Homology*, Section 1.1, for the cyclic quotient as zeroth Hochschild
  homology.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

section Signless

variable (k : Type w) [CommRing k] {R : Type u} [Quiver.{v} R] [HasReverse R] [Finite R]
  [∀ x : R, Fintype (Quiver.Star x)]

local notation "Π" => signlessPreprojectiveAlgebra k R
local notation "π" => signlessPreprojectiveMk k R

/-- **A path between distinct vertices is a sum of commutators**: it is the commutator
`e_b * p - p * e_b` of the path `p` with its target idempotent `e_b`. -/
theorem signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_ne {a b : R} (p : Path a b)
    (hab : a ≠ b) : π (ofPath ⟨a, b, p⟩) ∈ commutatorSubmodule k Π := by
  have hcomm := mul_sub_mul_mem_commutatorSubmodule k Π
    (π (vertexIdempotent k b)) (π (ofPath ⟨a, b, p⟩))
  rwa [← map_mul, ← map_mul, vertexIdempotent_mul_ofPath,
    ofPath_mul_vertexIdempotent_of_ne _ hab.symm, map_zero, sub_zero] at hcomm

/-- **If every path of positive length is a sum of commutators, then so is every graded piece of
positive degree** of the signless algebra. -/
theorem signlessPreprojectiveGrade_le_commutatorSubmodule
    (h : ∀ x : Quiver.TotalPath R, 0 < x.2.2.length → π (ofPath x) ∈ commutatorSubmodule k Π)
    {d : ℕ} (hd : 0 < d) : signlessPreprojectiveGrade k R d ≤ commutatorSubmodule k Π := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_signlessPreprojectiveGrade_iff k R).1 hx
  rw [grade_eq_span_range] at hy
  refine (Submodule.span_le
    (p := (commutatorSubmodule k Π).comap (π : pathAlgebra k R →ₐ[k] Π).toLinearMap)).2 ?_ hy
  rintro _ ⟨⟨p, hp⟩, rfl⟩
  exact h p (hp ▸ hd)

/-- **If every path of positive length is a sum of commutators, then the commutator submodule of
the signless algebra is the augmentation kernel.** The augmentation onto the commutative algebra of
vertex coefficients kills commutators, and every element of its kernel is a combination of paths
of positive length. -/
theorem commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker
    (h : ∀ x : Quiver.TotalPath R, 0 < x.2.2.length → π (ofPath x) ∈ commutatorSubmodule k Π) :
    commutatorSubmodule k Π =
      LinearMap.ker (signlessPreprojectiveAugmentation (R := R) k).toLinearMap := by
  refine le_antisymm ((commutatorSubmodule_le_ker_iff _).2 fun x y => ?_) fun x hx => ?_
  · simp only [AlgHom.toLinearMap_apply, map_mul, mul_comm]
  · rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply, ← RingHom.mem_ker,
      ker_signlessPreprojectiveAugmentation,
      Ideal.mem_map_iff_of_surjective _ (signlessPreprojectiveMk_surjective k R)] at hx
    obtain ⟨f, hf, rfl⟩ := hx
    rw [← (pathAlgebraBasis k R).linearCombination_repr f, Finsupp.linearCombination_apply,
      Finsupp.sum, map_sum]
    refine Submodule.sum_mem _ fun x hx => ?_
    rw [map_smul, coe_pathAlgebraBasis]
    exact Submodule.smul_mem _ _ (h x (mem_arrowIdeal_iff.1 hf x (Finsupp.mem_support_iff.1 hx)))

/-- **If every path of positive length is a sum of commutators, then the cyclic quotient of the
signless algebra is the module of vertex coefficients**, by the augmentation. -/
noncomputable def signlessPreprojectiveCyclicQuotientEquiv
    (h : ∀ x : Quiver.TotalPath R, 0 < x.2.2.length → π (ofPath x) ∈ commutatorSubmodule k Π) :
    cyclicQuotient k Π ≃ₗ[k] (R → k) :=
  (Submodule.quotEquivOfEq _ _ (commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker k h)).trans
    (LinearMap.quotKerEquivOfSurjective _ (signlessPreprojectiveAugmentation_surjective k))

/-- The cyclic class of an element is sent to its augmentation. -/
@[simp]
theorem signlessPreprojectiveCyclicQuotientEquiv_mk
    (h : ∀ x : Quiver.TotalPath R, 0 < x.2.2.length → π (ofPath x) ∈ commutatorSubmodule k Π)
    (x : Π) :
    signlessPreprojectiveCyclicQuotientEquiv k h (Submodule.Quotient.mk x) =
      signlessPreprojectiveAugmentation k x :=
  (rfl)

/-- **If every path of positive length is a sum of commutators, then the cyclic quotient of the
signless algebra has dimension the number of vertices** over every nontrivial commutative ring. -/
theorem finrank_cyclicQuotient_signlessPreprojectiveAlgebra [Nontrivial k]
    (h : ∀ x : Quiver.TotalPath R, 0 < x.2.2.length → π (ofPath x) ∈ commutatorSubmodule k Π) :
    Module.finrank k (cyclicQuotient k Π) = Nat.card R := by
  have : Fintype R := Fintype.ofFinite R
  rw [(signlessPreprojectiveCyclicQuotientEquiv k h).finrank_eq,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end Signless

section Preprojective

variable (k : Type w) [CommRing k] {Q : Type u} [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- **If every path of positive length is a sum of commutators, then so is every graded piece of
positive degree** of the preprojective algebra. -/
theorem preprojectiveGrade_le_commutatorSubmodule
    (h : ∀ x : Quiver.TotalPath (Symmetrify Q), 0 < x.2.2.length →
      preprojectiveMk k Q (ofPath x) ∈ commutatorSubmodule k (preprojectiveAlgebra k Q))
    {d : ℕ} (hd : 0 < d) :
    preprojectiveGrade k Q d ≤ commutatorSubmodule k (preprojectiveAlgebra k Q) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_preprojectiveGrade_iff k Q).1 hx
  rw [grade_eq_span_range] at hy
  refine (Submodule.span_le
    (p := (commutatorSubmodule k (preprojectiveAlgebra k Q)).comap
      (preprojectiveMk k Q).toLinearMap)).2 ?_ hy
  rintro _ ⟨⟨p, hp⟩, rfl⟩
  exact h p (hp ▸ hd)

end Preprojective

section GraphTransport

open DoubledQuiver

variable (k : Type w) [CommRing k] {V : Type u} {W : Type v} [Finite V] [Finite W]
  {G : SimpleGraph V} {H : SimpleGraph W}

/-- **Degree-`d` signless cyclic quotient vanishing descends along induced-subgraph embeddings.** -/
theorem signlessPreprojectiveGrade_le_commutatorSubmodule_of_embedding
    [instG : ∀ i, Fintype (G.neighborSet i)] [∀ j, Fintype (H.neighborSet j)]
    (f : H ↪g G) {d : ℕ}
    (hG : signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) :
    signlessPreprojectiveGrade k (DoubledQuiver H) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) := by
  have hinstG : instG = SimpleGraph.neighborSetFintypeOfFinite G := Subsingleton.elim _ _
  subst hinstG
  let _ := SimpleGraph.neighborSetFintypeOfFinite (G.induce (Set.range f))
  intro x hx
  let E := signlessPreprojectiveAlgebraEquiv k f.isoInduceRange
  have hEx : E x ∈ signlessPreprojectiveGrade k (DoubledQuiver (G.induce (Set.range f))) d :=
    signlessPreprojectiveAlgebraEquiv_mem_signlessPreprojectiveGrade k f.isoInduceRange hx
  rw [← signlessPreprojectiveGrade_map_signlessPreprojectiveInducedSubgraphHom k
    G (Set.range f) d] at hEx
  obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp hEx
  rw [AlgHom.toLinearMap_apply] at hzx
  have hcomm : E x ∈ commutatorSubmodule k _ :=
    hzx ▸ map_mem_commutatorSubmodule
      (signlessPreprojectiveInducedSubgraphHom k G (Set.range f)) (hG hz)
  simpa only [E, AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule E.symm hcomm

/-- **A degree-`d` signless cyclic class outside the commutator submodule lifts along any
induced-subgraph embedding.** -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_embedding
    [∀ i, Fintype (G.neighborSet i)] [∀ j, Fintype (H.neighborSet j)]
    (f : H ↪g G) {d : ℕ}
    (hH : ∃ z : signlessPreprojectiveAlgebra k (DoubledQuiver H),
      z ∈ signlessPreprojectiveGrade k (DoubledQuiver H) d ∧
        z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H))) :
    ∃ z : signlessPreprojectiveAlgebra k (DoubledQuiver G),
      z ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d ∧
        z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  by_contra! hall
  obtain ⟨z, hz, hz0⟩ := hH
  exact hz0 (signlessPreprojectiveGrade_le_commutatorSubmodule_of_embedding k f hall hz)

/-- **Degree-`d` signless cyclic quotient vanishing is invariant under graph isomorphisms.** -/
theorem signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso
    [∀ i, Fintype (G.neighborSet i)] [∀ j, Fintype (H.neighborSet j)]
    (e : G ≃g H) (d : ℕ) :
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) ↔
    signlessPreprojectiveGrade k (DoubledQuiver H) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) :=
  ⟨signlessPreprojectiveGrade_le_commutatorSubmodule_of_embedding k e.symm.toEmbedding,
   signlessPreprojectiveGrade_le_commutatorSubmodule_of_embedding k e.toEmbedding⟩

end GraphTransport

end TauCeti

namespace SimpleGraph.Coloring

open TauCeti TauCeti.DoubledQuiver TauCeti.PathAlgebra _root_.Quiver

universe u w

attribute [local instance] Fintype.ofFinite

variable {V : Type u} {G : SimpleGraph V} (k : Type w) [CommRing k] [Finite V]

/-- **The vanishing of cyclic classes of paths transfers to every orientation.** If every path of
positive length in the signless algebra of a two-coloured graph is a sum of commutators, then so is
every path of positive length in the additive preprojective algebra of each of its orientations:
the bipartite sign rescaling identifies the two algebras and rescales each path by a sign. -/
theorem preprojectiveMk_ofPath_mem_commutatorSubmodule (C : G.Coloring Bool) (o : Orientation G)
    (h : ∀ x : Quiver.TotalPath (DoubledQuiver G), 0 < x.2.2.length →
      signlessPreprojectiveMk k (DoubledQuiver G) (ofPath x) ∈
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)))
    (x : Quiver.TotalPath (Symmetrify (OrientedQuiver G o))) (hx : 0 < x.2.2.length) :
    preprojectiveMk k (OrientedQuiver G o) (ofPath x) ∈
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  let e := C.signlessPreprojectiveAlgebraEquiv k o
  have hsymm : e.symm (preprojectiveMk k (OrientedQuiver G o) (ofPath x)) ∈
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
    simp only [e, signlessPreprojectiveAlgebraEquiv_symm_preprojectiveMk, rescale_ofPath, map_smul,
      orientationPathAlgebraEquiv_symm_ofPath]
    exact Submodule.smul_mem _ _ (h _ (by rwa [Prefunctor.length_mapTotalPath]))
  have hmap := map_mem_commutatorSubmodule e hsymm
  rwa [AlgEquiv.apply_symm_apply] at hmap

/-- **For a two-coloured finite simple graph, degree-`d` cyclic quotient vanishing agrees between
every orientation and the signless presentation.** -/
theorem preprojectiveGrade_le_commutatorSubmodule_iff (C : G.Coloring Bool)
    [inst : ∀ i, Fintype (G.neighborSet i)] (o : Orientation G) (d : ℕ) :
    preprojectiveGrade k (OrientedQuiver G o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) ↔
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  have hinst : inst = fun _ => Fintype.ofFinite _ := Subsingleton.elim _ _
  subst hinst
  let E := C.signlessPreprojectiveAlgebraEquiv k o
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · have hEx := h (C.signlessPreprojectiveAlgebraEquiv_mem_preprojectiveGrade k o hx)
    simpa only [E, AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule E.symm hEx
  · have hEx := h (C.signlessPreprojectiveAlgebraEquiv_symm_mem_signlessPreprojectiveGrade k o hx)
    simpa only [E, AlgEquiv.apply_symm_apply] using map_mem_commutatorSubmodule E hEx

end SimpleGraph.Coloring

namespace SimpleGraph.IsBipartite

open TauCeti TauCeti.DoubledQuiver

/-- **For a bipartite finite simple graph, degree-`d` cyclic quotient vanishing is independent of
orientation and agrees with the signless presentation.** -/
theorem preprojectiveGrade_le_commutatorSubmodule_iff {V : Type*} [Finite V] {G : SimpleGraph V}
    (hb : G.IsBipartite) (k : Type*) [CommRing k] [∀ i, Fintype (G.neighborSet i)]
    (o : Orientation G) (d : ℕ) :
    preprojectiveGrade k (OrientedQuiver G o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) ↔
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) :=
  hb.coloringBool.preprojectiveGrade_le_commutatorSubmodule_iff k o d

end SimpleGraph.IsBipartite
