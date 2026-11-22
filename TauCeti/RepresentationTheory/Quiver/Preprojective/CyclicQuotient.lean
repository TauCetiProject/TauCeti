/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Cyclic.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.GradedOrientation
public import TauCeti.RepresentationTheory.Quiver.Preprojective.GraphOrientation
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Isomorphism
public import TauCeti.RepresentationTheory.Quiver.Preprojective.PathAlgebra
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Augmentation
import TauCeti.RepresentationTheory.Quiver.Preprojective.BaseChange.Basic
import TauCeti.RepresentationTheory.Quiver.Preprojective.InducedSubgraph

/-!
# Cyclic quotients of preprojective algebras from their paths

The cyclic quotient `Π / [Π, Π]` of a preprojective algebra is spanned by the classes of paths.
This file collects the steps of a vanishing argument for the cyclic quotient in positive degrees
which do not depend on the graph: once every path of positive length is known to be a sum of
commutators, the same holds for the graded pieces of positive degree, the commutator submodule is
the kernel of the augmentation, so that the cyclic quotient is the module of vertex coefficients,
and, for a two-coloured graph, the vanishing, as well as a homogeneous class outside the
commutators, transfers to the additive preprojective algebra of every orientation. Vanishing of a
graded piece of the additive cyclic quotient also transfers along any coefficient ring homomorphism
via `RingHom.preprojectiveBaseChange`, and vanishing of a graded piece of the signless cyclic
quotient descends along any induced-subgraph embedding `f : G ↪g H`. Conversely, any closed path in
a quiver or in one of its reorientations yields a homogeneous element of the same path degree in
`Π_k(Q)` outside `[Π_k(Q), Π_k(Q)]`, via the retraction
`TauCeti.preprojectiveToPathAlgebra`. The only paths which need a graph-specific argument are the
closed ones: a path between distinct vertices is a commutator with its target idempotent.

## Main results

* `TauCeti.signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_ne`: a path between distinct
  vertices is a sum of commutators.
* `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule` and
  `TauCeti.preprojectiveGrade_le_commutatorSubmodule`: if every path of positive length is a sum of
  commutators, then so is every graded piece of positive degree.
* `TauCeti.preprojectiveGrade_le_commutatorSubmodule_of_ringHom`: vanishing of a graded piece of
  the cyclic quotient transfers along any coefficient ring homomorphism.
* `TauCeti.commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker`: if every path of positive
  length is a sum of commutators, the commutator submodule is the augmentation kernel.
* `TauCeti.signlessPreprojectiveCyclicQuotientEquiv` and
  `TauCeti.finrank_cyclicQuotient_signlessPreprojectiveAlgebra`: in that case the augmentation
  identifies the cyclic quotient with the module of vertex coefficients, of dimension the number of
  vertices over a nontrivial ring.
* `TauCeti.forall_pos_length_signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_iff_of_iso` and
  `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_iff_of_iso`: graph
  isomorphisms preserve and reflect positive-length path vanishing and the existence of nonzero
  homogeneous cyclic classes in the signless preprojective algebra.
* `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_of_embedding` and
  `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso`: vanishing of each graded
  piece of the signless cyclic quotient descends along induced-subgraph embeddings and is invariant
  under graph isomorphisms.
* `TauCeti.pathAlgebraToPreprojective_ofPath_notMem_commutatorSubmodule` and
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_reorient`: over a nontrivial
  commutative ring, any closed path in `Q` or in a reorientation of `Q` yields a homogeneous
  element of the same path degree in `Π_k(Q)` outside the commutator submodule.
* `SimpleGraph.Coloring.preprojectiveMk_ofPath_mem_commutatorSubmodule`: for a two-coloured graph,
  the vanishing for paths of positive length transfers from the signless algebra to the additive
  preprojective algebra of every orientation.
* `SimpleGraph.Coloring.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule`: for a
  two-coloured graph, a homogeneous signless class outside the commutators gives one of the same
  degree for every orientation.
* `SimpleGraph.Coloring.preprojectiveGrade_le_commutatorSubmodule_iff` and
  `SimpleGraph.IsBipartite.preprojectiveGrade_le_commutatorSubmodule_iff`: for a two-coloured or
  bipartite graph, vanishing of a graded piece agrees between the signless algebra and every
  orientation.

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

section SignlessIso

open DoubledQuiver

variable (k : Type w) [CommRing k] {V : Type u} {W : Type v} [Finite V] [Finite W]
  {G : SimpleGraph V} {H : SimpleGraph W}
  [∀ i, Fintype (G.neighborSet i)] [∀ j, Fintype (H.neighborSet j)]

/-- A graph isomorphism preserves and reflects whether every positive-length path in the signless
preprojective algebra lies in the commutator submodule. -/
theorem forall_pos_length_signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_iff_of_iso
    (e : G ≃g H) :
    (∀ x : Quiver.TotalPath (DoubledQuiver G), 0 < x.2.2.length →
      signlessPreprojectiveMk k (DoubledQuiver G) (ofPath x) ∈
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
    (∀ y : Quiver.TotalPath (DoubledQuiver H), 0 < y.2.2.length →
      signlessPreprojectiveMk k (DoubledQuiver H) (ofPath y) ∈
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H))) := by
  constructor
  · intro hG y hy
    let E := signlessPreprojectiveAlgebraEquiv k e.symm
    have hmap : E (signlessPreprojectiveMk k (DoubledQuiver H) (ofPath y)) ∈
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
      rw [signlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk, pathAlgebraEquiv_ofPath]
      exact hG _ (by rwa [Prefunctor.length_mapTotalPath])
    simpa only [AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule E.symm hmap
  · intro hH x hx
    let E := signlessPreprojectiveAlgebraEquiv k e
    have hmap : E (signlessPreprojectiveMk k (DoubledQuiver G) (ofPath x)) ∈
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) := by
      rw [signlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk, pathAlgebraEquiv_ofPath]
      exact hH _ (by rwa [Prefunctor.length_mapTotalPath])
    simpa only [AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule E.symm hmap

/-- A graph isomorphism preserves and reflects the existence of a nonzero degree-`d` cyclic class
in the signless preprojective algebra. -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_iff_of_iso
    (e : G ≃g H) {d : ℕ} :
    (∃ z ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
    (∃ z ∈ signlessPreprojectiveGrade k (DoubledQuiver H) d,
      z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H))) := by
  constructor
  · rintro ⟨z, hz, hz0⟩
    let E := signlessPreprojectiveAlgebraEquiv k e
    refine ⟨E z, (signlessPreprojectiveAlgebraEquiv_mem_signlessPreprojectiveGrade_iff k e).mpr hz,
      fun h => hz0 ?_⟩
    simpa only [AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule E.symm h
  · rintro ⟨z, hz, hz0⟩
    let E := signlessPreprojectiveAlgebraEquiv k e
    refine ⟨E.symm z, ?_, fun h => hz0 ?_⟩
    · rw [signlessPreprojectiveAlgebraEquiv_symm,
        signlessPreprojectiveAlgebraEquiv_mem_signlessPreprojectiveGrade_iff]
      exact hz
    · simpa only [AlgEquiv.apply_symm_apply] using map_mem_commutatorSubmodule E h

end SignlessIso

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

/-- **Vanishing of a graded piece of the cyclic quotient transfers along any coefficient ring
homomorphism**, via `RingHom.preprojectiveBaseChange`: each path of length `d` over `l` is the
base-change image of the same path over `k`, and ring homomorphisms preserve commutators. -/
theorem preprojectiveGrade_le_commutatorSubmodule_of_ringHom {l : Type*} [CommRing l]
    (f : k →+* l) (d : ℕ)
    (h : preprojectiveGrade k Q d ≤ commutatorSubmodule k (preprojectiveAlgebra k Q)) :
    preprojectiveGrade l Q d ≤ commutatorSubmodule l (preprojectiveAlgebra l Q) := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := (mem_preprojectiveGrade_iff l Q).mp hy
  rw [grade_eq_span_range] at hz
  refine (Submodule.span_le
    (p := (commutatorSubmodule l (preprojectiveAlgebra l Q)).comap
      (preprojectiveMk l Q).toLinearMap)).2 ?_ hz
  rintro _ ⟨⟨p, hp⟩, rfl⟩
  have hx : preprojectiveMk k Q (ofPath p) ∈ preprojectiveGrade k Q d :=
    preprojectiveMk_mem_preprojectiveGrade k Q (ofPath_mem_grade_of_length hp)
  have hmap := map_mem_commutatorSubmodule_of_ringHom (l := l)
    (RingHom.preprojectiveBaseChange (Q := Q) f) (h hx)
  simpa only [SetLike.mem_coe, Submodule.mem_comap, AlgHom.toLinearMap_apply,
    RingHom.preprojectiveBaseChange_preprojectiveMk_ofPath] using hmap

/-- Over a nontrivial commutative ring, the image in `Π_k(Q)` of any closed basis path of `Q`
does not lie in the commutator submodule `[Π_k(Q), Π_k(Q)]`. -/
theorem pathAlgebraToPreprojective_ofPath_notMem_commutatorSubmodule [Nontrivial k]
    {a : Q} (p : Path a a) :
    pathAlgebraToPreprojective k Q (ofPath ⟨a, a, p⟩) ∉
      commutatorSubmodule k (preprojectiveAlgebra k Q) := by
  intro hp
  have hret := map_mem_commutatorSubmodule (preprojectiveToPathAlgebra k Q) hp
  rw [preprojectiveToPathAlgebra_pathAlgebraToPreprojective] at hret
  exact ofPath_notMem_commutatorSubmodule p hret

/-- Any closed path in a reorientation of `Q` produces a homogeneous element of the same path
degree in `Π_k(Q)` outside the commutator submodule over a nontrivial commutative ring. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_reorient [Nontrivial k]
    (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool) {a : Reorient Q σ} (p : Path a a) :
    ∃ x ∈ preprojectiveGrade k Q p.length,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k Q) := by
  let y := pathAlgebraToPreprojective k (Reorient Q σ) (ofPath ⟨a, a, p⟩)
  refine ⟨reorientPreprojectiveAlgebraEquiv k σ y,
    (reorientPreprojectiveAlgebraEquiv_mem_preprojectiveGrade k σ).2
      (pathAlgebraToPreprojective_ofPath_mem_preprojectiveGrade k ⟨a, a, p⟩), fun hx => ?_⟩
  apply pathAlgebraToPreprojective_ofPath_notMem_commutatorSubmodule k p
  simpa only [AlgEquiv.symm_apply_apply] using
    map_mem_commutatorSubmodule (reorientPreprojectiveAlgebraEquiv k σ).symm hx

end Preprojective

section Isomorphism

open DoubledQuiver

/-- **Vanishing of a graded piece of the signless cyclic quotient descends to induced subgraphs**:
for any graph embedding `f : G ↪g H`, if the degree-`d` piece of `Π⁺(H)` lies in the commutator
submodule, then so does the degree-`d` piece of `Π⁺(G)`. -/
theorem signlessPreprojectiveGrade_le_commutatorSubmodule_of_embedding (k : Type w) [CommRing k]
    {U V : Type*} [Finite U] [Finite V] {G : SimpleGraph U} {H : SimpleGraph V}
    [∀ i, Fintype (G.neighborSet i)] [instH : ∀ j, Fintype (H.neighborSet j)]
    (f : G ↪g H) (d : ℕ)
    (hH : signlessPreprojectiveGrade k (DoubledQuiver H) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H))) :
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  have hinst : instH = SimpleGraph.neighborSetFintypeOfFinite H := Subsingleton.elim _ _
  subst hinst
  let _ := SimpleGraph.neighborSetFintypeOfFinite H
  intro x hx
  rw [← map_signlessPreprojectiveGrade_signlessPreprojectiveEmbeddingHom k f d] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact map_mem_commutatorSubmodule (signlessPreprojectiveEmbeddingHom k f) (hH hy)

/-- **Vanishing of a graded piece of the signless cyclic quotient is invariant under graph
isomorphism.** -/
theorem signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso (k : Type w) [CommRing k]
    {V W : Type*} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    [∀ i, Fintype (G.neighborSet i)] [∀ j, Fintype (H.neighborSet j)]
    (e : G ≃g H) (d : ℕ) :
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) ↔
      signlessPreprojectiveGrade k (DoubledQuiver H) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) :=
  ⟨signlessPreprojectiveGrade_le_commutatorSubmodule_of_embedding k e.symm.toEmbedding d,
   signlessPreprojectiveGrade_le_commutatorSubmodule_of_embedding k e.toEmbedding d⟩

end Isomorphism

end TauCeti

namespace SimpleGraph.Coloring

open TauCeti TauCeti.DoubledQuiver TauCeti.PathAlgebra _root_.Quiver

universe u w

section Paths

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

/-- **Nonzero cyclic classes transfer to every orientation.** A homogeneous element of degree `d`
of the signless algebra of a two-coloured graph which is not a sum of commutators gives one of the
same degree in the additive preprojective algebra of each of its orientations: the bipartite sign
rescaling identifies the two algebras and preserves the grading. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule (C : G.Coloring Bool)
    (o : Orientation G) {d : ℕ}
    (h : ∃ z : signlessPreprojectiveAlgebra k (DoubledQuiver G),
      z ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d ∧
        z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) :
    ∃ z : preprojectiveAlgebra k (OrientedQuiver G o),
      z ∈ preprojectiveGrade k (OrientedQuiver G o) d ∧
        z ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  obtain ⟨z, hz, hz0⟩ := h
  let e := C.signlessPreprojectiveAlgebraEquiv k o
  refine ⟨e z, C.signlessPreprojectiveAlgebraEquiv_mem_preprojectiveGrade k o hz, fun he => hz0 ?_⟩
  simpa only [AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule e.symm he

end Paths

variable {V : Type u} {G : SimpleGraph V}

/-- **For a two-coloured graph, vanishing of a graded piece of the cyclic quotient agrees between
the signless algebra and the additive preprojective algebra of every orientation.** -/
theorem preprojectiveGrade_le_commutatorSubmodule_iff (C : G.Coloring Bool)
    (k : Type w) [CommRing k] [Finite V]
    [inst : ∀ i, Fintype (G.neighborSet i)] (o : Orientation G) (d : ℕ) :
    preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) ↔
      signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain rfl : inst = fun i => Fintype.ofFinite _ := Subsingleton.elim _ _
  let φ := C.signlessPreprojectiveAlgebraEquiv k o
  constructor
  · intro hO x hx
    have hy := hO (C.signlessPreprojectiveAlgebraEquiv_mem_preprojectiveGrade k o hx)
    simpa only [φ, AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule φ.symm hy
  · intro hS y hy
    have hx := hS (C.signlessPreprojectiveAlgebraEquiv_symm_mem_signlessPreprojectiveGrade k o hy)
    simpa only [φ, AlgEquiv.apply_symm_apply] using map_mem_commutatorSubmodule φ hx

end SimpleGraph.Coloring

namespace SimpleGraph.IsBipartite

open TauCeti TauCeti.DoubledQuiver

universe u w

variable {V : Type u} {G : SimpleGraph V}

/-- **For a bipartite graph, vanishing of a graded piece of the cyclic quotient agrees between the
signless algebra and the additive preprojective algebra of every orientation.** -/
theorem preprojectiveGrade_le_commutatorSubmodule_iff (hG : G.IsBipartite)
    (k : Type w) [CommRing k] [Finite V]
    [∀ i, Fintype (G.neighborSet i)] (o : Orientation G) (d : ℕ) :
    preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) ↔
      signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) :=
  hG.coloringBool.preprojectiveGrade_le_commutatorSubmodule_iff k o d

end SimpleGraph.IsBipartite
