/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import TauCeti.Algebra.Algebra.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Preprojective.BaseChange.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.GraphOrientation
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Augmentation
import TauCeti.Combinatorics.Quiver.Prefunctor
import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Cyclic.Necklace
import TauCeti.RepresentationTheory.Quiver.Preprojective.InducedSubgraph
import TauCeti.RepresentationTheory.Quiver.Preprojective.Isomorphism
import TauCeti.RepresentationTheory.Quiver.Zigzag.Connected

/-!
# Cyclic quotients of preprojective algebras from their paths

The cyclic quotient `Π / [Π, Π]` of a preprojective algebra is spanned by the classes of paths.
This file collects the graph-independent tools controlling vanishing and nonvanishing of the cyclic
quotient in positive path degrees:

* once every path of positive length is a sum of commutators, the same holds for the graded pieces
  of positive degree, the commutator submodule of the signless algebra is the augmentation kernel
  (identifying the cyclic quotient with the module of vertex coefficients), and for a two-coloured
  graph the vanishing transfers between the signless algebra and the additive preprojective algebra
  of every orientation;
* vanishing of a graded piece in the cyclic quotient is invariant under graph isomorphisms,
  descends to induced subgraphs, and is preserved under arbitrary ring homomorphisms via
  `RingHom.preprojectiveBaseChange`;
* over a nontrivial commutative ring, every simple closed path of length different from two
  survives modulo commutators, so a non-acyclic finite simple graph always carries a nonzero cyclic
  class in path degree at least three.

## Main results

* `TauCeti.signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_ne`: a path between distinct
  vertices is a sum of commutators.
* `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule` and
  `TauCeti.preprojectiveGrade_le_commutatorSubmodule`: if every path of positive length is a sum of
  commutators, then so is every graded piece of positive degree.
* `TauCeti.commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker`,
  `TauCeti.signlessPreprojectiveCyclicQuotientEquiv`, and
  `TauCeti.finrank_cyclicQuotient_signlessPreprojectiveAlgebra`: in that case the augmentation
  identifies the cyclic quotient with the module of vertex coefficients, of dimension the number of
  vertices over a nontrivial ring.
* `TauCeti.signlessPreprojectiveMk_ofPath_notMem_commutatorSubmodule_of_nodup`,
  `TauCeti.gaugedPreprojectiveMk_ofPath_notMem_commutatorSubmodule_of_nodup`, and
  `TauCeti.preprojectiveMk_ofPath_notMem_commutatorSubmodule_of_nodup`: a simple closed path of
  length different from two does not belong to the commutator submodule.
* `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso` and
  `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_of_embedding`: degreewise cyclic
  vanishing is invariant under graph isomorphism and descends along graph embeddings.
* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic` and
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic`: a non-acyclic
  finite simple graph has a nonzero cyclic class of degree at least three.
* `SimpleGraph.Coloring.preprojectiveGrade_le_commutatorSubmodule_iff` and
  `SimpleGraph.IsBipartite.preprojectiveGrade_le_commutatorSubmodule_iff`: for a bipartite graph,
  degreewise cyclic vanishing agrees between the signless algebra and the preprojective algebra of
  any orientation.
* `RingHom.preprojectiveBaseChange_mem_commutatorSubmodule` and
  `RingHom.preprojectiveGrade_le_commutatorSubmodule`: base change along a ring homomorphism
  preserves the commutator submodule and degreewise cyclic vanishing.

## References

* J.-L. Loday, *Cyclic Homology*, Section 1.1, for the cyclic quotient as zeroth Hochschild
  homology.
* T. Schedler, *Hochschild homology of preprojective algebras over the integers*, Adv. Math. 299
  (2016), Theorem 13.1.1, https://arxiv.org/abs/0704.3278.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  Corollary 3.4, https://arxiv.org/abs/2301.06757.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

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

/-- Over a nontrivial commutative ring, every simple closed path of length different from two
survives modulo commutators in the signless preprojective algebra. -/
theorem signlessPreprojectiveMk_ofPath_notMem_commutatorSubmodule_of_nodup [Nontrivial k]
    {u : R} (p : Path u u) (hlen : p.length ≠ 2) (hnodup : p.vertices.dropLast.Nodup) :
    π (ofPath ⟨u, u, p⟩) ∉ commutatorSubmodule k Π := by
  refine map_ofPath_notMem_commutatorSubmodule_of_nodup π (signlessPreprojectiveMk_surjective k R)
    (S := Set.range fun v : R => signlessPreprojectiveRelator k v) ?_ ?_ p hlen hnodup
  · rintro _ ⟨v, rfl⟩
    dsimp only
    rw [signlessPreprojectiveRelator_def]
    refine Submodule.sum_mem _ fun x _ =>
      Submodule.subset_span ⟨v, x.1, x.2, Quiver.reverse x.2, ?_⟩
    rw [ofArrow_eq_ofPath, ofArrow_eq_ofPath, ofPath_mul_ofPath_of_comp]
  · intro x hx
    rwa [← signlessPreprojectiveIdeal_eq_span, ← signlessPreprojectiveMk_eq_zero_iff]

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

private theorem gaugedPreprojectiveRelator_mem_span_twoStepLoop
    (ε : ∀ ⦃i j : Q⦄, (i ⟶ j) → k) :
    gaugedPreprojectiveRelator k ε ∈ Submodule.span k
      {z : pathAlgebra k (Symmetrify Q) |
        ∃ (v w : Symmetrify Q) (e₁ : v ⟶ w) (e₂ : w ⟶ v), z = ofArrow e₂ * ofArrow e₁} := by
  rw [gaugedPreprojectiveRelator_def]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ (ε a) (sub_mem ?_ ?_)
  · exact Submodule.subset_span ⟨Symmetrify.of.obj j, Symmetrify.of.obj i,
      Quiver.reverse (Symmetrify.of.map a), Symmetrify.of.map a,
      (ofArrow_mul_ofArrow_reverse_eq_headBacktrackElem k a).symm⟩
  · exact Submodule.subset_span ⟨Symmetrify.of.obj i, Symmetrify.of.obj j,
      Symmetrify.of.map a, Quiver.reverse (Symmetrify.of.map a),
      (ofArrow_reverse_mul_ofArrow_eq_tailBacktrackElem k a).symm⟩

/-- Over a nontrivial commutative ring, every simple closed path of length different from two
survives modulo commutators in any gauged preprojective algebra. -/
theorem gaugedPreprojectiveMk_ofPath_notMem_commutatorSubmodule_of_nodup [Nontrivial k]
    (ε : ∀ ⦃i j : Q⦄, (i ⟶ j) → k) {u : Symmetrify Q} (p : Path u u)
    (hlen : p.length ≠ 2) (hnodup : p.vertices.dropLast.Nodup) :
    gaugedPreprojectiveMk k ε (ofPath ⟨u, u, p⟩) ∉
      commutatorSubmodule k (gaugedPreprojectiveAlgebra k ε) := by
  refine map_ofPath_notMem_commutatorSubmodule_of_nodup (gaugedPreprojectiveMk k ε)
    (gaugedPreprojectiveMk_surjective k ε)
    (S := {gaugedPreprojectiveRelator k ε}) ?_ ?_ p hlen hnodup
  · rintro _ rfl
    exact gaugedPreprojectiveRelator_mem_span_twoStepLoop k ε
  · intro x hx
    rwa [← gaugedPreprojectiveIdeal_eq_span, ← gaugedPreprojectiveMk_eq_zero_iff]

/-- Over a nontrivial commutative ring, every simple closed path of length different from two
survives modulo commutators in the additive preprojective algebra. -/
theorem preprojectiveMk_ofPath_notMem_commutatorSubmodule_of_nodup [Nontrivial k]
    {u : Symmetrify Q} (p : Path u u)
    (hlen : p.length ≠ 2) (hnodup : p.vertices.dropLast.Nodup) :
    preprojectiveMk k Q (ofPath ⟨u, u, p⟩) ∉ commutatorSubmodule k (preprojectiveAlgebra k Q) := by
  refine map_ofPath_notMem_commutatorSubmodule_of_nodup (preprojectiveMk k Q)
    (preprojectiveMk_surjective k Q) (S := {preprojectiveRelator k Q}) ?_ ?_ p hlen hnodup
  · rintro _ rfl
    rw [← gaugedPreprojectiveRelator_one]
    exact gaugedPreprojectiveRelator_mem_span_twoStepLoop k _
  · intro x hx
    rwa [← preprojectiveIdeal_eq_span, ← preprojectiveMk_eq_zero_iff]

end Preprojective

section Graph

variable (k : Type w) [CommRing k]

private theorem signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso
    {V W : Type*} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    [∀ i, Fintype (G.neighborSet i)] [∀ j, Fintype (H.neighborSet j)]
    (e : G ≃g H) {d : ℕ}
    (h : signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) :
    signlessPreprojectiveGrade k (DoubledQuiver H) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) := by
  intro y hy
  let E := signlessPreprojectiveAlgebraEquiv k e
  have hx : E.symm y ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d := by
    rwa [signlessPreprojectiveAlgebraEquiv_symm,
      signlessPreprojectiveAlgebraEquiv_mem_signlessPreprojectiveGrade_iff]
  simpa only [AlgEquiv.apply_symm_apply] using map_mem_commutatorSubmodule E (h hx)

/-- Graph isomorphisms preserve and reflect vanishing of each graded piece of the signless
preprojective cyclic quotient, independently of the chosen neighbourhood enumerations. -/
theorem signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso
    {V W : Type*} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    [∀ i, Fintype (G.neighborSet i)] [∀ j, Fintype (H.neighborSet j)]
    (e : G ≃g H) (d : ℕ) :
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) ↔
      signlessPreprojectiveGrade k (DoubledQuiver H) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) :=
  ⟨signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k e,
   signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k e.symm⟩

private theorem signlessPreprojectiveGrade_induce_le_commutatorSubmodule
    {V : Type*} [Finite V] (G : SimpleGraph V) (S : Set V) {d : ℕ} :
    letI := SimpleGraph.neighborSetFintypeOfFinite G
    letI := SimpleGraph.neighborSetFintypeOfFinite (G.induce S)
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) →
      signlessPreprojectiveGrade k (DoubledQuiver (G.induce S)) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver (G.induce S))) := by
  let _ := SimpleGraph.neighborSetFintypeOfFinite G
  let _ := SimpleGraph.neighborSetFintypeOfFinite (G.induce S)
  intro h y hy
  obtain ⟨x, hxgrade, rfl⟩ :=
    exists_mem_signlessPreprojectiveGrade_signlessPreprojectiveInducedSubgraphHom_eq k G S hy
  exact map_mem_commutatorSubmodule (signlessPreprojectiveInducedSubgraphHom k G S) (h hxgrade)

/-- Vanishing of a graded piece of the signless preprojective cyclic quotient descends along any
graph embedding (induced subgraph inclusion). -/
theorem signlessPreprojectiveGrade_le_commutatorSubmodule_of_embedding
    {V W : Type*} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    [instG : ∀ i, Fintype (G.neighborSet i)] [instH : ∀ j, Fintype (H.neighborSet j)]
    (f : H ↪g G) {d : ℕ}
    (h : signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) :
    signlessPreprojectiveGrade k (DoubledQuiver H) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) := by
  have hG₀ := (@signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso k _ V V _ _ G G
    instG (SimpleGraph.neighborSetFintypeOfFinite G) SimpleGraph.Iso.refl d).mp h
  have hS₀ := signlessPreprojectiveGrade_induce_le_commutatorSubmodule k G (Set.range f) hG₀
  exact (@signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso k _ _ W _ _
    (G.induce (Set.range f)) H (SimpleGraph.neighborSetFintypeOfFinite (G.induce (Set.range f)))
    instH f.isoInduceRange.symm d).mp hS₀

/-- A nonzero cyclic class of degree `d` on an embedded subgraph lifts to a nonzero cyclic class of
degree `d` on the ambient graph. -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_embedding
    {k : Type w} [CommRing k]
    {V W : Type*} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    [∀ i, Fintype (G.neighborSet i)] [∀ j, Fintype (H.neighborSet j)]
    (f : H ↪g G) {d : ℕ}
    (h : ∃ y ∈ signlessPreprojectiveGrade k (DoubledQuiver H) d,
      y ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H))) :
    ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain ⟨y, hy, hy0⟩ := h
  by_contra! hG
  exact hy0 (signlessPreprojectiveGrade_le_commutatorSubmodule_of_embedding k f hG hy)

/-- **Non-acyclic graphs have nonzero cyclic classes in degree at least three.** Over any
nontrivial commutative ring, a simple cycle in `G` defines a homogeneous element of degree at least
three in the signless preprojective algebra outside the commutator submodule. -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic
    {k : Type w} [CommRing k] [Nontrivial k]
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    (hG : ¬ G.IsAcyclic) :
    ∃ d ≥ 3, ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  simp only [SimpleGraph.IsAcyclic, not_forall, not_not] at hG
  obtain ⟨v, c, hc⟩ := hG
  let p := walkToPath G c
  have hlen : 3 ≤ p.length := by
    simpa only [p, length_walkToPath] using hc.three_le_length
  have hnodup : p.vertices.dropLast.Nodup := by
    rw [vertices_walkToPath, ← List.map_dropLast]
    exact hc.nodup_dropLast_support.map (vertex_injective G)
  refine ⟨p.length, hlen, signlessPreprojectiveMk k _ (ofPath ⟨_, _, p⟩),
    signlessPreprojectiveMk_mem_grade k _ (ofPath_mem_grade_of_length rfl), ?_⟩
  exact signlessPreprojectiveMk_ofPath_notMem_commutatorSubmodule_of_nodup k p (by omega) hnodup

/-- **Non-acyclic graphs have nonzero preprojective cyclic classes in degree at least three.** Over
any nontrivial commutative ring and for any orientation `o` of `G`, a simple cycle in `G` lifts to
a homogeneous element of degree at least three in `Π_k(OrientedQuiver G o)` outside the commutator
submodule. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic
    {k : Type w} [CommRing k] [Nontrivial k]
    {V : Type*} [Finite V] {G : SimpleGraph V} (o : Orientation G)
    (hG : ¬ G.IsAcyclic) :
    ∃ d ≥ 3, ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  simp only [SimpleGraph.IsAcyclic, not_forall, not_not] at hG
  obtain ⟨v, c, hc⟩ := hG
  let q := (unsymmetrifyMap G o).mapPath (walkToPath G c)
  have hlen : 3 ≤ q.length := by
    simpa only [q, Prefunctor.length_mapPath, length_walkToPath] using hc.three_le_length
  have hinj : Function.Injective (unsymmetrifyMap G o).obj :=
    ((unsymmetrifyMap G o).obj_bijective_of_comp_eq_id (symmetrifyMap G o)
      (unsymmetrifyMap_comp_symmetrifyMap G o) (symmetrifyMap_comp_unsymmetrifyMap G o)).1
  have hnodup : q.vertices.dropLast.Nodup := by
    rw [Prefunctor.vertices_mapPath, vertices_walkToPath, ← List.map_dropLast, ← List.map_dropLast]
    exact (hc.nodup_dropLast_support.map (vertex_injective G)).map hinj
  refine ⟨q.length, hlen, preprojectiveMk k (OrientedQuiver G o) (ofPath ⟨_, _, q⟩),
    preprojectiveMk_mem_preprojectiveGrade k _ (ofPath_mem_grade_of_length rfl), ?_⟩
  exact preprojectiveMk_ofPath_notMem_commutatorSubmodule_of_nodup k q (by omega) hnodup

end Graph

end TauCeti

namespace SimpleGraph.Coloring

open TauCeti TauCeti.DoubledQuiver TauCeti.PathAlgebra _root_.Quiver

universe u w

section OfFinite

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

private theorem preprojectiveGrade_le_commutatorSubmodule_iff_ofFinite
    (C : G.Coloring Bool) (o : Orientation G) (d : ℕ) :
    preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) ↔
      signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  let e := C.signlessPreprojectiveAlgebraEquiv k o
  constructor
  · intro h x hx
    have hex : e x ∈ preprojectiveGrade k (OrientedQuiver G o) d :=
      (C.signlessPreprojectiveAlgebraEquiv_mem_preprojectiveGrade_iff k o).mpr hx
    simpa only [AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule e.symm (h hex)
  · intro h y hy
    have hsymm : e.symm y ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d :=
      C.signlessPreprojectiveAlgebraEquiv_symm_mem_signlessPreprojectiveGrade k o hy
    simpa only [AlgEquiv.apply_symm_apply] using map_mem_commutatorSubmodule e (h hsymm)

end OfFinite

/-- For a two-coloured graph, degree-`d` vanishing in the cyclic quotient of the additive
preprojective algebra of any orientation agrees with degree-`d` vanishing in the cyclic quotient of
the signless preprojective algebra. -/
theorem preprojectiveGrade_le_commutatorSubmodule_iff {V : Type u} {G : SimpleGraph V}
    (C : G.Coloring Bool) (k : Type w) [CommRing k] [Finite V] (o : Orientation G)
    [instG : ∀ i, Fintype (G.neighborSet i)] (d : ℕ) :
    preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) ↔
      signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) :=
  (C.preprojectiveGrade_le_commutatorSubmodule_iff_ofFinite k o d).trans
    (@signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso k _ V V _ _ G G
      (fun i => Fintype.ofFinite (G.neighborSet i)) instG SimpleGraph.Iso.refl d)

end SimpleGraph.Coloring

namespace SimpleGraph.IsBipartite

open TauCeti TauCeti.DoubledQuiver

universe u w

variable {V : Type u} {G : SimpleGraph V} (k : Type w) [CommRing k] [Finite V]

/-- For a bipartite graph, degree-`d` vanishing in the cyclic quotient of the additive
preprojective algebra of any orientation agrees with degree-`d` vanishing in the cyclic quotient of
the signless preprojective algebra. -/
theorem preprojectiveGrade_le_commutatorSubmodule_iff (hG : G.IsBipartite) (o : Orientation G)
    [∀ i, Fintype (G.neighborSet i)] (d : ℕ) :
    preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) ↔
      signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) :=
  SimpleGraph.Coloring.preprojectiveGrade_le_commutatorSubmodule_iff
    (SimpleGraph.IsBipartite.coloringBool hG) k o d

end SimpleGraph.IsBipartite

namespace RingHom

open _root_.Quiver TauCeti TauCeti.PathAlgebra

universe u v w z

variable {k : Type w} {l : Type z} {Q : Type u}
  [CommRing k] [CommRing l] [Quiver.{v} Q] [Fintype Q] [∀ i j : Q, Fintype (i ⟶ j)]

/-- Coefficient base change along any ring homomorphism carries the commutator submodule of
`Π_k(Q)` into the commutator submodule of `Π_l(Q)`. -/
theorem preprojectiveBaseChange_mem_commutatorSubmodule (f : k →+* l)
    {x : preprojectiveAlgebra k Q}
    (hx : x ∈ commutatorSubmodule k (preprojectiveAlgebra k Q)) :
    f.preprojectiveBaseChange x ∈ commutatorSubmodule l (preprojectiveAlgebra l Q) := by
  let M := cyclicQuotient l (preprojectiveAlgebra l Q)
  let _ : Module k M := Module.compHom M f
  let q : preprojectiveAlgebra k Q →ₗ[k] M :=
    { toFun y :=
        (commutatorSubmodule l (preprojectiveAlgebra l Q)).mkQ (f.preprojectiveBaseChange y)
      map_add' a b := by simp
      map_smul' r a := by
        rw [Algebra.smul_def, map_mul, f.preprojectiveBaseChange_algebraMap, ← Algebra.smul_def,
          map_smul]
        rfl }
  have hq (y : preprojectiveAlgebra k Q) :
      q y = (commutatorSubmodule l (preprojectiveAlgebra l Q)).mkQ (f.preprojectiveBaseChange y) :=
    rfl
  have hcomm (a b : preprojectiveAlgebra k Q) : q (a * b) = q (b * a) := by
    apply sub_eq_zero.mp
    rw [hq, hq, ← map_sub, map_mul, map_mul]
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (mul_sub_mul_mem_commutatorSubmodule l (preprojectiveAlgebra l Q) _ _)
  have hzero := LinearMap.mem_ker.mp ((commutatorSubmodule_le_ker_iff q).mpr hcomm hx)
  rw [hq] at hzero
  exact (Submodule.Quotient.mk_eq_zero _).mp hzero

/-- If degree `d` of `Π_k(Q)` lies in the commutator submodule over `k`, then for every ring
homomorphism `f : k →+* l` degree `d` of `Π_l(Q)` lies in the commutator submodule over `l`. -/
theorem preprojectiveGrade_le_commutatorSubmodule (f : k →+* l) {d : ℕ}
    (h : preprojectiveGrade k Q d ≤ commutatorSubmodule k (preprojectiveAlgebra k Q)) :
    preprojectiveGrade l Q d ≤ commutatorSubmodule l (preprojectiveAlgebra l Q) := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := (mem_preprojectiveGrade_iff l Q).mp hy
  clear hy
  rw [grade_eq_span_range] at hz
  induction hz using Submodule.span_induction with
  | mem _ hp =>
      obtain ⟨⟨p, hp⟩, rfl⟩ := hp
      rw [← f.preprojectiveBaseChange_preprojectiveMk_ofPath p]
      exact f.preprojectiveBaseChange_mem_commutatorSubmodule
        (h (preprojectiveMk_mem_preprojectiveGrade k _ (ofPath_mem_grade_of_length hp)))
  | zero =>
      rw [map_zero]
      exact zero_mem _
  | add _ _ _ _ ha hb =>
      rw [map_add]
      exact add_mem ha hb
  | smul r _ _ ha =>
      rw [map_smul]
      exact Submodule.smul_mem _ r ha

end RingHom
