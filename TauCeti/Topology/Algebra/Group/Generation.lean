/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Finiteness
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex
public import TauCeti.Topology.Algebra.Group.Subgroup
import Mathlib.GroupTheory.Schreier

/-!
# Topological generation of a topological group

A subset of a topological group *generates it topologically* when the subgroup it generates is
dense, that is when `(Subgroup.closure s).topologicalClosure = ⊤`. This file introduces the
predicate `IsTopologicallyFinitelyGenerated`, asking for a *finite* topological generating set,
and its basic API.

The predicate is covariant: a topological generating set is carried to a topological generating
set by any continuous homomorphism with dense range, hence in particular by a continuous
surjection and so to every quotient. It is invariant under a topological group isomorphism, and
it has the uniqueness half one expects of a notion of generation — a continuous homomorphism into
a Hausdorff monoid is determined by its values on a topological generating set, as is a
homomorphism with open kernel into an arbitrary group. Counting the latter over a finite target
is what bounds the supply of open subgroups of a compact group.

For a profinite group topological finite generation is detected by the finite quotients; that
criterion is in `TauCeti/Topology/Algebra/Group/Profinite/Generation.lean`.

## Main results

* `TauCeti.IsTopologicallyFinitelyGenerated`: some finite subset generates a dense subgroup.
* `TauCeti.topologicalClosure_closure_image_eq_top`: the image of a topological generating set
  under a continuous homomorphism with dense range is a topological generating set.
* `TauCeti.IsTopologicallyFinitelyGenerated.of_denseRange`,
  `TauCeti.IsTopologicallyFinitelyGenerated.of_surjective`,
  `TauCeti.IsTopologicallyFinitelyGenerated.quotient`: topological finite generation passes along
  continuous homomorphisms with dense range, along continuous surjections, and to quotients.
* `TauCeti.IsTopologicallyFinitelyGenerated.of_openSubgroup_of_finiteIndex`,
  `TauCeti.IsTopologicallyFinitelyGenerated.of_openSubgroup`: topological finite generation
  passes to open finite-index subgroups, in particular to open subgroups of compact groups.
* `MonoidHom.eq_of_eqOn_of_topologicalClosure_closure_eq_top`: a continuous homomorphism into a
  Hausdorff monoid is determined by its values on a topological generating set.
* `MonoidHom.eq_of_eqOn_of_isOpen_ker`: the same uniqueness statement for a homomorphism with
  open kernel, for which the target carries no topology.
* `TauCeti.IsTopologicallyFinitelyGenerated.finite_monoidHom_isOpen_ker`: only finitely many
  homomorphisms with open kernel go from a topologically finitely generated group to a fixed
  finite group.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Corollary 3.6.3.
* Mathlib's `Subgroup.fg_of_index_ne_zero` and
  `DenseRange.subset_closure_image_preimage_of_isOpen`.
-/

public section

namespace TauCeti

/-- **Topological finite generation**: some finite subset of `G` generates a dense subgroup.
For a profinite group this is the notion of finite generation that all of the pro-`p` theory
uses; abstract finite generation is strictly stronger and is never meant. -/
def IsTopologicallyFinitelyGenerated (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Prop :=
  ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The defining property of `IsTopologicallyFinitelyGenerated`, available to modules that only
see the declaration and not its body. -/
@[simp]
theorem isTopologicallyFinitelyGenerated_iff :
    IsTopologicallyFinitelyGenerated G ↔
      ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤ :=
  Iff.rfl

/-- A finite topological generating set, presented as a set rather than as a `Finset`, witnesses
topological finite generation. -/
theorem _root_.Set.Finite.isTopologicallyFinitelyGenerated {s : Set G} (hs : s.Finite)
    (hgen : (Subgroup.closure s).topologicalClosure = ⊤) :
    IsTopologicallyFinitelyGenerated G :=
  ⟨hs.toFinset, by rwa [hs.coe_toFinset]⟩

/-- A finitely generated group, in any group topology, is topologically finitely generated: an
algebraic generating set is a topological one. Via `Group.fg_of_finite` this covers the finite
groups, and so all the finite quotients of a profinite group. -/
theorem isTopologicallyFinitelyGenerated_of_fg [Group.FG G] :
    IsTopologicallyFinitelyGenerated G := by
  obtain ⟨s, hs, hsfin⟩ := Group.fg_iff.mp ‹Group.FG G›
  exact hsfin.isTopologicallyFinitelyGenerated <| by
    rw [hs]
    exact eq_top_iff.mpr (⊤ : Subgroup G).le_topologicalClosure

/-- The image of a topological generating set under a continuous homomorphism with dense range
is again a topological generating set. -/
theorem topologicalClosure_closure_image_eq_top {s : Set G}
    (hs : (Subgroup.closure s).topologicalClosure = ⊤) {f : G →* H} (hf : Continuous f)
    (hf' : DenseRange f) : (Subgroup.closure (f '' s)).topologicalClosure = ⊤ := by
  rw [← MonoidHom.map_closure]
  exact hf'.topologicalClosure_map_subgroup hf hs

/-- A continuous homomorphism out of a topological group is determined by its values on a
topological generating set, provided the target is a Hausdorff monoid. This is the uniqueness
half of every construction that defines a map on generators. -/
theorem _root_.MonoidHom.eq_of_eqOn_of_topologicalClosure_closure_eq_top {M : Type*} [Monoid M]
    [TopologicalSpace M] [T2Space M] {s : Set G}
    (hs : (Subgroup.closure s).topologicalClosure = ⊤) {f g : G →* M} (hf : Continuous f)
    (hg : Continuous g) (hfg : Set.EqOn f g s) : f = g := by
  have hdense : Dense (Subgroup.closure s : Set G) := by
    rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, hs, Subgroup.coe_top]
  exact DFunLike.coe_injective (hf.ext_on hdense hg (MonoidHom.eqOn_closure hfg))

/-- Topological finite generation passes along a continuous homomorphism with dense range. -/
theorem IsTopologicallyFinitelyGenerated.of_denseRange
    (hG : IsTopologicallyFinitelyGenerated G) {f : G →* H} (hf : Continuous f)
    (hf' : DenseRange f) : IsTopologicallyFinitelyGenerated H := by
  obtain ⟨s, hs⟩ := hG
  exact (s.finite_toSet.image f).isTopologicallyFinitelyGenerated
    (topologicalClosure_closure_image_eq_top hs hf hf')

/-- Topological finite generation passes to continuous surjective images. -/
theorem IsTopologicallyFinitelyGenerated.of_surjective
    (hG : IsTopologicallyFinitelyGenerated G) {f : G →* H} (hf : Continuous f)
    (hsurj : Function.Surjective f) : IsTopologicallyFinitelyGenerated H :=
  hG.of_denseRange hf hsurj.denseRange

/-- Topological finite generation passes to quotients by normal subgroups, closed or not. -/
theorem IsTopologicallyFinitelyGenerated.quotient (hG : IsTopologicallyFinitelyGenerated G)
    (N : Subgroup G) [N.Normal] : IsTopologicallyFinitelyGenerated (G ⧸ N) :=
  hG.of_surjective QuotientGroup.continuous_mk (QuotientGroup.mk'_surjective N)

/-- An open finite-index subgroup of a topologically finitely generated group is topologically
finitely generated. -/
theorem IsTopologicallyFinitelyGenerated.of_openSubgroup_of_finiteIndex
    (hG : IsTopologicallyFinitelyGenerated G) (U : OpenSubgroup G)
    [U.toSubgroup.FiniteIndex] : IsTopologicallyFinitelyGenerated (↥U.toSubgroup) := by
  -- A finite topological generating set `s` of `G` generates a dense subgroup `D`; the subgroup
  -- `U ⊓ D` has finite index in `D`, so it is finitely generated by Schreier's lemma, and it is
  -- dense in `U`.
  obtain ⟨s, hs⟩ := isTopologicallyFinitelyGenerated_iff.mp hG
  have hD : Dense ((Subgroup.closure (s : Set G) : Subgroup G) : Set G) := by
    rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, hs, Subgroup.coe_top]
  exact isTopologicallyFinitelyGenerated_of_fg.of_denseRange
    (Subgroup.continuous_subgroupOf_codRestrict _ _)
    (hD.denseRange_subgroupOf_codRestrict U.isOpen)

/-- An open subgroup of a topologically finitely generated compact topological group is
topologically finitely generated. -/
theorem IsTopologicallyFinitelyGenerated.of_openSubgroup [CompactSpace G]
    (hG : IsTopologicallyFinitelyGenerated G) (U : OpenSubgroup G) :
    IsTopologicallyFinitelyGenerated (↥U.toSubgroup) :=
  hG.of_openSubgroup_of_finiteIndex U

/-- Topological finite generation is invariant under topological group isomorphism. -/
theorem isTopologicallyFinitelyGenerated_congr (e : G ≃ₜ* H) :
    IsTopologicallyFinitelyGenerated G ↔ IsTopologicallyFinitelyGenerated H :=
  ⟨fun hG ↦ hG.of_surjective (f := (e : G →* H)) e.continuous e.surjective,
    fun hH ↦ hH.of_surjective (f := (e.symm : H →* G)) e.symm.continuous e.symm.surjective⟩

section OpenKernel

/-- A homomorphism from a topological group into a monoid carrying the discrete topology is
continuous exactly when its kernel is open. -/
theorem _root_.MonoidHom.continuous_iff_isOpen_ker {F : Type*} [MulOneClass F] [TopologicalSpace F]
    [DiscreteTopology F] (f : G →* F) : Continuous f ↔ IsOpen (f.ker : Set G) := by
  -- The kernel is the preimage of the open point `1`.
  refine ⟨fun hf ↦ ?_, f.continuous_of_isOpen_ker⟩
  rw [MonoidHom.coe_ker]
  exact (isOpen_discrete _).preimage hf

/-- A homomorphism whose kernel is open is determined by its values on a topological generating
set: the equalizer of two such homomorphisms contains the (open) intersection of their kernels,
hence is open, hence closed, hence contains the whole group. The target carries no topology at
all, which is what makes the statement usable for a target such as a permutation group that has
no topology to hand; compare `MonoidHom.eq_of_eqOn_of_topologicalClosure_closure_eq_top`, which
asks instead for continuity into a Hausdorff target. -/
theorem _root_.MonoidHom.eq_of_eqOn_of_isOpen_ker {F : Type*} [Group F] {s : Set G}
    (hs : (Subgroup.closure s).topologicalClosure = ⊤) {f g : G →* F}
    (hf : IsOpen (f.ker : Set G)) (hg : IsOpen (g.ker : Set G)) (hfg : Set.EqOn f g s) :
    f = g := by
  -- Membership in `MonoidHom.eqLocus` is the equation `f x = g x`, as in `MonoidHom.eqOn_closure`.
  have hsub : f.ker ⊓ g.ker ≤ f.eqLocus g := fun x hx ↦ by
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker] at hx
    exact hx.1.trans hx.2.symm
  have hopen : IsOpen ((f.eqLocus g : Subgroup G) : Set G) :=
    Subgroup.isOpen_mono hsub (by simpa only [Subgroup.coe_inf] using hf.inter hg)
  have htop : f.eqLocus g = ⊤ :=
    top_le_iff.mp <| hs ▸ Subgroup.topologicalClosure_minimal _
      ((Subgroup.closure_le _).mpr hfg) (Subgroup.isClosed_of_isOpen _ hopen)
  exact MonoidHom.eq_of_eqOn_top fun x _ ↦ htop.ge (Subgroup.mem_top x)

/-- **A topologically finitely generated group has few homomorphisms to a finite group.** There
are only finitely many homomorphisms with open kernel from a topologically finitely generated
topological group to a fixed finite group, because such a homomorphism is determined by its
values on a finite topological generating set. -/
theorem IsTopologicallyFinitelyGenerated.finite_monoidHom_isOpen_ker
    (hG : IsTopologicallyFinitelyGenerated G) (F : Type*) [Group F] [Finite F] :
    Finite {f : G →* F // IsOpen (f.ker : Set G)} := by
  obtain ⟨s, hs⟩ := hG
  have : Finite (s : Set G) := s.finite_toSet.to_subtype
  refine Finite.of_injective (fun f (x : (s : Set G)) ↦ f.1 x) fun f g hfg ↦ Subtype.ext ?_
  exact MonoidHom.eq_of_eqOn_of_isOpen_ker hs f.2 g.2 fun x hx ↦ congrFun hfg ⟨x, hx⟩

end OpenKernel

end TauCeti
