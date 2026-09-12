/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient

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
a Hausdorff group is determined by its values on a topological generating set.

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
* `MonoidHom.eq_of_eqOn_of_topologicalClosure_closure_eq_top`: a continuous homomorphism into a
  Hausdorff group is determined by its values on a topological generating set.
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

omit [IsTopologicalGroup H] in
/-- A continuous homomorphism out of a topological group is determined by its values on a
topological generating set, provided the target is Hausdorff. This is the uniqueness half of
every construction that defines a map on generators. -/
theorem _root_.MonoidHom.eq_of_eqOn_of_topologicalClosure_closure_eq_top [T2Space H] {s : Set G}
    (hs : (Subgroup.closure s).topologicalClosure = ⊤) {f g : G →* H} (hf : Continuous f)
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

/-- Topological finite generation is invariant under topological group isomorphism. -/
theorem isTopologicallyFinitelyGenerated_congr (e : G ≃ₜ* H) :
    IsTopologicallyFinitelyGenerated G ↔ IsTopologicallyFinitelyGenerated H :=
  ⟨fun hG ↦ hG.of_surjective (f := (e : G →* H)) e.continuous e.surjective,
    fun hH ↦ hH.of_surjective (f := (e.symm : H →* G)) e.symm.continuous e.symm.surjective⟩

end TauCeti
