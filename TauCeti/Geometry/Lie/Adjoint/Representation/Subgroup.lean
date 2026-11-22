/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Basic
public import TauCeti.Geometry.Lie.Subgroup.GroupLieAlgebra

/-!
# Adjoint actions on subgroup Lie algebras

Let `K` be a subgroup of a Lie group `G`, with Lie algebra `𝔨 = Subgroup.groupLieSubalgebra K`
in the tangent Lie algebra `𝔤`. The adjoint action `Ad_g` of an element `g` of the normalizer of
`K` preserves `𝔨`, so for a normal subgroup `N` the Lie algebra `𝔫` is a subrepresentation of the
adjoint representation. If moreover `N` is closed, then `Ad_n ξ - ξ ∈ 𝔫` for `n ∈ N` and every
`ξ ∈ 𝔤`, so `N` acts trivially on `𝔤 ⧸ 𝔫`.

The dual statements for the coadjoint action on the annihilator `𝔨⁰ ⊆ 𝔤*` are in
`TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Subgroup`.

## Main results

* `TauCeti.Lie.adjointRepresentation_apply_mem_groupLieSubalgebra`: invariance of `𝔨` under the
  adjoint action of the normalizer.
* `TauCeti.Lie.groupLieSubalgebra_le_comap_adjointRepresentation`: the Lie algebra of a normal
  subgroup is a subrepresentation of the adjoint representation.
* `TauCeti.Lie.adjointRepresentation_apply_sub_mem_groupLieSubalgebra`: for `n` in a closed normal
  subgroup `N`, `Ad_n - 1` maps `𝔤` into `𝔫`.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer (2012),
  Section 9.1.
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **The Lie algebra of `K` is invariant under the adjoint action of the normalizer of `K`.** -/
theorem adjointRepresentation_apply_mem_groupLieSubalgebra {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) {ξ : GroupLieAlgebra I G}
    (hξ : ξ ∈ K.groupLieSubalgebra (I := I)) :
    adjointRepresentation ℝ I G g ξ ∈ K.groupLieSubalgebra (I := I) := by
  have := I.t2Space_of_lieGroup (G := G) ∞
  rw [mem_groupLieSubalgebra_iff] at hξ ⊢
  rw [tangentToLeftInvariantDerivation_adjointRepresentation_apply]
  exact Ad_mem_lieSubalgebraOfSubgroup hg hξ

/-- The Lie algebra of a normal subgroup is a subrepresentation of the adjoint representation, in
the form consumed by `Representation.quotient` and `Representation.subrepresentation`. -/
theorem groupLieSubalgebra_le_comap_adjointRepresentation {N : Subgroup G} [N.Normal] (g : G) :
    (N.groupLieSubalgebra (I := I)).toSubmodule ≤
      (N.groupLieSubalgebra (I := I)).toSubmodule.comap (adjointRepresentation ℝ I G g) :=
  fun _ hξ ↦ adjointRepresentation_apply_mem_groupLieSubalgebra
    (Subgroup.normalizer_eq_top (H := N) ▸ Subgroup.mem_top g) hξ

/-- **A closed normal subgroup `N` acts trivially on `𝔤 ⧸ 𝔫`**: for `n ∈ N` and every `ξ ∈ 𝔤`,
`Ad_n ξ - ξ` lies in the Lie algebra `𝔫` of `N`. -/
theorem adjointRepresentation_apply_sub_mem_groupLieSubalgebra {N : Subgroup G}
    [N.Normal] (hN : IsClosed (N : Set G)) {n : G} (hn : n ∈ N) (ξ : GroupLieAlgebra I G) :
    adjointRepresentation ℝ I G n ξ - ξ ∈ N.groupLieSubalgebra (I := I) := by
  have := I.t2Space_of_lieGroup (G := G) ∞
  rw [mem_groupLieSubalgebra_iff, map_sub,
    tangentToLeftInvariantDerivation_adjointRepresentation_apply]
  exact Ad_sub_mem_lieSubalgebraOfSubgroup hN hn _

end TauCeti.Lie
