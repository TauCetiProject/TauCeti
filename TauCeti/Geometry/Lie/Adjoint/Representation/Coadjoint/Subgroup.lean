/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Lie.Adjoint.Representation.Subgroup
import TauCeti.RepresentationTheory.Dual

/-!
# Coadjoint actions on annihilators of subgroup Lie algebras

Let `K` be a subgroup of a Lie group `G`, with Lie algebra `𝔨 = Subgroup.groupLieSubalgebra K`
in the tangent Lie algebra `𝔤`. Dually to the invariance of `𝔨` under the adjoint action of the
normalizer of `K` (`TauCeti.Geometry.Lie.Adjoint.Representation.Subgroup`), the coadjoint action
of the normalizer preserves the annihilator `𝔨⁰ ⊆ 𝔤*`. Since `Ad_n ξ - ξ ∈ 𝔫` for `n` in a closed
normal subgroup `N` and every `ξ ∈ 𝔤`, such an `N` fixes `𝔫⁰` pointwise.

## Main results

* `TauCeti.Lie.coadjointRepresentation_apply_mem_dualAnnihilator_groupLieSubalgebra`: the
  coadjoint action of the normalizer of `K` preserves `𝔨⁰`.
* `TauCeti.Lie.coadjointRepresentation_apply_eq_self_of_mem_dualAnnihilator_groupLieSubalgebra`:
  a closed normal subgroup `N` fixes `𝔫⁰` pointwise.

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

/-- **The coadjoint action of the normalizer preserves the annihilator of the Lie algebra of a
subgroup**: for `g` in the normalizer of `K` and `ν ∈ 𝔨⁰`, `Ad*_g ν ∈ 𝔨⁰`. -/
theorem coadjointRepresentation_apply_mem_dualAnnihilator_groupLieSubalgebra
    {K : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    {ν : Module.Dual ℝ (GroupLieAlgebra I G)}
    (hν : ν ∈ (K.groupLieSubalgebra (I := I)).toSubmodule.dualAnnihilator) :
    coadjointRepresentation ℝ I G g ν ∈
      (K.groupLieSubalgebra (I := I)).toSubmodule.dualAnnihilator := by
  rw [coadjointRepresentation_def]
  exact (adjointRepresentation ℝ I G).dualAnnihilator_le_comap_dual
    (fun _ hξ ↦ adjointRepresentation_apply_mem_groupLieSubalgebra
      (Subgroup.inv_mem _ hg) hξ) hν

/-- **A closed normal subgroup fixes the annihilator of its Lie algebra**: `Ad*_n ν = ν` for
`n ∈ N` and `ν ∈ 𝔫⁰`. -/
theorem coadjointRepresentation_apply_eq_self_of_mem_dualAnnihilator_groupLieSubalgebra
    {N : Subgroup G} [N.Normal]
    (hN : IsClosed (N : Set G)) {n : G} (hn : n ∈ N) {ν : Module.Dual ℝ (GroupLieAlgebra I G)}
    (hν : ν ∈ (N.groupLieSubalgebra (I := I)).toSubmodule.dualAnnihilator) :
    coadjointRepresentation ℝ I G n ν = ν := by
  rw [coadjointRepresentation_def]
  exact Representation.dual_apply_eq_self_of_mem_dualAnnihilator
    (adjointRepresentation_apply_sub_mem_groupLieSubalgebra hN hn) hν

end TauCeti.Lie
