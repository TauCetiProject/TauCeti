/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.Projective
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Extension
public import TauCeti.Topology.Algebra.GroupExtension.Splitting

/-!
# Extensions of a projective pro-`p` group split

Let `G` be a projective pro-`p` group: every continuous homomorphism from `G` into a quotient of
a profinite pro-`p` group lifts continuously (`TauCeti.IsProjective`). An extension
`1 → M → E → G → 1` of topological groups with profinite total group `E` and pro-`p` kernel `M`
has pro-`p` total group, so projectivity lifts the identity of `G` through the projection `E ↠ G`
to a continuous homomorphic section: the extension splits
(`GroupExtension.exists_splitting_continuous_of_isProjective`). Only the Hausdorff topological
group structure of `G` enters; profiniteness of `G` is not needed.

Read through the classification of profinite extensions by continuous `H²`, the splitting is the
vanishing of `H²(G, M)` for every profinite pro-`p` abelian `G`-module `M`, proved in
`TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.Cohomology`. The free pro-`p` groups,
on a type or on a pointed profinite space, are projective, and the splitting of their extensions
in `TauCeti.Topology.Algebra.Group.Profinite.Free.Extension` is the instance of this statement at
`freeProP p X`.

## Main results

* `GroupExtension.exists_splitting_continuous_of_isProjective`: every profinite extension of a
  projective pro-`p` group by a pro-`p` group splits by a continuous homomorphic section.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §5.9.
* L. Ribes and P. Zalesskii, *Profinite Groups*, 2nd ed., Section 7.6.
-/

public section

namespace TauCeti

universe u v

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### Extensions split -/

section Splitting

variable [T2Space G] {M : Type*} [Group M] [TopologicalSpace M]
  {E : Type v} [Group E] [TopologicalSpace E] [IsTopologicalGroup E] [CompactSpace E]
  [TotallyDisconnectedSpace E]

/-- **Extensions of a projective pro-`p` group by a pro-`p` group split.** An extension
`1 → M → E → G → 1` of topological groups with profinite total group and pro-`p` kernel, over a
projective pro-`p` Hausdorff group `G`, has a continuous homomorphic section: the total group is
pro-`p`, and projectivity lifts the identity of `G` through the projection. -/
theorem _root_.GroupExtension.exists_splitting_continuous_of_isProjective
    (S : GroupExtension M E G) (hinl : Continuous S.inl) (hrh : Continuous S.rightHom)
    (hM : IsProP p M) (hG : IsProP p G) (hproj : IsProjective.{u, v, u} p G) :
    ∃ s : S.Splitting, Continuous ⇑s := by
  have hE : IsProP p E := S.isProP hinl hrh hM hG
  obtain ⟨σ, hσ⟩ := hproj.exists_continuous_lift hE ⟨S.rightHom, hrh⟩ S.rightHom_surjective
    (ContinuousMonoidHom.id G)
  obtain ⟨s, hs, -⟩ := S.exists_splitting_continuous_of_comp_eq_id hrh σ hσ
  exact ⟨s, hs⟩

end Splitting

end TauCeti
