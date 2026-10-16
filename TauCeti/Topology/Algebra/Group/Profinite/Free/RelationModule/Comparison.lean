/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Map
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Basic

/-!
# A weak comparison of free and arithmetic class-module extensions

Let `g : ι → G/W` be a family in a quotient of a profinite group. The homomorphism
`lift g` induced from the free profinite group has kernel `R`. Choosing lifts of the family
to `G` gives a continuous map `F / ker(R → Rᵃᵇ(p)) → G / ker(W → Wᵃᵇ(p))` covering `lift g`.

This map is not asserted to be surjective. For a finite Galois quotient, it is the weak
comparison used to detect a generating source extension class before correcting and lifting
a separate relation-module surjection. Its existence uses no cohomological-dimension theorem.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  proof of (7.4.1).
-/

public section

namespace TauCeti.freeProfiniteGroup

universe u

variable (p : ℕ) {ι G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  (W : Subgroup G) [W.Normal] [IsClosed (W : Set G)] (g : ι → G ⧸ W)

/-- The homomorphism `lift g` induced by a family in `G/W` admits a continuous comparison of
its pro-`p` class-module extension with that of `G`. The comparison covers `lift g`,
without any surjectivity assumption or conclusion. -/
theorem exists_abelianizationProPExtension_comparison :
    ∃ ψ : abelianizationProPExtensionGroup p (freeProfiniteGroup ι)
        (lift g : freeProfiniteGroup ι →* G ⧸ W).ker →ₜ*
      abelianizationProPExtensionGroup p G W,
      ∀ x : freeProfiniteGroup ι,
        (abelianizationProPExtension p G W).rightHom (ψ (QuotientGroup.mk x)) = lift g x := by
  let a : ι → G := fun i ↦ (g i).out
  let f := lift a
  let q := Subgroup.quotientMkContinuousMonoidHom W
  have hqa : (q : G → G ⧸ W) ∘ a = g := by
    funext i
    exact (Subgroup.quotientMkContinuousMonoidHom_apply W (a i)).trans (QuotientGroup.out_eq' (g i))
  have hcomp : q.comp f = lift g := (comp_lift q a).trans (congrArg lift hqa)
  have hVW : (lift g : freeProfiniteGroup ι →* G ⧸ W).ker ≤ W.comap f.toMonoidHom := by
    intro x hx
    rw [Subgroup.mem_comap, ← QuotientGroup.eq_one_iff]
    have hxone : lift g x = 1 := MonoidHom.mem_ker.mp hx
    exact (DFunLike.congr_fun hcomp x).trans hxone
  refine ⟨abelianizationProPExtensionMap p f.toMonoidHom f.continuous hVW, fun x ↦ ?_⟩
  rw [abelianizationProPExtensionMap_mk, abelianizationProPExtension_rightHom,
    QuotientGroup.mapOfLE_mk]
  exact DFunLike.congr_fun hcomp x

end TauCeti.freeProfiniteGroup
