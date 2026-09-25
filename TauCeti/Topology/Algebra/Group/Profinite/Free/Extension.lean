/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP
public import TauCeti.Topology.Algebra.Group.Profinite.Free.EmbeddingProblem
public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.Projective
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Extension

/-!
# Extensions of a free pro-`p` group split

Let `F = freeProP p X` be the free pro-`p` group on a type `X`, and let `1 → M → E → F → 1` be an
extension of topological groups with profinite total group `E` and pro-`p` kernel `M`. Then `E` is
pro-`p`, so the universal property of `F` extends any choice of preimages of the generators to a
continuous homomorphism `F → E`, which is a section of the projection because both composites agree
on the generators. So the extension splits by a continuous homomorphic section taking any
prescribed preimages on the generators
(`GroupExtension.exists_splitting_continuous_freeProP_forall_apply_of_eq`), and in particular
splits even when the total group lives in a different universe
(`GroupExtension.exists_splitting_continuous_freeProP`).

No finiteness of `X` is needed: the universal property and projectivity of `freeProP p X` hold
for every type. Read through the classification of profinite extensions
by continuous `H²`, this is the vanishing of `H²` of a free pro-`p` group, proved in
`TauCeti.Topology.Algebra.Group.Profinite.Free.Cohomology`.

## Main results

* `GroupExtension.exists_splitting_continuous_freeProP_forall_apply_of_eq`: a profinite extension
  of a free pro-`p` group by a pro-`p` group has a continuous homomorphic section with prescribed
  values on the generators, for any choice of preimages of the generators.
* `GroupExtension.exists_splitting_continuous_freeProP`: every profinite extension of a free
  pro-`p` group by a pro-`p` group splits by a continuous homomorphic section.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.4.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III, §5.
-/

public section

namespace TauCeti

universe u v

open freeProP

variable {p : ℕ} {X : Type u} {M : Type*} [Group M] [TopologicalSpace M]
  {E : Type u} [Group E] [TopologicalSpace E] [IsTopologicalGroup E] [CompactSpace E]
  [TotallyDisconnectedSpace E] (S : GroupExtension M E (freeProP p X))

/-- **A continuous homomorphic section with prescribed values on the generators.** Given an
extension `1 → M → E → freeProP p X → 1` of topological groups with profinite total group and
pro-`p` kernel, and a preimage `e x` of each generator `of x`, there is a continuous homomorphic
section sending `of x` to `e x`: the universal property of `freeProP p X` extends `e` to a
continuous homomorphism, which is a section because both composites agree on the generators. -/
theorem _root_.GroupExtension.exists_splitting_continuous_freeProP_forall_apply_of_eq
    (hinl : Continuous S.inl) (hrh : Continuous S.rightHom) (hM : IsProP p M) (e : X → E)
    (he : ∀ x, S.rightHom (e x) = of x) :
    ∃ s : S.Splitting, Continuous ⇑s ∧ ∀ x, s (of x) = e x := by
  have hE : IsProP p E := S.isProP hinl hrh hM (isProP_freeProP p X)
  -- The projection, bundled with its continuity; it evaluates as `S.rightHom` by construction.
  let π : E →ₜ* freeProP p X := ⟨S.rightHom, hrh⟩
  have hπ : ∀ z, π z = S.rightHom z := fun _ ↦ rfl
  have hs : π.comp (lift hE e) = ContinuousMonoidHom.id (freeProP p X) :=
    hom_ext fun x ↦ by simp [hπ, he]
  exact ⟨GroupExtension.Splitting.mk (lift hE e).toMonoidHom fun y ↦ by
    simpa [hπ] using DFunLike.congr_fun hs y, (lift hE e).continuous, fun x ↦ lift_of hE e x⟩

/-- **Extensions of a free pro-`p` group by a pro-`p` group split.** An extension
`1 → M → E → freeProP p X → 1` of topological groups with profinite total group and pro-`p` kernel
has a continuous homomorphic section, even when `E` and `freeProP p X` live in different
universes. -/
theorem _root_.GroupExtension.exists_splitting_continuous_freeProP
    {E' : Type v} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E'] [CompactSpace E']
    [TotallyDisconnectedSpace E'] (S : GroupExtension M E' (freeProP p X))
    (hinl : Continuous S.inl)
    (hrh : Continuous S.rightHom) (hM : IsProP p M) : ∃ s : S.Splitting, Continuous ⇑s := by
  have hE : IsProP p E' := S.isProP hinl hrh hM (isProP_freeProP p X)
  let π : E' →ₜ* freeProP p X := ⟨S.rightHom, hrh⟩
  obtain ⟨s, hs⟩ :=
    (isProjective_of_hasPGroupSolutions (hasPGroupSolutions_freeProP p X)).exists_continuous_lift
      hE π S.rightHom_surjective (ContinuousMonoidHom.id _)
  exact ⟨GroupExtension.Splitting.mk s.toMonoidHom fun y ↦ by
    have hy := DFunLike.congr_fun hs y
    change S.rightHom (s y) = y at hy
    exact hy, s.continuous⟩

end TauCeti
