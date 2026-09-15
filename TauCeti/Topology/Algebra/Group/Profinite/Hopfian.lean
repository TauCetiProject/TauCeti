/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.OpenSubgroup
public import TauCeti.Topology.Algebra.Group.Profinite.Basic

/-!
# Topologically finitely generated profinite groups are Hopfian

A group is *Hopfian* when every surjective endomorphism of it is injective. A profinite group
that is topologically finitely generated is Hopfian in the continuous sense: a continuous
surjective `f : G →* G` is automatically a topological automorphism.

The proof is a counting argument on the open subgroups. Pulling back along a continuous
surjection preserves the index of a subgroup and is injective, so it restricts to an injective
self-map of the open subgroups of any fixed index; finite generation makes each of those sets
finite (`TauCeti.IsTopologicallyFinitelyGenerated.finite_openSubgroup_index_eq`), so the
restriction is a bijection and every open subgroup of `G` is a preimage `f ⁻¹' V`. Any such
preimage contains `ker f`, and in a profinite group the open subgroups intersect in the trivial
subgroup, so `ker f` is trivial. A continuous bijection of compact Hausdorff groups is a
topological isomorphism, which upgrades injectivity to
`TauCeti.IsTopologicallyFinitelyGenerated.continuousMulEquivOfSurjective`.

## Sharpness

Finite generation cannot be dropped: on `G = ∏_{i : ℕ} F` with `F` a nontrivial finite group
the shift `(x₀, x₁, …) ↦ (x₁, x₂, …)` is a continuous surjective endomorphism with nontrivial
kernel.

There is no co-Hopfian counterpart: the converse implication, that a continuous *injective*
endomorphism is surjective, is false even for `G = ℤ_p`, where multiplication by `p` is injective
and not surjective.

## Main results

* `TauCeti.IsTopologicallyFinitelyGenerated.ker_eq_bot_of_surjective`: a continuous surjective
  endomorphism of a topologically finitely generated profinite group has trivial kernel.
* `TauCeti.IsTopologicallyFinitelyGenerated.injective_of_surjective`: such an endomorphism is
  injective (the Hopf property).
* `TauCeti.IsTopologicallyFinitelyGenerated.bijective_of_surjective`: such an endomorphism is
  bijective.
* `TauCeti.IsTopologicallyFinitelyGenerated.continuousMulEquivOfSurjective`: it is a
  topological automorphism.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Proposition 2.5.2.
-/

public section

namespace TauCeti

namespace IsTopologicallyFinitelyGenerated

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {f : G →* G}

/-- **A continuous surjective endomorphism of a topologically finitely generated profinite group
has trivial kernel.** Every open subgroup of `G` is a preimage `f ⁻¹' V`
(`TauCeti.IsTopologicallyFinitelyGenerated.openSubgroup_comap_surjective`), hence contains
`ker f`; the open normal subgroups of a profinite group intersect in `⊥`. -/
theorem ker_eq_bot_of_surjective (hG : IsTopologicallyFinitelyGenerated G) (hf : Continuous f)
    (hsurj : Function.Surjective f) : f.ker = ⊥ := by
  refine le_bot_iff.mp ?_
  rw [← Subgroup.iInf_openNormalSubgroup_eq_bot (G := G)]
  refine le_iInf fun N ↦ ?_
  obtain ⟨V, hV⟩ := hG.openSubgroup_comap_surjective hf hsurj N.toOpenSubgroup
  intro x hx
  have hxV : x ∈ V.comap f hf := by
    simp [MonoidHom.mem_ker.mp hx]
  exact hV ▸ hxV

/-- **Topologically finitely generated profinite groups are Hopfian.** A continuous surjective
endomorphism of such a group is injective. -/
theorem injective_of_surjective (hG : IsTopologicallyFinitelyGenerated G) (hf : Continuous f)
    (hsurj : Function.Surjective f) : Function.Injective f :=
  (MonoidHom.ker_eq_bot_iff f).mp (hG.ker_eq_bot_of_surjective hf hsurj)

/-- A continuous surjective endomorphism of a topologically finitely generated profinite group is
bijective. -/
theorem bijective_of_surjective (hG : IsTopologicallyFinitelyGenerated G) (hf : Continuous f)
    (hsurj : Function.Surjective f) : Function.Bijective f :=
  ⟨hG.injective_of_surjective hf hsurj, hsurj⟩

/-- A continuous surjective endomorphism of a topologically finitely generated profinite group,
packaged as a topological automorphism: it is bijective, and a continuous bijection from a
compact space to a Hausdorff space is a homeomorphism. -/
noncomputable def continuousMulEquivOfSurjective (hG : IsTopologicallyFinitelyGenerated G)
    (hf : Continuous f) (hsurj : Function.Surjective f) : G ≃ₜ* G := by
  have hb := hG.bijective_of_surjective hf hsurj
  exact ContinuousMulEquiv.mk (MulEquiv.ofBijective f hb) hf
    (hf.continuous_symm_of_equiv_compact_to_t2 (f := (MulEquiv.ofBijective f hb).toEquiv))

/-- The topological automorphism attached to a continuous surjective endomorphism is that
endomorphism. -/
@[simp]
theorem continuousMulEquivOfSurjective_apply (hG : IsTopologicallyFinitelyGenerated G)
    (hf : Continuous f) (hsurj : Function.Surjective f) (x : G) :
    hG.continuousMulEquivOfSurjective hf hsurj x = f x :=
  (rfl)

end IsTopologicallyFinitelyGenerated

end TauCeti
