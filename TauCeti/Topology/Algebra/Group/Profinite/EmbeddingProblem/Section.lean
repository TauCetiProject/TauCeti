/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.CohomologicalDimension

/-!
# Sections through pro-`p` kernels

A continuous surjection `f : E ↠ G` of profinite groups whose kernel is pro-`p` has a continuous
homomorphic section as soon as `cd_p G ≤ 1`. The bound solves every finite embedding problem for
`G` with `p`-group kernel, and such solutions lift continuous homomorphisms through surjections with
pro-`p` kernel (`TauCeti.HasPGroupSolutions.exists_continuous_lift_of_isProP_ker`); lifting the
identity of `G` gives the section. Neither `E` nor `G` need be pro-`p` or finitely generated.

The relative form finds the section inside any closed subgroup `E'` of `E` with `f(E') = G`, needing
only the part of the kernel inside `E'` to be pro-`p`.

The hypothesis on `G` cannot be dropped: `ℤ/p² ↠ ℤ/p` has kernel of order `p` and no section, and
`cd_p (ℤ/p) = ∞`.

## Main results

* `TauCeti.exists_continuous_section_of_isProP_ker`: a continuous surjection of profinite groups
  with pro-`p` kernel onto a group with `cd_p ≤ 1` has a continuous homomorphic section.
* `TauCeti.exists_continuous_section_mem_of_isProP_ker`: the section can be chosen with values in
  any closed subgroup that surjects onto the target and meets the kernel in a pro-`p` subgroup.

## References

* J.-P. Serre, *Galois Cohomology*, Chapter I, §3.4, Proposition 16.
* F.-V. Kuhlmann, M. Pank and P. Roquette, *Immediate and purely wild extensions of valued
  fields*, Manuscripta Math. 55 (1986), 39–67, p. 44.
-/

public section

namespace TauCeti

universe u v

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
variable {E : Type v} [Group E] [TopologicalSpace E] [IsTopologicalGroup E]
  [CompactSpace E] [TotallyDisconnectedSpace E]

/-- **Sections through pro-`p` kernels.** A continuous surjection `f : E ↠ G` of profinite groups
with pro-`p` kernel has a continuous homomorphic section when `cd_p G ≤ 1`. -/
theorem exists_continuous_section_of_isProP_ker [Fact p.Prime]
    (hG : cohomologicalDimensionAt.{u} p G ≤ 1) (f : E →ₜ* G) (hf : Function.Surjective f)
    (hker : IsProP p f.toMonoidHom.ker) :
    ∃ s : G →ₜ* E, f.comp s = ContinuousMonoidHom.id G := by
  rw [← Nat.cast_one, cohomologicalDimensionAt_le_iff] at hG
  exact hG.hasElementaryAbelianSolutions.hasPGroupSolutions.exists_continuous_lift_of_isProP_ker
    f hf hker _

/-- **Sections through pro-`p` kernels, relative form.** Let `f : E ↠ G` be a continuous
homomorphism of profinite groups with `cd_p G ≤ 1`, and `E'` a closed subgroup of `E` with
`f(E') = G` whose intersection with the kernel of `f` is pro-`p`. Then `f` has a continuous
homomorphic section with values in `E'`. -/
theorem exists_continuous_section_mem_of_isProP_ker [Fact p.Prime]
    (hG : cohomologicalDimensionAt.{u} p G ≤ 1) (f : E →ₜ* G) {E' : Subgroup E}
    (hE' : IsClosed (E' : Set E)) (hf : E'.map f.toMonoidHom = ⊤)
    (hker : IsProP p (f.toMonoidHom.ker ⊓ E' : Subgroup E)) :
    ∃ s : G →ₜ* E, f.comp s = ContinuousMonoidHom.id G ∧ ∀ g, s g ∈ E' := by
  have : CompactSpace E' := isCompact_iff_compactSpace.mp hE'.isCompact
  -- Restrict `f` to `E'`; its kernel is the kernel of `f` intersected with `E'`, read in `E'`.
  let ι : E' →ₜ* E := ⟨E'.subtype, continuous_subtype_val⟩
  let f' : E' →ₜ* G := f.comp ι
  have hf' : Function.Surjective f' := fun g ↦ by
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp (hf ▸ Subgroup.mem_top g)
    exact ⟨⟨e, he⟩, rfl⟩
  have hker' : IsProP p f'.toMonoidHom.ker := by
    -- `f'.toMonoidHom` is `f.toMonoidHom.domRestrict E'` by definition: both send `x : E'` to
    -- `f x`, so `ker_domRestrict` applies after unfolding `ContinuousMonoidHom.comp` and `ι`.
    rw [show f'.toMonoidHom.ker = _ from MonoidHom.ker_domRestrict E' f.toMonoidHom,
      ← Subgroup.inf_subgroupOf_right, Subgroup.isProP_subgroupOf_iff inf_le_right]
    exact hker
  obtain ⟨s, hs⟩ := exists_continuous_section_of_isProP_ker hG f' hf' hker'
  exact ⟨ι.comp s, hs, fun g ↦ (s g).2⟩

end TauCeti
