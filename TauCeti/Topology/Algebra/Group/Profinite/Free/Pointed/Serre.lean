/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.CohomologicalDimension
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Pointed.EmbeddingProblem
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Pointed.Presentation
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Burnside

/-!
# Serre's theorem at arbitrary rank: projective pro-`p` groups are free

Let `G` be a pro-`p` group, not necessarily topologically finitely generated. If `G` is
projective, meaning that every continuous homomorphism from `G` into a quotient of a profinite
pro-`p` group lifts continuously, then `G` is free pro-`p` on a pointed profinite space: some
subset `s ⊆ G` converging to `1` has a presentation `F_p(insert 1 s, 1) → G`
(`TauCeti.IsProP.presentation`) that is a topological isomorphism. In particular this holds when
`cd_p G ≤ 1`, which is **Serre's theorem** with no finite generation hypothesis. Conversely the
free pro-`p` group on a pointed space is projective, so for pro-`p` groups projectivity and
freeness coincide.

The proof runs the finite-rank argument of `TauCeti.Topology.Algebra.Group.Profinite.Free.Serre`
on a minimal presentation on a pointed space: `G` has a presentation on a subset `s` converging to
`1` whose kernel lies in the Frattini subgroup of `F_p(insert 1 s, 1)`. Projectivity lifts the
identity of `G` through it to a continuous homomorphic section, and a Frattini cover of a pro-`p`
group with such a section is an isomorphism (`TauCeti.IsProP.continuousMulEquivOfLeftInverse`).
Only this direction of Serre's cohomological characterisation of free pro-`p` groups is proved
here.

## Main results

* `TauCeti.IsProP.exists_convergesToOne_continuousMulEquiv_presentation_of_isProjective`: a
  projective pro-`p` group is free pro-`p` on a pointed profinite space, its presentation on some
  subset converging to `1` being a topological isomorphism.
* `TauCeti.IsProP.isProjective_iff_exists_convergesToOne_continuousMulEquiv_presentation`: a
  pro-`p` group is projective if and only if it is free pro-`p` on a pointed profinite space.
* `IsProP.exists_convergesToOne_continuousMulEquiv_presentation_of_cohomologicalDimensionAt_le_one`
  (in the `TauCeti` namespace): **Serre's theorem at arbitrary rank**, a pro-`p` group with
  `cd_p ≤ 1` is free pro-`p` on a pointed profinite space.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §4.2 and §5.9.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III, §5.
* L. Ribes and P. Zalesskii, *Profinite Groups*, 2nd ed., Section 7.7.
-/

public section

namespace TauCeti

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace IsProP

/-- **Projective pro-`p` groups are free pro-`p` on a pointed profinite space.** A projective
pro-`p` group `G` has a subset `s` converging to `1` whose presentation `F_p(insert 1 s, 1) → G`
is a topological isomorphism. -/
theorem exists_convergesToOne_continuousMulEquiv_presentation_of_isProjective (hG : IsProP p G)
    (hproj : IsProjective.{u, u, u} p G) :
    ∃ s : Set G, ConvergesToOne s ∧
      ∃ e : freeProPInsertOne p s ≃ₜ* G, ⇑e = ⇑(hG.presentation s) := by
  -- A minimal presentation on a set converging to `1`: its kernel lies in the Frattini subgroup.
  obtain ⟨s, hs, hsurj, hker, -⟩ :=
    hG.exists_convergesToOne_presentation_surjective_ker_le_proPFrattini
  have hF : IsProP p (freeProPInsertOne p s) :=
    isProC_finiteGroupClassP_iff.mp
      (isProC_freeProCPointed (finiteGroupClassP.{u} p) _)
  -- Projectivity lifts the identity of `G` through the presentation to a continuous section.
  obtain ⟨σ, hσ⟩ := hproj.exists_continuous_lift hF (hG.presentation s) hsurj (.id G)
  have hσ' : Function.LeftInverse (hG.presentation s) σ := fun g ↦ by
    simpa using DFunLike.congr_fun hσ g
  exact ⟨s, hs, hF.continuousMulEquivOfLeftInverse (hG.presentation s) σ hσ' hker,
    funext (hF.continuousMulEquivOfLeftInverse_apply (hG.presentation s) σ hσ' hker)⟩

/-- **A pro-`p` group is projective if and only if it is free pro-`p` on a pointed profinite
space**, its presentation on some subset converging to `1` being a topological isomorphism. -/
theorem isProjective_iff_exists_convergesToOne_continuousMulEquiv_presentation (hG : IsProP p G) :
    IsProjective.{u, u, u} p G ↔ ∃ s : Set G, ConvergesToOne s ∧
      ∃ e : freeProPInsertOne p s ≃ₜ* G, ⇑e = ⇑(hG.presentation s) :=
  ⟨hG.exists_convergesToOne_continuousMulEquiv_presentation_of_isProjective,
    fun ⟨_, _, e, _⟩ ↦ (isProjective_freeProCPointed p _).of_equiv e⟩

/-- **Serre's theorem at arbitrary rank.** A pro-`p` group `G` with `cd_p G ≤ 1` is free pro-`p`
on a pointed profinite space: some subset `s` of `G` converging to `1` has a presentation
`F_p(insert 1 s, 1) → G` that is a topological isomorphism. No finite generation is assumed. -/
theorem exists_convergesToOne_continuousMulEquiv_presentation_of_cohomologicalDimensionAt_le_one
    (hG : IsProP p G) (hcd : cohomologicalDimensionAt.{u} p G ≤ 1) :
    ∃ s : Set G, ConvergesToOne s ∧
      ∃ e : freeProPInsertOne p s ≃ₜ* G, ⇑e = ⇑(hG.presentation s) :=
  hG.exists_convergesToOne_continuousMulEquiv_presentation_of_isProjective
    ((cohomologicalDimensionAt_le_iff p G 1).mp (by exact_mod_cast hcd)).isProjective

end IsProP

end TauCeti
