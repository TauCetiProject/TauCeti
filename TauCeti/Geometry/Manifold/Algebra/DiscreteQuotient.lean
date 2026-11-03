/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Geometry.Manifold.Instances.Quotient
public import Mathlib.Topology.Covering.Quotient

/-!
# Smooth quotients of Lie groups by discrete subgroups

For a discrete subgroup `N` of a Lie group `G`, the native coset space `G ⧸ N` carries
charts pushed forward along its covering projection. Right translations by elements of `N`
are smooth deck transformations, so these charts make the coset space a manifold and the
projection a local diffeomorphism. No normality or local compactness is needed for this step.

If `N` is normal, the existing quotient group operations are smooth. A homomorphism trivial
on `N` descends smoothly exactly as expected: smoothness is tested after precomposition with
the quotient projection. In particular this supplies the smooth quotient and descent step
for representations of finite central quotients, without replacing the native quotient
carrier by an orbit-space model.

The chart and local-diffeomorphism construction uses
`IsLocalHomeomorph.isManifold_chartedSpaceOfRightInverse` and
`IsLocalHomeomorph.isLocalDiffeomorph_chartedSpaceOfRightInverse`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 21.
-/

public section

noncomputable section

open scoped Manifold ContDiff
open Topology

namespace Subgroup

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace H G]
  (N : Subgroup G) [DiscreteTopology N]

/-- The charts on the native coset space are pushed forward from the Lie group along the
covering projection. -/
instance instChartedSpaceDiscreteQuotient : ChartedSpace H (G ⧸ N) :=
  (N.isQuotientCoveringMap (SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance))
    |>.isCoveringMap.isLocalHomeomorph.chartedSpaceOfRightInverse
    QuotientGroup.mk_surjective.hasRightInverse.choose_spec

variable [LieGroup I n G]

omit [IsTopologicalGroup G] [DiscreteTopology N] in
/-- Right multiplication by a subgroup element is a smooth deck transformation. -/
private theorem quotientMk_smooth_deck (z w : G)
    (h : (QuotientGroup.mk z : G ⧸ N) = QuotientGroup.mk w) :
    ∃ φ : G → G, ContMDiffAt I I n φ z ∧ φ z = w ∧
      QuotientGroup.mk (s := N) ∘ φ =ᶠ[nhds z] QuotientGroup.mk (s := N) := by
  have hn : z⁻¹ * w ∈ N := QuotientGroup.eq.mp h
  refine ⟨fun x ↦ x * (z⁻¹ * w), (contMDiff_id.mul contMDiff_const).contMDiffAt,
    by simp, Filter.Eventually.of_forall fun x ↦ ?_⟩
  exact QuotientGroup.eq.mpr (by simpa using N.inv_mem hn)

/-- A discrete subgroup's native coset space is a manifold, with the same model as the group. -/
instance instIsManifoldDiscreteQuotient : IsManifold I n (G ⧸ N) :=
  (N.isQuotientCoveringMap (SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance))
    |>.isCoveringMap.isLocalHomeomorph.isManifold_chartedSpaceOfRightInverse (I := I) (n := n)
    QuotientGroup.mk_surjective.hasRightInverse.choose_spec (quotientMk_smooth_deck N)

/-- The native coset projection is a local diffeomorphism for the pushed-forward charts. -/
theorem isLocalDiffeomorph_quotientMk :
    IsLocalDiffeomorph I I n (QuotientGroup.mk (s := N)) :=
  (N.isQuotientCoveringMap (SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance))
    |>.isCoveringMap.isLocalHomeomorph
    |>.isLocalDiffeomorph_chartedSpaceOfRightInverse (I := I) (n := n)
    QuotientGroup.mk_surjective.hasRightInverse.choose_spec (quotientMk_smooth_deck N)

/-- Quotients by discrete normal subgroups are Lie groups for their native group structure
and the covering charts. -/
instance instLieGroupDiscreteQuotient [N.Normal] : LieGroup I n (G ⧸ N) :=
  (isLocalDiffeomorph_quotientMk (I := I) (n := n) N).lieGroup
    (QuotientGroup.mk' N) QuotientGroup.mk_surjective

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

/-- A map out of the native coset space is smooth if and only if it is smooth on the covering
group. This also applies to finite differentiability below the regularity of the group. -/
theorem contMDiff_quotient_iff {m : ℕ∞ω} (hm : m ≤ n) (f : G ⧸ N → M) :
    ContMDiff I I' m f ↔ ContMDiff I I' m (f ∘ QuotientGroup.mk (s := N)) :=
  ((isLocalDiffeomorph_quotientMk (I := I) (n := n) N).contMDiff_comp_iff
    QuotientGroup.mk_surjective hm).symm

/-- A smooth homomorphism killing a discrete normal subgroup descends smoothly to the native
quotient group. The target need only be a charted monoid, such as an endomorphism monoid;
its operations need not be smooth. -/
theorem contMDiff_quotientGroup_lift [N.Normal] [Monoid M] (f : G →* M) (hN : N ≤ f.ker)
    {m : ℕ∞ω} (hm : m ≤ n) (hf : ContMDiff I I' m f) :
    ContMDiff I I' m (QuotientGroup.lift N f hN) := by
  apply (N.contMDiff_quotient_iff (I := I) hm _).mpr
  simpa only [Function.comp_def, QuotientGroup.lift_mk] using hf

end Subgroup
