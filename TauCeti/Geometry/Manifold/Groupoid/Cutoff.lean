/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.PartitionOfUnity.Cutoff
public import TauCeti.Topology.CategoryTheory.Cutoff
public import TauCeti.Topology.CategoryTheory.IsomorphismClasses

/-!
# Smooth cutoff functions for proper étale groupoids

Let `C` be a groupoid whose objects form a Hausdorff σ-compact finite-dimensional real manifold
and whose total arrows form a Hausdorff manifold, with source and target `C^n` local
diffeomorphisms and proper source-target map `a ↦ (a.left, a.right)`. Then `C` has a `C^n` cutoff
function (`TauCeti.Quiver.exists_isCutoff_contMDiff`): a nonnegative `C^n` function `c` on objects
with `∑ᶠ a ∈ Quiver.Total.left ⁻¹' {x}, c a.right = 1` for every object `x`, such that the source
map is proper on the support of `c` composed with the target. No effectiveness is assumed: every
arrow is counted, so isotropy arrows acting trivially near their object are retained.

This generalizes the cutoff functions of proper actions of discrete groups,
`TauCeti.MulAction.exists_isCutoff_contMDiff`, to proper étale groupoids. Cutoff functions are used
to average data over the arrows of a proper groupoid, and so to contract complexes of cochains on
its nerve.

## Implementation notes

The construction starts from a nonnegative smooth function `β` on objects which is nonzero
somewhere on every isomorphism class, and whose support meets the preimage of each compact set of
the coarse space of isomorphism classes in a compact set
(`TauCeti.exists_contMDiff_nonneg_isCompact_tsupport_inter_preimage`). The properness of the
source-target map then gives the compactness condition of a cutoff function, and
`c = β / ∑ᶠ a, β a.right` by `TauCeti.Quiver.isCutoff_div_finsum`. Near each object the denominator
is a finite sum of `β` composed with the target and local inverses of the source
(`IsLocalHomeomorph.eventually_finsum_mem_preimage_singleton_eq_sum`), hence `C^n`.

## References

* M. Crainic, *Differentiable and algebroid cohomology, van Est isomorphisms, and characteristic
  classes*, Comment. Math. Helv. **78** (2003), Section 2, for cutoff functions on proper
  groupoids.
-/

public section

open CategoryTheory Function Set Topology
open scoped Manifold ContDiff

namespace TauCeti

namespace Quiver

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {C : Type*} [CategoryTheory.Groupoid C] [TopologicalSpace C] [ChartedSpace H C]
  [IsManifold I ∞ C] [T2Space C] [SigmaCompactSpace C]
  [TopologicalSpace (Quiver.Total C)]

/-- A proper groupoid with locally homeomorphic source and target, whose objects form a Hausdorff
σ-compact finite-dimensional manifold, has a nonnegative smooth function on objects meeting every
orbit, such that the arrows with source in a compact set and target in its support form a compact
set. -/
private theorem exists_contMDiff_nonneg_isCompact_preimage_inter
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalHomeomorph (Quiver.Total.right : Quiver.Total C → C)) :
    ∃ β : C → ℝ, CMDiff ∞ β ∧ (∀ x, 0 ≤ β x) ∧
      (∀ ⦃K : Set C⦄, IsCompact K →
        IsCompact (Quiver.Total.left ⁻¹' K ∩ Quiver.Total.right ⁻¹' tsupport β)) ∧
      ∀ x, ∃ a ∈ Quiver.Total.left ⁻¹' {x}, β a.right ≠ 0 := by
  let π : C → Quotient (isIsomorphicSetoid C) := Quotient.mk _
  have hπ : IsOpenQuotientMap π :=
    isOpenQuotientMap_isomorphismClassesMk hs.continuous ht.isOpenMap
  have : T2Space (Quotient (isIsomorphicSetoid C)) :=
    t2Space_isomorphismClasses hs.continuous ht.isOpenMap hp.isClosedMap.isClosed_range
  obtain ⟨β, hβs, hβ0, hβK, hpos⟩ := exists_contMDiff_nonneg_isCompact_tsupport_inter_preimage I hπ
  refine ⟨β, hβs, hβ0, fun K hK ↦ ?_, fun x ↦ ?_⟩
  · -- The targets of these arrows lie in the support of `β` over the image of `K`.
    refine (hp.isCompact_preimage (hK.prod (hβK (hK.image hπ.continuous)))).of_isClosed_subset
      ((hK.isClosed.preimage hs.continuous).inter ((isClosed_tsupport _).preimage ht.continuous))
      fun a ⟨haK, ha⟩ ↦ ⟨haK, ha, a.left, haK, isomorphismClassesMk_eq_iff.2 ⟨a.hom⟩⟩
  · obtain ⟨z, hzx, hz⟩ := hpos x
    obtain ⟨f⟩ := isomorphismClassesMk_eq_iff.1 hzx.symm
    exact ⟨⟨x, z, f⟩, rfl, hz⟩

variable {I} [ChartedSpace H' (Quiver.Total C)] [T2Space (Quiver.Total C)] {n : ℕ∞}

/-- **Smooth cutoff functions of proper étale groupoids.** A groupoid whose objects form a
Hausdorff σ-compact finite-dimensional real manifold, whose total arrows form a Hausdorff manifold,
whose source and target are `C^n` local diffeomorphisms, and whose source-target map is proper, has
a `C^n` cutoff function. -/
theorem exists_isCutoff_contMDiff
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C)) :
    ∃ c : C → ℝ, IsCutoff c ∧ CMDiff n c := by
  have : LocallyCompactSpace C := Manifold.locallyCompact_of_finiteDimensional I
  have hs' := hs.isLocalHomeomorph
  have ht' := ht.isLocalHomeomorph
  obtain ⟨β, hβs, hβ0, hβK, hpos⟩ := exists_contMDiff_nonneg_isCompact_preimage_inter I hp hs' ht'
  refine ⟨_, isCutoff_div_finsum hs' hβ0 hβK hpos,
    (hβs.of_le (by simp)).div₀ (fun x₀ ↦ ?_) fun x ↦
      (finsum_mem_preimage_left_singleton_pos hs' hβ0 hβK (hpos x)).ne'⟩
  -- Near `x₀` the sum is a finite sum of `β` composed with the target and local inverses of the
  -- source.
  obtain ⟨F, hF, hev⟩ := hs'.eventually_finsum_mem_preimage_singleton_eq_sum
    (f := β ∘ Quiver.Total.right)
    (fun K hK ↦ isCompact_preimage_left_inter_tsupport_comp ht'.continuous (hβK hK))
    (σ := fun a ↦ (hs a).localInverse)
    (fun a ↦ (hs a).continuousAt_localInverse)
    (fun a ↦ (hs a).localInverse_left_inv (hs a).localInverse_mem_target)
    (fun a ↦ (hs a).localInverse_eventuallyEq_right) x₀
  refine (ContMDiffAt.sum fun a ha ↦ ?_).congr_of_eventuallyEq hev
  rw [← hF a ha]
  exact (hβs.of_le (by simp)).contMDiffAt.comp _
    (ht.contMDiff.contMDiffAt.comp _ (hs a).contMDiffAt_localInverse)

end Quiver

end TauCeti
