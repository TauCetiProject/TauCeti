/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.ShrinkingLemma
public import TauCeti.Topology.CategoryTheory.Cutoff
public import TauCeti.Topology.CategoryTheory.IsomorphismClasses
import TauCeti.Topology.LocallyFinite.Basic

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

Both constructions start from a nonnegative smooth function `β` on a manifold `M` which is nonzero
somewhere on every fiber of an open quotient map `π : M → Q` onto a Hausdorff space, and whose
support meets the preimage of each compact subset of `Q` in a compact set
(`TauCeti.exists_contMDiff_nonneg_isCompact_tsupport_inter_preimage`). Here `Q` is the orbit space
or the coarse space of isomorphism classes.

## Implementation notes

To construct `β`, note that `Q` is paracompact. Cover it by a locally finite family of open sets
`O y` contained in the images of compact sets `K₀ y`, shrink it to a cover by sets `V y` with
`closure (V y) ⊆ O y`, and sum smooth bump functions equal to one on `K₀ y ∩ π ⁻¹' closure (V y)`
and supported in a compact neighbourhood of `K₀ y` over `O y`. For a groupoid, the properness of
the source-target map then gives the compactness condition of a cutoff function, and
`c = β / ∑ᶠ a, β a.right` by `TauCeti.Quiver.isCutoff_div_finsum`. Near each object the denominator
is a finite sum of `β` composed with the target and local inverses of the source
(`IsLocalHomeomorph.eventually_finsum_mem_preimage_singleton_eq_sum`), hence `C^n`.

## References

* M. Crainic, *Differentiable and algebroid cohomology, van Est isomorphisms, and characteristic
  classes*, Comment. Math. Helv. **78** (2003), Section 2, for cutoff functions on proper
  groupoids.
* N. Bourbaki, *Integration II*, Chapter VII, §2, for Bruhat functions of proper actions.
-/

public section

open CategoryTheory Function Set Topology
open scoped Manifold ContDiff

namespace TauCeti

section Proper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- Let `π : M → Q` be an open quotient map from a Hausdorff σ-compact finite-dimensional real
manifold onto a Hausdorff space, such as the projection to the orbit space of a proper action or
to the coarse space of a proper étale groupoid. Then `M` has a nonnegative smooth function which
is nonzero somewhere on every fiber of `π`, and whose topological support meets the preimage of
each compact set in a compact set. -/
theorem exists_contMDiff_nonneg_isCompact_tsupport_inter_preimage {Q : Type*} [TopologicalSpace Q]
    [T2Space Q] {π : M → Q} (hπ : IsOpenQuotientMap π) :
    ∃ β : M → ℝ, CMDiff ∞ β ∧ (∀ x, 0 ≤ β x) ∧
      (∀ ⦃L : Set Q⦄, IsCompact L → IsCompact (tsupport β ∩ π ⁻¹' L)) ∧
      ∀ x, ∃ z, π z = π x ∧ β z ≠ 0 := by
  -- Choose a locally finite cover of the paracompact space `Q` by sets `O y` lying under compact
  -- sets `K₀ y`, shrink it to `V y`, and let `β` be the sum of bumps `b y` equal to one on
  -- `K₀ y ∩ π ⁻¹' closure (V y)` and supported in `K₁ y ∩ π ⁻¹' O y`.
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  have : LocallyCompactSpace Q := hπ.locallyCompactSpace
  have : SigmaCompactSpace Q := isSigmaCompact_univ_iff.1 <| by
    simpa only [hπ.surjective.range_eq] using isSigmaCompact_range hπ.continuous
  -- For each `y`, a compact neighbourhood `K₀ y` of a point over `y` and a compact
  -- neighbourhood `K₁ y` of `K₀ y`.
  choose K₀ hK₀ hxK₀ using fun y : Q ↦ exists_compact_superset
    (isCompact_singleton (x := hπ.surjective.hasRightInverse.choose y))
  choose K₁ hK₁ hK₀₁ using fun y ↦ exists_compact_superset (hK₀ y)
  have hcov : ⋃ y, π '' interior (K₀ y) = univ := eq_univ_of_forall fun y ↦
    mem_iUnion.2 ⟨y, _, hxK₀ y rfl, hπ.surjective.hasRightInverse.choose_spec y⟩
  obtain ⟨O, hOo, hOcov, hOlf, hOsub⟩ :=
    precise_refinement _ (fun y ↦ hπ.isOpenMap _ isOpen_interior) hcov
  obtain ⟨V, hVcov, hV⟩ := exists_iUnion_eq_closure_subset hOo (fun y ↦ hOlf.point_finite y) hOcov
  -- Bump functions equal to one near `K₀ y ∩ π ⁻¹' closure (V y)`, supported over `O y` in `K₁ y`.
  have hsub (y) : K₀ y ∩ π ⁻¹' closure (V y) ⊆ interior (K₁ y ∩ π ⁻¹' O y) := by
    rw [interior_inter, ((hOo y).preimage hπ.continuous).interior_eq]
    exact fun x hx ↦ ⟨hK₀₁ y hx.1, (hV.2 y) hx.2⟩
  choose b hb1 hb0 hb01 using fun y ↦ exists_contMDiffMap_one_nhds_of_subset_interior I (n := ⊤)
    ((hK₀ y).isClosed.inter (isClosed_closure.preimage hπ.continuous)) (hsub y)
  have htsupp (y) : tsupport (b y) ⊆ K₁ y ∩ π ⁻¹' closure (O y) := by
    refine closure_minimal (fun x hx ↦ ?_)
      ((hK₁ y).isClosed.inter (isClosed_closure.preimage hπ.continuous))
    obtain ⟨hxK, hxO⟩ := of_not_not fun h ↦ hx (hb0 y x h)
    exact ⟨hxK, subset_closure hxO⟩
  have hlf : LocallyFinite fun y ↦ tsupport (b y) :=
    (hOlf.closure.preimage_continuous hπ.continuous).subset fun y ↦
      (htsupp y).trans inter_subset_right
  have hsupp := (hlf.subset fun y ↦ subset_tsupport (b y)).tsupport_finsum_subset
  refine ⟨fun x ↦ ∑ᶠ y, b y x,
    contMDiff_finsum (fun y ↦ (b y).contMDiff) (hlf.subset fun y ↦ subset_tsupport _),
    fun x ↦ finsum_nonneg fun y ↦ (hb01 y x).1, fun L hL ↦ ?_, fun x ↦ ?_⟩
  · -- A point over `L` in `tsupport (b y)` forces `L` to meet `closure (O y)`, which happens for
    -- finitely many `y`, and the point to lie in `K₁ y`.
    refine IsCompact.of_isClosed_subset
      ((hOlf.closure.finite_nonempty_inter_compact hL).isCompact_biUnion fun y _ ↦ hK₁ y)
      ((isClosed_tsupport _).inter (hL.isClosed.preimage hπ.continuous)) ?_
    rintro x ⟨hx, hxL⟩
    obtain ⟨y, hy⟩ := mem_iUnion.1 (hsupp hx)
    exact mem_biUnion ⟨π x, (htsupp y hy).2, hxL⟩ (htsupp y hy).1
  · -- The fiber through `x` meets some `K₀ y ∩ π ⁻¹' closure (V y)`, where `b y` equals one.
    obtain ⟨y, hy⟩ := mem_iUnion.1 (hVcov.symm ▸ mem_univ (π x) : π x ∈ ⋃ y, V y)
    obtain ⟨z, hz, hzx⟩ := hOsub y ((hV.2 y) (subset_closure hy))
    refine ⟨z, hzx, (zero_lt_one.trans_le ?_).ne'⟩
    have hbz : b y z = 1 := (hb1 y).self_of_nhdsSet _
      ⟨interior_subset hz, by rw [mem_preimage, hzx]; exact subset_closure hy⟩
    rw [← hbz]
    exact single_le_finsum y ((hlf.point_finite z).subset fun y' hy' ↦
      subset_tsupport _ hy') fun y' ↦ (hb01 y' _).1

end Proper

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
  refine ⟨_, isCutoff_div_finsum hs' ht'.continuous hβ0 hβK hpos,
    (hβs.of_le (by simp)).div₀ (fun x₀ ↦ ?_) fun x ↦ (finsum_mem_pos hs' hβ0 hβK (hpos x)).ne'⟩
  -- Near `x₀` the sum is a finite sum of `β` composed with the target and local inverses of the
  -- source.
  have hf (K : Set C) (hK : IsCompact K) :
      IsCompact (Quiver.Total.left ⁻¹' K ∩ tsupport (β ∘ Quiver.Total.right)) :=
    (hβK hK).of_isClosed_subset ((hK.isClosed.preimage hs'.continuous).inter (isClosed_tsupport _))
      (inter_subset_inter_right _ (tsupport_comp_subset_preimage β ht'.continuous))
  obtain ⟨F, hF, hev⟩ := hs'.eventually_finsum_mem_preimage_singleton_eq_sum
    (f := β ∘ Quiver.Total.right) hf (σ := fun a ↦ (hs a).localInverse)
    (fun a ↦ (hs a).continuousAt_localInverse)
    (fun a ↦ (hs a).localInverse_left_inv (hs a).localInverse_mem_target)
    (fun a ↦ (hs a).localInverse_eventuallyEq_right) x₀
  refine (ContMDiffAt.sum fun a ha ↦ ?_).congr_of_eventuallyEq hev
  rw [← hF a ha]
  exact (hβs.of_le (by simp)).contMDiffAt.comp _
    (ht.contMDiff.contMDiffAt.comp _ (hs a).contMDiffAt_localInverse)

end Quiver

end TauCeti
