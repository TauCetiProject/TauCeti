/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.ShrinkingLemma
import TauCeti.Topology.LocallyFinite.Basic

/-!
# Smooth functions meeting every fiber of an open quotient map

Let `π : M → Q` be an open quotient map from a Hausdorff σ-compact finite-dimensional real manifold
onto a Hausdorff space. Then `M` has a nonnegative smooth function `β` which is nonzero somewhere
on every fiber of `π`, and whose support meets the preimage of each compact subset of `Q` in a
compact set (`TauCeti.exists_contMDiff_nonneg_isCompact_tsupport_inter_preimage`).

Such functions are the starting point for cutoff functions: dividing `β` by its sums along orbits
gives the cutoff functions of proper actions of discrete groups
(`TauCeti.MulAction.exists_isCutoff_contMDiff`), where `Q` is the orbit space, and of proper étale
groupoids (`TauCeti.Quiver.exists_isCutoff_contMDiff`), where `Q` is the coarse space of
isomorphism classes.

## Implementation notes

Note that `Q` is paracompact. Cover it by a locally finite family of open sets `O y` contained in
the images of compact sets `K₀ y`, shrink it to a cover by sets `V y` with
`closure (V y) ⊆ O y`, and sum smooth bump functions equal to one on
`K₀ y ∩ π ⁻¹' closure (V y)` and supported in a compact neighbourhood of `K₀ y` over `O y`.

## References

* N. Bourbaki, *Integration II*, Chapter VII, §2, for Bruhat functions of proper actions.
-/

public section

open Function Set Topology
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

end TauCeti
