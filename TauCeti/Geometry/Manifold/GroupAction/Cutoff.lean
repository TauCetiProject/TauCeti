/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.ShrinkingLemma
public import TauCeti.Topology.Algebra.GroupAction.Cutoff
public import TauCeti.Topology.LocallyFinite

/-!
# Smooth cutoff functions for proper actions on manifolds

Let a group `G` act properly discontinuously on a Hausdorff σ-compact finite-dimensional real
manifold `M` by `C^n` maps. Then `M` carries a `C^n` cutoff function for the action
(`TauCeti.MulAction.exists_isCutoff_contMDiff`): a nonnegative `C^n` function `c` with
`∑ᶠ g, c (g • x) = 1` for every `x`, whose support meets only finitely many translates of each
compact set. No faithfulness or freeness is assumed: every group element is counted, including
those acting trivially, so stabilizers and the ineffective kernel are retained.

For the action presentation `G ⋉ M` this is a cutoff function on the objects, summing to one over
the targets of the arrows with each given source, with the source map proper on the support of `c`
composed with the target (`TauCeti.MulAction.IsCutoff.isProperMap_snd`). Such functions turn
averages over the orbits of a proper action with noncompact orbit space into locally finite sums.

## Implementation notes

The construction first builds a nonnegative smooth function `β` whose support meets each orbit and
has the finiteness property. Cover the orbit space, which is paracompact, by a locally finite family
of open sets `O y` contained in the images of compact sets `C y ⊆ M`, shrink it to a cover by sets
`V y` with `closure (V y) ⊆ O y`, and sum smooth bump functions equal to one on
`C y ∩ π ⁻¹' closure (V y)` and supported in a compact neighbourhood of `C y` over `O y`. Then
`c = β / ∑ᶠ g, β (g • ·)` by `TauCeti.MulAction.isCutoff_div_finsum`.

## References

* N. Bourbaki, *Integration II*, Chapter VII, §2, for Bruhat functions of proper actions.
* M. Crainic, *Differentiable and algebroid cohomology, van Est isomorphisms, and characteristic
  classes*, Comment. Math. Helv. **78** (2003), Section 2, for cutoff functions on proper
  groupoids.
-/

public section

open Function MulAction Set Topology
open scoped Manifold ContDiff Pointwise

namespace TauCeti.MulAction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  (G : Type*) [Group G] [MulAction G M]

/-- A properly discontinuous action by homeomorphisms on a Hausdorff σ-compact finite-dimensional
manifold has a nonnegative smooth function meeting every orbit, whose topological support meets only
finitely many translates of each compact set. -/
private theorem exists_contMDiff_nonneg_finite_smul_inter_tsupport [ContinuousConstSMul G M]
    [ProperlyDiscontinuousSMul G M] :
    ∃ β : M → ℝ, CMDiff ∞ β ∧ (∀ x, 0 ≤ β x) ∧
      (∀ ⦃K : Set M⦄, IsCompact K → {g : G | (g • K ∩ tsupport β).Nonempty}.Finite) ∧
      ∀ x, ∃ g : G, β (g • x) ≠ 0 := by
  -- Choose a locally finite cover of the paracompact orbit space by sets `O y` lying under compact
  -- sets `C y`, shrink it to `V y`, and let `β` be the sum of bumps `b y` equal to one on
  -- `C y ∩ π ⁻¹' closure (V y)` and supported in `D y ∩ π ⁻¹' O y`.
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  let π : M → orbitRel.Quotient G M := Quotient.mk _
  have hπ : IsOpenQuotientMap π := isOpenQuotientMap_quotientMk
  have hπsmul (g : G) (x : M) : π (g • x) = π x := Quotient.sound ⟨g, rfl⟩
  have : LocallyCompactSpace (orbitRel.Quotient G M) := hπ.locallyCompactSpace
  have : SigmaCompactSpace (orbitRel.Quotient G M) := isSigmaCompact_univ_iff.1 <| by
    simpa only [hπ.surjective.range_eq] using isSigmaCompact_range hπ.continuous
  -- For each orbit `y`, a compact neighbourhood `C y` of a representative and a compact
  -- neighbourhood `D y` of `C y`.
  choose C hC hxC using fun y : orbitRel.Quotient G M ↦ exists_compact_superset
    (isCompact_singleton (x := y.out))
  choose D hD hCD using fun y ↦ exists_compact_superset (hC y)
  have hcov : ⋃ y, π '' interior (C y) = univ := eq_univ_of_forall fun y ↦
    mem_iUnion.2 ⟨y, y.out, hxC y rfl, y.out_eq⟩
  obtain ⟨O, hOo, hOcov, hOlf, hOsub⟩ :=
    precise_refinement _ (fun y ↦ hπ.isOpenMap _ isOpen_interior) hcov
  obtain ⟨V, hVcov, hV⟩ := exists_iUnion_eq_closure_subset hOo (fun y ↦ hOlf.point_finite y) hOcov
  -- Bump functions equal to one near `C y ∩ π ⁻¹' closure (V y)`, supported over `O y` in `D y`.
  have hsub (y) : C y ∩ π ⁻¹' closure (V y) ⊆ interior (D y ∩ π ⁻¹' O y) := by
    rw [interior_inter, ((hOo y).preimage hπ.continuous).interior_eq]
    exact fun x hx ↦ ⟨hCD y hx.1, (hV.2 y) hx.2⟩
  choose b hb1 hb0 hb01 using fun y ↦ exists_contMDiffMap_one_nhds_of_subset_interior I (n := ⊤)
    ((hC y).isClosed.inter (isClosed_closure.preimage hπ.continuous)) (hsub y)
  have htsupp (y) : tsupport (b y) ⊆ D y ∩ π ⁻¹' closure (O y) := by
    refine closure_minimal (fun x hx ↦ ?_)
      ((hD y).isClosed.inter (isClosed_closure.preimage hπ.continuous))
    obtain ⟨hxD, hxO⟩ := of_not_not fun h ↦ hx (hb0 y x h)
    exact ⟨hxD, subset_closure hxO⟩
  have hlf : LocallyFinite fun y ↦ tsupport (b y) :=
    (hOlf.closure.preimage_continuous hπ.continuous).subset fun y ↦
      (htsupp y).trans inter_subset_right
  have hsupp := (hlf.subset fun y ↦ subset_tsupport (b y)).tsupport_finsum_subset
  refine ⟨fun x ↦ ∑ᶠ y, b y x,
    contMDiff_finsum (fun y ↦ (b y).contMDiff) (hlf.subset fun y ↦ subset_tsupport _),
    fun x ↦ finsum_nonneg fun y ↦ (hb01 y x).1, fun K hK ↦ ?_, fun x ↦ ?_⟩
  · -- A translate `g • K` meeting `tsupport (b y)` forces `π '' K` to meet `closure (O y)`, which
    -- happens for finitely many `y`, and `g • K` to meet the compact set `D y`.
    refine ((hOlf.closure.finite_nonempty_inter_compact (hK.image hπ.continuous)).biUnion
      fun y _ ↦ properlyDiscontinuousSMul_iff.1 ‹_› hK (hD y)).subset ?_
    rintro g ⟨_, ⟨x, hx, rfl⟩, hgx⟩
    obtain ⟨y, hy⟩ := mem_iUnion.1 (hsupp hgx)
    obtain ⟨hyD, hyO⟩ := htsupp y hy
    rw [mem_preimage, hπsmul] at hyO
    exact mem_biUnion ⟨π x, hyO, x, hx, rfl⟩ ⟨g • x, smul_mem_smul_set hx, hyD⟩
  · -- The orbit of `x` meets some `C y ∩ π ⁻¹' closure (V y)`, where `b y` equals one.
    obtain ⟨y, hy⟩ := mem_iUnion.1 (hVcov.symm ▸ mem_univ (π x) : π x ∈ ⋃ y, V y)
    obtain ⟨z, hz, hzx⟩ := hOsub y ((hV.2 y) (subset_closure hy))
    obtain ⟨g, rfl⟩ := Quotient.exact hzx
    refine ⟨g, (zero_lt_one.trans_le ?_).ne'⟩
    have hbz : b y (g • x) = 1 := (hb1 y).self_of_nhdsSet _
      ⟨interior_subset hz, by simpa [hπsmul] using subset_closure hy⟩
    rw [← hbz]
    exact single_le_finsum y ((hlf.point_finite (g • x)).subset fun y' hy' ↦
      subset_tsupport _ hy') fun y' ↦ (hb01 y' _).1

variable {I} {n : ℕ∞} [ContMDiffConstSMul I n G M]

/-- A group acting properly discontinuously by `C^n` maps on a Hausdorff σ-compact
finite-dimensional real manifold has a `C^n` cutoff function. -/
theorem exists_isCutoff_contMDiff [ProperlyDiscontinuousSMul G M] :
    ∃ c : M → ℝ, IsCutoff G c ∧ CMDiff n c := by
  have := ContMDiffConstSMul.continuousConstSMul (I := I) (Γ := G) (M := M) n
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨β, hβs, hβ0, hfin, hpos⟩ :=
    exists_contMDiff_nonneg_finite_smul_inter_tsupport I (M := M) G
  have hc := isCutoff_div_finsum hβ0 hfin hpos
  refine ⟨_, hc, (hβs.of_le (by simp)).div₀ ?_ fun x ↦ ?_⟩
  · exact contMDiff_finsum (fun g ↦ (hβs.of_le (by simp)).comp (contMDiff_const_smul g))
      (locallyFinite_support_apply_smul hfin)
  · exact (finsum_apply_smul_pos hβ0 hfin (hpos x)).ne'

end TauCeti.MulAction
