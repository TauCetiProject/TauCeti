/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Topology.Algebra.GroupAction.Cutoff
import Mathlib.Geometry.Manifold.Algebra.Structures
import TauCeti.Geometry.Manifold.GroupAction.Cutoff
import TauCeti.Topology.LocallyFinite

/-!
# Invariant smooth partitions of unity

Let a group `G` act on a manifold `M` by smooth maps (`ContMDiffConstSMul I ∞ G M`). A smooth
partition of unity `f` of a `G`-stable set `s` can be averaged over the action in two ways.

* If `G` is finite, `(f.average G hs) i x = |G|⁻¹ * ∑ g, f i (g • x)`.
* If `c` is a smooth cutoff function for the action (`TauCeti.MulAction.IsCutoff`: `c ≥ 0`,
  `∑ᶠ g, c (g • x) = 1`, and the support of `c` meets only finitely many translates of each compact
  set), `(f.cutoffAverage hc hcs hs) i x = ∑ᶠ g, c (g • x) * f i (g • x)`. Here `G` may be
  infinite, and `M` must be weakly locally compact.

In both cases the result is again a smooth partition of unity of `s`, every function of which is
`G`-invariant, and it is subordinate to every `G`-invariant cover to which `f` is subordinate.
Every group element is counted, including those acting trivially on `M`, so the action may be
ineffective. Proper discontinuous actions on finite-dimensional σ-compact Hausdorff manifolds have
smooth cutoff functions (`TauCeti.MulAction.exists_isCutoff_contMDiff`). Combined with Mathlib's
existence theorem `SmoothPartitionOfUnity.exists_isSubordinate`, this gives `G`-invariant smooth
partitions of unity subordinate to any `G`-invariant open cover of a closed `G`-stable set, for
every proper discontinuous action and in particular every finite group action.

Such partitions glue `G`-invariant local data (sections, connections, metrics) on a manifold with a
group action without leaving the invariant world: on finite quotient charts `U/G`, and globally on
the action presentation `G ⋉ M` of a proper action of a discrete group, whose orbit space need not
be compact.

## Main definitions and results

* `SmoothPartitionOfUnity.average`: the average of a smooth partition of unity of `s` over a finite
  group (or any finite nonempty type) acting by smooth maps that preserve `s`.
* `SmoothPartitionOfUnity.average_apply_smul`: for a group action, the averaged functions are
  invariant.
* `SmoothPartitionOfUnity.average_eq_self`: averaging does not change a partition of unity whose
  functions are already invariant.
* `SmoothPartitionOfUnity.IsSubordinate.average`: averaging preserves subordination to a
  `G`-invariant cover.
* `SmoothPartitionOfUnity.cutoffAverage`: the average of a smooth partition of unity of `s`
  weighted by a smooth cutoff function of an action by smooth maps that preserve `s`, with the
  same three properties `SmoothPartitionOfUnity.cutoffAverage_apply_smul`,
  `SmoothPartitionOfUnity.cutoffAverage_eq_self` and
  `SmoothPartitionOfUnity.IsSubordinate.cutoffAverage`.
* `SmoothPartitionOfUnity.exists_isSubordinate_smul_invariant`: for a proper discontinuous action,
  a closed `G`-stable set covered by `G`-invariant open sets has a `G`-invariant smooth partition of
  unity subordinate to the cover.

## References

* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Cambridge University Press,
  2007, Chapter 1.
* M. Crainic, *Differentiable and algebroid cohomology, van Est isomorphisms, and characteristic
  classes*, Comment. Math. Helv. **78** (2003), Section 2, for averaging with cutoff functions on
  proper groupoids.
-/

public section

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace SmoothPartitionOfUnity

variable {ι E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {s : Set M}

section SMul

variable (G : Type*) [Fintype G] [SMul G M] (f : SmoothPartitionOfUnity ι I M s)

/-- An averaged function vanishes at `x` unless some `f i` is nonzero at a translate of `x`. -/
private theorem support_inv_card_mul_sum_subset (i : ι) :
    support (fun x ↦ (Fintype.card G : ℝ)⁻¹ * ∑ g : G, f i (g • x)) ⊆
      ⋃ g : G, (g • ·) ⁻¹' support (f i) := fun x hx ↦ by
  obtain ⟨g, -, hg⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hx)
  exact mem_iUnion.2 ⟨g, hg⟩

/-- Summing the averaged functions over the index set commutes with the average over `G`. -/
private theorem finsum_inv_card_mul_sum (x : M) :
    ∑ᶠ i, (Fintype.card G : ℝ)⁻¹ * ∑ g : G, f i (g • x) =
      (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ∑ᶠ i, f i (g • x) := by
  rw [← mul_finsum, finsum_sum_comm _ _ fun g _ ↦ f.locallyFinite.point_finite (g • x)]

variable [Nonempty G] [ContMDiffConstSMul I ∞ G M] (hs : ∀ g : G, ∀ x ∈ s, g • x ∈ s)

/-- The average of a smooth partition of unity of a `G`-stable set `s` over a finite nonempty type
`G` acting by smooth maps, typically a finite group: its `i`-th function is
`x ↦ |G|⁻¹ * ∑ g, f i (g • x)`. For a group action its functions are `G`-invariant
(`SmoothPartitionOfUnity.average_apply_smul`). -/
def average : SmoothPartitionOfUnity ι I M s where
  toFun i := ⟨fun x ↦ (Fintype.card G : ℝ)⁻¹ * ∑ g : G, f i (g • x),
    contMDiff_const.mul <| ContMDiff.sum fun g _ ↦ (f i).contMDiff.comp (contMDiff_const_smul g)⟩
  locallyFinite' :=
    (LocallyFinite.iUnion fun g : G ↦ f.locallyFinite.preimage_continuous
      (contMDiff_const_smul (I := I) (n := ∞) g).continuous).subset
        (support_inv_card_mul_sum_subset G f)
  nonneg' i x := mul_nonneg (by positivity) (Finset.sum_nonneg fun g _ ↦ f.nonneg i _)
  sum_eq_one' x hx := by
    simp [finsum_inv_card_mul_sum, f.sum_eq_one (hs _ x hx), Fintype.card_ne_zero]
  sum_le_one' x := by
    simp only [ContMDiffMap.coeFn_mk, finsum_inv_card_mul_sum]
    calc (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ∑ᶠ i, f i (g • x)
        ≤ (Fintype.card G : ℝ)⁻¹ * ∑ _g : G, 1 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g _ ↦ f.sum_le_one _) (by positivity)
      _ = 1 := by
          simp [Fintype.card_ne_zero]

variable {G f hs}

/-- The `i`-th averaged function at `x` is the mean of `f i` over the translates `g • x`. -/
@[simp]
theorem average_apply (i : ι) (x : M) :
    f.average G hs i x = (Fintype.card G : ℝ)⁻¹ * ∑ g : G, f i (g • x) :=
  (rfl)

/-- An averaged function is supported on the translates of the support of the original one. -/
theorem support_average_subset (i : ι) :
    support (f.average G hs i) ⊆ ⋃ g : G, (g • ·) ⁻¹' support (f i) :=
  support_inv_card_mul_sum_subset G f i

/-- An averaged function is topologically supported on the translates of the topological support
of the original one. -/
theorem tsupport_average_subset (i : ι) :
    tsupport (f.average G hs i) ⊆ ⋃ g : G, (g • ·) ⁻¹' tsupport (f i) :=
  closure_minimal ((support_average_subset i).trans <| iUnion_mono fun _ ↦
      preimage_mono (subset_tsupport _))
    (isClosed_iUnion_of_finite fun g ↦
      (isClosed_tsupport _).preimage (contMDiff_const_smul (I := I) (n := ∞) g).continuous)

/-- **Averaging fixes invariant partitions of unity.** If every function of `f` is invariant under
`G`, then averaging over `G` returns `f`. -/
theorem average_eq_self (hf : ∀ i (g : G) x, f i (g • x) = f i x) : f.average G hs = f :=
  DFunLike.ext _ _ fun i ↦ ContMDiffMap.ext fun x ↦ by
    simp [hf, Fintype.card_ne_zero]

end SMul

section Group

variable {G : Type*} [Group G] [Fintype G] [MulAction G M] [ContMDiffConstSMul I ∞ G M]
  {f : SmoothPartitionOfUnity ι I M s} {hs : ∀ g : G, ∀ x ∈ s, g • x ∈ s}

/-- **Averaged partitions of unity are invariant.** For a finite group acting by smooth maps, every
function of the averaged partition of unity is `G`-invariant. -/
@[simp high]
theorem average_apply_smul (i : ι) (h : G) (x : M) :
    f.average G hs i (h • x) = f.average G hs i x := by
  simp only [average_apply, smul_smul]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight h) _ _ fun _ ↦ rfl

/-- **Averaging preserves subordination to an invariant cover.** If `f` is subordinate to a cover
`U` each of whose members is `G`-invariant, then so is its average over `G`. -/
theorem IsSubordinate.average {U : ι → Set M} (hf : f.IsSubordinate U)
    (hU : ∀ (g : G) i, ∀ x ∈ U i, g • x ∈ U i) : (f.average G hs).IsSubordinate U := fun i ↦
  (tsupport_average_subset i).trans <| iUnion_subset fun g x hx ↦ by
    simpa using hU g⁻¹ i _ (hf i hx)

end Group

section Cutoff

variable {G : Type*} [SMul G M] {c : M → ℝ}

/-- Summing cutoff averages over the index set commutes with the cutoff average. -/
private theorem finsum_finsum_cutoff_mul (hc : TauCeti.MulAction.IsCutoff G c)
    (f : SmoothPartitionOfUnity ι I M s) (x : M) :
    ∑ᶠ i, ∑ᶠ g : G, c (g • x) * f i (g • x) = ∑ᶠ g : G, c (g • x) * ∑ᶠ i, f i (g • x) := by
  classical
  -- Only the finitely many `g` with `c (g • x) ≠ 0` contribute, so both sums over `G` are
  -- finite sums over the same finset.
  let S := (hc.hasFiniteSupport x).toFinset
  have hS (h : G → ℝ) : ∑ᶠ g : G, c (g • x) * h g = ∑ g ∈ S, c (g • x) * h g :=
    finsum_eq_sum_of_support_subset _ fun _ hg ↦
      Finset.mem_coe.2 <| (hc.hasFiniteSupport x).mem_toFinset.2 (left_ne_zero_of_mul hg)
  calc ∑ᶠ i, ∑ᶠ g : G, c (g • x) * f i (g • x)
      = ∑ᶠ i, ∑ g ∈ S, c (g • x) * f i (g • x) := finsum_congr fun i ↦ hS _
    _ = ∑ g ∈ S, ∑ᶠ i, c (g • x) * f i (g • x) :=
        finsum_sum_comm S _ fun g _ ↦ (f.locallyFinite.point_finite (g • x)).subset
          fun _ hi ↦ right_ne_zero_of_mul hi
    _ = ∑ g ∈ S, c (g • x) * ∑ᶠ i, f i (g • x) := by simp only [mul_finsum]
    _ = ∑ᶠ g : G, c (g • x) * ∑ᶠ i, f i (g • x) := (hS _).symm

variable [ContMDiffConstSMul I ∞ G M] [WeaklyLocallyCompactSpace M]
  (hc : TauCeti.MulAction.IsCutoff G c) (hcs : CMDiff ∞ c) (hs : ∀ g : G, ∀ x ∈ s, g • x ∈ s)
  (f : SmoothPartitionOfUnity ι I M s)

/-- The cutoff average of a smooth partition of unity of a `G`-stable set `s`, for a smooth cutoff
function `c` of an action of `G` by smooth maps (`TauCeti.MulAction.IsCutoff`): its `i`-th function
is `x ↦ ∑ᶠ g, c (g • x) * f i (g • x)`. The group `G` may be infinite, as for a proper action of a
discrete group, and every element is counted, including those acting trivially. For a group action
its functions are `G`-invariant (`SmoothPartitionOfUnity.cutoffAverage_apply_smul`). -/
def cutoffAverage : SmoothPartitionOfUnity ι I M s where
  toFun i := ⟨fun x ↦ ∑ᶠ g : G, c (g • x) * f i (g • x),
    contMDiff_finsum (fun g ↦ (hcs.comp (contMDiff_const_smul g)).mul
      ((f i).contMDiff.comp (contMDiff_const_smul g)))
      (hc.locallyFinite_support.subset fun _ _ hx ↦ left_ne_zero_of_mul hx)⟩
  locallyFinite' x := by
    -- Only finitely many `g` carry a compact neighbourhood `K` of `x` onto the support of `c`,
    -- and each translate `g • K` meets the supports of only finitely many `f i`.
    have := ContMDiffConstSMul.continuousConstSMul (I := I) (Γ := G) (M := M) ∞
    obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
    refine ⟨K, hKx, ((hc.finite_smul_inter_tsupport hK).biUnion fun g _ ↦
      f.locallyFinite.finite_nonempty_inter_compact (hK.smul g)).subset ?_⟩
    rintro i ⟨y, hy, hyK⟩
    obtain ⟨g, hg⟩ : ∃ g : G, c (g • y) * f i (g • y) ≠ 0 := by
      by_contra! H
      exact hy (by simp [H])
    exact mem_biUnion (x := g)
      ⟨g • y, smul_mem_smul_set hyK, subset_tsupport c (left_ne_zero_of_mul hg)⟩
      ⟨g • y, right_ne_zero_of_mul hg, smul_mem_smul_set hyK⟩
  nonneg' i x := finsum_nonneg fun g ↦ mul_nonneg (hc.nonneg _) (f.nonneg i _)
  sum_eq_one' x hx := by
    simp [finsum_finsum_cutoff_mul hc, f.sum_eq_one (hs _ x hx), hc.finsum_smul_eq_one]
  sum_le_one' x := by
    simp only [ContMDiffMap.coeFn_mk, finsum_finsum_cutoff_mul hc]
    calc ∑ᶠ g : G, c (g • x) * ∑ᶠ i, f i (g • x)
        ≤ ∑ᶠ g : G, c (g • x) :=
          finsum_le_finsum ((hc.hasFiniteSupport x).subset fun _ hg ↦ left_ne_zero_of_mul hg)
            (hc.hasFiniteSupport x) fun g ↦ mul_le_of_le_one_right (hc.nonneg _) (f.sum_le_one _)
      _ = 1 := hc.finsum_smul_eq_one x

variable {hc hcs hs f}

/-- The `i`-th function of a cutoff average at `x` is the sum of `f i` over the translates
`g • x`, weighted by the cutoff function. -/
@[simp]
theorem cutoffAverage_apply (i : ι) (x : M) :
    f.cutoffAverage hc hcs hs i x = ∑ᶠ g : G, c (g • x) * f i (g • x) :=
  (rfl)

/-- A function of a cutoff average is supported on the translates of the locus where both the
cutoff function and the original function are nonzero. -/
theorem support_cutoffAverage_subset (i : ι) :
    support (f.cutoffAverage hc hcs hs i) ⊆ ⋃ g : G, (g • ·) ⁻¹' (support c ∩ support (f i)) :=
  fun x hx ↦ by
    obtain ⟨g, hg⟩ : ∃ g : G, c (g • x) * f i (g • x) ≠ 0 := by
      by_contra! H
      exact hx (by simp [H])
    exact mem_iUnion.2 ⟨g, left_ne_zero_of_mul hg, right_ne_zero_of_mul hg⟩

/-- A function of a cutoff average is topologically supported on the translates of the locus where
both the cutoff function and the original function are topologically supported. -/
theorem tsupport_cutoffAverage_subset (i : ι) :
    tsupport (f.cutoffAverage hc hcs hs i) ⊆
      ⋃ g : G, (g • ·) ⁻¹' (tsupport c ∩ tsupport (f i)) := by
  -- These preimages form a locally finite family of closed sets, so their union is closed.
  have hlf : LocallyFinite fun g : G ↦ (g • ·) ⁻¹' (tsupport c ∩ tsupport (f i)) :=
    (TauCeti.MulAction.locallyFinite_preimage_smul_tsupport hc.finite_smul_inter_tsupport).subset
      fun _ ↦ preimage_mono inter_subset_left
  refine closure_minimal ((support_cutoffAverage_subset i).trans <| iUnion_mono fun _ ↦
    preimage_mono <| inter_subset_inter (subset_tsupport c) (subset_tsupport _)) ?_
  exact hlf.isClosed_iUnion fun g ↦ ((isClosed_tsupport c).inter (isClosed_tsupport _)).preimage
    (contMDiff_const_smul (I := I) (n := ∞) g).continuous

/-- **Cutoff averaging fixes invariant partitions of unity.** If every function of `f` is invariant
under `G`, then its cutoff average is `f`. -/
theorem cutoffAverage_eq_self (hf : ∀ i (g : G) x, f i (g • x) = f i x) :
    f.cutoffAverage hc hcs hs = f :=
  DFunLike.ext _ _ fun i ↦ ContMDiffMap.ext fun x ↦ by
    simp [hf, ← finsum_mul, hc.finsum_smul_eq_one]

end Cutoff

section Group

variable {G : Type*} [Group G] [MulAction G M] [ContMDiffConstSMul I ∞ G M]
  [WeaklyLocallyCompactSpace M] {c : M → ℝ} {hc : TauCeti.MulAction.IsCutoff G c}
  {hcs : CMDiff ∞ c} {f : SmoothPartitionOfUnity ι I M s} {hs : ∀ g : G, ∀ x ∈ s, g • x ∈ s}

/-- **Cutoff averages are invariant.** For a group acting by smooth maps, every function of a
cutoff average of a partition of unity is `G`-invariant. -/
@[simp high]
theorem cutoffAverage_apply_smul (i : ι) (h : G) (x : M) :
    f.cutoffAverage hc hcs hs i (h • x) = f.cutoffAverage hc hcs hs i x := by
  simpa only [cutoffAverage_apply, Equiv.coe_mulRight, mul_smul] using
    finsum_comp_equiv (Equiv.mulRight h) (f := fun g ↦ c (g • x) * f i (g • x))

/-- **Cutoff averaging preserves subordination to an invariant cover.** If `f` is subordinate to a
cover `U` each of whose members is `G`-invariant, then so is its cutoff average. -/
theorem IsSubordinate.cutoffAverage {U : ι → Set M} (hf : f.IsSubordinate U)
    (hU : ∀ (g : G) i, ∀ x ∈ U i, g • x ∈ U i) :
    (f.cutoffAverage hc hcs hs).IsSubordinate U := fun i ↦
  (tsupport_cutoffAverage_subset i).trans <| iUnion_subset fun g x hx ↦ by
    simpa using hU g⁻¹ i _ (hf i hx.2)

end Group

/-- **Invariant smooth partitions of unity exist.** Let a group `G` act properly discontinuously by
smooth maps on a finite-dimensional σ-compact Hausdorff manifold `M`; for instance `G` may be
finite. If a closed `G`-stable set `s` is covered by open `G`-invariant sets `U i`, then there is a
smooth partition of unity of `s` subordinate to `U` whose functions are all `G`-invariant. -/
theorem exists_isSubordinate_smul_invariant [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] {G : Type*} [Group G] [MulAction G M]
    [ContMDiffConstSMul I ∞ G M] [ProperlyDiscontinuousSMul G M] (hs : IsClosed s)
    (hsG : ∀ g : G, ∀ x ∈ s, g • x ∈ s) (U : ι → Set M) (ho : ∀ i, IsOpen (U i))
    (hU : s ⊆ ⋃ i, U i) (hUG : ∀ (g : G) i, ∀ x ∈ U i, g • x ∈ U i) :
    ∃ f : SmoothPartitionOfUnity ι I M s,
      f.IsSubordinate U ∧ ∀ i (g : G) x, f i (g • x) = f i x := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨c, hc, hcs⟩ := TauCeti.MulAction.exists_isCutoff_contMDiff (I := I) (M := M) (n := ⊤) G
  obtain ⟨f, hf⟩ := exists_isSubordinate I hs U ho hU
  exact ⟨f.cutoffAverage hc hcs hsG, hf.cutoffAverage hUG, fun i g x ↦
    cutoffAverage_apply_smul i g x⟩

end SmoothPartitionOfUnity
