/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Algebra.Structures
import TauCeti.Topology.LocallyFinite

/-!
# Invariant smooth partitions of unity for finite group actions

Let a finite group `G` act on a manifold `M` by smooth maps (`ContMDiffConstSMul I ∞ G M`). Any
smooth partition of unity `f` of a `G`-stable set `s` can be averaged over the action:
`(f.average G hs) i x = |G|⁻¹ * ∑ g, f i (g • x)`. The result is again a smooth partition of
unity of `s`, every function of which is `G`-invariant, and it is subordinate to every
`G`-invariant cover to which `f` is subordinate. Combined with Mathlib's existence theorem
`SmoothPartitionOfUnity.exists_isSubordinate`, this gives `G`-invariant smooth partitions of unity
subordinate to any `G`-invariant open cover of a closed `G`-stable set.

Such partitions glue `G`-invariant local data (sections, connections, metrics) on a manifold with a
finite group action, without leaving the invariant world. This is the basic averaging device for
finite quotient charts `U/G`, where the action may be ineffective: the full group is averaged
over, including elements that act trivially on `M`.

## Main definitions and results

* `SmoothPartitionOfUnity.average`: the average of a smooth partition of unity of `s` over a finite
  group (or any finite nonempty type) acting by smooth maps that preserve `s`.
* `SmoothPartitionOfUnity.average_apply_smul`: for a group action, the averaged functions are
  invariant.
* `SmoothPartitionOfUnity.average_eq_self`: averaging does not change a partition of unity whose
  functions are already invariant.
* `SmoothPartitionOfUnity.IsSubordinate.average`: averaging preserves subordination to a
  `G`-invariant cover.
* `SmoothPartitionOfUnity.exists_isSubordinate_smul_invariant`: a closed `G`-stable set covered by
  `G`-invariant open sets has a `G`-invariant smooth partition of unity subordinate to the cover.

## References

* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Cambridge University Press,
  2007, Chapter 1.
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

/-- **Invariant smooth partitions of unity exist.** Let a finite group `G` act by smooth maps on a
finite-dimensional σ-compact Hausdorff manifold `M`. If a closed `G`-stable set `s` is covered by
open `G`-invariant sets `U i`, then there is a smooth partition of unity of `s` subordinate to `U`
whose functions are all `G`-invariant. -/
theorem exists_isSubordinate_smul_invariant [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] {G : Type*} [Group G] [Finite G] [MulAction G M]
    [ContMDiffConstSMul I ∞ G M] (hs : IsClosed s) (hsG : ∀ g : G, ∀ x ∈ s, g • x ∈ s)
    (U : ι → Set M) (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃ i, U i)
    (hUG : ∀ (g : G) i, ∀ x ∈ U i, g • x ∈ U i) :
    ∃ f : SmoothPartitionOfUnity ι I M s,
      f.IsSubordinate U ∧ ∀ i (g : G) x, f i (g • x) = f i x := by
  let _ := Fintype.ofFinite G
  obtain ⟨f, hf⟩ := exists_isSubordinate I hs U ho hU
  exact ⟨f.average G hsG, hf.average hUG, fun i g x ↦ average_apply_smul i g x⟩

end SmoothPartitionOfUnity
