/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Countable
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Basic
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Locally finite weighted orthonormal coordinates

A partition of unity and local orthonormal frames give a fibrewise linear injection into
finitely supported coordinate blocks. The block of colour `i` is the inverse frame multiplied
by the square root of the weight. Its squared norm is the weight times the squared fibre norm,
so the sum of squared block norms is exactly the squared fibre norm.

Only the positive set of a weight needs to lie in its chart domain. Continuity across the
zero-weight boundary follows from the norm identity, even when the chart has no continuous
extension there. Locally all blocks lie in a fixed finite set, uniformly over the whole fibre.
For countably many colours this gives a local bound by an initial coordinate segment, which
is the finite-stage control needed for maps to the infinite Grassmannian with its final topology.

The gap partition and glued gap charts supply these coordinates from an arbitrarily indexed
subordinate partition of unity. No countability assumption on the original chart family is used.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, §5, in particular Lemma 5.9.
-/

public noncomputable section

open Bundle Set Function Filter
open scoped Topology

namespace PartitionOfUnity

variable {𝕜 B F V ι : Type*} [RCLike 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace 𝕜 (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  {r : ℕ} {s : Set B} (ρ : PartitionOfUnity ι B s)
  (e : ι → Trivialization F (π F E)) [∀ i, (e i).IsLinear 𝕜]
  (c : Module.Basis (Fin r) 𝕜 F) (b : OrthonormalBasis (Fin r) 𝕜 V)

/-- Square-root-weighted orthonormal coordinates, with finite support in the chart indices.
The frames are the Gram–Schmidt frames of `e`, using the preferred bundle chart outside its
domain; a zero weight makes that extension immaterial. -/
def weightedFrameCoordinates (x : B) : E x →ₗ[𝕜] (ι →₀ V) where
  toFun v := Finsupp.ofSupportFinite
    (fun i ↦ (Real.sqrt (ρ i x) : 𝕜) • ((e i).orthonormalFrameAt c b x).symm v)
    ((ρ.locallyFinite.point_finite x).subset fun i hi ↦ by
      contrapose hi
      have hz : ρ i x = 0 := by simpa only [mem_ofPred_eq, mem_support, not_not] using hi
      simp [hz])
  map_add' v w := by ext i; simp [map_add, smul_add]
  map_smul' a v := by ext i; simp [smul_smul, mul_comm]

/-- The block indexed by `i` is the inverse orthonormal frame scaled by `sqrt (ρ i x)`. -/
@[simp]
theorem weightedFrameCoordinates_apply (x : B) (v : E x) (i : ι) :
    ρ.weightedFrameCoordinates e c b x v i =
      (Real.sqrt (ρ i x) : 𝕜) • ((e i).orthonormalFrameAt c b x).symm v := (rfl)

/-- Every coordinate block has norm `sqrt (ρ i x) * ‖v‖`, including at zero weights. -/
theorem norm_weightedFrameCoordinates_apply (x : B) (v : E x) (i : ι) :
    ‖ρ.weightedFrameCoordinates e c b x v i‖ = Real.sqrt (ρ i x) * ‖v‖ := by
  simp [norm_smul, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- The squared norm of a coordinate block is its partition weight times `‖v‖²`. -/
theorem norm_weightedFrameCoordinates_apply_sq (x : B) (v : E x) (i : ι) :
    ‖ρ.weightedFrameCoordinates e c b x v i‖ ^ 2 = ρ i x * ‖v‖ ^ 2 := by
  rw [norm_weightedFrameCoordinates_apply, mul_pow, Real.sq_sqrt (ρ.nonneg i x)]

/-- Weighted coordinates vanish outside the finite support of the partition at the base point. -/
theorem support_weightedFrameCoordinates_subset (x : B) (v : E x) :
    (ρ.weightedFrameCoordinates e c b x v).support ⊆ ρ.finsupport x := by
  intro i hi
  by_contra h
  have hzero : ρ i x = 0 := by simpa using h
  simpa [hzero] using (Finsupp.mem_support_iff.1 hi)

/-- The sum of the squared block norms recovers the squared fibre norm on the partition's set. -/
theorem finsum_norm_weightedFrameCoordinates_sq {x : B} (hx : x ∈ s) (v : E x) :
    ∑ᶠ i, ‖ρ.weightedFrameCoordinates e c b x v i‖ ^ 2 = ‖v‖ ^ 2 := by
  simp_rw [norm_weightedFrameCoordinates_apply_sq]
  rw [← finsum_mul, ρ.sum_eq_one hx, one_mul]

/-- On the partition's set the weighted coordinates are injective on every fibre. -/
theorem weightedFrameCoordinates_injective {x : B} (hx : x ∈ s) :
    Injective (ρ.weightedFrameCoordinates e c b x) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have h := ρ.finsum_norm_weightedFrameCoordinates_sq e c b hx v
  rw [hv] at h
  simpa using h.symm

/-- Each weighted coordinate is continuous on the whole total space. The positive set of its
weight suffices as a chart domain; the topological support need not lie in that domain. -/
theorem continuous_weightedFrameCoordinates_apply [TauCeti.ContinuousFiberNorm F E]
    (he : ∀ i, {x | 0 < ρ i x} ⊆ (e i).baseSet) (i : ι) :
    Continuous fun p : TotalSpace F E ↦ ρ.weightedFrameCoordinates e c b p.proj p.2 i := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  have hw : Continuous (fun q : TotalSpace F E ↦ Real.sqrt (ρ i q.proj)) :=
    ((ρ i).continuous.comp (FiberBundle.continuous_proj F E)).sqrt
  by_cases hpos : 0 < ρ i p.proj
  · have hmem : TotalSpace.proj ⁻¹' (e i).baseSet ∈ 𝓝 p :=
      ((e i).open_baseSet.preimage (FiberBundle.continuous_proj F E)).mem_nhds (he i hpos)
    exact (RCLike.continuous_ofReal.comp hw).continuousAt.smul
      (((e i).continuousOn_orthonormalFrameAt_symm c b).continuousAt hmem)
  · have hz : ρ i p.proj = 0 := le_antisymm (not_lt.1 hpos) (ρ.nonneg i p.proj)
    have hzero : ρ.weightedFrameCoordinates e c b p.proj p.2 i = 0 := by simp [hz]
    rw [ContinuousAt, hzero]
    apply squeeze_zero_norm (a := fun q : TotalSpace F E ↦
      Real.sqrt (ρ i q.proj) * ‖q.2‖)
      (fun q ↦ (ρ.norm_weightedFrameCoordinates_apply e c b q.proj q.2 i).le)
    simpa only [hz, Real.sqrt_zero, zero_mul] using
      (hw.tendsto p).mul ((TauCeti.ContinuousFiberNorm.continuous_norm
        (F := F) (E := E)).tendsto p)

/-- For countably many blocks, near each base point the coordinates of every fibre lie in one
initial finite segment. This bound is uniform in the fibre vector. -/
theorem locally_support_weightedFrameCoordinates_range
    (ρ : PartitionOfUnity ℕ B s) (e : ℕ → Trivialization F (π F E))
    [∀ n, (e n).IsLinear 𝕜] (x : B) :
    ∃ N : ℕ, ∀ᶠ y in 𝓝 x, ∀ v : E y,
      (ρ.weightedFrameCoordinates e c b y v).support ⊆ Finset.range N := by
  classical
  refine ⟨(ρ.fintsupport x).sup id + 1,
    (ρ.eventually_finsupport_subset x).mono fun y hy v n hn ↦ Finset.mem_range.2 ?_⟩
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id)
    (hy (ρ.support_weightedFrameCoordinates_subset e c b y v hn)))

include c b in
/-- An arbitrarily indexed subordinate partition supplies countably many weighted orthonormal
coordinate blocks. Their weights are exactly the gap-colour weights; the coordinates are
continuous even at their zero-weight boundaries and locally use one fixed finite initial segment.
The squared block norms sum to the squared fibre norm. -/
theorem exists_gap_weightedFrameCoordinates [TauCeti.ContinuousFiberNorm F E]
    (ρ : PartitionOfUnity ι B univ)
    (he : ρ.IsSubordinate fun i ↦ (e i).baseSet) :
    ∃ j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ V),
      (∀ (x : B) (v : E x) (n : ℕ),
        ‖j x v n‖ ^ 2 =
          (n : ℝ) * (∑ᶠ (S : Finset ι) (_ : S.card = n), ρ.gap S x) * ‖v‖ ^ 2) ∧
      (∀ n, Continuous fun p : TotalSpace F E ↦ j p.proj p.2 n) ∧
      (∀ x, ∃ N : ℕ, ∀ᶠ y in 𝓝 x, ∀ v : E y, (j y v).support ⊆ Finset.range N) ∧
      (∀ (x : B) (v : E x), ∑ᶠ n, ‖j x v n‖ ^ 2 = ‖v‖ ^ 2) ∧
      ∀ x, Injective (j x) := by
  let g := ρ.gapTrivialization e he
  have hg : ∀ n, {x | 0 < ρ.gapPartition n x} ⊆ (g n).baseSet := by
    intro n
    rw [gapTrivialization_baseSet]
  refine ⟨ρ.gapPartition.weightedFrameCoordinates g c b, ?_, ?_, ?_, ?_, ?_⟩
  · intro x v n
    rw [norm_weightedFrameCoordinates_apply_sq, gapPartition_apply]
  · exact fun n ↦ ρ.gapPartition.continuous_weightedFrameCoordinates_apply g c b hg n
  · exact fun x ↦ ρ.gapPartition.locally_support_weightedFrameCoordinates_range c b g x
  · exact fun x v ↦ ρ.gapPartition.finsum_norm_weightedFrameCoordinates_sq g c b (mem_univ x) v
  · exact fun x ↦ ρ.gapPartition.weightedFrameCoordinates_injective g c b (mem_univ x)

include c b in
/-- A finite-rank Riemannian or Hermitian bundle over a paracompact normal base admits
continuous, fibrewise injective, square-norm-preserving countable block coordinates which
locally lie in a finite initial coordinate stage. The original bundle cover may be uncountable. -/
theorem _root_.TauCeti.exists_countable_weightedFrameCoordinates [TauCeti.ContinuousFiberNorm F E]
    [ParacompactSpace B] [NormalSpace B] :
    ∃ j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ V),
      (∀ n, Continuous fun p : TotalSpace F E ↦ j p.proj p.2 n) ∧
      (∀ x, ∃ N : ℕ, ∀ᶠ y in 𝓝 x, ∀ v : E y, (j y v).support ⊆ Finset.range N) ∧
      (∀ (x : B) (v : E x), ∑ᶠ n, ‖j x v n‖ ^ 2 = ‖v‖ ^ 2) ∧
      ∀ x, Injective (j x) := by
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun x ↦ (trivializationAt F E x).baseSet)
    (fun x ↦ (trivializationAt F E x).open_baseSet)
    (fun x _ ↦ mem_iUnion.2 ⟨x, mem_baseSet_trivializationAt F E x⟩)
  obtain ⟨j, _, hj⟩ := ρ.exists_gap_weightedFrameCoordinates (trivializationAt F E) c b hρ
  exact ⟨j, hj⟩

end PartitionOfUnity
