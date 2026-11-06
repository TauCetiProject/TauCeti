/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.PartitionOfUnity

/-!
# Finite-rank approximation of compactly supported functions

A compactly supported continuous function with values in a real normed space can be
approximated in integral norm by finite sums of real compactly supported scalar functions
times vectors from any prescribed dense subset. Only finiteness of the measure on compact
sets is needed. In particular, no global finiteness or countability assumption is imposed.

This is the partition-of-unity approximation used to lift convolution coefficients through
dense coefficient maps. We use Mathlib's compactly supported partitions of unity.
-/

public section

open MeasureTheory Set Metric
open scoped CompactlySupported

namespace CompactlySupportedContinuousMap

variable {X E : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [LocallyCompactSpace X] [T2Space X] [MeasurableSpace X] in
/-- A partition of unity over the support of `f`, all of whose members are supported where `f`
is within `δ` of the corresponding vector, gives a sum of scalar multiples of those vectors
within `δ` of `f` everywhere. -/
theorem _root_.PartitionOfUnity.norm_sub_sum_smul_le {ι : Type*} [Fintype ι] (f : X → E)
    (ρ : PartitionOfUnity ι X (tsupport f)) (c : ι → E) {δ : ℝ} (hδ : 0 ≤ δ)
    (hρ : ∀ i x, ρ i x ≠ 0 → ‖f x - c i‖ < δ) (x : X) :
    ‖f x - ∑ i, ρ i x • c i‖ ≤ δ := by
  have hsum : ∑ i, ρ i x • f x = f x := by
    rw [← Finset.sum_smul]
    by_cases hx : x ∈ tsupport f
    · simpa only [finsum_eq_sum_of_fintype, one_smul] using
        congrArg (fun r : ℝ => r • f x) (ρ.sum_eq_one hx)
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have heq : f x - ∑ i, ρ i x • c i = ∑ i, ρ i x • (f x - c i) := by
    simp only [smul_sub, Finset.sum_sub_distrib, hsum]
  rw [heq]
  calc
    ‖∑ i, ρ i x • (f x - c i)‖ ≤ ∑ i, ‖ρ i x • (f x - c i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ρ i x * δ := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : ρ i x = 0
      · simp [hi]
      · rw [norm_smul, Real.norm_of_nonneg (ρ.nonneg i x)]
        exact mul_le_mul_of_nonneg_left (hρ i x hi).le (ρ.nonneg i x)
    _ ≤ δ := by
      rw [← Finset.sum_mul]
      exact mul_le_of_le_one_left hδ (by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_le_one x)

omit [MeasurableSpace X] [NormedSpace ℝ E] in
/-- A compactly supported continuous function admits a partition of unity over its support,
finitely indexed by a subset of a dense set, whose members have compact support inside a given
neighbourhood of the support and are supported where `f` is `δ`-close to the index. -/
private theorem exists_partitionOfUnity_norm_sub_lt (f : C_c(X, E)) {S : Set E} (hS : Dense S)
    {K : Set X} (hfK : tsupport f ⊆ interior K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (s : Finset S) (ρ : PartitionOfUnity s X (tsupport f)),
      (∀ i, HasCompactSupport (ρ i)) ∧
        ∀ i x, ρ i x ≠ 0 → x ∈ interior K ∧ ‖f x - (i.val.val : E)‖ < δ := by
  let U (a : S) := interior K ∩ f ⁻¹' ball (a : E) δ
  have hU (a : S) : IsOpen (U a) :=
    isOpen_interior.inter (isOpen_ball.preimage f.continuous)
  have hcover : tsupport f ⊆ ⋃ a : S, U a := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := hS.exists_dist_lt (f x) hδ
    exact mem_iUnion.2 ⟨⟨a, ha⟩, hfK hx, hax⟩
  obtain ⟨s, hs⟩ := f.hasCompactSupport.elim_finite_subcover U hU hcover
  obtain ⟨ρ, hρ, hρc⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space
    f.hasCompactSupport (fun a : s => U a) (fun a => hU a)
    (locallyFinite_of_finite _) (fun x hx => by
      obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hs hx)
      exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩)
  refine ⟨s, ρ, hρc, fun i x hx => ?_⟩
  have hxU := (hρ i (subset_closure hx))
  exact ⟨hxU.1, by simpa only [mem_preimage, mem_ball, dist_eq_norm] using hxU.2⟩

/-- Finite sums of scalar compactly supported functions times vectors from a dense set
approximate every compactly supported continuous function in integral norm. -/
theorem exists_integral_norm_sub_sum_smul_lt (f : C_c(X, E)) (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] {S : Set E} (hS : Dense S) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset S) (φ : s → C_c(X, ℝ)),
      (∫ x, ‖f x - ∑ i : s, φ i x • (i.val.val : E)‖ ∂μ) < ε := by
  classical
  -- A fixed compact neighbourhood bounds the measures of all the approximation supports.
  obtain ⟨K, hK, hfK⟩ := exists_compact_superset f.hasCompactSupport
  let δ := ε / (μ.real K + 1)
  have hδ : 0 < δ := by positivity
  obtain ⟨s, ρ, hρc, hρ⟩ := exists_partitionOfUnity_norm_sub_lt f hS hfK hδ
  let φ (i : s) : C_c(X, ℝ) := ⟨ρ i, hρc i⟩
  refine ⟨s, φ, ?_⟩
  have hbound (x : X) : ‖f x - ∑ i : s, φ i x • (i.val.val : E)‖ ≤ δ :=
    ρ.norm_sub_sum_smul_le f (fun i => (i.val.val : E)) hδ.le (fun i x hx => (hρ i x hx).2) x
  have hout (x : X) (hx : x ∉ K) : f x - ∑ i : s, φ i x • (i.val.val : E) = 0 := by
    have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport fun h =>
      hx (interior_subset (hfK h))
    have hφ (i : s) : φ i x = 0 := by
      by_contra hi
      exact hx (interior_subset (hρ i x hi).1)
    simp [hfx, hφ]
  -- Integrate the uniform error only on that fixed compact neighbourhood.
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
    (fun x hx => by rw [hout x hx, norm_zero])]
  calc
    (∫ x in K, ‖f x - ∑ i : s, φ i x • (i.val.val : E)‖ ∂μ)
        ≤ δ * μ.real K := by
      exact (le_abs_self _).trans (by
        simpa only [Real.norm_eq_abs, abs_norm] using
          norm_setIntegral_le_of_norm_le_const (μ := μ)
            (f := fun x => ‖f x - ∑ i : s, φ i x • (i.val.val : E)‖)
            hK.measure_lt_top (fun x _ => by simpa only [norm_norm] using hbound x))
    _ < ε := by
      dsimp [δ]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [measureReal_nonneg (μ := μ) (s := K)]

end CompactlySupportedContinuousMap
