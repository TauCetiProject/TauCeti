/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.MeasureTheory.VectorMeasure.RiemannSums

/-!
# Tagged sums for the interval integral

Tagged sums of a continuous Banach-space-valued function converge to its interval integral
along arbitrary vanishing-mesh partitions. Repeated dates, empty partitions and either endpoint
as tag are allowed. This specializes
`MeasureTheory.VectorMeasure.tendsto_sum_tagged_Ioc` to the signed measure associated to
restricted Lebesgue measure. In stochastic change-of-variables arguments it identifies the ordinary
time term after centering the quadratic increments.
-/

public section

open MeasureTheory Set Filter
open scoped Topology NNReal

/-- Tagged Riemann sums for a continuous function converge to its interval integral.
Only the portion of each grid through its final endpoint needs to be ordered. -/
theorem ContinuousOn.tendsto_sum_tagged_sub_smul
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    {l : Filter ι} {n : ι → ℕ} {τ ξ : ι → ℕ → ℝ}
    (hτ : ∀ k, MonotoneOn (τ k) (Iic (n k)))
    (h₀ : ∀ k, τ k 0 = a) (hn : ∀ k, τ k (n k) = b)
    (hξ : ∀ k i, i < n k → ξ k i ∈ Icc (τ k i) (τ k (i + 1)))
    {δ : ι → ℝ} (hmesh : ∀ k i, i < n k → τ k (i + 1) - τ k i ≤ δ k)
    (hδ : Tendsto δ l (𝓝 0)) :
    Tendsto (fun k ↦ ∑ i ∈ Finset.range (n k),
      (τ k (i + 1) - τ k i) • f (ξ k i)) l (𝓝 (∫ x in a..b, f x)) := by
  by_cases hab : a ≤ b
  swap
  · have : IsEmpty ι := ⟨fun k ↦ hab (by
      simpa [h₀ k, hn k] using
        hτ k (mem_Iic.mpr (Nat.zero_le _)) self_mem_Iic (Nat.zero_le _))⟩
    have hl : l = ⊥ := Subsingleton.elim _ _
    simp [hl]
  -- Regard finite Lebesgue measure as a real vector measure, then identify its integral.
  let ν := volume.restrict (Ioc a b)
  let μ := ν.toSignedMeasure
  have : IsFiniteMeasure μ.variation := by
    rw [Measure.variation_toSignedMeasure]
    infer_instance
  let B : E →L[ℝ] ℝ →L[ℝ] E := (ContinuousLinearMap.lsmul ℝ ℝ).flip
  have hcap k : Monotone (fun i ↦ τ k (min i (n k))) := fun i j hij ↦
    hτ k (mem_Iic.mpr (min_le_right _ _)) (mem_Iic.mpr (min_le_right _ _))
      (min_le_min_right _ hij)
  have h := VectorMeasure.tendsto_sum_tagged_Ioc (μ := μ) (B := B)
    (n := n) (ξ := ξ) hf hcap (by simpa using h₀) (by simpa using hn)
    (fun k i hi ↦ by
      simpa [min_eq_left hi.le, min_eq_left (Nat.succ_le_of_lt hi)] using hξ k i hi)
    (fun k i hi ↦ by
      simpa [min_eq_left hi.le, min_eq_left (Nat.succ_le_of_lt hi)] using hmesh k i hi) hδ
  have hμ (k : ι) (i : ℕ) (hi : i < n k) :
      μ (Ioc (τ k i) (τ k (i + 1))) = τ k (i + 1) - τ k i := by
    have hleft : a ≤ τ k i := by
      simpa [h₀ k] using
        hτ k (mem_Iic.mpr (Nat.zero_le _)) (mem_Iic.mpr hi.le) (Nat.zero_le _)
    have hright : τ k (i + 1) ≤ b := by simpa [hn k] using hτ k (mem_Iic.mpr hi) self_mem_Iic hi
    have hstep := hτ k (mem_Iic.mpr hi.le) (mem_Iic.mpr hi) (Nat.le_succ i)
    simp only [μ, Measure.toSignedMeasure_apply_measurable measurableSet_Ioc, ν, Measure.real,
      Measure.restrict_apply measurableSet_Ioc]
    rw [inter_eq_left.mpr (Ioc_subset_Ioc hleft hright), Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hstep)]
  have heq : (∫ᵛ x in Ioc a b, f x ∂[B; μ]) = ∫ x in a..b, f x := by
    rw [VectorMeasure.setIntegral_toSignedMeasure measurableSet_Ioc]
    simp only [ν, Measure.restrict_restrict measurableSet_Ioc, inter_self,
      ← intervalIntegral.integral_of_le hab]
  rw [heq] at h
  refine h.congr fun k ↦ Finset.sum_congr rfl fun i hi ↦ ?_
  have hi := Finset.mem_range.mp hi
  simp [min_eq_left hi.le, min_eq_left (Nat.succ_le_of_lt hi), hμ k i hi, B]

/-- Tagged Riemann sums on nonnegative time converge to the real interval integral,
using `Real.toNNReal` to extend the integrand. Only values on the given interval are used. -/
theorem ContinuousOn.tendsto_sum_tagged_sub_smul_toNNReal
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ≥0 → E} {a b : ℝ≥0} (hf : ContinuousOn f (Icc a b))
    {l : Filter ι} {n : ι → ℕ} {τ ξ : ι → ℕ → ℝ≥0}
    (hτ : ∀ k, MonotoneOn (τ k) (Iic (n k)))
    (h₀ : ∀ k, τ k 0 = a) (hn : ∀ k, τ k (n k) = b)
    (hξ : ∀ k i, i < n k → ξ k i ∈ Icc (τ k i) (τ k (i + 1)))
    {δ : ι → ℝ} (hmesh : ∀ k i, i < n k → (τ k (i + 1) : ℝ) - τ k i ≤ δ k)
    (hδ : Tendsto δ l (𝓝 0)) :
    Tendsto (fun k ↦ ∑ i ∈ Finset.range (n k),
      ((τ k (i + 1) : ℝ) - τ k i) • f (ξ k i)) l
      (𝓝 (∫ x in (a : ℝ)..b, f x.toNNReal)) := by
  have hreal : ContinuousOn (fun x : ℝ ↦ f x.toNNReal) (Icc (a : ℝ) b) :=
    hf.comp continuous_real_toNNReal.continuousOn
      (by simpa using Real.toNNReal_monotone.mapsTo_Icc (a := (a : ℝ)) (b := (b : ℝ)))
  simpa only [Real.toNNReal_coe] using hreal.tendsto_sum_tagged_sub_smul
    (τ := fun k i ↦ (τ k i : ℝ)) (ξ := fun k i ↦ (ξ k i : ℝ))
    (fun k i hi j hj hij ↦ NNReal.coe_le_coe.mpr (hτ k hi hj hij))
    (fun k ↦ congrArg NNReal.toReal (h₀ k)) (fun k ↦ congrArg NNReal.toReal (hn k))
    (fun k i hi ↦ ⟨NNReal.coe_le_coe.mpr (hξ k i hi).1,
      NNReal.coe_le_coe.mpr (hξ k i hi).2⟩) hmesh hδ
