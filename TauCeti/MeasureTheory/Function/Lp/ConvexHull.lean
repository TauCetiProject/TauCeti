/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space

import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Analysis.InnerProductSpace.Projection.Minimal
import TauCeti.Analysis.Normed.Lp.ProdLp
import TauCeti.MeasureTheory.Function.Lp.Basic

/-!
# Forward convex combinations in `L²` converging in norm and almost everywhere

Every norm-bounded sequence in a Hilbert space admits finite tail convex combinations converging in
norm (`TauCeti.exists_tendsto_sum_smul_of_isBounded_range`). Applying this to `L²(μ)` (or to the
`ℓ²` product `L²(μ) × L²(ν)` of two `L²` spaces) and passing to an almost everywhere convergent
subsequence via convergence in measure produces finite tail convex combinations with common weights
that converge both in `L²` norm and almost everywhere. This is the Hilbert-space (`p = 2`) form of
Komlós-type forward-convex-combination compactness, used to pass to pointwise limits while
preserving convex constraints such as upper-envelope inequalities and integral bounds.

## Main results

* `TauCeti.exists_tendsto_sum_smul_toLp_and_ae_prod_of_isBounded_range`: given norm-bounded
  sequences `u : ℕ → α → E` in `L²(μ)` and `v : ℕ → β → F` in `L²(ν)` taking values in complete real
  inner product spaces, there exist common finite tail convex combinations converging simultaneously
  in `L²(μ)`, in `L²(ν)`, `μ`-almost everywhere, and `ν`-almost everywhere.
* `TauCeti.exists_tendsto_sum_smul_toLp_and_ae_of_isBounded_range`: single-space specialization for
  a norm-bounded sequence `u : ℕ → α → E` in `L²(μ)`.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace TauCeti

variable {α β E F : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **Joint `L²` and almost-everywhere forward convex combinations.** Given sequences
`u : ℕ → α → E` in `L²(μ)` and `v : ℕ → β → F` in `L²(ν)` with bounded `L²` norms (for complete real
inner product spaces `E` and `F`), there exist limits `p₁ : Lp E 2 μ` and `p₂ : Lp F 2 ν`, finite
index sets `s : ℕ → Finset ℕ`, and weights `w : ℕ → ℕ → ℝ` with `∀ i ∈ s n, 0 ≤ w n i` and
`∑ i ∈ s n, w n i = 1` such that the common tail convex combinations converge simultaneously in
`L²(μ)`, in `L²(ν)`, `μ`-almost everywhere, and `ν`-almost everywhere. -/
theorem exists_tendsto_sum_smul_toLp_and_ae_prod_of_isBounded_range
    {u : ℕ → α → E} {v : ℕ → β → F}
    (hu : ∀ n, MemLp (u n) 2 μ) (hv : ∀ n, MemLp (v n) 2 ν)
    (hu_bdd : Bornology.IsBounded (range fun n ↦ (hu n).toLp (u n)))
    (hv_bdd : Bornology.IsBounded (range fun n ↦ (hv n).toLp (v n))) :
    ∃ (p₁ : Lp E 2 μ) (p₂ : Lp F 2 ν) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ),
      (∀ n i, i ∈ s n → 0 ≤ w n i) ∧ (∀ n, ∑ i ∈ s n, w n i = 1) ∧
      Tendsto (fun n ↦ ∑ i ∈ s n, w n i • (hu (n + i)).toLp (u (n + i))) atTop (𝓝 p₁) ∧
      Tendsto (fun n ↦ ∑ i ∈ s n, w n i • (hv (n + i)).toLp (v (n + i))) atTop (𝓝 p₂) ∧
      (∀ᵐ x ∂μ, Tendsto (fun n ↦ ∑ i ∈ s n, w n i • u (n + i) x) atTop (𝓝 (p₁ x))) ∧
      (∀ᵐ y ∂ν, Tendsto (fun n ↦ ∑ i ∈ s n, w n i • v (n + i) y) atTop (𝓝 (p₂ y))) := by
  -- Step 1: obtain norm-convergent tail convex combinations in `WithLp 2 (L²(μ) × L²(ν))`.
  obtain ⟨p_lim, s₀, w₀, hw₀_nn, hw₀_sum, hP_tendsto⟩ :=
    exists_tendsto_sum_smul_of_isBounded_range ((isBounded_range_toLp (p := 2)).2 ⟨hu_bdd, hv_bdd⟩)
  let π₁ := WithLp.fstL 2 ℝ (Lp E 2 μ) (Lp F 2 ν)
  let π₂ := WithLp.sndL 2 ℝ (Lp E 2 μ) (Lp F 2 ν)
  have ht₁ : Tendsto (fun m ↦ ∑ i ∈ s₀ m, w₀ m i • (hu (m + i)).toLp (u (m + i)))
      atTop (𝓝 (π₁ p_lim)) :=
    ((π₁.continuous.tendsto p_lim).comp hP_tendsto).congr fun m ↦ by
      simp only [Function.comp_apply, map_sum, map_smul, WithLp.fstL_apply, WithLp.toLp_fst, π₁]
  have ht₂ : Tendsto (fun m ↦ ∑ i ∈ s₀ m, w₀ m i • (hv (m + i)).toLp (v (m + i)))
      atTop (𝓝 (π₂ p_lim)) :=
    ((π₂.continuous.tendsto p_lim).comp hP_tendsto).congr fun m ↦ by
      simp only [Function.comp_apply, map_sum, map_smul, WithLp.sndL_apply, WithLp.toLp_snd, π₂]
  -- Step 2: extract a common subsequence converging both `μ`-a.e. and `ν`-a.e.
  let u₀ : ℕ → α → E := fun m x ↦ ∑ i ∈ s₀ m, w₀ m i • u (m + i) x
  let v₀ : ℕ → β → F := fun m y ↦ ∑ i ∈ s₀ m, w₀ m i • v (m + i) y
  have hu₀_ae (m : ℕ) : ⇑(∑ i ∈ s₀ m, w₀ m i • (hu (m + i)).toLp (u (m + i))) =ᵐ[μ] u₀ m :=
    (((memLp_finsetSum (s₀ m) fun i _ ↦ (hu (m + i)).const_smul (w₀ m i)).toLp_finsetSum
      fun i ↦ (hu (m + i)).const_smul (w₀ m i)).trans
      (Finset.sum_congr rfl fun i _ ↦ MemLp.toLp_const_smul (w₀ m i) (hu (m + i)))) ▸
      MemLp.coeFn_toLp _
  have hv₀_ae (m : ℕ) : ⇑(∑ i ∈ s₀ m, w₀ m i • (hv (m + i)).toLp (v (m + i))) =ᵐ[ν] v₀ m :=
    (((memLp_finsetSum (s₀ m) fun i _ ↦ (hv (m + i)).const_smul (w₀ m i)).toLp_finsetSum
      fun i ↦ (hv (m + i)).const_smul (w₀ m i)).trans
      (Finset.sum_congr rfl fun i _ ↦ MemLp.toLp_const_smul (w₀ m i) (hv (m + i)))) ▸
      MemLp.coeFn_toLp _
  obtain ⟨φ₁, hφ₁, hae₁⟩ :=
    ((tendstoInMeasure_of_tendsto_Lp ht₁).congr_left hu₀_ae).exists_seq_tendsto_ae
  obtain ⟨φ₂, hφ₂, hae₂⟩ :=
    ((tendstoInMeasure_of_tendsto_Lp (ht₂.comp hφ₁.tendsto_atTop)).congr_left
      fun j ↦ hv₀_ae (φ₁ j)).exists_seq_tendsto_ae
  -- Step 3: re-index the subsequence `ψ = φ₁ ∘ φ₂` as tail convex combinations starting at `n`.
  let ψ : ℕ → ℕ := φ₁ ∘ φ₂
  have hψ : StrictMono ψ := hφ₁.comp hφ₂
  let d : ℕ → ℕ := fun n ↦ ψ n - n
  let s : ℕ → Finset ℕ := fun n ↦ (s₀ (ψ n)).map (addLeftEmbedding (d n))
  let w : ℕ → ℕ → ℝ := fun n k ↦ w₀ (ψ n) (k - d n)
  have hn (n i : ℕ) : n + (d n + i) = ψ n + i := by
    rw [← Nat.add_assoc, Nat.add_sub_of_le hψ.le_apply]
  refine ⟨π₁ p_lim, π₂ p_lim, s, w,
    fun n k hk ↦ ?_, fun n ↦ ?_,
    (ht₁.comp hψ.tendsto_atTop).congr fun n ↦ ?_,
    (ht₂.comp hψ.tendsto_atTop).congr fun n ↦ ?_,
    hae₁.mono fun x hx ↦ (hx.comp hφ₂.tendsto_atTop).congr fun n ↦ ?_,
    hae₂.mono fun y hy ↦ hy.congr fun n ↦ ?_⟩
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hk
    simpa only [w, addLeftEmbedding_apply, Nat.add_sub_cancel_left] using hw₀_nn (ψ n) i hi
  · rw [Finset.sum_map]
    simpa only [w, addLeftEmbedding_apply, Nat.add_sub_cancel_left] using hw₀_sum (ψ n)
  · rw [Function.comp_apply, Finset.sum_map]
    simp only [w, addLeftEmbedding_apply, Nat.add_sub_cancel_left, hn]
  · rw [Function.comp_apply, Finset.sum_map]
    simp only [w, addLeftEmbedding_apply, Nat.add_sub_cancel_left, hn]
  · rw [Function.comp_apply, Finset.sum_map]
    simp only [u₀, ψ, Function.comp_apply, w, addLeftEmbedding_apply, Nat.add_sub_cancel_left, hn]
  · rw [Finset.sum_map]
    simp only [v₀, ψ, Function.comp_apply, w, addLeftEmbedding_apply, Nat.add_sub_cancel_left, hn]

/-- **Forward convex combinations converging in `L²` and almost everywhere.** Every sequence
`u : ℕ → α → E` in `L²(μ)` with bounded `L²` norms (where `E` is a complete real inner product
space) admits a limit `p : Lp E 2 μ`, finite index sets `s : ℕ → Finset ℕ`, and weights
`w : ℕ → ℕ → ℝ` with `∀ i ∈ s n, 0 ≤ w n i` and `∑ i ∈ s n, w n i = 1` such that the tail convex
combinations converge to `p` both in `L²(μ)` and `μ`-almost everywhere. -/
theorem exists_tendsto_sum_smul_toLp_and_ae_of_isBounded_range
    {u : ℕ → α → E} (hu : ∀ n, MemLp (u n) 2 μ)
    (hu_bdd : Bornology.IsBounded (range fun n ↦ (hu n).toLp (u n))) :
    ∃ (p : Lp E 2 μ) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ),
      (∀ n i, i ∈ s n → 0 ≤ w n i) ∧ (∀ n, ∑ i ∈ s n, w n i = 1) ∧
      Tendsto (fun n ↦ ∑ i ∈ s n, w n i • (hu (n + i)).toLp (u (n + i))) atTop (𝓝 p) ∧
      (∀ᵐ x ∂μ, Tendsto (fun n ↦ ∑ i ∈ s n, w n i • u (n + i) x) atTop (𝓝 (p x))) := by
  obtain ⟨p, -, s, w, hw0, hw1, ht, -, hae, -⟩ :=
    exists_tendsto_sum_smul_toLp_and_ae_prod_of_isBounded_range hu hu hu_bdd hu_bdd
  exact ⟨p, s, w, hw0, hw1, ht, hae⟩

end TauCeti
