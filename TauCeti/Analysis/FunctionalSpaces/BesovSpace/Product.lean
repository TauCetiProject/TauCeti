/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Paraproduct
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Products of Besov distributions of opposite regularity

Let `u ∈ B^α_{p₁,q₁}` be scalar and `v ∈ B^β_{p₂,q₂}`, and let `1/r = 1/p₁ + 1/p₂`. When one of
the two regularities is negative, the product `u v` is not defined pointwise, but it is defined as
a tempered distribution as soon as `α + β > 0`: the products `S_M u · S_M v` of the low-frequency
cut-offs `S_M = ∑_{k < M} Δₖ` converge in `𝓢'(E, F)`, and the limit lies in the Besov space of the
rougher factor. This is the product map `𝒞^α × 𝒞^β → 𝒞^α` for `α < 0 < β` with `α + β > 0` on the
Hölder–Zygmund scale, a consequence of the paraproduct and resonant estimates of
Bahouri–Chemin–Danchin (Theorems 2.82 and 2.85), here for all integrability exponents:

`‖u v‖_{B^α_{r,q₁}} ≤ C ‖u‖_{B^α_{p₁,q₁}} ‖v‖_{B^β_{p₂,q₂}}` when `α < 0 < α + β`, and
`‖u v‖_{B^β_{r,q₂}} ≤ C ‖u‖_{B^α_{p₁,q₁}} ‖v‖_{B^β_{p₂,q₂}}` when `β < 0 < α + β`,

with `C` depending only on the bump function and the regularities. The product is characterised
as the limit of the truncated products, so it involves no choice beyond the bump function `φ` that
defines the Besov spaces; in particular it does not depend on the gap used in the proof.

The proof goes through Bony's decomposition `u v = T_u v + T_v u + R(u, v)`
(`TauCeti.BesovSpace.lowPass_smul_lowPass`), with a gap `N` large enough for the paraproduct terms
to be spectrally localized in dyadic annuli. The factor of positive regularity is an `Lᵖ` function
(`TauCeti.BesovSpace.exists_toDistr_eq_and_norm_le_of_pos`), so the paraproduct in which it is the
low-frequency factor lies in the Besov space of the rough factor; the other paraproduct and the
resonant part gain the full regularity `α + β`, which exceeds that of the rough factor. The
truncation `S_M u · S_M v` sums the resonant terms only over block indices below `M`; the missing
terms lie within `N` of `M`, and since `α + β > 0` their `Lʳ` norms are `O(2^{-(α+β) M})`.

## Main declarations

* `TauCeti.BesovSpace.exists_tendsto_lowPass_smul_lowPass_and_norm_le_of_neg_left`: the product of
  `u ∈ B^α_{p₁,q₁}`, `α < 0`, and `v ∈ B^β_{p₂,q₂}`, `α + β > 0`, lies in `B^α_{r,q₁}`.
* `TauCeti.BesovSpace.exists_tendsto_lowPass_smul_lowPass_and_norm_le_of_neg_right`: the product of
  `u ∈ B^α_{p₁,q₁}` and `v ∈ B^β_{p₂,q₂}`, `β < 0`, `α + β > 0`, lies in `B^β_{r,q₂}`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Chapter 2
  (Bony's decomposition and the paraproduct and remainder estimates, Theorems 2.82 and 2.85).
-/

public section

noncomputable section

open MeasureTheory Filter Topology TemperedDistribution
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti.BesovSpace

variable {φ : ContDiffBump (0 : E)} {α β : ℝ}

section Truncation

variable {p₁ p₂ r q₁ q₂ : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [Fact (1 ≤ q₁)]
  [Fact (1 ≤ q₂)] [p₁.HolderTriple p₂ r]

/-- **The resonant terms missed by the truncation.** In `S_M u · S_M v` the resonant part is
summed only over block indices below `M`; the missing terms `Δⱼ u · Δₖ v` with `j < M ≤ k ≤ j + N`
tend to zero in `Lʳ` as `M → ∞` when `0 < α + β`, since their norms are `O(2^{-(α+β) j})` with
`j ≥ M - N`. -/
private theorem tendsto_sum_block_smul_sum_block_filter (hαβ : 0 < α + β)
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂) (N : ℕ) :
    Tendsto (fun M ↦ ∑ j ∈ Finset.range M, (u.block j •
      ∑ k ∈ (Finset.Icc (j - N) (j + N)).filter (fun k ↦ ¬k < M), v.block k :
        Lp F r (volume : Measure E))) atTop (𝓝 0) := by
  set K := ‖u‖ * (2 ^ (|β| * (N + 1 : ℕ)) * (2 * (N + 1 : ℕ) * ‖v‖))
  set ρ : ℝ := 2 ^ (-(α + β))
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hαβ)
  set D : ℕ → ℕ → Lp F r (volume : Measure E) := fun M j ↦
    u.block j • ∑ k ∈ (Finset.Icc (j - N) (j + N)).filter (fun k ↦ ¬k < M), v.block k
  -- The window sums of the weighted block norms of `v` are at most `2 (N + 1) ‖v‖`.
  have hwin (j : ℕ) : ∑ k ∈ Finset.Ico (j - (N + 1)) (j + (N + 1)), 2 ^ (β * k) * ‖v.block k‖ ≤
      2 * (N + 1 : ℕ) * ‖v‖ := by
    refine (Finset.sum_le_sum fun k _ ↦ v.rpow_mul_norm_block_le k).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
    gcongr
    exact_mod_cast (by omega : j + (N + 1) - (j - (N + 1)) ≤ 2 * (N + 1))
  -- Each term is `O(ρ ^ j)`, and only the indices `M - N ≤ j < M` contribute.
  have hD (M j : ℕ) : ‖D M j‖ ≤ K * ρ ^ j :=
    Real.le_mul_rpow_neg_pow_of_rpow_mul_le two_pos <|
      (rpow_mul_norm_block_smul_sum_block_le u v (Finset.filter_subset _ _)).trans <|
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hwin j) (by positivity))
          (norm_nonneg _)
  have hsub (M : ℕ) : ∑ j ∈ Finset.range M, D M j = ∑ j ∈ Finset.Ico (M - N) M, D M j := by
    refine (Finset.sum_subset (fun j hj ↦ ?_) fun j hjM hj ↦ ?_).symm
    · exact Finset.mem_range.2 (Finset.mem_Ico.1 hj).2
    · have hjN : j + N < M := by
        simp only [Finset.mem_range, Finset.mem_Ico, not_and_or, not_le, not_lt] at hjM hj
        omega
      have hempty : (Finset.Icc (j - N) (j + N)).filter (fun k ↦ ¬k < M) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun k hk ↦ by
          simp only [Finset.mem_Icc] at hk
          omega
      simp only [D, hempty, Finset.sum_empty, Lp.smul_zero]
  have hbound (M : ℕ) : ‖∑ j ∈ Finset.range M, D M j‖ ≤ N * K * ρ ^ (M - N) := by
    rw [hsub]
    calc ‖∑ j ∈ Finset.Ico (M - N) M, D M j‖ ≤ ∑ _j ∈ Finset.Ico (M - N) M, K * ρ ^ (M - N) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj ↦ (hD M j).trans ?_)
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one hρ0 hρ1.le (Finset.mem_Ico.1 hj).1) (by positivity)
      _ = (Finset.Ico (M - N) M).card * (K * ρ ^ (M - N)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ N * (K * ρ ^ (M - N)) := by
          gcongr
          rw [Nat.card_Ico]
          exact_mod_cast (by omega : M - (M - N) ≤ N)
      _ = N * K * ρ ^ (M - N) := by ring
  refine squeeze_zero_norm hbound ?_
  simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp
    (tendsto_sub_atTop_nat N)).const_mul (N * K)

/-- **The truncated products converge to the sum of Bony's three series.** If the paraproducts
`T_u v`, `T_v u` and the resonant part `R(u, v)` with gap `N` converge in `𝓢'(E, F)` and
`0 < α + β`, then `S_M u · S_M v` converges to the sum of their limits. -/
private theorem tendsto_lowPass_smul_lowPass_of_hasSum (hαβ : 0 < α + β)
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂) (N : ℕ) {w₁ w₂ w₃ : 𝓢'(E, F)}
    (h₁ : HasSum (fun j ↦ ((u.lowPass (j - N) • v.block j : Lp F r (volume : Measure E)) :
      𝓢'(E, F))) w₁)
    (h₂ : HasSum (fun j ↦ ((u.block j • v.lowPass (j - N) : Lp F r (volume : Measure E)) :
      𝓢'(E, F))) w₂)
    (h₃ : HasSum (fun j ↦ ((u.block j • ∑ k ∈ Finset.Icc (j - N) (j + N), v.block k :
      Lp F r (volume : Measure E)) : 𝓢'(E, F))) w₃) :
    Tendsto (fun M ↦ ((u.lowPass M • v.lowPass M : Lp F r (volume : Measure E)) : 𝓢'(E, F)))
      atTop (𝓝 (w₁ + w₂ + w₃)) := by
  have hD := ((Lp.toTemperedDistributionCLM F volume r).continuous.tendsto 0).comp
    (tendsto_sum_block_smul_sum_block_filter hαβ u v N)
  rw [map_zero] at hD
  have h := (h₁.tendsto_sum_nat.add h₂.tendsto_sum_nat).add (h₃.tendsto_sum_nat.sub hD)
  rw [sub_zero] at h
  refine h.congr fun M ↦ ?_
  -- The window `[j - N, j + N]` splits into the indices below `M`, which the truncation keeps,
  -- and the indices from `M` on.
  have hsplit (j : ℕ) : (u.block j • ∑ k ∈ Finset.Icc (j - N) (j + N), v.block k :
      Lp F r (volume : Measure E)) =
        (u.block j • ∑ k ∈ (Finset.range M).filter (fun k ↦ k ≤ j + N ∧ j ≤ k + N), v.block k :
          Lp F r (volume : Measure E)) +
        u.block j • ∑ k ∈ (Finset.Icc (j - N) (j + N)).filter (fun k ↦ ¬k < M), v.block k := by
    have hfilter : (Finset.range M).filter (fun k ↦ k ≤ j + N ∧ j ≤ k + N) =
        (Finset.Icc (j - N) (j + N)).filter (fun k ↦ k < M) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega
    rw [hfilter, ← Lp.add_smul, Finset.sum_filter_add_sum_filter_not]
  simp only [Function.comp_apply, Lp.toTemperedDistributionCLM_apply,
    lowPass_smul_lowPass N M u v, hsplit, Finset.sum_add_distrib, Lp.toTemperedDistribution_add,
    Lp.toTemperedDistribution_sum]
  abel

end Truncation

variable (φ) in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A gap `N` for which the paraproduct terms are spectrally localized in dyadic annuli. -/
private theorem exists_rOut_lt_two_pow_mul_rIn : ∃ N : ℕ, φ.rOut < 2 ^ N * φ.rIn := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (φ.rOut / φ.rIn) one_lt_two
  exact ⟨N, (div_lt_iff₀ φ.rIn_pos).1 hN⟩

variable (φ) in
/-- **The product of a distribution of negative regularity and a smoother one**, a consequence of
Bahouri–Chemin–Danchin, Theorems 2.82 and 2.85. Let `α < 0 < α + β`. There is `C ≥ 0`,
depending only on `φ`, `α` and `β`, with the following property for all exponents
`1 ≤ p₁, p₂, r, q₁, q₂ ≤ ∞` with `1/r = 1/p₁ + 1/p₂`. If `u ∈ B^α_{p₁,q₁}` and
`v ∈ B^β_{p₂,q₂}`, then the products `S_M u · S_M v` of the low-frequency cut-offs converge in the
tempered distributions to an element `w` of `B^α_{r,q₁}` with `‖w‖ ≤ C ‖u‖ ‖v‖`. For
`p₁ = p₂ = r = q₁ = q₂ = ∞` this is the product map `𝒞^α × 𝒞^β → 𝒞^α`. -/
theorem exists_tendsto_lowPass_smul_lowPass_and_norm_le_of_neg_left (hα : α < 0)
    (hαβ : 0 < α + β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q₁ q₂ : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)]
      [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [p₁.HolderTriple p₂ r] (u : BesovSpace ℂ φ α p₁ q₁)
      (v : BesovSpace F φ β p₂ q₂), ∃ w : BesovSpace F φ α r q₁,
        Tendsto (fun M ↦ ((u.lowPass M • v.lowPass M : Lp F r (volume : Measure E)) :
          𝓢'(E, F))) atTop (𝓝 w.toDistr) ∧ ‖w‖ ≤ C * ‖u‖ * ‖v‖ := by
  have hβ : 0 < β := by linarith
  have hlt : α < α + β := by linarith
  obtain ⟨N, hN⟩ := exists_rOut_lt_two_pow_mul_rIn φ
  obtain ⟨C₁, hC₁, h₁⟩ := exists_hasSum_lowPass_smul_block_and_norm_le_of_neg (F := F) φ hα β hN
  obtain ⟨C₂, hC₂, h₂⟩ :=
    exists_hasSum_block_smul_lowPass_and_norm_le_of_toDistr_eq (F := F) φ α hN
  obtain ⟨C₃, hC₃, h₃⟩ := exists_hasSum_block_smul_sum_block_and_norm_le (F := F) φ hαβ N
  have hc : 0 < 1 - (2 : ℝ) ^ (α - (α + β)) :=
    sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith))
  have hd : 0 < 1 - (2 : ℝ) ^ (-β) :=
    sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith))
  set c := (1 - (2 : ℝ) ^ (α - (α + β)))⁻¹
  set d := (1 - (2 : ℝ) ^ (-β))⁻¹
  refine ⟨c * C₁ + C₂ * d + c * C₃, by positivity,
    fun {p₁ p₂ r q₁ q₂} _ _ _ _ _ _ u v ↦ ?_⟩
  obtain ⟨g, hg, hgn⟩ := exists_toDistr_eq_and_norm_le_of_pos hβ v
  obtain ⟨w₁, hw₁, hn₁⟩ := h₁ (r := r) u v
  obtain ⟨w₂, hw₂, hn₂⟩ := h₂ (r := r) u v hg
  obtain ⟨w₃, hw₃, hn₃⟩ := h₃ (r := r) u v
  -- `T_u v` and `R(u, v)` lie in `B^{α+β}_{r,q₂} ⊆ B^α_{r,q₁}`, and `T_v u` in `B^α_{r,q₁}`.
  refine ⟨inclusionOfLT F φ r q₂ q₁ hlt w₁ + w₂ + inclusionOfLT F φ r q₂ q₁ hlt w₃, ?_, ?_⟩
  · simpa only [toDistr_add, toDistr_inclusionOfLT] using
      tendsto_lowPass_smul_lowPass_of_hasSum hαβ u v N hw₁ hw₂ hw₃
  · calc ‖inclusionOfLT F φ r q₂ q₁ hlt w₁ + w₂ + inclusionOfLT F φ r q₂ q₁ hlt w₃‖
        ≤ c * ‖w₁‖ + ‖w₂‖ + c * ‖w₃‖ :=
          (norm_add₃_le).trans (add_le_add_three (norm_inclusionOfLT_le hlt w₁) le_rfl
            (norm_inclusionOfLT_le hlt w₃))
      _ ≤ c * (C₁ * ‖u‖ * ‖v‖) + C₂ * ‖u‖ * (d * ‖v‖) + c * (C₃ * ‖u‖ * ‖v‖) := by
          gcongr
          exact hn₂.trans (by gcongr)
      _ = (c * C₁ + C₂ * d + c * C₃) * ‖u‖ * ‖v‖ := by ring

variable (φ) in
/-- **The product of a smoother distribution and one of negative regularity**, a consequence of
Bahouri–Chemin–Danchin, Theorems 2.82 and 2.85. Let `β < 0 < α + β`. There is `C ≥ 0`,
depending only on `φ`, `α` and `β`, with the following property for all exponents
`1 ≤ p₁, p₂, r, q₁, q₂ ≤ ∞` with `1/r = 1/p₁ + 1/p₂`. If `u ∈ B^α_{p₁,q₁}` and
`v ∈ B^β_{p₂,q₂}`, then the products `S_M u · S_M v` of the low-frequency cut-offs converge in the
tempered distributions to an element `w` of `B^β_{r,q₂}` with `‖w‖ ≤ C ‖u‖ ‖v‖`. -/
theorem exists_tendsto_lowPass_smul_lowPass_and_norm_le_of_neg_right (hβ : β < 0)
    (hαβ : 0 < α + β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q₁ q₂ : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)]
      [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [p₁.HolderTriple p₂ r] (u : BesovSpace ℂ φ α p₁ q₁)
      (v : BesovSpace F φ β p₂ q₂), ∃ w : BesovSpace F φ β r q₂,
        Tendsto (fun M ↦ ((u.lowPass M • v.lowPass M : Lp F r (volume : Measure E)) :
          𝓢'(E, F))) atTop (𝓝 w.toDistr) ∧ ‖w‖ ≤ C * ‖u‖ * ‖v‖ := by
  have hα : 0 < α := by linarith
  have hlt : β < α + β := by linarith
  obtain ⟨N, hN⟩ := exists_rOut_lt_two_pow_mul_rIn φ
  obtain ⟨C₁, hC₁, h₁⟩ :=
    exists_hasSum_lowPass_smul_block_and_norm_le_of_toDistr_eq (F := F) φ β hN
  obtain ⟨C₂, hC₂, h₂⟩ := exists_hasSum_block_smul_lowPass_and_norm_le_of_neg (F := F) φ α hβ hN
  obtain ⟨C₃, hC₃, h₃⟩ := exists_hasSum_block_smul_sum_block_and_norm_le (F := F) φ hαβ N
  have hc : 0 < 1 - (2 : ℝ) ^ (β - (α + β)) :=
    sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith))
  have hd : 0 < 1 - (2 : ℝ) ^ (-α) :=
    sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith))
  set c := (1 - (2 : ℝ) ^ (β - (α + β)))⁻¹
  set d := (1 - (2 : ℝ) ^ (-α))⁻¹
  refine ⟨C₁ * d + c * C₂ + c * C₃, by positivity,
    fun {p₁ p₂ r q₁ q₂} _ _ _ _ _ _ u v ↦ ?_⟩
  obtain ⟨f, hf, hfn⟩ := exists_toDistr_eq_and_norm_le_of_pos hα u
  obtain ⟨w₁, hw₁, hn₁⟩ := h₁ (r := r) u hf v
  obtain ⟨w₂, hw₂, hn₂⟩ := h₂ (r := r) u v
  obtain ⟨w₃, hw₃, hn₃⟩ := h₃ (r := r) u v
  -- `T_u v` lies in `B^β_{r,q₂}`, and `T_v u` and `R(u, v)` in `B^{α+β}_{r,q} ⊆ B^β_{r,q₂}`.
  refine ⟨w₁ + inclusionOfLT F φ r q₁ q₂ hlt w₂ + inclusionOfLT F φ r q₂ q₂ hlt w₃, ?_, ?_⟩
  · simpa only [toDistr_add, toDistr_inclusionOfLT] using
      tendsto_lowPass_smul_lowPass_of_hasSum hαβ u v N hw₁ hw₂ hw₃
  · calc ‖w₁ + inclusionOfLT F φ r q₁ q₂ hlt w₂ + inclusionOfLT F φ r q₂ q₂ hlt w₃‖
        ≤ ‖w₁‖ + c * ‖w₂‖ + c * ‖w₃‖ :=
          (norm_add₃_le).trans (add_le_add_three le_rfl (norm_inclusionOfLT_le hlt w₂)
            (norm_inclusionOfLT_le hlt w₃))
      _ ≤ C₁ * (d * ‖u‖) * ‖v‖ + c * (C₂ * ‖u‖ * ‖v‖) + c * (C₃ * ‖u‖ * ‖v‖) := by
          gcongr
          exact hn₁.trans (by gcongr)
      _ = (C₁ * d + c * C₂ + c * C₃) * ‖u‖ * ‖v‖ := by ring

end TauCeti.BesovSpace
