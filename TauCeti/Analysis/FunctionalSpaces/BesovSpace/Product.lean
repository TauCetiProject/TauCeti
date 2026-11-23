/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Paraproduct
public import TauCeti.Analysis.FunctionalSpaces.TimeWeighted

/-!
# The product of Besov elements of negative and positive regularity

Let `α < 0 < β` with `α + β > 0`. A tempered distribution `u ∈ B^α_{p₁,q₁}` of negative
regularity cannot be multiplied by an arbitrary function, but it can be multiplied by an element
`v ∈ B^β_{p₂,q₂}` of the larger positive regularity `β > -α`: the products `S_M u · S_M v` of the
low-frequency cut-offs `S_M = ∑_{k < M} Δₖ` converge in the tempered distributions, and the limit,
the product `u v`, lies in `B^α_{r,q₁}` for `1/r = 1/p₁ + 1/p₂`, with norm `O(‖u‖ ‖v‖)`. On the
Hölder–Zygmund scale `𝒞^s = B^s_{∞,∞}` this is the product map `𝒞^α × 𝒞^β → 𝒞^α`, the
multiplication used to give a meaning to products of distributional fields with Hölder
coefficients in singular stochastic equations.

The proof is Bony's decomposition (`TauCeti.BesovSpace.lowPass_smul_lowPass`): with a gap `N` such
that `φ.rOut < 2^N φ.rIn`, `S_M u · S_M v` is the sum of the truncations of the paraproducts
`T_u v = ∑ⱼ S_{j-N} u · Δⱼ v` and `T_v u = ∑ⱼ Δⱼ u · S_{j-N} v` and of the resonant part
`R(u, v) = ∑ⱼ Δⱼ u · ∑_{|k - j| ≤ N} Δₖ v`, up to the resonant pairs `(j, k)` with
`j < M ≤ k`, whose sum is `O(2^{-(α+β) M} ‖u‖ ‖v‖)` in `Lʳ`. The three series converge:

* `T_u v` lies in `B^{α+β}_{r,q₂}` since `α < 0`
  (`TauCeti.BesovSpace.exists_hasSum_lowPass_smul_block_and_norm_le_of_neg`);
* `T_v u` lies in `B^α_{r,q₁}` since `v` is an `L^{p₂}` function for `β > 0`
  (`TauCeti.BesovSpace.exists_toDistr_eq_and_norm_le_of_pos` and
  `TauCeti.BesovSpace.exists_hasSum_block_smul_lowPass_and_norm_le_of_toDistr_eq`);
* `R(u, v)` lies in `B^{α+β}_{r,q₂}` since `α + β > 0`
  (`TauCeti.BesovSpace.exists_hasSum_block_smul_sum_block_and_norm_le`);

and `B^{α+β}_{r,q₂} ⊆ B^α_{r,q₁}` since `β > 0`.

## Main declarations

* `TauCeti.BesovSpace.smulL`: the product `B^α_{p₁,q₁} × B^β_{p₂,q₂} → B^α_{r,q₁}` as a continuous
  bilinear map, for `α < 0 < α + β` and `1/r = 1/p₁ + 1/p₂`.
* `TauCeti.BesovSpace.tendsto_lowPass_smul_lowPass` and `TauCeti.BesovSpace.smulL_eq_iff`: the
  product is the limit of `S_M u · S_M v` in the tempered distributions, and is characterized by it.
* `TauCeti.BesovSpace.exists_norm_smulL_apply_le`: the bound `‖u v‖ ≤ C ‖u‖ ‖v‖` with a constant
  depending only on the bump function and the regularities, not on the integrability exponents.
* `TauCeti.BesovSpace.exists_norm_timeWeighted_bilinear_smulL_apply_apply_le`: the local-in-time
  weighted form. For `u ∈ C_{η₁}((0, T]; B^α_{p₁,q₁})` and `v ∈ C_{η₂}((0, T]; B^β_{p₂,q₂})`, the
  pointwise product `t ↦ u t v t` (`TauCeti.TimeWeighted.bilinear` applied to `smulL`) lies in
  `C_{η₁ + η₂}((0, T]; B^α_{r,q₁})`, with `sup_t t^{η₁ + η₂} ‖u t v t‖ ≤ C ‖u‖ ‖v‖` for a constant
  `C` depending only on `φ`, `α` and `β`, not on the exponents, `T`, `η₁` or `η₂`.

## References

* J.-M. Bony, *Calcul symbolique et propagation des singularités pour les équations aux dérivées
  partielles non linéaires*, Ann. Sci. École Norm. Sup. (4) 14 (1981), 209–246.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, §2.8
  (Bony's decomposition and Theorems 2.82 and 2.85, from which the product estimate follows).
-/

public section

noncomputable section

open MeasureTheory Filter Topology TemperedDistribution
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti.BesovSpace

variable {φ : ContDiffBump (0 : E)} {α β : ℝ} {p₁ p₂ r q₁ q₂ : ℝ≥0∞} [Fact (1 ≤ p₁)]
  [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [p₁.HolderTriple p₂ r]

/-- The resonant pairs `(j, k)` with `j < M ≤ k` and `k ≤ j + N`, which the truncated resonant
part of `S_M u · S_M v` misses. -/
private def resonantTail (N M : ℕ) (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂) :
    Lp F r (volume : Measure E) :=
  ∑ j ∈ Finset.range M,
    (u.block j • ∑ k ∈ (Finset.Icc (j - N) (j + N)).filter (M ≤ ·), v.block k :
      Lp F r (volume : Measure E))

omit [Fact (1 ≤ r)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] in
/-- **Bony's decomposition with the full resonant terms.** The truncated resonant part of
`S_M u · S_M v` is the partial sum of the resonant series minus `resonantTail`. -/
private theorem lowPass_smul_lowPass_eq (N M : ℕ) (u : BesovSpace ℂ φ α p₁ q₁)
    (v : BesovSpace F φ β p₂ q₂) :
    (u.lowPass M • v.lowPass M : Lp F r (volume : Measure E)) =
      ∑ j ∈ Finset.range M, (u.lowPass (j - N) • v.block j : Lp F r (volume : Measure E)) +
        ∑ j ∈ Finset.range M, (u.block j • v.lowPass (j - N) : Lp F r (volume : Measure E)) +
        (∑ j ∈ Finset.range M, (u.block j • ∑ k ∈ Finset.Icc (j - N) (j + N), v.block k :
          Lp F r (volume : Measure E)) - resonantTail N M u v) := by
  rw [lowPass_smul_lowPass N M u v, resonantTail, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  -- Split the window `|k - j| ≤ N` into the indices below `M` and the others.
  have hsplit : ∑ k ∈ Finset.Icc (j - N) (j + N), v.block k =
      ∑ k ∈ (Finset.range M).filter (fun k ↦ k ≤ j + N ∧ j ≤ k + N), v.block k +
        ∑ k ∈ (Finset.Icc (j - N) (j + N)).filter (M ≤ ·), v.block k := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc (j - N) (j + N)) (· < M)]
    congr 2 <;> ext k <;> simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] <;> omega
  rw [eq_sub_iff_add_eq, ← Lp.add_smul, hsplit]

/-- **The missing resonant pairs are negligible.** For `α < 0 < α + β`,
`‖resonantTail N M u v‖_r ≤ N ‖u‖ ‖v‖ (2^{-(α+β)})^M / (2^{-α} - 1)`: the terms have `j < M ≤ k`,
so `‖Δⱼ u‖ ≤ 2^{-α j} ‖u‖` sums to `O(2^{-α M})`, and each of the at most `N` blocks
`‖Δₖ v‖ ≤ 2^{-β k} ‖v‖` is `O(2^{-β M})`. -/
private theorem norm_resonantTail_le (hα : α < 0) (hαβ : 0 < α + β) (N M : ℕ)
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂) :
    ‖(resonantTail N M u v : Lp F r (volume : Measure E))‖ ≤
      N * ‖u‖ * ‖v‖ / (2 ^ (-α) - 1) * (2 ^ (-(α + β))) ^ M := by
  set b : ℝ := 2 ^ (-β)
  have hb : b ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by linarith)
  -- The blocks of `v` of index at least `M` are at most `b^M ‖v‖`, and at most `N` of them
  -- meet the window of an index `j < M`.
  have hv (j : ℕ) (hj : j < M) :
      ‖∑ k ∈ (Finset.Icc (j - N) (j + N)).filter (M ≤ ·), v.block k‖ ≤ N * (b ^ M * ‖v‖) := by
    have hsub : (Finset.Icc (j - N) (j + N)).filter (M ≤ ·) ⊆ Finset.Ico M (M + N) := fun k hk ↦ by
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico] at hk ⊢
      omega
    calc ‖∑ k ∈ (Finset.Icc (j - N) (j + N)).filter (M ≤ ·), v.block k‖
        ≤ ∑ k ∈ (Finset.Icc (j - N) (j + N)).filter (M ≤ ·), ‖v.block k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.Ico M (M + N), ‖v.block k‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ norm_nonneg _
      _ ≤ ∑ _k ∈ Finset.Ico M (M + N), b ^ M * ‖v‖ := Finset.sum_le_sum fun k hk ↦
          (v.norm_block_le k).trans <| mul_le_mul_of_nonneg_right
            (pow_le_pow_of_le_one (by positivity) hb (Finset.mem_Ico.1 hk).1) (norm_nonneg _)
      _ = N * (b ^ M * ‖v‖) := by simp
  have hab : (2 : ℝ) ^ (-α * M) * b ^ M = (2 ^ (-(α + β))) ^ M := by
    rw [Real.rpow_mul zero_le_two, Real.rpow_natCast, ← mul_pow, ← Real.rpow_add two_pos,
      neg_add]
  calc ‖(resonantTail N M u v : Lp F r (volume : Measure E))‖
      ≤ ∑ j ∈ Finset.range M, ‖(u.block j •
          ∑ k ∈ (Finset.Icc (j - N) (j + N)).filter (M ≤ ·), v.block k :
            Lp F r (volume : Measure E))‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range M, ‖u.block j‖ * (N * (b ^ M * ‖v‖)) :=
        Finset.sum_le_sum fun j hj ↦ (Lp.norm_smul_le _ _).trans <|
          mul_le_mul_of_nonneg_left (hv j (Finset.mem_range.1 hj)) (norm_nonneg _)
    _ = (∑ j ∈ Finset.range M, ‖u.block j‖) * (N * (b ^ M * ‖v‖)) := (Finset.sum_mul ..).symm
    _ ≤ 2 ^ (-α * M) / (2 ^ (-α) - 1) * ‖u‖ * (N * (b ^ M * ‖v‖)) := by
        gcongr
        exact sum_norm_block_le_of_neg hα u M
    _ = N * ‖u‖ * ‖v‖ / (2 ^ (-α) - 1) * (2 ^ (-α * M) * b ^ M) := by ring
    _ = _ := by rw [hab]

/-- The missing resonant pairs tend to `0` in the tempered distributions. -/
private theorem tendsto_resonantTail (hα : α < 0) (hαβ : 0 < α + β) (N : ℕ)
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂) :
    Tendsto (fun M ↦ ((resonantTail N M u v : Lp F r (volume : Measure E)) : 𝓢'(E, F))) atTop
      (𝓝 0) := by
  have hx : (2 : ℝ) ^ (-(α + β)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 hαβ)
  have hL : Tendsto (fun M ↦ (resonantTail N M u v : Lp F r (volume : Measure E))) atTop (𝓝 0) :=
    squeeze_zero_norm (fun M ↦ norm_resonantTail_le hα hαβ N M u v) <| by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hx).const_mul
        (N * ‖u‖ * ‖v‖ / (2 ^ (-α) - 1))
  have h := ((Lp.toTemperedDistributionCLM F volume r).continuous.tendsto 0).comp hL
  rwa [map_zero] at h

variable (φ) in
/-- **The product estimate**, with a constant independent of the integrability exponents. -/
private theorem exists_tendsto_lowPass_smul_lowPass_and_norm_le (hα : α < 0) (hαβ : 0 < α + β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q₁ q₂ : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)]
      [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [p₁.HolderTriple p₂ r] (u : BesovSpace ℂ φ α p₁ q₁)
      (v : BesovSpace F φ β p₂ q₂), ∃ w : BesovSpace F φ α r q₁,
        Tendsto (fun M ↦ ((u.lowPass M • v.lowPass M : Lp F r (volume : Measure E)) :
          𝓢'(E, F))) atTop (𝓝 w.toDistr) ∧ ‖w‖ ≤ C * ‖u‖ * ‖v‖ := by
  have hβ : 0 < β := by linarith
  have hlt : α < α + β := by linarith
  -- A gap `N` for which the terms of the paraproducts have spectra in dyadic annuli.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, φ.rOut < 2 ^ N * φ.rIn := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (φ.rOut / φ.rIn) (one_lt_two (α := ℝ))
    exact ⟨N, (div_lt_iff₀ φ.rIn_pos).1 hN⟩
  obtain ⟨C₁, hC₁, h₁⟩ := exists_hasSum_lowPass_smul_block_and_norm_le_of_neg (F := F) φ hα β hN
  obtain ⟨C₂, hC₂, h₂⟩ := exists_hasSum_block_smul_lowPass_and_norm_le_of_toDistr_eq (F := F) φ α hN
  obtain ⟨C₃, hC₃, h₃⟩ := exists_hasSum_block_smul_sum_block_and_norm_le (F := F) φ hαβ N
  set K : ℝ := (1 - 2 ^ (-β))⁻¹
  have hK : 0 ≤ K := inv_nonneg.2 <| sub_nonneg.2 <|
    Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by linarith)
  have hK' : (1 - 2 ^ (α - (α + β)))⁻¹ = K := by rw [sub_add_cancel_left]
  refine ⟨K * C₁ + C₂ * K + K * C₃, by positivity, fun {p₁ p₂ r q₁ q₂} _ _ _ _ _ _ u v ↦ ?_⟩
  obtain ⟨w₁, hw₁, hw₁n⟩ := h₁ (r := r) u v
  obtain ⟨g, hg, hgn⟩ := exists_toDistr_eq_and_norm_le_of_pos hβ v
  obtain ⟨w₂, hw₂, hw₂n⟩ := h₂ (r := r) u v hg
  obtain ⟨w₃, hw₃, hw₃n⟩ := h₃ (r := r) u v
  set ι := inclusionOfLT F φ r q₂ q₁ hlt
  refine ⟨ι w₁ + w₂ + ι w₃, ?_, ?_⟩
  · have h := ((hw₁.tendsto_sum_nat.add hw₂.tendsto_sum_nat).add
      hw₃.tendsto_sum_nat).sub (tendsto_resonantTail (r := r) hα hαβ N u v)
    simp only [sub_zero] at h
    rw [toDistr_add, toDistr_add, toDistr_inclusionOfLT, toDistr_inclusionOfLT]
    refine h.congr fun M ↦ ?_
    rw [lowPass_smul_lowPass_eq (r := r) N M u v]
    simp only [← Lp.toTemperedDistributionCLM_apply, map_add, map_sub, map_sum, add_sub_assoc]
  · calc ‖ι w₁ + w₂ + ι w₃‖ ≤ ‖ι w₁‖ + ‖w₂‖ + ‖ι w₃‖ := norm_add₃_le
      _ ≤ K * (C₁ * ‖u‖ * ‖v‖) + C₂ * ‖u‖ * (K * ‖v‖) + K * (C₃ * ‖u‖ * ‖v‖) := by
          gcongr
          · exact (norm_inclusionOfLT_le hlt w₁).trans_eq (by rw [hK'])  |>.trans
              (mul_le_mul_of_nonneg_left hw₁n hK)
          · exact hw₂n.trans (by gcongr)
          · exact (norm_inclusionOfLT_le hlt w₃).trans_eq (by rw [hK'])  |>.trans
              (mul_le_mul_of_nonneg_left hw₃n hK)
      _ = (K * C₁ + C₂ * K + K * C₃) * ‖u‖ * ‖v‖ := by ring

variable (F φ) in
/-- The constant of the product estimate. -/
private def smulBound (hα : α < 0) (hαβ : 0 < α + β) : ℝ :=
  (exists_tendsto_lowPass_smul_lowPass_and_norm_le (F := F) φ hα hαβ).choose

variable (r) in
/-- The product, as a function of the two factors. -/
private def smulAux (hα : α < 0) (hαβ : 0 < α + β) (u : BesovSpace ℂ φ α p₁ q₁)
    (v : BesovSpace F φ β p₂ q₂) : BesovSpace F φ α r q₁ :=
  ((exists_tendsto_lowPass_smul_lowPass_and_norm_le (F := F) φ hα hαβ).choose_spec.2
    (r := r) u v).choose

private theorem tendsto_smulAux (hα : α < 0) (hαβ : 0 < α + β) (u : BesovSpace ℂ φ α p₁ q₁)
    (v : BesovSpace F φ β p₂ q₂) :
    Tendsto (fun M ↦ ((u.lowPass M • v.lowPass M : Lp F r (volume : Measure E)) : 𝓢'(E, F)))
      atTop (𝓝 (smulAux r hα hαβ u v).toDistr) :=
  ((exists_tendsto_lowPass_smul_lowPass_and_norm_le (F := F) φ hα hαβ).choose_spec.2
    (r := r) u v).choose_spec.1

private theorem norm_smulAux_le (hα : α < 0) (hαβ : 0 < α + β) (u : BesovSpace ℂ φ α p₁ q₁)
    (v : BesovSpace F φ β p₂ q₂) :
    ‖smulAux r hα hαβ u v‖ ≤ smulBound F φ hα hαβ * ‖u‖ * ‖v‖ :=
  ((exists_tendsto_lowPass_smul_lowPass_and_norm_le (F := F) φ hα hαβ).choose_spec.2
    (r := r) u v).choose_spec.2

private theorem smulAux_eq_iff (hα : α < 0) (hαβ : 0 < α + β) {u : BesovSpace ℂ φ α p₁ q₁}
    {v : BesovSpace F φ β p₂ q₂} {w : BesovSpace F φ α r q₁} :
    smulAux r hα hαβ u v = w ↔
      Tendsto (fun M ↦ ((u.lowPass M • v.lowPass M : Lp F r (volume : Measure E)) : 𝓢'(E, F)))
        atTop (𝓝 w.toDistr) :=
  ⟨fun h ↦ h ▸ tendsto_smulAux hα hαβ u v,
    fun h ↦ ext (tendsto_nhds_unique (tendsto_smulAux hα hαβ u v) h)⟩

variable (r) in
/-- **The product of Besov elements of negative and positive regularity.** Let `α < 0 < α + β`
and `1/r = 1/p₁ + 1/p₂`. For `u ∈ B^α_{p₁,q₁}` and `v ∈ B^β_{p₂,q₂}`, the product
`u v ∈ B^α_{r,q₁}` is the limit in the tempered distributions of the products `S_M u · S_M v` of
the low-frequency cut-offs
(`TauCeti.BesovSpace.tendsto_lowPass_smul_lowPass`), and `(u, v) ↦ u v` is a continuous bilinear
map. For `p₁ = p₂ = r = q₁ = q₂ = ∞` this is the product map `𝒞^α × 𝒞^β → 𝒞^α` on the
Hölder–Zygmund scale. -/
def smulL (hα : α < 0) (hαβ : 0 < α + β) :
    BesovSpace ℂ φ α p₁ q₁ →L[ℂ] BesovSpace F φ β p₂ q₂ →L[ℂ] BesovSpace F φ α r q₁ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (smulAux r hα hαβ)
      (fun u₁ u₂ v ↦ (smulAux_eq_iff hα hαβ).2 <| by
        rw [toDistr_add]
        refine ((tendsto_smulAux hα hαβ u₁ v).add (tendsto_smulAux hα hαβ u₂ v)).congr fun M ↦ ?_
        simp only [lowPass_add, Lp.smul_add, ← Lp.toTemperedDistributionCLM_apply, map_add])
      (fun c u v ↦ (smulAux_eq_iff hα hαβ).2 <| by
        rw [toDistr_smul]
        refine ((tendsto_smulAux hα hαβ u v).const_smul c).congr fun M ↦ ?_
        simp only [lowPass_smul, Lp.smul_assoc, ← Lp.toTemperedDistributionCLM_apply, map_smul])
      (fun u v₁ v₂ ↦ (smulAux_eq_iff hα hαβ).2 <| by
        rw [toDistr_add]
        refine ((tendsto_smulAux hα hαβ u v₁).add (tendsto_smulAux hα hαβ u v₂)).congr fun M ↦ ?_
        simp only [lowPass_add, Lp.add_smul, ← Lp.toTemperedDistributionCLM_apply, map_add])
      (fun c u v ↦ (smulAux_eq_iff hα hαβ).2 <| by
        rw [toDistr_smul]
        refine ((tendsto_smulAux hα hαβ u v).const_smul c).congr fun M ↦ ?_
        simp only [lowPass_smul, ← Lp.smul_comm, ← Lp.toTemperedDistributionCLM_apply, map_smul]))
    (smulBound F φ hα hαβ) (norm_smulAux_le hα hαβ)

private theorem smulL_apply (hα : α < 0) (hαβ : 0 < α + β) (u : BesovSpace ℂ φ α p₁ q₁)
    (v : BesovSpace F φ β p₂ q₂) : smulL r hα hαβ u v = smulAux r hα hαβ u v :=
  (LinearMap.mkContinuous₂_apply _ _ u v).trans (LinearMap.mk₂_apply _ _ u v)

/-- **The product is the limit of the products of the low-frequency cut-offs:**
`S_M u · S_M v → u v` in the tempered distributions. -/
theorem tendsto_lowPass_smul_lowPass (hα : α < 0) (hαβ : 0 < α + β)
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂) :
    Tendsto (fun M ↦ ((u.lowPass M • v.lowPass M : Lp F r (volume : Measure E)) : 𝓢'(E, F)))
      atTop (𝓝 (smulL r hα hαβ u v).toDistr) := by
  rw [smulL_apply]
  exact tendsto_smulAux hα hαβ u v

/-- **Characterization of the product:** `u v = w` exactly when `S_M u · S_M v → w` in the
tempered distributions. -/
theorem smulL_eq_iff (hα : α < 0) (hαβ : 0 < α + β) {u : BesovSpace ℂ φ α p₁ q₁}
    {v : BesovSpace F φ β p₂ q₂} {w : BesovSpace F φ α r q₁} :
    smulL r hα hαβ u v = w ↔
      Tendsto (fun M ↦ ((u.lowPass M • v.lowPass M : Lp F r (volume : Measure E)) : 𝓢'(E, F)))
        atTop (𝓝 w.toDistr) := by
  rw [smulL_apply]
  exact smulAux_eq_iff hα hαβ

variable (F φ) in
/-- **The product estimate.** For `α < 0 < α + β` there
is `C ≥ 0`, depending only on `φ`, `α` and `β`, such that `‖u v‖_{B^α_{r,q₁}} ≤ C ‖u‖ ‖v‖` for
all exponents `1 ≤ p₁, p₂, r, q₁, q₂ ≤ ∞` with `1/r = 1/p₁ + 1/p₂`, all `u ∈ B^α_{p₁,q₁}` and
all `v ∈ B^β_{p₂,q₂}`. -/
theorem exists_norm_smulL_apply_le (hα : α < 0) (hαβ : 0 < α + β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q₁ q₂ : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)]
      [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [p₁.HolderTriple p₂ r] (u : BesovSpace ℂ φ α p₁ q₁)
      (v : BesovSpace F φ β p₂ q₂), ‖smulL r hα hαβ u v‖ ≤ C * ‖u‖ * ‖v‖ :=
  ⟨smulBound F φ hα hαβ,
    (exists_tendsto_lowPass_smul_lowPass_and_norm_le (F := F) φ hα hαβ).choose_spec.1,
    fun {p₁ p₂ r q₁ q₂} _ _ _ _ _ _ u v ↦ by
      rw [smulL_apply]
      exact norm_smulAux_le hα hαβ u v⟩

variable (F φ) in
/-- **The product estimate in time-weighted spaces.** For `α < 0 < α + β` there is `C ≥ 0`,
depending only on `φ`, `α` and `β`, such that for all exponents with `1/r = 1/p₁ + 1/p₂`, all
`T, η₁, η₂ : ℝ`, all `u ∈ C_{η₁}((0, T]; B^α_{p₁,q₁})` and all `v ∈ C_{η₂}((0, T]; B^β_{p₂,q₂})`,
the pointwise product `t ↦ u t v t` in `C_{η₁ + η₂}((0, T]; B^α_{r,q₁})` satisfies
`sup_{0 < t ≤ T} t^{η₁ + η₂} ‖u t v t‖ ≤ C ‖u‖ ‖v‖`. On the Hölder–Zygmund scale this is the
product `C_{η₁}((0, T]; 𝒞^α) × C_{η₂}((0, T]; 𝒞^β) → C_{η₁ + η₂}((0, T]; 𝒞^α)`. -/
theorem exists_norm_timeWeighted_bilinear_smulL_apply_apply_le (hα : α < 0) (hαβ : 0 < α + β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q₁ q₂ : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)]
      [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [p₁.HolderTriple p₂ r] (T η₁ η₂ : ℝ)
      (u : TimeWeighted T η₁ (BesovSpace ℂ φ α p₁ q₁))
      (v : TimeWeighted T η₂ (BesovSpace F φ β p₂ q₂)),
      ‖TimeWeighted.bilinear T η₁ η₂ (smulL r hα hαβ) u v‖ ≤ C * ‖u‖ * ‖v‖ := by
  obtain ⟨C, hC, h⟩ := exists_norm_smulL_apply_le F φ hα hαβ
  refine ⟨C, hC, fun {p₁ p₂ r q₁ q₂} _ _ _ _ _ _ T η₁ η₂ u v ↦ ?_⟩
  have hB : ‖smulL (φ := φ) (F := F) (p₁ := p₁) (p₂ := p₂) (q₁ := q₁) (q₂ := q₂) r hα hαβ‖ ≤ C :=
    ContinuousLinearMap.opNorm_le_bound₂ _ hC h
  calc ‖TimeWeighted.bilinear T η₁ η₂ (smulL r hα hαβ) u v‖
      ≤ ‖smulL (φ := φ) (F := F) (p₁ := p₁) (p₂ := p₂) (q₁ := q₁) (q₂ := q₂) r hα hαβ‖ * ‖u‖ *
          ‖v‖ :=
        TimeWeighted.norm_bilinear_apply_apply_le _ u v
    _ ≤ C * ‖u‖ * ‖v‖ := by gcongr

end TauCeti.BesovSpace
