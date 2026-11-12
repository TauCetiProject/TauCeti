/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.WeightedSequence
public import TauCeti.Analysis.Sobolev.BesselPotential.Besov
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import TauCeti.Analysis.Distribution.TemperedDistribution.BesselPotential
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Real interpolation of Bessel-potential spaces

Let `E` be a finite-dimensional real inner product space, `1 ≤ p ≤ ∞`, and let `s₀ ≠ s₁` be real
smoothness indices. The Bessel-potential spaces `H^{s₀,p}` and `H^{s₁,p}` both embed continuously
and injectively into the tempered distributions (`BesselPotentialSpace.toDistrCLM`), so they form
a compatible couple (`TauCeti.CompatibleCouple.besselPotentialSpace`). For `0 < θ < 1` and
`1 ≤ q ≤ ∞` its real interpolation space is a Besov space:

`(H^{s₀,p}, H^{s₁,p})_{θ,q} = B^{s_θ}_{p,q}`, where `s_θ = (1 - θ) s₀ + θ s₁`,

with equivalent norms (`TauCeti.CompatibleCouple.besselPotentialSpaceKMethodEquiv`). The Besov space
is built from the Littlewood–Paley blocks `Δⱼ` of any bump function `φ`.

The proof sandwiches the couple between two couples of weighted sequence spaces of `Lᵖ`
functions, whose real interpolation spaces are known
(`TauCeti.CompatibleCouple.weightedLpKMethodEquiv`).

* **Analysis.** The blocks `u ↦ (Δⱼ u)ⱼ` map `H^{sᵢ,p}` boundedly into `ℓ^∞_{sᵢ}(Lᵖ)`, because
  `H^{s,p} ⊆ B^s_{p,∞}` (`BesselPotentialSpace.toBesovSpace`). By the exactness of the real method,
  the blocks of an element of `(H^{s₀,p}, H^{s₁,p})_{θ,q}` lie in
  `(ℓ^∞_{s₀}(Lᵖ), ℓ^∞_{s₁}(Lᵖ))_{θ,q} = ℓ^q_{s_θ}(Lᵖ)`, which is the Besov condition.
* **Synthesis.** Every block `Δⱼ` meets only the blocks `Δₖ` with `j - L ≤ k < j + L`, for some `L`
  depending on `φ` (`TemperedDistribution.exists_littlewoodPaleyBlock_eq_sum_Ico`), so the window
  `Wⱼ = ∑_{j - L ≤ k < j + L} Δₖ` satisfies `Wⱼ Δⱼ = Δⱼ`. The window is localized in frequency
  near `2ʲ`, so `‖J^s Wⱼ f‖_p ≤ C 2^{js} ‖f‖_p` for the Bessel potential `J^s`, and the synthesis
  `(aⱼ)ⱼ ↦ ∑ⱼ Wⱼ aⱼ` maps `ℓ¹_{sᵢ}(Lᵖ)` boundedly into `H^{sᵢ,p}`. By the exactness of the real
  method it maps `(ℓ¹_{s₀}(Lᵖ), ℓ¹_{s₁}(Lᵖ))_{θ,q} = ℓ^q_{s_θ}(Lᵖ)` into
  `(H^{s₀,p}, H^{s₁,p})_{θ,q}`, and it sends the blocks of `u` back to `∑ⱼ Δⱼ u = u`.

## Main declarations

* `TauCeti.CompatibleCouple.besselPotentialSpace E F p s₀ s₁`: the couple `(H^{s₀,p}, H^{s₁,p})`.
* `TauCeti.CompatibleCouple.besselPotentialSpaceKMethodEquiv`: the isomorphism
  `(H^{s₀,p}, H^{s₁,p})_{θ,q} ≃L[ℂ] B^{s_θ}_{p,q}`, which keeps the underlying tempered
  distribution.
* `TauCeti.CompatibleCouple.mem_kMethod_besselPotentialSpace_iff`: an element of
  `H^{s₀,p} + H^{s₁,p}` lies in `(H^{s₀,p}, H^{s₁,p})_{θ,q}` exactly when it lies in
  `B^{s_θ}_{p,q}`, and
  `TauCeti.CompatibleCouple.memBesov_iff_exists_mem_kMethod_besselPotentialSpace`: every element
  of `B^{s_θ}_{p,q}` arises this way.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Grundlehren 223, Springer,
  1976, Theorem 6.2.4 and Theorem 6.4.5 (4).
* H. Triebel, *Interpolation Theory, Function Spaces, Differential Operators*, North-Holland,
  1978, §2.4.2.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti

namespace CompatibleCouple

open BesselPotentialSpace TemperedDistribution KMethodSpace

section Couple

variable (E F) (p : ℝ≥0∞) [Fact (1 ≤ p)] in
/-- The compatible couple `(H^{s₀,p}, H^{s₁,p})` of Bessel-potential spaces, both embedded into
the tempered distributions. -/
def besselPotentialSpace (s₀ s₁ : ℝ) :
    CompatibleCouple ℂ H^{s₀, p}(E, F) H^{s₁, p}(E, F) 𝓢'(E, F) where
  embed₀ := toDistrCLM E F s₀ p
  embed₁ := toDistrCLM E F s₁ p
  embed₀_injective := toDistrCLM_injective
  embed₁_injective := toDistrCLM_injective

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {s₀ s₁ : ℝ}

@[simp]
theorem besselPotentialSpace_embed₀_apply (u : H^{s₀, p}(E, F)) :
    (besselPotentialSpace E F p s₀ s₁).embed₀ u = u.toDistr :=
  toDistrCLM_apply u

@[simp]
theorem besselPotentialSpace_embed₁_apply (u : H^{s₁, p}(E, F)) :
    (besselPotentialSpace E F p s₀ s₁).embed₁ u = u.toDistr :=
  toDistrCLM_apply u

end Couple

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (φ : ContDiffBump (0 : E)) {s s₀ s₁ θ : ℝ} {q : ℝ≥0∞}

/-! ### Analysis: the Littlewood–Paley blocks -/

section Analysis

variable (F p) in
/-- The weighted blocks `(2^{js} Δⱼ u)ⱼ` of an element of `H^{s,p}`, as an `ℓ^∞` sequence. -/
private def weightedBlocksCLM (s : ℝ) :
    H^{s, p}(E, F) →L[ℂ] lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) ∞ :=
  (BesovSpace.weightedBlocksₗᵢ F φ s p ∞).toContinuousLinearMap ∘L toBesovSpace φ

/-- The `j`-th weighted block, rescaled by `2^{-js}`, is the block `Δⱼ u`. -/
private theorem inv_smul_weightedBlocksCLM_apply (u : H^{s, p}(E, F)) (j : ℕ) :
    (((2 : ℝ) ^ (s * j) : ℝ) : ℂ)⁻¹ • weightedBlocksCLM F p φ s u j =
      (toBesovSpace φ u).block j := by
  simp only [weightedBlocksCLM, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, BesovSpace.weightedBlocksₗᵢ_apply]
  rw [BesovSpace.weightedBlocks_apply]
  exact inv_smul_smul₀ (Complex.ofReal_ne_zero.2 (by positivity)) _

private theorem weightedLp_embed₀_weightedBlocksCLM (u : H^{s₀, p}(E, F)) (j : ℕ) :
    (weightedLp ℂ (Lp F p (volume : Measure E)) ∞ ∞ s₀ s₁).embed₀ (weightedBlocksCLM F p φ s₀ u) j =
      (toBesovSpace φ u).block j := by
  rw [weightedLp_embed₀_apply]
  exact inv_smul_weightedBlocksCLM_apply φ u j

private theorem weightedLp_embed₁_weightedBlocksCLM (u : H^{s₁, p}(E, F)) (j : ℕ) :
    (weightedLp ℂ (Lp F p (volume : Measure E)) ∞ ∞ s₀ s₁).embed₁ (weightedBlocksCLM F p φ s₁ u) j =
      (toBesovSpace φ u).block j := by
  rw [weightedLp_embed₁_apply]
  exact inv_smul_weightedBlocksCLM_apply φ u j

variable (F p s₀ s₁) in
/-- The blocks `u ↦ (Δⱼ u)ⱼ`, from `H^{s₀,p} + H^{s₁,p}` to `ℓ^∞_{s₀}(Lᵖ) + ℓ^∞_{s₁}(Lᵖ)`. -/
private def blocksMap : (besselPotentialSpace E F p s₀ s₁).SumSpace →L[ℂ]
    (weightedLp ℂ (Lp F p (volume : Measure E)) ∞ ∞ s₀ s₁).SumSpace :=
  sumLift _ (fstToSum _ ∘L weightedBlocksCLM F p φ s₀) (sndToSum _ ∘L weightedBlocksCLM F p φ s₁)
    fun x ↦ sumSpace_ext _ <| funext fun j ↦ by
      have hx := (besselPotentialSpace E F p s₀ s₁).embed₀_interFst x
      simp only [besselPotentialSpace_embed₀_apply, besselPotentialSpace_embed₁_apply] at hx
      simp only [ContinuousLinearMap.comp_apply, sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum,
        weightedLp_embed₀_weightedBlocksCLM, weightedLp_embed₁_weightedBlocksCLM]
      exact BesovSpace.block_eq_of_toDistr_eq (u := toBesovSpace φ (interFst _ x))
        (v := toBesovSpace φ (interSnd _ x))
        (by rw [toDistr_toBesovSpace, toDistr_toBesovSpace]; exact hx) j

/-- The `j`-th entry of the blocks of `u` is the `Lᵖ` function `Δⱼ u`. -/
private theorem coe_sumSpaceEmbed_blocksMap (u : (besselPotentialSpace E F p s₀ s₁).SumSpace)
    (j : ℕ) :
    ((weightedLp ℂ (Lp F p (volume : Measure E)) ∞ ∞ s₀ s₁).sumSpaceEmbed
        (blocksMap F p φ s₀ s₁ u) j : 𝓢'(E, F)) =
      littlewoodPaleyBlock F φ j ((besselPotentialSpace E F p s₀ s₁).sumSpaceEmbed u) := by
  obtain ⟨x₀, x₁, rfl⟩ := exists_fstToSum_add_sndToSum_eq _ u
  simp only [blocksMap, map_add, sumLift_fstToSum, sumLift_sndToSum, ContinuousLinearMap.comp_apply,
    sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, Pi.add_apply,
    weightedLp_embed₀_weightedBlocksCLM, weightedLp_embed₁_weightedBlocksCLM]
  simp [Lp.toTemperedDistribution_add]

end Analysis

/-! ### Synthesis: the windows of blocks -/

section Synthesis

variable (F) in
/-- The width `L` of the windows: `Δⱼ` meets only the blocks `Δₖ` with `j - L ≤ k < j + L`. -/
private def windowWidth : ℕ :=
  (exists_littlewoodPaleyBlock_eq_sum_Ico (F := F) φ φ).choose

variable (F) in
/-- The window `Wⱼ = ∑_{j - L ≤ k < j + L} Δₖ` of blocks around `Δⱼ`. -/
private def window (j : ℕ) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  ∑ k ∈ Finset.Ico (j - windowWidth F φ) (j + windowWidth F φ), littlewoodPaleyBlock F φ k

omit [CompleteSpace F] in
/-- The window around `Δⱼ` reproduces the block `Δⱼ u`. -/
private theorem window_littlewoodPaleyBlock (j : ℕ) (u : 𝓢'(E, F)) :
    window F φ j (littlewoodPaleyBlock F φ j u) = littlewoodPaleyBlock F φ j u := by
  conv_rhs => rw [(exists_littlewoodPaleyBlock_eq_sum_Ico (F := F) φ φ).choose_spec j u]
  simp only [window, _root_.sum_apply]
  exact Finset.sum_congr rfl fun k _ ↦ littlewoodPaleyBlock_comm φ k j u

/-- **The window estimate.** `J^s Wⱼ f` is an `Lᵖ` function of norm at most `C 2^{js} ‖f‖_p` for
every `f ∈ Lᵖ`, with `C` independent of `j` and `p`. -/
private theorem exists_besselPotential_window_eq_and_norm_le (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j : ℕ) (f : Lp F p (volume : Measure E)),
      ∃ g : Lp F p (volume : Measure E), besselPotential E F s (window F φ j f) = g ∧
        ‖g‖ ≤ C * 2 ^ (s * j) * ‖f‖ := by
  obtain ⟨C₁, hC₁⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  obtain ⟨C₂, hC₂, hJ⟩ := exists_besselPotential_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ s
  set L := windowWidth F φ
  refine ⟨2 * L * (C₂ * max C₁ 0 * 2 ^ (|s| * L)), by positivity, fun {p} _ j f ↦ ?_⟩
  -- Each block `Δₖ f` of the window is an `Lᵖ` function, and so is `J^s Δₖ f`.
  choose f' hf' hf'f using fun k ↦ hC₁ (p := p) k f
  choose g hg hgf using fun k ↦ hJ (p := p) k (f : 𝓢'(E, F)) (f' k) (hf' k)
  refine ⟨∑ k ∈ Finset.Ico (j - L) (j + L), g k, ?_, ?_⟩
  · simp [window, L, _root_.sum_apply, map_sum, hg, Lp.toTemperedDistribution_sum]
  -- For `k` in the window, `2^{ks} ≤ 2^{|s| L} 2^{js}`.
  have hterm : ∀ k ∈ Finset.Ico (j - L) (j + L),
      ‖g k‖ ≤ C₂ * max C₁ 0 * 2 ^ (|s| * L) * 2 ^ (s * j) * ‖f‖ := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hpow : (2 : ℝ) ^ (s * k) ≤ 2 ^ (|s| * L) * 2 ^ (s * j) := by
      refine Real.rpow_mul_le_rpow_abs_mul_mul_rpow_mul one_le_two s (abs_sub_le_iff.2 ⟨?_, ?_⟩)
      all_goals rw [sub_le_iff_le_add']; exact_mod_cast (by omega)
    calc ‖g k‖ ≤ C₂ * 2 ^ (s * k) * ‖f' k‖ := hgf k
      _ ≤ C₂ * (2 ^ (|s| * L) * 2 ^ (s * j)) * (max C₁ 0 * ‖f‖) := by
        gcongr
        exact (hf'f k).trans (by gcongr; exact le_max_left _ _)
      _ = C₂ * max C₁ 0 * 2 ^ (|s| * L) * 2 ^ (s * j) * ‖f‖ := by ring
  calc ‖∑ k ∈ Finset.Ico (j - L) (j + L), g k‖
      ≤ ∑ k ∈ Finset.Ico (j - L) (j + L), ‖g k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Ico (j - L) (j + L), C₂ * max C₁ 0 * 2 ^ (|s| * L) * 2 ^ (s * j) * ‖f‖ :=
        Finset.sum_le_sum hterm
    _ ≤ 2 * L * (C₂ * max C₁ 0 * 2 ^ (|s| * L) * 2 ^ (s * j) * ‖f‖) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        rw [Nat.card_Ico]
        exact_mod_cast (by omega : j + L - (j - L) ≤ 2 * L)
    _ = 2 * L * (C₂ * max C₁ 0 * 2 ^ (|s| * L)) * 2 ^ (s * j) * ‖f‖ := by ring

/-- The `j`-th term `Wⱼ (2^{-js} bⱼ)` of the synthesis of an `ℓ¹` sequence `b` of `Lᵖ`
functions. -/
private abbrev synthesisTerm (s : ℝ) (b : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) 1)
    (j : ℕ) : 𝓢'(E, F) :=
  window F φ j (((((2 : ℝ) ^ (s * j) : ℝ) : ℂ)⁻¹ • b j : Lp F p (volume : Measure E)) :
    𝓢'(E, F))

/-- **The synthesis estimate.** For an `ℓ¹` sequence `b` of `Lᵖ` functions, the synthesis
`∑ⱼ Wⱼ (2^{-js} bⱼ)` converges in the tempered distributions to an element of `H^{s,p}` of norm
at most `C ‖b‖_{ℓ¹}`. -/
private theorem exists_hasSum_synthesisTerm (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) 1,
      ∃ u : H^{s, p}(E, F), HasSum (synthesisTerm φ s b) u.toDistr ∧ ‖u‖ ≤ C * ‖b‖ := by
  obtain ⟨C, hC, hW⟩ := exists_besselPotential_window_eq_and_norm_le (F := F) φ s
  refine ⟨C, hC, fun b ↦ ?_⟩
  -- `J^s` of the `j`-th term is the `Lᵖ` function `g j`, of norm at most `C ‖bⱼ‖`.
  choose g hg hgb using fun j ↦
    hW (p := p) j ((((2 : ℝ) ^ (s * j) : ℝ) : ℂ)⁻¹ • b j)
  have hbound (j : ℕ) : ‖g j‖ ≤ C * ‖b j‖ := by
    refine (hgb j).trans_eq ?_
    rw [norm_smul, norm_inv, Complex.norm_of_nonneg (by positivity)]
    field_simp
  have hb : Summable fun j ↦ ‖b j‖ := by
    simpa using (memℓp_gen_iff (p := 1) (by simp)).1 (lp.memℓp b)
  have hg' : Summable fun j ↦ ‖g j‖ :=
    (hb.mul_left C).of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbound
  set G := ∑' j, g j
  refine ⟨⟨besselPotential E F (-s) G, G, by simp [besselPotential_besselPotential_apply]⟩, ?_, ?_⟩
  · -- The terms are `J^{-s} (g j)`, which sum to `J^{-s} G` in the tempered distributions.
    have h := (hg'.of_norm.hasSum.map (Lp.toTemperedDistributionCLM F volume p)
      (Lp.toTemperedDistributionCLM F volume p).continuous).map
      (besselPotential E F (-s)) (besselPotential E F (-s)).continuous
    refine h.congr_fun fun j ↦ ?_
    simp only [Function.comp_apply, Lp.toTemperedDistributionCLM_apply]
    exact ((besselPotential_neg_apply_eq_iff s _ _).2 (hg j)).symm
  · rw [← norm_toLp_eq]
    dsimp only
    calc ‖G‖ ≤ ∑' j, ‖g j‖ := norm_tsum_le_tsum_norm hg'
      _ ≤ ∑' j, C * ‖b j‖ := hg'.tsum_le_tsum hbound (hb.mul_left C)
      _ = C * ‖b‖ := by
        rw [tsum_mul_left, lp.norm_eq_tsum_rpow (by simp) b]
        simp

variable (F p) in
/-- The synthesis `b ↦ ∑ⱼ Wⱼ (2^{-js} bⱼ)`, from `ℓ¹_s(Lᵖ)` to `H^{s,p}`. -/
private def synthesis (s : ℝ) :
    lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) 1 →L[ℂ] H^{s, p}(E, F) :=
  have h := exists_hasSum_synthesisTerm (F := F) (p := p) φ s
  LinearMap.mkContinuous
    { toFun b := (h.choose_spec.2 b).choose
      map_add' b b' := BesselPotentialSpace.ext <|
        ((h.choose_spec.2 (b + b')).choose_spec.1.unique <| by
          refine ((h.choose_spec.2 b).choose_spec.1.add
            (h.choose_spec.2 b').choose_spec.1).congr_fun fun j ↦ ?_
          simp [synthesisTerm, smul_add, Lp.toTemperedDistribution_add])
      map_smul' c b := BesselPotentialSpace.ext <|
        ((h.choose_spec.2 (c • b)).choose_spec.1.unique <| by
          refine ((h.choose_spec.2 b).choose_spec.1.const_smul c).congr_fun fun j ↦ ?_
          simp [synthesisTerm, Lp.toTemperedDistribution_smul, smul_smul, mul_comm]) }
    h.choose fun b ↦ (h.choose_spec.2 b).choose_spec.2

private theorem hasSum_synthesis (b : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) 1) :
    HasSum (synthesisTerm φ s b) (synthesis F p φ s b).toDistr :=
  ((exists_hasSum_synthesisTerm (F := F) (p := p) φ s).choose_spec.2 b).choose_spec.1

variable (F p s₀ s₁) in
/-- The synthesis `(aⱼ)ⱼ ↦ ∑ⱼ Wⱼ aⱼ`, from `ℓ¹_{s₀}(Lᵖ) + ℓ¹_{s₁}(Lᵖ)` to
`H^{s₀,p} + H^{s₁,p}`. -/
private def synthesisMap : (weightedLp ℂ (Lp F p (volume : Measure E)) 1 1 s₀ s₁).SumSpace →L[ℂ]
    (besselPotentialSpace E F p s₀ s₁).SumSpace :=
  sumLift _ (fstToSum _ ∘L synthesis F p φ s₀) (sndToSum _ ∘L synthesis F p φ s₁) fun x ↦
    sumSpace_ext _ <| by
      have hx := (weightedLp ℂ (Lp F p (volume : Measure E)) 1 1 s₀ s₁).embed₀_interFst x
      simp only [ContinuousLinearMap.comp_apply, sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum,
        besselPotentialSpace_embed₀_apply, besselPotentialSpace_embed₁_apply]
      refine (hasSum_synthesis φ _).unique ((hasSum_synthesis φ _).congr_fun fun j ↦ ?_)
      have hj := congr_fun hx j
      simp only [weightedLp_embed₀_apply, weightedLp_embed₁_apply] at hj
      exact congrArg (fun f : Lp F p (volume : Measure E) ↦ window F φ j (f : 𝓢'(E, F))) hj

/-- The synthesis of a sequence `a` in `ℓ¹_{s₀}(Lᵖ) + ℓ¹_{s₁}(Lᵖ)` is the sum `∑ⱼ Wⱼ aⱼ` in the
tempered distributions. -/
private theorem hasSum_sumSpaceEmbed_synthesisMap
    (w : (weightedLp ℂ (Lp F p (volume : Measure E)) 1 1 s₀ s₁).SumSpace) :
    HasSum (fun j ↦ window F φ j
        ((weightedLp ℂ (Lp F p (volume : Measure E)) 1 1 s₀ s₁).sumSpaceEmbed w j : 𝓢'(E, F)))
      ((besselPotentialSpace E F p s₀ s₁).sumSpaceEmbed (synthesisMap F p φ s₀ s₁ w)) := by
  obtain ⟨b₀, b₁, rfl⟩ := exists_fstToSum_add_sndToSum_eq _ w
  convert (hasSum_synthesis (s := s₀) φ b₀).add (hasSum_synthesis (s := s₁) φ b₁) using 1
  · funext j
    simp [synthesisTerm, Lp.toTemperedDistribution_add, Lp.toTemperedDistribution_smul]
  · simp [synthesisMap]

end Synthesis

/-! ### The interpolation identity -/

section Equiv

variable [Fact (1 ≤ q)] (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)

/-- The weighted blocks `(2^{j s_θ} Δⱼ u)ⱼ` of an element `u` of `(H^{s₀,p}, H^{s₁,p})_{θ,q}`, as
an `ℓ^q` sequence: the blocks map `(H^{s₀,p}, H^{s₁,p})_{θ,q}` into
`(ℓ^∞_{s₀}(Lᵖ), ℓ^∞_{s₁}(Lᵖ))_{θ,q} = ℓ^q_{s_θ}(Lᵖ)`. -/
private def kMethodWeightedBlocks :
    (besselPotentialSpace E F p s₀ s₁).KMethodSpace θ q →L[ℂ]
      lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q :=
  (weightedLpKMethodEquiv (𝕜 := ℂ) (A := Lp F p (volume : Measure E)) (q₀ := ∞) (q₁ := ∞)
      (q := q) hs hθ : _ →L[ℂ] _) ∘L
    map (blocksMap F p φ s₀ s₁).toLinearMap (T₀ := weightedBlocksCLM F p φ s₀)
      (T₁ := weightedBlocksCLM F p φ s₁) (fun _ ↦ by simp [blocksMap])
      (fun _ ↦ by simp [blocksMap])

private theorem coe_kMethodWeightedBlocks_apply
    (u : (besselPotentialSpace E F p s₀ s₁).KMethodSpace θ q) (j : ℕ) :
    (kMethodWeightedBlocks φ hs hθ u j : 𝓢'(E, F)) =
      (((2 : ℝ) ^ (((1 - θ) * s₀ + θ * s₁) * j) : ℝ) : ℂ) •
        littlewoodPaleyBlock F φ j
          ((besselPotentialSpace E F p s₀ s₁).sumSpaceEmbed (toSumₗ u)) := by
  simp only [kMethodWeightedBlocks, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    weightedLpKMethodEquiv_apply, toSumₗ_map, ContinuousLinearMap.coe_coe]
  refine (Lp.toTemperedDistribution_smul _ _).trans ?_
  rw [coe_sumSpaceEmbed_blocksMap, RCLike.ofReal_eq_complex_ofReal]

/-- The inclusion `(H^{s₀,p}, H^{s₁,p})_{θ,q} → B^{s_θ}_{p,q}`. -/
private def kMethodToBesov :
    (besselPotentialSpace E F p s₀ s₁).KMethodSpace θ q →L[ℂ]
      BesovSpace F φ ((1 - θ) * s₀ + θ * s₁) p q :=
  LinearMap.mkContinuous
    { toFun u := ⟨(besselPotentialSpace E F p s₀ s₁).sumSpaceEmbed (toSumₗ u),
        kMethodWeightedBlocks φ hs hθ u, coe_kMethodWeightedBlocks_apply φ hs hθ u⟩
      map_add' u v := BesovSpace.ext (by simp)
      map_smul' c u := BesovSpace.ext (by simp) }
    ‖(kMethodWeightedBlocks φ hs hθ : (besselPotentialSpace E F p s₀ s₁).KMethodSpace θ q →L[ℂ] _)‖
    fun u ↦ by
      rw [← BesovSpace.norm_weightedBlocks]
      exact (kMethodWeightedBlocks φ hs hθ).le_opNorm u

private theorem toDistr_kMethodToBesov (u : (besselPotentialSpace E F p s₀ s₁).KMethodSpace θ q) :
    (kMethodToBesov φ hs hθ u).toDistr =
      (besselPotentialSpace E F p s₀ s₁).sumSpaceEmbed (toSumₗ u) :=
  (rfl)

/-- The inclusion `B^{s_θ}_{p,q} → (H^{s₀,p}, H^{s₁,p})_{θ,q}`: the weighted blocks of `v` lie in
`ℓ^q_{s_θ}(Lᵖ) = (ℓ¹_{s₀}(Lᵖ), ℓ¹_{s₁}(Lᵖ))_{θ,q}`, and the synthesis maps them back to `v`. -/
private def besovToKMethod :
    BesovSpace F φ ((1 - θ) * s₀ + θ * s₁) p q →L[ℂ]
      (besselPotentialSpace E F p s₀ s₁).KMethodSpace θ q :=
  map (synthesisMap F p φ s₀ s₁).toLinearMap (T₀ := synthesis F p φ s₀)
      (T₁ := synthesis F p φ s₁) (fun _ ↦ by simp [synthesisMap])
      (fun _ ↦ by simp [synthesisMap]) ∘L
    ((weightedLpKMethodEquiv (𝕜 := ℂ) (A := Lp F p (volume : Measure E)) (q₀ := 1) (q₁ := 1)
      (q := q) hs hθ).symm : _ →L[ℂ] _) ∘L
    (BesovSpace.weightedBlocksₗᵢ F φ _ p q).toContinuousLinearMap

private theorem sumSpaceEmbed_toSumₗ_besovToKMethod
    (v : BesovSpace F φ ((1 - θ) * s₀ + θ * s₁) p q) :
    (besselPotentialSpace E F p s₀ s₁).sumSpaceEmbed (toSumₗ (besovToKMethod φ hs hθ v)) =
      v.toDistr := by
  have h := hasSum_sumSpaceEmbed_synthesisMap φ (toSumₗ ((weightedLpKMethodEquiv (𝕜 := ℂ)
    (A := Lp F p (volume : Measure E)) (q₀ := 1) (q₁ := 1) (q := q) hs hθ).symm v.weightedBlocks))
  -- The `j`-th term of the synthesis is `Wⱼ Δⱼ v = Δⱼ v`.
  have hb (j : ℕ) : (weightedLp ℂ (Lp F p (volume : Measure E)) 1 1 s₀ s₁).sumSpaceEmbed
      (toSumₗ ((weightedLpKMethodEquiv (q := q) hs hθ).symm v.weightedBlocks)) j = v.block j := by
    rw [sumSpaceEmbed_toSumₗ_weightedLpKMethodEquiv_symm_apply, BesovSpace.weightedBlocks_apply]
    exact inv_smul_smul₀ (Complex.ofReal_ne_zero.2 (by positivity)) _
  simp only [hb, BesovSpace.coe_block, window_littlewoodPaleyBlock] at h
  simp only [besovToKMethod, ContinuousLinearMap.comp_apply, toSumₗ_map,
    ContinuousLinearMap.coe_coe, LinearIsometry.coe_toContinuousLinearMap,
    BesovSpace.weightedBlocksₗᵢ_apply, ContinuousLinearEquiv.coe_coe]
  exact tendsto_nhds_unique h.tendsto_sum_nat (tendsto_sum_littlewoodPaleyBlock φ v.toDistr)

/-- **Real interpolation of Bessel-potential spaces.** For `s₀ ≠ s₁`, `0 < θ < 1`,
`1 ≤ p ≤ ∞` and `1 ≤ q ≤ ∞`, the real interpolation space `(H^{s₀,p}, H^{s₁,p})_{θ,q}` is the
Besov space `B^{s_θ}_{p,q}` with `s_θ = (1 - θ) s₀ + θ s₁`, with equivalent norms. The
isomorphism keeps the underlying tempered distribution
(`TauCeti.CompatibleCouple.toDistr_besselPotentialSpaceKMethodEquiv_apply`). -/
def besselPotentialSpaceKMethodEquiv :
    (besselPotentialSpace E F p s₀ s₁).KMethodSpace θ q ≃L[ℂ]
      BesovSpace F φ ((1 - θ) * s₀ + θ * s₁) p q :=
  ContinuousLinearEquiv.equivOfInverse (kMethodToBesov φ hs hθ) (besovToKMethod φ hs hθ)
    (fun u ↦ KMethodSpace.ext <| sumSpace_ext _ <| by
      rw [sumSpaceEmbed_toSumₗ_besovToKMethod, toDistr_kMethodToBesov])
    (fun v ↦ BesovSpace.ext <| by
      rw [toDistr_kMethodToBesov, sumSpaceEmbed_toSumₗ_besovToKMethod])

@[simp]
theorem toDistr_besselPotentialSpaceKMethodEquiv_apply
    (u : (besselPotentialSpace E F p s₀ s₁).KMethodSpace θ q) :
    (besselPotentialSpaceKMethodEquiv φ hs hθ u).toDistr =
      (besselPotentialSpace E F p s₀ s₁).sumSpaceEmbed (toSumₗ u) :=
  (rfl)

@[simp]
theorem sumSpaceEmbed_toSumₗ_besselPotentialSpaceKMethodEquiv_symm_apply
    (v : BesovSpace F φ ((1 - θ) * s₀ + θ * s₁) p q) :
    (besselPotentialSpace E F p s₀ s₁).sumSpaceEmbed
        (toSumₗ ((besselPotentialSpaceKMethodEquiv φ hs hθ).symm v)) = v.toDistr :=
  sumSpaceEmbed_toSumₗ_besovToKMethod φ hs hθ v

end Equiv

/-- **Real interpolation of Bessel-potential spaces**, membership form: for `s₀ ≠ s₁`,
`0 < θ < 1` and `1 ≤ q`, an element `u` of `H^{s₀,p} + H^{s₁,p}` lies in
`(H^{s₀,p}, H^{s₁,p})_{θ,q}` exactly when its tempered distribution lies in the Besov space
`B^{s_θ}_{p,q}`, where `s_θ = (1 - θ) s₀ + θ s₁`. -/
theorem mem_kMethod_besselPotentialSpace_iff (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) (hq : 1 ≤ q)
    {u : (besselPotentialSpace E F p s₀ s₁).SumSpace} :
    u ∈ (besselPotentialSpace E F p s₀ s₁).kMethod θ q ↔
      ((besselPotentialSpace E F p s₀ s₁).sumSpaceEmbed u).MemBesov φ
        ((1 - θ) * s₀ + θ * s₁) p q := by
  have : Fact (1 ≤ q) := ⟨hq⟩
  refine ⟨fun hu ↦ ?_, fun hu ↦ ?_⟩
  · simpa using (besselPotentialSpaceKMethodEquiv φ hs hθ (KMethodSpace.mk u hu)).memBesov_toDistr
  · have h := sumSpaceEmbed_toSumₗ_besselPotentialSpaceKMethodEquiv_symm_apply φ hs hθ
      hu.toBesovSpace
    rw [MemBesov.toDistr_toBesovSpace] at h
    rw [← sumSpace_ext _ h]
    exact toSumₗ_mem _

/-- **Real interpolation of Bessel-potential spaces**, image form: for `s₀ ≠ s₁`, `0 < θ < 1`
and `1 ≤ q`, a tempered distribution lies in the Besov space `B^{s_θ}_{p,q}`, where
`s_θ = (1 - θ) s₀ + θ s₁`, exactly when it is the image of an element of
`(H^{s₀,p}, H^{s₁,p})_{θ,q}`. -/
theorem memBesov_iff_exists_mem_kMethod_besselPotentialSpace (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (hq : 1 ≤ q) {v : 𝓢'(E, F)} :
    v.MemBesov φ ((1 - θ) * s₀ + θ * s₁) p q ↔
      ∃ u ∈ (besselPotentialSpace E F p s₀ s₁).kMethod θ q,
        (besselPotentialSpace E F p s₀ s₁).sumSpaceEmbed u = v := by
  refine ⟨fun hv ↦ ?_, ?_⟩
  · have : Fact (1 ≤ q) := ⟨hq⟩
    exact ⟨_, toSumₗ_mem ((besselPotentialSpaceKMethodEquiv φ hs hθ).symm hv.toBesovSpace),
      by simp⟩
  · rintro ⟨u, hu, rfl⟩
    exact (mem_kMethod_besselPotentialSpace_iff φ hs hθ hq).1 hu

end CompatibleCouple

end TauCeti
