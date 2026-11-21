/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.Bernstein
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Almost diagonal operators on Besov spaces

Let `T` be a continuous linear map of tempered distributions which moves frequencies between the
Littlewood–Paley blocks only a little: for a real number `N`, the block `Δⱼ T Δₖ u` is an `Lᵖ`
function with

`‖Δⱼ T Δₖ u‖_p ≤ K 2^{-N |j - k|} ‖Δₖ u‖_p`.

If `N > |s|`, then `T` maps `B^s_{p,q}` boundedly to itself, for all `1 ≤ p, q ≤ ∞`
(`TauCeti.BesovSpace.exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_le`). Indeed the
weighted interaction `2^{js} 2^{-N |j - k|} 2^{-ks}` of the blocks `j` and `k` is at most
`r^{|j - k|}` with `r = 2^{|s| - N} < 1`, so the weighted blocks of `T u` are the row sums of a
matrix with geometric decay away from the diagonal, applied to the weighted blocks of `u`. Grouping
the terms by the offset `d = k - j ∈ ℤ` gives a series in `ℓ^q(ℕ, Lᵖ)` whose `d`-th term has norm
`O(r^{|d|} ‖u‖)` (`lp.exists_hasSum_and_norm_le_of_summable`).

Multiplication by a smooth function and pullback by a diffeomorphism with bounded derivatives are
almost diagonal in this sense, and this is how they are shown to be bounded on Besov spaces. For
the blocks above the diagonal the decay comes from smoothness: if the derivatives of order `M` of
a tempered distribution `T` along an orthonormal basis are `Lᵖ` functions of norm at most `A`,
then the reverse Bernstein inequality on the `(j+1)`-st dyadic annulus bounds the block
`Δ_{j+1} T` by a constant multiple of `2^{-jM} A`
(`TauCeti.exists_norm_littlewoodPaleyBlock_succ_le_of_iteratedLineDerivOp`).

## References

* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §2.8.
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Springer, 1976, §6.4.
-/

public section

noncomputable section

open MeasureTheory Distribution
open scoped ENNReal SchwartzMap LineDeriv FourierTransform

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti

open TemperedDistribution

/-- **Blocks of a smooth distribution.** Let `M` be a natural number. There is `C`, depending only
on `φ` and `M`, with the following property. Let the block `Δ_{j+1} T` of a tempered distribution
be an `Lᵖ` function `w`, and let the derivatives `∂_{b_{i₁}} ⋯ ∂_{b_{i_M}} T` of order `M` along
the standard orthonormal basis `b` be `Lᵖ` functions of norm at most `A`. Then
`‖w‖_p ≤ C A / (2^j)^M`. -/
theorem exists_norm_littlewoodPaleyBlock_succ_le_of_iteratedLineDerivOp
    (φ : ContDiffBump (0 : E)) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j : ℕ) (T : 𝓢'(E, F))
      (w : Lp F p (volume : Measure E)), littlewoodPaleyBlock F φ (j + 1) T = w → ∀ {A : ℝ},
      (∀ i : Fin M → Fin (Module.finrank ℝ E), ∃ y : Lp F p (volume : Measure E),
        ∂^{⇑(stdOrthonormalBasis ℝ E) ∘ i} T = y ∧ ‖y‖ ≤ A) →
      ‖w‖ ≤ C * A / (2 ^ j) ^ M := by
  set b := stdOrthonormalBasis ℝ E
  obtain ⟨Cr, hCr, hrev⟩ :=
    exists_norm_littlewoodPaleyBlock_succ_le_sum_of_iteratedLineDerivOp_eq (F := F) φ b
  obtain ⟨CΔ, hΔ⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  have hrIn := φ.rIn_pos
  refine ⟨(Cr / φ.rIn) ^ M * Module.finrank ℝ E ^ M * max CΔ 0, by positivity,
    fun {p} _ j T w hw {A} hA ↦ ?_⟩
  -- Its derivatives are the blocks of those of `T`.
  choose y hy hyn using hA
  choose z hz hzn using fun i ↦ hΔ (j + 1) (y i)
  have hder (i : Fin M → Fin (Module.finrank ℝ E)) : ∂^{⇑b ∘ i} (w : 𝓢'(E, F)) = z i := by
    rw [← hw, ← littlewoodPaleyBlock_iteratedLineDerivOp, hy i, hz i]
  calc ‖w‖ ≤ (Cr / (2 ^ j * φ.rIn)) ^ M * ∑ i, ‖z i‖ := hrev M j T w z hw hder
    _ ≤ (Cr / (2 ^ j * φ.rIn)) ^ M * ∑ _i : Fin M → Fin (Module.finrank ℝ E), max CΔ 0 * A := by
        gcongr with i
        exact (hzn i).trans (mul_le_mul (le_max_left _ _) (hyn i) (norm_nonneg _)
          (le_max_right _ _))
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, div_pow, mul_pow]
        push_cast
        field_simp

/-- **Off-diagonal decay between Littlewood–Paley blocks.** Let `T` be a map of tempered
distributions and `M` a natural number, and let `1 ≤ p ≤ ∞`. Suppose that every block `Δⱼ T f`
of an `Lᵖ` function `f` is an `Lᵖ` function of norm at most `K₀ ‖f‖_p`, that for `j > k` and `f`
with spectrum in the ball of radius `2^k φ.rOut` it has norm at most `K₁ (2^k / 2^j)^M ‖f‖_p`,
and that for `f` with spectrum in the annulus `R ≤ ‖ξ‖ ≤ (2 φ.rOut / φ.rIn) R` it has norm at
most `K₂ (2^j / R)^M ‖f‖_p`. If the block `Δₖ u` of a tempered distribution is an `Lᵖ` function
`f`, then every block `Δⱼ T f` is an `Lᵖ` function of norm at most
`(K₁ + K₂ (2 / φ.rIn)^M + K₀) 2^{-M |j - k|} ‖f‖_p`. -/
theorem exists_littlewoodPaleyBlock_eq_and_norm_le_of_ball_of_annulus (φ : ContDiffBump (0 : E))
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (T : 𝓢'(E, F) → 𝓢'(E, F)) {M : ℕ} {K₀ K₁ K₂ : ℝ} (hK₀ : 0 ≤ K₀)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₀ : ∀ (j : ℕ) (f : Lp F p (volume : Measure E)), ∃ v : Lp F p (volume : Measure E),
      littlewoodPaleyBlock F φ j (T f) = v ∧ ‖v‖ ≤ K₀ * ‖f‖)
    (h₁ : ∀ {j k : ℕ}, k < j → ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (Metric.closedBall 0 (2 ^ k * φ.rOut))ᶜ →
      ∃ v : Lp F p (volume : Measure E), littlewoodPaleyBlock F φ j (T f) = v ∧
        ‖v‖ ≤ K₁ * ((2 : ℝ) ^ k / 2 ^ j) ^ M * ‖f‖)
    (h₂ : ∀ (j : ℕ) {R : ℝ}, 0 < R → ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F))
        (Metric.ball 0 R ∪ (Metric.closedBall 0 (2 * φ.rOut / φ.rIn * R))ᶜ) →
      ∃ v : Lp F p (volume : Measure E), littlewoodPaleyBlock F φ j (T f) = v ∧
        ‖v‖ ≤ K₂ * ((2 : ℝ) ^ j / R) ^ M * ‖f‖)
    (j k : ℕ) (u : 𝓢'(E, F)) (f : Lp F p (volume : Measure E))
    (hf : littlewoodPaleyBlock F φ k u = f) :
    ∃ v : Lp F p (volume : Measure E), littlewoodPaleyBlock F φ j (T f) = v ∧
      ‖v‖ ≤ (K₁ + K₂ * (2 / φ.rIn) ^ M + K₀) * (2 : ℝ) ^ (-(M * |(j : ℝ) - k|)) * ‖f‖ := by
  have hrIn := φ.rIn_pos
  have h₂' : 0 ≤ K₂ * (2 / φ.rIn) ^ M := by positivity
  have hK (K : ℝ) (hKK : K ≤ K₁ + K₂ * (2 / φ.rIn) ^ M + K₀) :
      K * (2 : ℝ) ^ (-(M * |(j : ℝ) - k|)) * ‖f‖ ≤
        (K₁ + K₂ * (2 / φ.rIn) ^ M + K₀) * (2 : ℝ) ^ (-(M * |(j : ℝ) - k|)) * ‖f‖ := by
    gcongr
  rcases lt_trichotomy k j with hkj | rfl | hjk
  · -- High output frequency: the block `f` is band-limited to the ball of radius `2^k φ.rOut`.
    obtain ⟨v, hv, hvn⟩ := h₁ hkj f (hf ▸ isVanishingOn_fourier_littlewoodPaleyBlock φ k u)
    refine ⟨v, hv, (hvn.trans_eq ?_).trans (hK K₁ (by linarith))⟩
    rw [Real.pow_div_pow_pow_eq_rpow_of_le two_pos hkj.le]
  · -- Equal frequencies: `T` and the block are bounded on `Lᵖ`.
    obtain ⟨v, hv, hvn⟩ := h₀ k f
    refine ⟨v, hv, ?_⟩
    calc ‖v‖ ≤ K₀ * (2 : ℝ) ^ (-(M * |(k : ℝ) - k|)) * ‖f‖ := by simpa using hvn
      _ ≤ _ := hK _ (by linarith)
  · -- High input frequency: the block `f` has spectrum in the `k`-th dyadic annulus.
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hR : (0 : ℝ) < 2 ^ k * φ.rIn := by positivity
    obtain ⟨v, hv, hvn⟩ := h₂ j hR f (by
      rw [φ.two_mul_rOut_div_rIn_mul, ← hf]
      simpa only [Set.compl_sdiff, Set.union_comm] using
        isVanishingOn_fourier_littlewoodPaleyBlock_succ φ k u)
    refine ⟨v, hv, (hvn.trans_eq ?_).trans (hK (K₂ * (2 / φ.rIn) ^ M) (by linarith))⟩
    rw [abs_sub_comm, ← Real.pow_div_pow_pow_eq_rpow_of_le two_pos hjk.le, div_pow, div_pow,
      div_pow, mul_pow, pow_succ]
    field_simp
    ring

namespace BesovSpace

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **Almost diagonal operators are bounded on Besov spaces.** Let `T` be a continuous linear map
of tempered distributions, `N` a real number with `|s| < N` and `u ∈ B^s_{p,q}`. If every block
`Δⱼ T Δₖ u` is an `Lᵖ` function of norm at most `K 2^{-N |j - k|} ‖Δₖ u‖_p`, then `T u` lies in
`B^s_{p,q}`, with norm at most `K ∑_{d ∈ ℤ} r^{|d|} ‖u‖` for `r = 2^{|s| - N} < 1`. -/
theorem exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_le
    (T : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F)) {N : ℝ} (hN : |s| < N) {K : ℝ} (hK : 0 ≤ K)
    (u : BesovSpace F φ s p q)
    (hT : ∀ j k : ℕ, ∃ v : Lp F p (volume : Measure E),
      littlewoodPaleyBlock F φ j (T (u.block k : 𝓢'(E, F))) = v ∧
        ‖v‖ ≤ K * (2 : ℝ) ^ (-(N * |(j : ℝ) - k|)) * ‖u.block k‖) :
    ∃ v : BesovSpace F φ s p q, v.toDistr = T u.toDistr ∧
      ‖v‖ ≤ K * (∑' d : ℤ, ((2 : ℝ) ^ (|s| - N)) ^ d.natAbs) * ‖u‖ := by
  set r : ℝ := 2 ^ (|s| - N)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  set c : ℕ → ℂ := fun j ↦ (((2 : ℝ) ^ (s * j) : ℝ) : ℂ)
  choose v hv hvn using hT
  -- `2^{js} Δⱼ T Δₖ u` is dominated by `K r^{|k - j|}` times the weighted block `2^{ks} Δₖ u`.
  have hentry (j k : ℕ) :
      ‖c j • v j k‖ ≤ K * r ^ ((k : ℤ) - j).natAbs * ‖u.weightedBlocks k‖ := by
    have hexp : s * j + -(N * |(j : ℝ) - k|) ≤ (|s| - N) * |(j : ℝ) - k| + s * k := by
      have := (le_abs_self (s * (j - k))).trans_eq (abs_mul s ((j : ℝ) - k))
      nlinarith
    have hr : r ^ ((k : ℤ) - j).natAbs = (2 : ℝ) ^ ((|s| - N) * |(j : ℝ) - k|) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, Nat.cast_natAbs, Int.cast_abs,
        abs_sub_comm, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
    rw [norm_smul, Complex.norm_of_nonneg (by positivity), u.norm_weightedBlocks_apply k, hr]
    calc (2 : ℝ) ^ (s * j) * ‖v j k‖
        ≤ (2 : ℝ) ^ (s * j) * (K * (2 : ℝ) ^ (-(N * |(j : ℝ) - k|)) * ‖u.block k‖) := by
          gcongr
          exact hvn j k
      _ = K * (2 : ℝ) ^ (s * j + -(N * |(j : ℝ) - k|)) * ‖u.block k‖ := by
          rw [Real.rpow_add two_pos]
          ring
      _ ≤ K * (2 : ℝ) ^ ((|s| - N) * |(j : ℝ) - k| + s * k) * ‖u.block k‖ := by
          gcongr
          exact one_le_two
      _ = _ := by
          rw [Real.rpow_add two_pos]
          ring
  have hsum : Summable fun d : ℤ ↦ r ^ d.natAbs :=
    summable_int_iff_summable_nat_and_neg.2
      ⟨by simpa using summable_geometric_of_lt_one hr0 hr1,
        by simpa using summable_geometric_of_lt_one hr0 hr1⟩
  obtain ⟨W, hWj, hWn⟩ := lp.exists_hasSum_and_norm_le_of_summable u.weightedBlocks
    (fun d ↦ by positivity) hsum hK (fun j k ↦ c j • v j k) hentry
  -- The tempered distribution of `W j` is `2^{js} Δⱼ T u`, the limit of
  -- `2^{js} Δⱼ T ∑_{k < n} Δₖ u`.
  have hW (j : ℕ) : (W j : 𝓢'(E, F)) = c j • littlewoodPaleyBlock F φ j (T u.toDistr) := by
    have h₁ := ((Lp.toTemperedDistributionCLM F volume p).continuous.tendsto _).comp
      (hWj j).tendsto_sum_nat
    have h₂ := ((c j • (littlewoodPaleyBlock F φ j ∘L T)).continuous.tendsto _).comp
      (tendsto_sum_littlewoodPaleyBlock φ u.toDistr)
    refine tendsto_nhds_unique h₁ (h₂.congr fun n ↦ ?_)
    simp only [Function.comp_apply, map_sum, map_smul, smul_apply,
      ContinuousLinearMap.comp_apply, Lp.toTemperedDistributionCLM_apply]
    simp_rw [← u.coe_block, hv]
  refine ⟨⟨T u.toDistr, W, hW⟩, rfl, ?_⟩
  rw [← norm_weightedBlocks, ← u.norm_weightedBlocks]
  exact hWn.trans_eq (by ring)

end BesovSpace

end TauCeti
