/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Normed.Lp.Reindex

/-!
# Reconstruction from pieces with spectra in dyadic balls

Let `s > 0`, `R ∈ ℝ`, `1 ≤ p, q ≤ ∞`, and let `uⱼ ∈ Lᵖ` (`j ≥ 0`) be functions whose Fourier
transforms are carried by the balls of radius `2^j R`, with `(2^{js} ‖uⱼ‖_p)ⱼ ∈ ℓ^q`. Then the
series `∑ⱼ uⱼ` converges in `Lᵖ`, and its sum `u` lies in the Besov space `B^s_{p,q}`, with

`‖u‖_{B^s_{p,q}} ≤ C ‖(2^{js} ‖uⱼ‖_p)ⱼ‖_{ℓ^q}`

for a constant `C` depending only on the bump function, `R` and `s`, and not on `p` or `q`
(`TauCeti.BesovSpace.exists_hasSum_toDistr_eq_and_norm_le`; Bahouri–Chemin–Danchin,
Lemma 2.84). A sequence bounded termwise by `2^{js} ‖uⱼ‖_p` may be used on the right instead.

This is how Besov regularity is recognised for a sum of pieces that are localised in balls rather
than in annuli. The typical example is the resonant term `∑ⱼ Δⱼ f · Δⱼ g` of Bony's paraproduct
decomposition: each product of two blocks of frequency `2^j` has its spectrum in a ball of radius
of order `2^j`, but not in an annulus, and the lemma gives `R(f, g) ∈ 𝒞^{α+β}` when `α + β > 0`.
The hypothesis `s > 0` cannot be dropped: for `s ≤ 0` all the pieces could carry the same low
frequencies, and their sum need not even converge.

## The argument

Let `C₀` bound the blocks `Δₖ` on `Lᵖ` uniformly in `k` and `p`
(`TemperedDistribution.exists_littlewoodPaleyBlock_eq_and_norm_le`), and choose `L`, depending
on `R`, with `Δₖ uⱼ = 0` whenever `j + L ≤ k`: the symbol of `Δₖ` vanishes on a ball containing
the spectrum of `uⱼ` (`TemperedDistribution.exists_littlewoodPaleyBlock_eq_zero_of_isVanishingOn`).
Since `s > 0`, the norms `‖uⱼ‖_p ≤ 2^{-js} ‖w‖` are summable, so the series converges in `Lᵖ`.
Writing the series as `∑ᵢ Tuᵢ` with the shifted sequence `Tuᵢ = u_{i-L}` (and `Tuᵢ = 0` for
`i < L`), only the tail `∑_{m ≥ 0} Tu_{k+m}` contributes to `Δₖ u`, so

`2^{ks} ‖Δₖ u‖_p ≤ C₀ 2^{Ls} ∑_{m ≥ 0} 2^{-ms} Tw_{k+m}`,

where `Tw` is the same shift of a dominating sequence `w`. The right side is a one-sided
convolution of `Tw` with the summable kernel `2^{-ms}`, whose `ℓ^q` norm is at most
`(1 - 2^{-s})⁻¹ ‖Tw‖_{ℓ^q} ≤ (1 - 2^{-s})⁻¹ ‖w‖_{ℓ^q}` (`lp.exists_eq_tsum_smul_add_and_norm_le`).

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Lemma 2.84.
-/

public section

noncomputable section

open MeasureTheory FourierTransform Metric
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti.BesovSpace

open TemperedDistribution

/-- The sequence `x` shifted `M` places to the right and padded with zeros. -/
private def shiftRight {α : Type*} [Zero α] (M : ℕ) (x : ℕ → α) (i : ℕ) : α :=
  if M ≤ i then x (i - M) else 0

private theorem shiftRight_add {α : Type*} [Zero α] (M : ℕ) (x : ℕ → α) (n : ℕ) :
    shiftRight M x (n + M) = x n := by
  simp [shiftRight]

private theorem shiftRight_of_lt {α : Type*} [Zero α] {M i : ℕ} (x : ℕ → α) (hi : i < M) :
    shiftRight M x i = 0 := by
  simp [shiftRight, not_le.2 hi]

/-- The one-sided convolution `k ↦ ∑ₘ rᵐ (Tw)_{k+m}` of the right shift `Tw` of a sequence
`w ∈ ℓ^q` with the geometric kernel `rᵐ`, `0 ≤ r < 1`, converges termwise and lies in `ℓ^q` with
norm at most `(1 - r)⁻¹ ‖w‖`. -/
private theorem exists_hasSum_geometric_shiftRight {q : ℝ≥0∞} [Fact (1 ≤ q)] {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) (w : lp (fun _ : ℕ ↦ ℝ) q) :
    ∃ y : lp (fun _ : ℕ ↦ ℝ) q,
      (∀ k, HasSum (fun m ↦ r ^ m * shiftRight M w (k + m)) (y k)) ∧
        ‖y‖ ≤ (1 - r)⁻¹ * ‖w‖ := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  -- The right shift of `w` lies in `ℓ^q`, with norm at most `‖w‖`: it is `w` reindexed along
  -- `i ↦ i - M`, which is injective on `{i | M ≤ i}`.
  have hinj : {i | M ≤ i}.InjOn (· - M) := fun _ ha _ hb h ↦ tsub_inj_left ha hb h
  let w' : lp (fun _ : ℕ ↦ ℝ) q :=
    ⟨{i | M ≤ i}.indicator (w ∘ (· - M)), (lp.memℓp w).indicator_comp hinj⟩
  have hw' (i : ℕ) : w' i = shiftRight M w i := by
    by_cases hi : M ≤ i <;> simp [w', shiftRight, hi]
  have hgeom : Summable fun m : ℕ ↦ ‖r ^ m‖ := by
    simpa only [norm_pow, Real.norm_of_nonneg hr0] using summable_geometric_of_lt_one hr0 hr1
  obtain ⟨y, hy, hy_norm⟩ := lp.exists_eq_tsum_smul_add_and_norm_le hgeom w'
  refine ⟨y, fun k ↦ ?_, hy_norm.trans ?_⟩
  · have hsum : Summable fun m ↦ r ^ m * w' (k + m) :=
      Summable.of_norm_bounded (hgeom.mul_right ‖w'‖) fun m ↦ (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm hq0 w' _) (norm_nonneg _))
    simpa only [hy k, hw', smul_eq_mul] using hsum.hasSum
  · rw [show (∑' m : ℕ, ‖r ^ m‖) = (1 - r)⁻¹ by
      simpa only [norm_pow, Real.norm_of_nonneg hr0] using tsum_geometric_of_lt_one hr0 hr1]
    exact mul_le_mul_of_nonneg_left
      (lp.norm_le_of_forall_eq_indicator_comp hq0 hinj fun _ ↦ rfl)
      (inv_nonneg.2 (sub_nonneg.2 hr1.le))

/-- **Reconstruction from pieces with spectra in dyadic balls** (Bahouri–Chemin–Danchin,
Lemma 2.84). Let `s > 0`. There is `C`, depending only on `φ`, `R` and `s`, such that for all
`1 ≤ p, q ≤ ∞`: if the Fourier transform of each `uⱼ ∈ Lᵖ` vanishes outside the closed ball of
radius `2^j R`, and `2^{js} ‖uⱼ‖_p ≤ wⱼ` for some `w ∈ ℓ^q`, then `∑ⱼ uⱼ` converges in `Lᵖ` to an
element of the Besov space `B^s_{p,q}` of norm at most `C ‖w‖_{ℓ^q}`. -/
theorem exists_hasSum_toDistr_eq_and_norm_le (φ : ContDiffBump (0 : E)) (R : ℝ) {s : ℝ}
    (hs : 0 < s) :
    ∃ C : ℝ, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {q : ℝ≥0∞} [Fact (1 ≤ q)]
      (u : ℕ → Lp F p (volume : Measure E)) (w : lp (fun _ : ℕ ↦ ℝ) q),
      (∀ j : ℕ, Distribution.IsVanishingOn (𝓕 (u j : 𝓢'(E, F)) : 𝓢'(E, F))
        (closedBall 0 (2 ^ j * R))ᶜ) →
      (∀ j : ℕ, 2 ^ (s * j) * ‖u j‖ ≤ w j) →
      ∃ (v : BesovSpace F φ s p q) (f : Lp F p (volume : Measure E)),
        HasSum u f ∧ v.toDistr = f ∧ ‖v‖ ≤ C * ‖w‖ := by
  obtain ⟨C₀, hC₀⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  obtain ⟨L, hL⟩ := exists_littlewoodPaleyBlock_eq_zero_of_isVanishingOn (F := F) φ R
  set ρ : ℝ := 2 ^ s
  have hρ1 : 1 < ρ := Real.one_lt_rpow one_lt_two hs
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ1
  have hr0 : 0 ≤ ρ⁻¹ := inv_nonneg.2 hρ0.le
  have hr1 : ρ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ1
  have hρr (n : ℕ) : ρ ^ n * ρ⁻¹ ^ n = 1 := by rw [← mul_pow, mul_inv_cancel₀ hρ0.ne', one_pow]
  set C₁ := max C₀ 0
  refine ⟨C₁ * ρ ^ L * (1 - ρ⁻¹)⁻¹, fun {p} _ {q} _ u w hu hw ↦ ?_⟩
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hpow (j : ℕ) : (2 : ℝ) ^ (s * j) = ρ ^ j := Real.rpow_mul_natCast zero_le_two s j
  -- The pieces are bounded by `ρ⁻ʲ wⱼ ≤ ρ⁻ʲ ‖w‖`.
  have hu_le (j : ℕ) : ‖u j‖ ≤ ρ⁻¹ ^ j * w j := by
    rw [inv_pow, inv_mul_eq_div, le_div_iff₀ (pow_pos hρ0 j), mul_comm, ← hpow]
    exact hw j
  have hw_le (j : ℕ) : w j ≤ ‖w‖ := (Real.le_norm_self _).trans (lp.norm_apply_le_norm hq0 w j)
  -- Since `s > 0`, the series converges in `Lᵖ`.
  have hsum : Summable u :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr1).mul_right ‖w‖) fun j ↦
      (hu_le j).trans (mul_le_mul_of_nonneg_left (hw_le j) (pow_nonneg hr0 j))
  set f := ∑' j, u j
  -- Shift the pieces and the dominating sequence `L` places to the right.
  set Tu : ℕ → Lp F p (volume : Measure E) := shiftRight L u
  set Tw : ℕ → ℝ := shiftRight L w
  have hTu : HasSum Tu f := by
    refine (hasSum_nat_add_iff' L).1 ?_
    rw [Finset.sum_eq_zero fun i hi ↦ shiftRight_of_lt u (Finset.mem_range.1 hi), sub_zero]
    simpa only [Tu, shiftRight_add] using hsum.hasSum
  have hblock_Tu {i k : ℕ} (hik : i < k) :
      littlewoodPaleyBlock F φ k (Tu i : 𝓢'(E, F)) = 0 := by
    by_cases hi : L ≤ i
    · simp only [Tu, shiftRight, hi, ↓reduceIte]
      exact hL _ _ _ (hu _) (by omega)
    · simp [Tu, shiftRight_of_lt u (not_le.1 hi)]
  have hTu_norm (i : ℕ) : ‖Tu i‖ ≤ ρ ^ L * (ρ⁻¹ ^ i * Tw i) := by
    by_cases hi : L ≤ i
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + L := ⟨i - L, by omega⟩
      simp only [Tu, Tw, shiftRight_add]
      calc ‖u j‖ ≤ ρ⁻¹ ^ j * w j := hu_le j
        _ = ρ ^ L * (ρ⁻¹ ^ (j + L) * w j) := by
            rw [pow_add]
            linear_combination (-(ρ⁻¹ ^ j * w j)) * hρr L
    · simp [Tu, Tw, shiftRight_of_lt _ (not_le.1 hi)]
  -- The dominating sequence: the one-sided convolution of `Tw` with the kernel `ρ⁻ᵐ`.
  obtain ⟨y, hy, hy_norm⟩ := exists_hasSum_geometric_shiftRight hr0 hr1 L w
  -- Only the tail of the shifted series contributes to the `k`-th block.
  set tail : ℕ → Lp F p (volume : Measure E) := fun k ↦ f - ∑ i ∈ Finset.range k, Tu i
  have htail (k : ℕ) : HasSum (fun m ↦ Tu (m + k)) (tail k) := (hasSum_nat_add_iff' k).2 hTu
  have hblock_tail (k : ℕ) : littlewoodPaleyBlock F φ k (tail k : 𝓢'(E, F)) =
      littlewoodPaleyBlock F φ k (f : 𝓢'(E, F)) := by
    simp only [tail]
    rw [Lp.toTemperedDistribution_sub, map_sub,
      show ((∑ i ∈ Finset.range k, Tu i : Lp F p volume) : 𝓢'(E, F)) =
        ∑ i ∈ Finset.range k, (Tu i : 𝓢'(E, F)) from
        map_sum (Lp.toTemperedDistributionCLM F volume p) _ _,
      map_sum, Finset.sum_eq_zero fun i hi ↦ hblock_Tu (Finset.mem_range.1 hi), sub_zero]
  have htail_norm (k : ℕ) : ‖tail k‖ ≤ ρ ^ L * ρ⁻¹ ^ k * y k :=
    (htail k).norm_le_of_bounded ((hy k).mul_left _) fun m ↦
      (hTu_norm (m + k)).trans_eq (by rw [add_comm m k, pow_add]; ring)
  -- The blocks of the sum, as `Lᵖ` functions, and their weighted bounds.
  choose b hb hbn using fun k ↦ hC₀ k (tail k)
  have hbk (k : ℕ) : 2 ^ (s * k) * ‖b k‖ ≤ C₁ * ρ ^ L * y k := by
    rw [hpow]
    calc ρ ^ k * ‖b k‖ ≤ ρ ^ k * (C₁ * (ρ ^ L * ρ⁻¹ ^ k * y k)) := by
          gcongr
          exact (hbn k).trans (mul_le_mul (le_max_left _ _) (htail_norm k) (norm_nonneg _)
            (le_max_right _ _))
      _ = C₁ * ρ ^ L * y k := by
          linear_combination (C₁ * ρ ^ L * y k) * hρr k
  have hmem : Memℓp (fun k : ℕ ↦ (((2 : ℝ) ^ (s * k) : ℝ) : ℂ) • b k) q :=
    ((lp.memℓp y).const_smul (C₁ * ρ ^ L)).mono fun k ↦ by
      rw [norm_smul, Complex.norm_of_nonneg (by positivity), Pi.smul_apply, smul_eq_mul]
      exact hbk k
  let B : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q := ⟨_, hmem⟩
  have hB (k : ℕ) : B k = (((2 : ℝ) ^ (s * k) : ℝ) : ℂ) • b k := (rfl)
  let v : BesovSpace F φ s p q := ⟨f, B, fun k ↦ by
    rw [hB, Lp.toTemperedDistribution_smul, ← hb k, hblock_tail]⟩
  refine ⟨v, f, hsum.hasSum, rfl, ?_⟩
  calc ‖v‖ = ‖B‖ := (norm_weightedBlocks v).symm
    _ ≤ ‖(C₁ * ρ ^ L) • y‖ := lp.norm_mono hq0 fun k ↦ by
        rw [hB, norm_smul, Complex.norm_of_nonneg (by positivity), lp.coeFn_smul, Pi.smul_apply,
          smul_eq_mul]
        exact (hbk k).trans (Real.le_norm_self _)
    _ = C₁ * ρ ^ L * ‖y‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ C₁ * ρ ^ L * ((1 - ρ⁻¹)⁻¹ * ‖w‖) := by gcongr
    _ = C₁ * ρ ^ L * (1 - ρ⁻¹)⁻¹ * ‖w‖ := by ring

end TauCeti.BesovSpace
