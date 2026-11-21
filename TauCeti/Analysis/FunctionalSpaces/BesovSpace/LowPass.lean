/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Normed.Lp.Reindex

/-!
# The low-frequency cut-offs of a Besov space element

Let `Δⱼ` be the inhomogeneous Littlewood–Paley blocks of a bump function `φ`
(`TemperedDistribution.littlewoodPaleyBlock`). The **low-frequency cut-off** of an element `u` of
a Besov space `B^s_{p,q}` is the `Lᵖ` function `S_m u = ∑_{k < m} Δₖ u`. For `m ≥ 1` it is the
Fourier multiplier by `φ (2^{1-m} ·)`, so its spectrum lies in a ball of radius `O(2^m)`, and only
finitely many of its own blocks are nonzero. As a tempered distribution it is the dyadic partial
sum `TauCeti.BesovSpace.partialSumCLM`, through which it lies in every Besov space built on `Lᵖ`.
If the blocks of `u` are `Lᵖ` limits of Schwartz functions, so is `S_m u`. The size of `S_m u`
itself is bounded uniformly in `m` when `u` is an `Lᵖ` function (in particular for `s > 0`, where
`S_m u → toLpCLM u`), and geometrically in `m` when `s < 0` (with an `ℓ^q`-weighted bound).

## Main declarations

* `TauCeti.BesovSpace.lowPass`: the low-frequency cut-off `S_m u = ∑_{k < m} Δₖ u` as an `Lᵖ`
  function; `TauCeti.BesovSpace.coe_lowPass_succ` identifies `S_{m+1}` with the Fourier
  multiplier by `φ (2^{-m} ·)`.
* `TauCeti.BesovSpace.isVanishingOn_fourier_lowPass_succ`: `S_{m+1} u` has spectrum in the ball of
  radius `2^m φ.rOut`.
* `TauCeti.BesovSpace.exists_littlewoodPaleyBlock_lowPass_eq_zero`: the blocks of `S_m u` vanish
  from index `m + L` on, for an `L` depending only on the bump function.
* `TauCeti.BesovSpace.lowPass_mem_closure_range_toLp`: if the blocks of `u` are `Lᵖ` limits of
  Schwartz functions, so is `S_m u`.
* `TauCeti.BesovSpace.norm_lowPass_le_of_toDistr_eq`, `TauCeti.BesovSpace.norm_lowPass_le_of_pos`,
  `TauCeti.BesovSpace.tendsto_lowPass`, `TauCeti.BesovSpace.norm_lowPass_le_of_neg`, and
  `TauCeti.BesovSpace.exists_lp_lowPass_le_of_neg`: the size and convergence of the low-frequency
  cut-offs.
* `TauCeti.BesovSpace.lowPass_one_succ`, `TauCeti.BesovSpace.lowPass_one`: the cut-offs of `1`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory Metric Filter Distribution FourierTransform TemperedDistribution
open scoped ENNReal SchwartzMap Topology

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti.BesovSpace

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The **low-frequency cut-off** `S_m u = ∑_{k < m} Δₖ u` of an element of a Besov space, as an
`Lᵖ` function: the sum of the Littlewood–Paley blocks of index less than `m`. For `m ≥ 1` it is
the Fourier multiplier by `φ (2^{1-m} ·)` (`TauCeti.BesovSpace.coe_lowPass_succ`). -/
def lowPass (u : BesovSpace F φ s p q) (m : ℕ) : Lp F p (volume : Measure E) :=
  ∑ k ∈ Finset.range m, u.block k

/-- Unfolding `TauCeti.BesovSpace.lowPass`. -/
theorem lowPass_eq_sum (u : BesovSpace F φ s p q) (m : ℕ) :
    u.lowPass m = ∑ k ∈ Finset.range m, u.block k :=
  (rfl)

@[simp]
theorem lowPass_zero_right (u : BesovSpace F φ s p q) : u.lowPass 0 = 0 := by
  simp [lowPass_eq_sum]

theorem lowPass_succ (u : BesovSpace F φ s p q) (m : ℕ) :
    u.lowPass (m + 1) = u.lowPass m + u.block m := by
  simp [lowPass_eq_sum, Finset.sum_range_succ]

@[simp]
theorem lowPass_zero (m : ℕ) : (0 : BesovSpace F φ s p q).lowPass m = 0 := by
  simp [lowPass_eq_sum]

@[simp]
theorem lowPass_add (u v : BesovSpace F φ s p q) (m : ℕ) :
    (u + v).lowPass m = u.lowPass m + v.lowPass m := by
  simp [lowPass_eq_sum, Finset.sum_add_distrib]

@[simp]
theorem lowPass_smul (c : ℂ) (u : BesovSpace F φ s p q) (m : ℕ) :
    (c • u).lowPass m = c • u.lowPass m := by
  simp [lowPass_eq_sum, Finset.smul_sum]

@[simp]
theorem lowPass_neg (u : BesovSpace F φ s p q) (m : ℕ) : (-u).lowPass m = -u.lowPass m := by
  simp [lowPass_eq_sum]

@[simp]
theorem lowPass_sub (u v : BesovSpace F φ s p q) (m : ℕ) :
    (u - v).lowPass m = u.lowPass m - v.lowPass m := by
  simp [lowPass_eq_sum]

/-- The `Lᵖ` function `u.lowPass m` is the sum `∑_{k < m} Δₖ u` of the Littlewood–Paley blocks of
the tempered distribution of `u`. -/
@[simp]
theorem coe_lowPass (u : BesovSpace F φ s p q) (m : ℕ) :
    (u.lowPass m : 𝓢'(E, F)) = ∑ k ∈ Finset.range m, littlewoodPaleyBlock F φ k u.toDistr := by
  simp [lowPass_eq_sum]

/-- The low-frequency cut-off `S_{m+1}` is the Fourier multiplier by `φ (2^{-m} ·)`. -/
theorem coe_lowPass_succ (u : BesovSpace F φ s p q) (m : ℕ) :
    (u.lowPass (m + 1) : 𝓢'(E, F)) =
      fourierMultiplierCLM F (fun ξ ↦ (φ (((2 : ℝ) ^ m)⁻¹ • ξ) : ℂ)) u.toDistr := by
  rw [coe_lowPass, ← _root_.sum_apply, sum_littlewoodPaleyBlock_range]

/-- Elements of two Besov spaces with the same tempered distribution have the same low-frequency
cut-offs. -/
theorem lowPass_eq_of_toDistr_eq {s' : ℝ} {q' : ℝ≥0∞} {u : BesovSpace F φ s p q}
    {v : BesovSpace F φ s' p q'} (h : u.toDistr = v.toDistr) (m : ℕ) :
    u.lowPass m = v.lowPass m := by
  simp only [lowPass_eq_sum, block_eq_of_toDistr_eq h]

/-- **The spectrum of a low-frequency cut-off.** The Fourier transform of `S_{m+1} u` vanishes
outside the closed ball of radius `2^m φ.rOut`. -/
theorem isVanishingOn_fourier_lowPass_succ (u : BesovSpace F φ s p q) (m : ℕ) :
    IsVanishingOn (𝓕 (u.lowPass (m + 1) : 𝓢'(E, F)) : 𝓢'(E, F))
      (closedBall 0 (2 ^ m * φ.rOut))ᶜ := by
  rw [coe_lowPass]
  exact isVanishingOn_fourier_sum_littlewoodPaleyBlock φ
    (fun k hk ↦ Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) _

/-- **The low-frequency cut-offs are band-limited.** There is `L`, depending only on `φ`, such
that the blocks `Δₖ S_m u` vanish for `k ≥ m + L`. -/
theorem exists_littlewoodPaleyBlock_lowPass_eq_zero :
    ∃ L : ℕ, ∀ {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] (u : BesovSpace F φ s p q) (m k : ℕ),
      m + L ≤ k → littlewoodPaleyBlock F φ k (u.lowPass m : 𝓢'(E, F)) = 0 := by
  obtain ⟨L, hL⟩ := exists_sum_littlewoodPaleyBlock_littlewoodPaleyBlock (F := F) φ
  refine ⟨L, fun u m k hk ↦ ?_⟩
  rcases m with _ | N
  · simp
  · rw [coe_lowPass]
    exact (hL k N).2 (by omega) u.toDistr

/-- If every block `Δⱼ u` is a limit of Schwartz functions in `Lᵖ`, then so is every
low-frequency cut-off `S_m u = ∑_{k < m} Δₖ u`. -/
theorem lowPass_mem_closure_range_toLp {u : BesovSpace F φ s p q}
    (hblock : ∀ j, u.block j ∈ closure (Set.range fun f : 𝓢(E, F) ↦ f.toLp p)) (m : ℕ) :
    u.lowPass m ∈ closure (Set.range fun f : 𝓢(E, F) ↦ f.toLp p) := by
  -- The `Lᵖ` closure of the Schwartz functions is a subspace.
  have hS := SchwartzMap.closure_range_toLp_eq (F := F) (μ := (volume : Measure E)) p
  rw [hS, lowPass_eq_sum]
  exact Submodule.sum_mem _ fun j _ ↦ by rw [← SetLike.mem_coe, ← hS]; exact hblock j

/-- **The low-frequency cut-offs of an `Lᵖ` function are uniformly bounded.** If the tempered
distribution of `u` is an `Lᵖ` function `f`, then `‖S_m u‖_p ≤ ‖𝓕⁻ φ‖₁ ‖f‖_p` for every `m`. -/
theorem norm_lowPass_le_of_toDistr_eq (u : BesovSpace F φ s p q)
    {f : Lp F p (volume : Measure E)} (hf : u.toDistr = f) (m : ℕ) :
    ‖u.lowPass m‖ ≤ (∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖) * ‖f‖ := by
  rcases m with _ | m
  · simpa using mul_nonneg (MeasureTheory.integral_nonneg fun _ ↦ norm_nonneg _) (norm_nonneg f)
  obtain ⟨g, hg, hgf⟩ := exists_sum_littlewoodPaleyBlock_eq_and_norm_le φ m f
  -- `S_{m+1} u` and `g` are the same tempered distribution, hence the same `Lᵖ` function.
  have h : u.lowPass (m + 1) = g :=
    LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
      simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply]
      rw [coe_lowPass, hf, hg]
  rwa [h]

/-- **The low-frequency cut-offs at negative regularity.** If `u ∈ B^s_{p,q}` with `s < 0`, then
`‖S_m u‖_p ≤ 2^{-s m} ‖u‖ / (2^{-s} - 1)`. -/
theorem norm_lowPass_le_of_neg [Fact (1 ≤ q)] (hs : s < 0) (u : BesovSpace F φ s p q) (m : ℕ) :
    ‖u.lowPass m‖ ≤ 2 ^ (-s * m) / (2 ^ (-s) - 1) * ‖u‖ :=
  (norm_sum_le _ _).trans (sum_norm_block_le_of_neg hs u m)

/-- For every `m ≥ 1`, the low-frequency cut-off `S_m 1` of `1 ∈ B^s_{∞,q}` equals `1 ∈ L^∞`. -/
@[simp] theorem lowPass_one_succ (m : ℕ) : (1 : BesovSpace ℂ φ s ∞ q).lowPass (m + 1) = 1 := by
  induction m with
  | zero => rw [lowPass_succ, lowPass_zero_right, block_one_zero, zero_add]
  | succ m ih => rw [lowPass_succ, ih, block_one_succ, add_zero]

/-- The low-frequency cut-off `S_m 1` of `1 ∈ B^s_{∞,q}` is `0` at `m = 0` and `1` for `m ≥ 1`. -/
theorem lowPass_one (m : ℕ) : (1 : BesovSpace ℂ φ s ∞ q).lowPass m = if m = 0 then 0 else 1 := by
  rcases m with _ | m <;> simp

/-- For `s > 0`, the low-frequency cut-offs `S_m u` converge in `Lᵖ` to `toLpCLM F φ p q hs u`. -/
theorem tendsto_lowPass [Fact (1 ≤ q)] (hs : 0 < s) (u : BesovSpace F φ s p q) :
    Tendsto u.lowPass atTop (𝓝 (toLpCLM F φ p q hs u)) :=
  (hasSum_block hs u).tendsto_sum_nat.congr fun m ↦ (u.lowPass_eq_sum m).symm

/-- For `s > 0`, the low-frequency cut-offs `S_m u` are bounded in `Lᵖ` uniformly in `m`. -/
theorem norm_lowPass_le_of_pos [Fact (1 ≤ q)] (hs : 0 < s) (u : BesovSpace F φ s p q) (m : ℕ) :
    ‖u.lowPass m‖ ≤ (∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖) * (1 - 2 ^ (-s))⁻¹ * ‖u‖ := by
  calc ‖u.lowPass m‖ ≤ (∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖) * ‖toLpCLM F φ p q hs u‖ :=
        u.norm_lowPass_le_of_toDistr_eq (coe_toLpCLM hs u).symm m
    _ ≤ (∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖) * ((1 - 2 ^ (-s))⁻¹ * ‖u‖) :=
        mul_le_mul_of_nonneg_left (norm_toLpCLM_apply_le hs u)
          (MeasureTheory.integral_nonneg fun _ ↦ norm_nonneg _)
    _ = _ := by ring

/-- **Weighted `ℓ^q` bound for the low-frequency cut-offs at negative regularity.** For `s < 0` and
`u ∈ B^s_{p,q}`, the sequence `2^{s m} ‖S_m u‖_p` is bounded pointwise by a nonnegative sequence
`a ∈ ℓ^q` of norm at most `(2^{-s} - 1)⁻¹ ‖u‖`. -/
theorem exists_lp_lowPass_le_of_neg [Fact (1 ≤ q)] (hs : s < 0) (u : BesovSpace F φ s p q) :
    ∃ a : lp (fun _ : ℕ ↦ ℝ) q, (∀ m, 0 ≤ a m) ∧
      (∀ m : ℕ, 2 ^ (s * m) * ‖u.lowPass m‖ ≤ a m) ∧ ‖a‖ ≤ (2 ^ (-s) - 1)⁻¹ * ‖u‖ := by
  have hr1 : (2 : ℝ) ^ s < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two hs
  obtain ⟨a, ha, han⟩ := lp.exists_forall_eq_sum_pow_smul_and_norm_le
    (lp.toNorm u.weightedBlocks) (by positivity) hr1
  have hratio : (2 : ℝ) ^ s * (1 - 2 ^ s)⁻¹ = (2 ^ (-s) - 1)⁻¹ := by
    have hmul : (2 : ℝ) ^ s * 2 ^ (-s) = 1 := by rw [← Real.rpow_add two_pos]; simp
    refine eq_inv_of_mul_eq_one_left ?_
    calc (2 : ℝ) ^ s * (1 - 2 ^ s)⁻¹ * (2 ^ (-s) - 1)
        = (2 ^ s * 2 ^ (-s) - 2 ^ s) * (1 - 2 ^ s)⁻¹ := by ring
      _ = 1 := by rw [hmul, mul_inv_cancel₀ (sub_pos.2 hr1).ne']
  refine ⟨a, fun m ↦ by
      rw [ha]
      exact Finset.sum_nonneg fun k _ ↦ by simp only [lp.toNorm_coe, smul_eq_mul]; positivity,
    fun m ↦ ?_, by simpa only [lp.norm_toNorm, u.norm_weightedBlocks, hratio] using han⟩
  rw [ha m, lowPass_eq_sum]
  refine ((mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans_eq
    (Finset.mul_sum ..)).trans (Finset.sum_le_sum fun k hk ↦ ?_)
  have hexp : (2 : ℝ) ^ (s * m) = (2 ^ s) ^ (m - k) * 2 ^ (s * k) := by
    rw [← Real.rpow_mul_natCast zero_le_two, ← Real.rpow_add two_pos, ← mul_add]
    congr 2; exact_mod_cast (Nat.sub_add_cancel (Finset.mem_range.1 hk).le).symm
  rw [smul_eq_mul, lp.toNorm_coe, hexp, mul_assoc, u.norm_weightedBlocks_apply]

end TauCeti.BesovSpace
