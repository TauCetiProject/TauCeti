/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# The low-frequency cut-offs of a Besov space element

Let `Δⱼ` be the inhomogeneous Littlewood–Paley blocks of a bump function `φ`
(`TemperedDistribution.littlewoodPaleyBlock`). The **low-frequency cut-off** of an element `u` of
a Besov space `B^s_{p,q}` is the `Lᵖ` function `S_m u = ∑_{k < m} Δₖ u`. For `m ≥ 1` it is the
Fourier multiplier by `φ (2^{1-m} ·)`, so its spectrum lies in a ball of radius `O(2^m)`, and only
finitely many of its own blocks are nonzero. As a tempered distribution it is the dyadic partial
sum `TauCeti.BesovSpace.partialSumCLM`, through which it lies in every Besov space built on `Lᵖ`.
If the blocks of `u` are `Lᵖ` limits of Schwartz functions, so is `S_m u`. The size of `S_m u`
itself is bounded uniformly in `m` when `u` is an `Lᵖ` function, and geometrically in `m` when
`s < 0`.

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
* `TauCeti.BesovSpace.norm_lowPass_le_of_toDistr_eq` and
  `TauCeti.BesovSpace.norm_lowPass_le_of_neg`: the size of the low-frequency cut-offs.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory Metric Distribution FourierTransform TemperedDistribution
open scoped ENNReal SchwartzMap

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

/-- **The low-frequency cut-offs of a single block.** If every block of `u` other than `Δₘ u`
vanishes, then `S_n u = Δₘ u` for `n > m` and `S_n u = 0` for `n ≤ m`. -/
theorem lowPass_eq_ite_of_block_eq_zero {u : BesovSpace F φ s p q} {m : ℕ}
    (hu : ∀ k, k ≠ m → u.block k = 0) (n : ℕ) :
    u.lowPass n = if m < n then u.block m else 0 := by
  rw [lowPass_eq_sum]
  split_ifs with hmn
  · exact Finset.sum_eq_single_of_mem m (Finset.mem_range.2 hmn) fun k _ hk ↦ hu k hk
  · exact Finset.sum_eq_zero fun k hk ↦ hu k (by rw [Finset.mem_range] at hk; omega)

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

end TauCeti.BesovSpace
