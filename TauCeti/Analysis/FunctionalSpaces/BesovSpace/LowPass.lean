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
finitely many of its own blocks are nonzero. Hence it lies in every Besov space built on `Lᵖ`.
Since the blocks commute, `Δₖ (u - S_{N+1} u) = Δₖ u - S_{N+1} Δₖ u`, which vanishes at low
frequencies and is bounded by a constant times `Δₖ u` in general. The size of `S_m u` itself is
bounded uniformly in `m` when `u` is an `Lᵖ` function, and geometrically in `m` when `s < 0`.

## Main declarations

* `TauCeti.BesovSpace.lowPass`: the low-frequency cut-off `S_m u = ∑_{k < m} Δₖ u` as an `Lᵖ`
  function; `TauCeti.BesovSpace.coe_lowPass_succ` identifies `S_{m+1}` with the Fourier
  multiplier by `φ (2^{-m} ·)`.
* `TauCeti.BesovSpace.isVanishingOn_fourier_lowPass_succ`: `S_{m+1} u` has spectrum in the ball of
  radius `2^m φ.rOut`.
* `TauCeti.BesovSpace.exists_littlewoodPaleyBlock_lowPass_eq_zero`: the blocks of `S_m u` vanish
  from index `m + L` on, for an `L` depending only on the bump function.
* `TauCeti.BesovSpace.memBesov_lowPass`: `S_m u` lies in every `B^{s'}_{p,q'}`; as an element
  of that space it is `TauCeti.BesovSpace.exists_toDistr_eq_lowPass`.
* `TauCeti.BesovSpace.lowPass_mem_closure_range_toLp`: if the blocks of `u` are `Lᵖ` limits of
  Schwartz functions, so is `S_m u`.
* `TauCeti.BesovSpace.exists_block_sub_eq_zero_and_norm_le_of_toDistr_eq_lowPass`: the blocks of
  `u - S_{N+1} u` vanish below index `N + 1 - L` and are at most `(1 + ‖𝓕⁻ φ‖₁)` times those of `u`.
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

/-- **The low-frequency cut-offs lie in every Besov space.** The `Lᵖ` function
`S_m u = ∑_{k < m} Δₖ u` has only finitely many nonzero blocks, so it lies in `B^{s'}_{p,q'}` for
every smoothness `s'` and every fine index `q'`. -/
theorem memBesov_lowPass (u : BesovSpace F φ s p q) (m : ℕ) (s' : ℝ) (q' : ℝ≥0∞) :
    (u.lowPass m : 𝓢'(E, F)).MemBesov φ s' p q' := by
  obtain ⟨L, hL⟩ := exists_littlewoodPaleyBlock_lowPass_eq_zero (F := F) (φ := φ)
  obtain ⟨C, -, hC⟩ := exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_eq_zero F φ
  obtain ⟨x, hx, -⟩ := hC s' (m + L) (u.lowPass m) fun k hk ↦ hL u m k hk
  -- Only the blocks of index below `m + L` are nonzero, so the weighted blocks lie in `ℓ⁰`.
  refine (memBesov_iff.2 ⟨x.block, fun k ↦ by rw [coe_block, hx], memℓp_zero ?_⟩).mono le_rfl
    bot_le
  refine (Set.finite_lt_nat (m + L)).subset fun k hk ↦ Set.mem_ofPred.2 <| not_le.1 fun hkL ↦ ?_
  have h0 : x.block k = 0 := Lp.toTemperedDistribution_injective <| by
    simp only [coe_block, hx, hL u m k hkL, Lp.toTemperedDistribution_zero]
  simp [h0] at hk

/-- The low-frequency cut-off `S_m u` as an element of `B^{s'}_{p,q'}`, for every smoothness `s'`
and every fine index `q'` (`TauCeti.BesovSpace.memBesov_lowPass`). -/
theorem exists_toDistr_eq_lowPass (u : BesovSpace F φ s p q) (m : ℕ) (s' : ℝ) (q' : ℝ≥0∞) :
    ∃ x : BesovSpace F φ s' p q', x.toDistr = u.lowPass m :=
  ⟨_, (memBesov_lowPass u m s' q').toDistr_toBesovSpace⟩

/-- If every block `Δⱼ u` is a limit of Schwartz functions in `Lᵖ`, then so is every
low-frequency cut-off `S_m u = ∑_{k < m} Δₖ u`. -/
theorem lowPass_mem_closure_range_toLp {u : BesovSpace F φ s p q}
    (hblock : ∀ j, u.block j ∈ closure (Set.range fun f : 𝓢(E, F) ↦ f.toLp p)) (m : ℕ) :
    u.lowPass m ∈ closure (Set.range fun f : 𝓢(E, F) ↦ f.toLp p) := by
  -- The `Lᵖ` closure of the Schwartz functions is a subspace.
  have hS := SchwartzMap.closure_range_toLp_eq (F := F) (μ := (volume : Measure E)) p
  rw [hS, lowPass_eq_sum]
  exact Submodule.sum_mem _ fun j _ ↦ by rw [← SetLike.mem_coe, ← hS]; exact hblock j

/-- **The blocks of `u - S_{N+1} u`.** There is `L`, depending only on `φ`, such that for every
`v` with tempered distribution `S_{N+1} u` the block `Δₖ (u - v) = Δₖ u - S_{N+1} Δₖ u` vanishes
for `k + L ≤ N`, and has `Lᵖ` norm at most `(1 + ‖𝓕⁻ φ‖₁) ‖Δₖ u‖_p` for every `k`. -/
theorem exists_block_sub_eq_zero_and_norm_le_of_toDistr_eq_lowPass :
    ∃ L : ℕ, ∀ {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] (u v : BesovSpace F φ s p q) (N k : ℕ),
      v.toDistr = u.lowPass (N + 1) →
        (k + L ≤ N → (u - v).block k = 0) ∧
          ‖(u - v).block k‖ ≤ (1 + ∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖) * ‖u.block k‖ := by
  obtain ⟨L, hL⟩ := exists_sum_littlewoodPaleyBlock_littlewoodPaleyBlock (F := F) φ
  refine ⟨L, fun u v N k hv ↦ ?_⟩
  -- The block `Δₖ v = S_{N+1} Δₖ u` is the `Lᵖ` function `g`.
  obtain ⟨g, hg, hgu⟩ := exists_sum_littlewoodPaleyBlock_eq_and_norm_le φ N (u.block k)
  have hvk : v.block k = g := Lp.toTemperedDistribution_injective <| by
    simp only [coe_block, hv, coe_lowPass, map_sum, ← hg]
    exact Finset.sum_congr rfl fun j _ ↦ littlewoodPaleyBlock_comm φ k j u.toDistr
  rw [block_sub, hvk]
  refine ⟨fun hkN ↦ sub_eq_zero.2 ?_, (norm_sub_le _ _).trans (by linarith)⟩
  -- Low frequencies: `S_{N+1}` fixes `Δₖ u`.
  refine Lp.toTemperedDistribution_injective ?_
  simp only [← hg, coe_block]
  exact ((hL k N).1 hkN u.toDistr).symm

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
`‖S_m u‖_p ≤ 2^{-s m} ‖u‖ / (2^{-s} - 1)`, since the blocks satisfy `‖Δₖ u‖_p ≤ 2^{-s k} ‖u‖` and
`∑_{k < m} 2^{-s k} ≤ 2^{-s m} / (2^{-s} - 1)`. -/
theorem norm_lowPass_le_of_neg [Fact (1 ≤ q)] (hs : s < 0) (u : BesovSpace F φ s p q) (m : ℕ) :
    ‖u.lowPass m‖ ≤ 2 ^ (-s * m) / (2 ^ (-s) - 1) * ‖u‖ := by
  set x : ℝ := 2 ^ (-s)
  have hx : 1 < x := Real.one_lt_rpow one_lt_two (neg_pos.2 hs)
  have hpow : ∀ k : ℕ, (2 : ℝ) ^ (-s * k) = x ^ k := fun k ↦ by
    rw [Real.rpow_mul zero_le_two, Real.rpow_natCast]
  -- Each block is bounded by `2^{-s k} ‖u‖ = x^k ‖u‖`.
  have hblock : ∀ k : ℕ, ‖u.block k‖ ≤ x ^ k * ‖u‖ := fun k ↦ by
    calc ‖u.block k‖ = 2 ^ (-s * k) * (2 ^ (s * k) * ‖u.block k‖) := by
          rw [← mul_assoc, ← Real.rpow_add two_pos, neg_mul, neg_add_cancel, Real.rpow_zero,
            one_mul]
      _ ≤ 2 ^ (-s * k) * ‖u‖ := mul_le_mul_of_nonneg_left (u.rpow_mul_norm_block_le k)
          (by positivity)
      _ = x ^ k * ‖u‖ := by rw [hpow]
  calc ‖u.lowPass m‖ ≤ ∑ k ∈ Finset.range m, ‖u.block k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range m, x ^ k * ‖u‖ := Finset.sum_le_sum fun k _ ↦ hblock k
    _ = (x ^ m - 1) / (x - 1) * ‖u‖ := by rw [← Finset.sum_mul, geom_sum_eq hx.ne']
    _ ≤ x ^ m / (x - 1) * ‖u‖ := by
        gcongr
        linarith
    _ = 2 ^ (-s * m) / (2 ^ (-s) - 1) * ‖u‖ := by rw [hpow]

end TauCeti.BesovSpace
