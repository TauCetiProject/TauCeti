/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Reconstruction from pieces with spectra in dyadic balls

Let `0 < s`, `R : ℝ` and `1 ≤ p, q ≤ ∞`. Suppose that `fⱼ ∈ Lᵖ`, `j ≥ 0`, has Fourier transform
vanishing outside the dyadic ball `‖ξ‖ ≤ 2^j R`, and that `2^{js} ‖fⱼ‖_p ≤ aⱼ` for some
`a ∈ ℓ^q`. Then the series `∑ⱼ fⱼ` converges in the tempered distributions to an element of the
inhomogeneous Besov space `B^s_{p,q}`, with

`‖∑ⱼ fⱼ‖_{B^s_{p,q}} ≤ C ‖a‖_{ℓ^q}`,

where `C` depends only on the bump function, `s` and `R`, not on `p` or `q`
(`TauCeti.BesovSpace.exists_hasSum_toDistr_and_norm_le_of_ball`; Bahouri–Chemin–Danchin,
Lemma 2.84).

This is the summation step behind Bony's remainder estimate: the remainder
`∑_{|j - k| ≤ 1} Δⱼ f · Δₖ g` is a series of pieces with spectra in dyadic balls. For pieces with
spectra in dyadic annuli the same conclusion holds for every `s`
(`TauCeti.BesovSpace.exists_hasSum_toDistr_and_norm_le_of_annulus`).

## The argument

A piece `fⱼ` has no block `Δₖ fⱼ` with `k ≥ j + N`, for some `N` depending only on the bump
function and `R`
(`TemperedDistribution.exists_littlewoodPaleyBlock_eq_zero_of_isVanishingOn_compl_closedBall`),
but it may meet every block of lower index. So the block `Δₖ ∑ⱼ fⱼ` involves the whole tail
`j > k - N`. Since `s > 0`, the pieces decay geometrically in `Lᵖ`, so the series converges
absolutely in `Lᵖ`, and along the tail the weights `2^{(k - j)s}` decay geometrically too. Splitting
each block at `j = k` bounds `2^{ks} ‖Δₖ ∑ⱼ fⱼ‖_p` by a window sum of `a` below `k` plus a
geometric tail sum of `a` above it (`TauCeti.two_rpow_mul_norm_tsum_le`), and both have `ℓ^q` norm
controlled by `‖a‖` (`lp.norm_le_of_forall_eq_sum_Ico_sub_add`,
`lp.exists_forall_hasSum_pow_smul_add_and_norm_le`).

The positivity of `s` is needed: the pieces `fⱼ = Δ₀ u` for every `j`, with `u` a fixed nonzero
function, satisfy the hypotheses for `s = 0`, `q = ∞` and their sum diverges.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Lemma 2.84.
-/
public section

noncomputable section

open MeasureTheory FourierTransform Filter Topology Metric Distribution TemperedDistribution
open scoped ENNReal SchwartzMap

namespace TauCeti.BesovSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {φ : ContDiffBump (0 : E)} {s : ℝ}

variable (φ) in
/-- **Series with spectra in dyadic balls.** For `0 < s` and `R` there is `C ≥ 0`, depending only
on `φ`, `s` and `R`, with the following property for all `1 ≤ p, q ≤ ∞`. Let `fⱼ ∈ Lᵖ` have
Fourier transforms vanishing outside the ball `‖ξ‖ ≤ 2^j R`, and let `a ∈ ℓ^q` bound their weighted
norms, `2^{js} ‖fⱼ‖_p ≤ aⱼ`. Then `∑ⱼ fⱼ` converges in the tempered distributions to an element
`v` of `B^s_{p,q}` with `‖v‖ ≤ C ‖a‖` (Bahouri, Chemin and Danchin, Lemma 2.84). -/
theorem exists_hasSum_toDistr_and_norm_le_of_ball (hs : 0 < s) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
      (f : ℕ → Lp F p (volume : Measure E)) (a : lp (fun _ : ℕ ↦ ℝ) q),
      (∀ j, IsVanishingOn (𝓕 (f j : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 (2 ^ j * R))ᶜ) →
      (∀ j : ℕ, 2 ^ (s * j) * ‖f j‖ ≤ a j) →
      ∃ v : BesovSpace F φ s p q, HasSum (fun j ↦ (f j : 𝓢'(E, F))) v.toDistr ∧
        ‖v‖ ≤ C * ‖a‖ := by
  obtain ⟨N, hN⟩ := exists_littlewoodPaleyBlock_eq_zero_of_isVanishingOn_compl_closedBall
    (F := F) φ R
  obtain ⟨C₀, hC₀⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  set ρ : ℝ := 2 ^ (-s)
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hs)
  set K := max C₀ 0
  refine ⟨K * 2 ^ (|s| * N) * (2 * N) + K * (1 - ρ)⁻¹, by have := sub_pos.2 hρ1; positivity,
    fun {p q} _ _ f a h1 ha ↦ ?_⟩
  -- Since `s > 0`, the pieces decay geometrically in `Lᵖ`: `‖fⱼ‖ ≤ ρ ^ j ‖a‖`.
  have hfn (j : ℕ) : ‖f j‖ ≤ ‖a‖ * ρ ^ j := by
    have hρj : ρ ^ j * 2 ^ (s * j) = 1 := by
      simpa using Real.rpow_neg_pow_mul_rpow_mul_natCast_add two_pos s j 0
    calc ‖f j‖ = ρ ^ j * (2 ^ (s * j) * ‖f j‖) := by rw [← mul_assoc, hρj, one_mul]
      _ ≤ ρ ^ j * ‖a‖ := by
          gcongr
          exact (ha j).trans <| (Real.le_norm_self _).trans <|
            lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' a j
      _ = _ := mul_comm _ _
  have hgeom := (summable_geometric_of_lt_one hρ0 hρ1).mul_left ‖a‖
  have hW := ((Summable.of_norm_bounded hgeom hfn).hasSum).map
    (Lp.toTemperedDistributionCLM F volume p) (ContinuousLinearMap.continuous _)
  choose g hg hgn using fun j k ↦ hC₀ (p := p) k (f j)
  have hgn' (j k : ℕ) : ‖g j k‖ ≤ K * ‖f j‖ :=
    (hgn j k).trans (by gcongr; exact le_max_left _ _)
  -- A piece `fⱼ` has no block `Δₖ fⱼ` with `j + N ≤ k`.
  have hg0 (k j : ℕ) (hjk : j + N ≤ k) : g j k = 0 :=
    LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
      simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply, ← hg,
        hN j k _ (h1 j) hjk, map_zero]
  have hgsum (k : ℕ) : Summable fun j ↦ ‖g j k‖ :=
    (hgeom.mul_left K).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun j ↦
      (hgn' j k).trans (by gcongr; exact hfn j)
  -- The blocks of the sum: `Δₖ ∑ⱼ fⱼ = ∑ⱼ Δₖ fⱼ`, a sum converging in `Lᵖ`.
  set G : ℕ → Lp F p (volume : Measure E) := fun k ↦ ∑' j, g j k
  have hG (k : ℕ) : littlewoodPaleyBlock F φ k
      (Lp.toTemperedDistributionCLM F volume p (∑' j, f j)) = G k := by
    refine (hW.map (littlewoodPaleyBlock F φ k) (ContinuousLinearMap.continuous _)).unique ?_
    convert ((hgsum k).of_norm.hasSum.map (Lp.toTemperedDistributionCLM F volume p)
      (ContinuousLinearMap.continuous _)) using 1
    · funext j
      simp only [Function.comp_apply, Lp.toTemperedDistributionCLM_apply, hg]
    · rw [Lp.toTemperedDistributionCLM_apply]
  obtain ⟨T, hT, hTn⟩ := lp.exists_forall_hasSum_pow_smul_add_and_norm_le a hρ0 hρ1
  set A : lp (fun _ : ℕ ↦ ℝ) q :=
    ⟨fun k ↦ ∑ j ∈ Finset.Ico (k - N) (k + N), a j, (lp.memℓp a).sum_Ico_sub_add N⟩
  -- The entries of the anonymous `lp` element `A` are its defining window sums by definition:
  -- `lp` coerces through `Subtype.val` and has no lemma evaluating an anonymous constructor.
  have hA (k : ℕ) : A k = ∑ j ∈ Finset.Ico (k - N) (k + N), a j := rfl
  have hGn (k : ℕ) : 2 ^ (s * k) * ‖G k‖ ≤ ((K * 2 ^ (|s| * N)) • A + K • T) k := by
    rw [lp.coeFn_add, lp.coeFn_smul, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul, hA]
    exact TauCeti.two_rpow_mul_norm_tsum_le (le_max_right _ _) (hg0 k) (hgn' · k)
      (fun _ ↦ norm_nonneg _) ha (hgsum k) (hT k)
  obtain ⟨v, hv, hvn⟩ := exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_eq G _ hG hGn
  refine ⟨v, hv ▸ hW, hvn.trans ?_⟩
  calc ‖(K * 2 ^ (|s| * N)) • A + K • T‖ ≤ K * 2 ^ (|s| * N) * ‖A‖ + K * ‖T‖ := by
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
          Real.norm_of_nonneg (by positivity)]
    _ ≤ K * 2 ^ (|s| * N) * (2 * N * ‖a‖) + K * ((1 - ρ)⁻¹ * ‖a‖) := by
        gcongr
        exact lp.norm_le_of_forall_eq_sum_Ico_sub_add N hA
    _ = (K * 2 ^ (|s| * N) * (2 * N) + K * (1 - ρ)⁻¹) * ‖a‖ := by ring

end TauCeti.BesovSpace

end
