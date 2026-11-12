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
geometric tail sum of `a` above it, and both have `ℓ^q` norm controlled by `‖a‖`
(`lp.norm_le_of_forall_eq_sum_Ico_sub_add`, `lp.exists_forall_hasSum_pow_smul_add_and_norm_le`).

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

/-- **The block estimate for spectra in dyadic balls.** Let `gⱼ` be vectors that vanish for
`j + N ≤ k`, with `‖gⱼ‖ ≤ K xⱼ` and `2^{js} xⱼ ≤ aⱼ`. Splitting `∑ⱼ gⱼ` at `j = k`, the
contributing terms below `k` lie within `N` of `k`, and each term above `k` carries the weight
`2^{(k - j)s} = (2^{-s})^{j - k}`, so
`2^{ks} ‖∑ⱼ gⱼ‖ ≤ K 2^{|s| N} ∑_{k - N ≤ j < k + N} aⱼ + K ∑_{d ≥ 0} (2^{-s})^d a_{k + d}`. -/
private theorem two_rpow_mul_norm_tsum_le {V : Type*} [NormedAddCommGroup V] [CompleteSpace V]
    {k N : ℕ} {K : ℝ} (hK : 0 ≤ K) {g : ℕ → V} {x a : ℕ → ℝ}
    (hg0 : ∀ j, j + N ≤ k → g j = 0) (hgx : ∀ j, ‖g j‖ ≤ K * x j)
    (hx0 : ∀ j, 0 ≤ x j) (hxa : ∀ j : ℕ, 2 ^ (s * j) * x j ≤ a j)
    (hsum : Summable fun j ↦ ‖g j‖) {T : ℝ}
    (hT : HasSum (fun d ↦ ((2 : ℝ) ^ (-s)) ^ d • a (d + k)) T) :
    2 ^ (s * k) * ‖∑' j, g j‖ ≤
      K * 2 ^ (|s| * N) * ∑ j ∈ Finset.Ico (k - N) (k + N), a j + K * T := by
  have ha0 (j : ℕ) : 0 ≤ a j := (by have := hx0 j; positivity : (0 : ℝ) ≤ _).trans (hxa j)
  have hlow : ∑ j ∈ Finset.range k, g j = ∑ j ∈ Finset.Ico (k - N) k, g j :=
    (Finset.sum_subset (fun j hj ↦ Finset.mem_range.2 (Finset.mem_Ico.1 hj).2)
      fun j hj hj' ↦ hg0 j (by rw [Finset.mem_range] at hj; rw [Finset.mem_Ico] at hj'; omega)).symm
  -- The terms below `k`.
  have hlow' : 2 ^ (s * k) * ‖∑ j ∈ Finset.Ico (k - N) k, g j‖ ≤
      K * 2 ^ (|s| * N) * ∑ j ∈ Finset.Ico (k - N) (k + N), a j := by
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine (Finset.sum_le_sum fun j hj ↦ ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Ico_subset_Ico_right (by omega)) fun j _ _ ↦ by have := ha0 j; positivity)
    rw [Finset.mem_Ico] at hj
    calc 2 ^ (s * k) * ‖g j‖ ≤ 2 ^ (|s| * N) * 2 ^ (s * j) * (K * x j) := by
          gcongr
          · exact Real.rpow_mul_natCast_le_of_mem_Ico' one_le_two s
              (Finset.mem_Ico.2 ⟨by omega, by omega⟩)
          · exact hgx j
      _ = K * 2 ^ (|s| * N) * (2 ^ (s * j) * x j) := by ring
      _ ≤ K * 2 ^ (|s| * N) * a j := by gcongr; exact hxa j
  -- The terms above `k`.
  have hhigh : 2 ^ (s * k) * ‖∑' d, g (d + k)‖ ≤ K * T := by
    have hsum' : Summable fun d ↦ ‖g (d + k)‖ := (summable_nat_add_iff k).2 hsum
    refine (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsum') (by positivity)).trans ?_
    refine hasSum_le (fun d ↦ ?_) (hsum'.hasSum.mul_left _) (hT.mul_left K)
    have e : ((2 : ℝ) ^ (-s)) ^ d * 2 ^ (s * (d + k : ℕ)) = 2 ^ (s * k) := by
      rw [← Real.rpow_mul_natCast zero_le_two, Nat.cast_add, mul_add, Real.rpow_add two_pos,
        ← mul_assoc, ← Real.rpow_add two_pos, neg_mul, neg_add_cancel, Real.rpow_zero, one_mul]
    calc 2 ^ (s * k) * ‖g (d + k)‖
        ≤ ((2 : ℝ) ^ (-s)) ^ d * 2 ^ (s * (d + k : ℕ)) * (K * x (d + k)) := by
          rw [e]
          exact mul_le_mul_of_nonneg_left (hgx _) (by positivity)
      _ = K * (((2 : ℝ) ^ (-s)) ^ d * (2 ^ (s * (d + k : ℕ)) * x (d + k))) := by ring
      _ ≤ K * (((2 : ℝ) ^ (-s)) ^ d • a (d + k)) := by rw [smul_eq_mul]; gcongr; exact hxa _
  calc 2 ^ (s * k) * ‖∑' j, g j‖
      = 2 ^ (s * k) * ‖∑ j ∈ Finset.Ico (k - N) k, g j + ∑' d, g (d + k)‖ := by
        rw [← hlow, hsum.of_norm.sum_add_tsum_nat_add k]
    _ ≤ 2 ^ (s * k) * ‖∑ j ∈ Finset.Ico (k - N) k, g j‖ + 2 ^ (s * k) * ‖∑' d, g (d + k)‖ := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ _ := add_le_add hlow' hhigh

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
      rw [← Real.rpow_mul_natCast zero_le_two, ← Real.rpow_add two_pos, neg_mul, neg_add_cancel,
        Real.rpow_zero]
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
    exact two_rpow_mul_norm_tsum_le (le_max_right _ _) (hg0 k) (hgn' · k)
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
