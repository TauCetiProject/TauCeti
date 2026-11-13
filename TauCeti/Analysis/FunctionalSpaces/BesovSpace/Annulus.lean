/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace
import TauCeti.Analysis.Distribution.TemperedDistribution.BesselPotential
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Normed.Lp.Reindex

/-!
# Reconstruction from pieces with spectra in dyadic annuli

Let `0 < a`, `b`, `s ∈ ℝ` and `1 ≤ p, q ≤ ∞`. Suppose that `uⱼ ∈ Lᵖ`, `j ≥ 0`, has Fourier
transform vanishing outside the dyadic annulus `2^j a ≤ ‖ξ‖ ≤ 2^j b` (for `j = 0`, outside the
ball of radius `b`), and that `2^{js} ‖uⱼ‖_p ≤ wⱼ` for some `w ∈ ℓ^q`. Then the series `∑ⱼ uⱼ`
converges in the tempered distributions to an element of the inhomogeneous Besov space
`B^s_{p,q}`, with

`‖∑ⱼ uⱼ‖_{B^s_{p,q}} ≤ C ‖w‖_{ℓ^q}`,

where `C` depends only on the bump function, `a`, `b` and `s`, not on `p` or `q`
(`TauCeti.BesovSpace.exists_hasSum_toDistr_and_norm_le_of_annulus`; Bahouri–Chemin–Danchin,
Lemma 2.69).

This is how Besov regularity is recognised for a sum of pieces localised in dyadic annuli, as
the terms `S_{j-1} f · Δⱼ g` of Bony's paraproduct are. Unlike for pieces localised only in
balls, no sign condition on `s` is needed: a block `Δₖ` meets only the boundedly many pieces
`uⱼ` with `|j - k|` bounded, so each block of the sum is a finite sum. For `s ≤ 0` the series
need not converge in any `Lᵖ`, which is why its sum is taken in the tempered distributions.

## The argument

Choose `L`, depending only on the bump function, `a` and `b`, with `Δₖ uⱼ = 0` unless
`|j - k| < L` (`TemperedDistribution.exists_littlewoodPaleyBlock_eq_zero_of_isVanishingOn_annulus`).

* *Convergence.* On the annulus of `uⱼ` the Bessel potential `J^{s-1}` costs a factor `2^{j(s-1)}`
  (`TemperedDistribution.exists_besselPotential_eq_and_norm_le_of_isVanishingOn`), so
  `‖J^{s-1} uⱼ‖_p ≤ C 2^{-j} wⱼ ≤ C 2^{-j} ‖w‖`. The series `∑ⱼ J^{s-1} uⱼ` therefore converges
  absolutely in `Lᵖ`, and applying the continuous map `J^{1-s}` shows that `∑ⱼ uⱼ` converges in
  the tempered distributions. This is the device used for the completeness of `B^s_{p,q}`.
* *The Besov bound.* Applying `Δₖ` to the series, `Δₖ u = ∑_{k - L ≤ j < k + L} Δₖ uⱼ`, so
  `2^{ks} ‖Δₖ u‖_p ≤ C₀ 2^{|s| L} ∑_{k - L ≤ j < k + L} wⱼ`, where `C₀` bounds the blocks on `Lᵖ`.
  The window sums of `w` have `ℓ^q` norm at most `2 L ‖w‖`
  (`lp.norm_le_of_forall_eq_sum_Ico_sub_add`).

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Lemma 2.69.
* H. Triebel, *Theory of Function Spaces*, Section 2.3.2.
-/

public section

noncomputable section

open MeasureTheory FourierTransform Distribution TemperedDistribution Metric
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti.BesovSpace

/-- `2^{j(s-1)} x ≤ 2^{-j} y` when `2^{js} x ≤ y`. -/
private theorem rpow_sub_one_mul_le {s x y : ℝ} (j : ℕ) (h : 2 ^ (s * j) * x ≤ y) :
    (2 : ℝ) ^ ((s - 1) * j) * x ≤ (1 / 2) ^ j * y := by
  have h2 : (2 : ℝ) ^ ((s - 1) * j) = (1 / 2) ^ j * 2 ^ (s * j) := by
    rw [sub_mul, one_mul, Real.rpow_sub two_pos, Real.rpow_natCast, div_pow, one_pow]
    ring
  rw [h2, mul_assoc]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- **Convergence of a series of annular pieces.** If `uⱼ ∈ Lᵖ` has spectrum in the dyadic
annulus of radii `2^j a` and `2^j b` and `2^{js} ‖uⱼ‖_p` is bounded by an `ℓ^q` sequence, then
`∑ⱼ uⱼ` converges in the tempered distributions: the series `∑ⱼ J^{s-1} uⱼ` converges absolutely
in `Lᵖ`. -/
private theorem exists_hasSum_of_annulus (s : ℝ) {a : ℝ} (ha : 0 < a) (b : ℝ) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {q : ℝ≥0∞} [Fact (1 ≤ q)] (u : ℕ → Lp F p (volume : Measure E))
    (w : lp (fun _ : ℕ ↦ ℝ) q)
    (hb : ∀ j : ℕ, IsVanishingOn (𝓕 (u j : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 (2 ^ j * b))ᶜ)
    (ha' : ∀ j : ℕ, 0 < j → IsVanishingOn (𝓕 (u j : 𝓢'(E, F)) : 𝓢'(E, F)) (ball 0 (2 ^ j * a)))
    (huw : ∀ j : ℕ, 2 ^ (s * j) * ‖u j‖ ≤ w j) :
    ∃ U : 𝓢'(E, F), HasSum (fun j ↦ (u j : 𝓢'(E, F))) U := by
  obtain ⟨C, hC, hJ⟩ :=
    exists_besselPotential_eq_and_norm_le_of_isVanishingOn (E := E) (F := F) (s - 1) ha b
  choose g hg hgC using fun j ↦ hJ j (u j) (hb j) (ha' j)
  have hq : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hbound (j : ℕ) : ‖g j‖ ≤ C * ‖w‖ * (1 / 2) ^ j := by
    calc ‖g j‖ ≤ C * (2 ^ ((s - 1) * j) * ‖u j‖) := (hgC j).trans_eq (mul_assoc _ _ _)
      _ ≤ C * ((1 / 2) ^ j * w j) := mul_le_mul_of_nonneg_left (rpow_sub_one_mul_le j (huw j)) hC
      _ ≤ C * ((1 / 2) ^ j * ‖w‖) := by
        gcongr
        exact (Real.le_norm_self _).trans (lp.norm_apply_le_norm hq w j)
      _ = C * ‖w‖ * (1 / 2) ^ j := by ring
  have hsum : Summable fun j ↦ ‖g j‖ :=
    (summable_geometric_two.mul_left (C * ‖w‖)).of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbound
  -- `uⱼ = J^{1-s} gⱼ`, and `J^{1-s}` is continuous from `Lᵖ` to the tempered distributions.
  set T := besselPotential E F (1 - s) ∘L Lp.toTemperedDistributionCLM F volume p
  have hT (j : ℕ) : T (g j) = u j := by
    rw [ContinuousLinearMap.comp_apply, Lp.toTemperedDistributionCLM_apply, ← hg j,
      besselPotential_besselPotential_apply, show s - 1 + (1 - s) = 0 by ring,
      besselPotential_zero, ContinuousLinearMap.id_apply]
  exact ⟨_, by simpa only [Function.comp_def, hT] using hsum.of_norm.hasSum.map T T.continuous⟩

variable (φ : ContDiffBump (0 : E))

/-- **The blocks of a series of annular pieces.** There are `K ≥ 0` and `L`, depending only on
`φ`, `a`, `b` and `s`, with the following property. If `uⱼ ∈ Lᵖ` has spectrum in the dyadic annulus
of radii `2^j a` and `2^j b` and `∑ⱼ uⱼ = U` in the tempered distributions, then the blocks `Δₖ U`
are `Lᵖ` functions `fₖ` with `2^{ks} ‖fₖ‖_p ≤ K ∑_{k - L ≤ j < k + L} 2^{js} ‖uⱼ‖_p`. -/
private theorem exists_littlewoodPaleyBlock_eq_and_le_of_hasSum (s : ℝ) {a : ℝ} (ha : 0 < a)
    (b : ℝ) :
    ∃ K : ℝ, ∃ L : ℕ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : ℕ → Lp F p (volume : Measure E))
      {U : 𝓢'(E, F)}, HasSum (fun j ↦ (u j : 𝓢'(E, F))) U →
      (∀ j : ℕ, IsVanishingOn (𝓕 (u j : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 (2 ^ j * b))ᶜ) →
      (∀ j : ℕ, 0 < j → IsVanishingOn (𝓕 (u j : 𝓢'(E, F)) : 𝓢'(E, F)) (ball 0 (2 ^ j * a))) →
      ∃ f : ℕ → Lp F p (volume : Measure E), (∀ k, littlewoodPaleyBlock F φ k U = f k) ∧
        ∀ k : ℕ, 2 ^ (s * k) * ‖f k‖ ≤
          K * ∑ j ∈ Finset.Ico (k - L) (k + L), 2 ^ (s * j) * ‖u j‖ := by
  obtain ⟨L, hL⟩ := exists_littlewoodPaleyBlock_eq_zero_of_isVanishingOn_annulus (F := F) φ ha b
  obtain ⟨C₀, hC₀⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  refine ⟨max C₀ 0 * 2 ^ (|s| * L), L, by positivity, fun {p} _ u U hU hb ha' ↦ ?_⟩
  -- `Δₖ U = ∑_{k - L ≤ j < k + L} Δₖ uⱼ`, and each `Δₖ uⱼ` is an `Lᵖ` function `gₖⱼ`.
  choose g hg hgC using fun k j ↦ hC₀ (p := p) k (u j)
  refine ⟨fun k ↦ ∑ j ∈ Finset.Ico (k - L) (k + L), g k j, fun k ↦ ?_, fun k ↦ ?_⟩
  · rw [littlewoodPaleyBlock_eq_sum_Ico_of_hasSum φ hU (fun j k ↦ hL j k _ (hb j) (ha' j)) k,
      Lp.toTemperedDistribution_sum]
    exact Finset.sum_congr rfl fun j _ ↦ hg k j
  · exact two_rpow_mul_norm_sum_Ico_le s (hgC k) k L

/-- **Reconstruction from pieces with spectra in dyadic annuli** (Bahouri–Chemin–Danchin,
Lemma 2.69). Let `s : ℝ`, `a > 0` and `b : ℝ`. There is `C`, depending only on `φ`, `a`, `b` and
`s`, with the following property. Let `1 ≤ p, q ≤ ∞`, and let `uⱼ ∈ Lᵖ` have Fourier transform
vanishing outside the closed ball of radius `2^j b` and, for `j > 0`, on the open ball of radius
`2^j a`. If `2^{js} ‖uⱼ‖_p ≤ wⱼ` for a sequence `w ∈ ℓ^q`, then `∑ⱼ uⱼ` converges in the tempered
distributions to an element `v` of the Besov space `B^s_{p,q}` with `‖v‖ ≤ C ‖w‖`. -/
theorem exists_hasSum_toDistr_and_norm_le_of_annulus (s : ℝ) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∃ C : ℝ, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {q : ℝ≥0∞} [Fact (1 ≤ q)]
      (u : ℕ → Lp F p (volume : Measure E)) (w : lp (fun _ : ℕ ↦ ℝ) q),
      (∀ j : ℕ, IsVanishingOn (𝓕 (u j : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 (2 ^ j * b))ᶜ) →
      (∀ j : ℕ, 0 < j → IsVanishingOn (𝓕 (u j : 𝓢'(E, F)) : 𝓢'(E, F)) (ball 0 (2 ^ j * a))) →
      (∀ j : ℕ, 2 ^ (s * j) * ‖u j‖ ≤ w j) →
      ∃ v : BesovSpace F φ s p q,
        HasSum (fun j ↦ (u j : 𝓢'(E, F))) v.toDistr ∧ ‖v‖ ≤ C * ‖w‖ := by
  obtain ⟨K, L, hK, hKL⟩ := exists_littlewoodPaleyBlock_eq_and_le_of_hasSum (F := F) φ s ha b
  refine ⟨K * (2 * L), fun {p} _ {q} _ u w hb ha' huw ↦ ?_⟩
  have hq : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  obtain ⟨U, hU⟩ := exists_hasSum_of_annulus s ha b u w hb ha' huw
  obtain ⟨f, hf, hfu⟩ := hKL u hU hb ha'
  -- The window sums of `w`, as an element of `ℓ^q`; they dominate the weighted blocks of `U`.
  set W : lp (fun _ : ℕ ↦ ℝ) q :=
    ⟨fun k ↦ ∑ j ∈ Finset.Ico (k - L) (k + L), w j, (lp.memℓp w).sum_Ico_sub_add L⟩
  -- The entries of the anonymous `lp` element `W` are its defining sequence by definition.
  have hW (k : ℕ) : W k = ∑ j ∈ Finset.Ico (k - L) (k + L), w j := rfl
  have hle (k : ℕ) : 2 ^ (s * k) * ‖f k‖ ≤ ‖(K • W) k‖ := by
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hW]
    exact (hfu k).trans <| (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ ↦ huw j) hK).trans
      (Real.le_norm_self _)
  have hmem : U.MemBesov φ s p q :=
    memBesov_iff.2 ⟨f, hf, (lp.memℓp (K • W)).norm.mono fun k ↦ by
      rw [Real.norm_of_nonneg (by positivity)]
      exact hle k⟩
  refine ⟨hmem.toBesovSpace, by rwa [MemBesov.toDistr_toBesovSpace], ?_⟩
  have hblock (k : ℕ) : hmem.toBesovSpace.block k = f k :=
    LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
      simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply, coe_block,
        MemBesov.toDistr_toBesovSpace, hf k]
  calc ‖hmem.toBesovSpace‖ ≤ ‖K • W‖ := by
        rw [← norm_weightedBlocks]
        refine lp.norm_mono hq fun k ↦ ?_
        rw [norm_weightedBlocks_apply, hblock]
        exact hle k
    _ = K * ‖W‖ := by rw [norm_smul, Real.norm_of_nonneg hK]
    _ ≤ K * (2 * L * ‖w‖) := by
        gcongr
        exact lp.norm_le_of_forall_eq_sum_Ico_sub_add L hW
    _ = K * (2 * L) * ‖w‖ := by ring

end TauCeti.BesovSpace
