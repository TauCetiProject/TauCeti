/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.LowPass
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.ProductSpectrum
import TauCeti.Analysis.Normed.Group.Pointwise
import TauCeti.MeasureTheory.Function.Holder

/-!
# Bony's paraproduct decomposition

Let `Δⱼ` be the inhomogeneous Littlewood–Paley blocks of a bump function `φ`
(`TemperedDistribution.littlewoodPaleyBlock`), and let `S_m u = ∑_{k < m} Δₖ u` be the
**low-frequency cut-off** (`TauCeti.BesovSpace.lowPass`). For scalar `u` with `L^{p₁}` blocks
and `v` with `L^{p₂}` blocks, for instance elements of the Besov spaces `B^α_{p₁,q}` and
`B^β_{p₂,q'}`, every product `Δₖ u · Δₗ v` is an `Lʳ` function, `1/r = 1/p₁ + 1/p₂`, and
grouping the products by the relative size of the two frequencies gives **Bony's decomposition**
of the product `u v` into two paraproducts and a resonant term,

`u v = T_u v + T_v u + R(u, v)`, with
`T_u v = ∑ⱼ S_{j-N} u · Δⱼ v`, `T_v u = ∑ⱼ Δⱼ u · S_{j-N} v`,
`R(u, v) = ∑ⱼ Δⱼ u · ∑_{|k - j| ≤ N} Δₖ v`.

Here `N` is a gap parameter: the paraproduct `T_u v` collects the pairs `(k, l)` of block indices
of `u` and `v` with `k + N < l`, the term `T_v u` those with `l + N < k`, and `R(u, v)` the pairs
with `|k - l| ≤ N`. These three classes partition all pairs, so on the truncations `S_M u` and
`S_M v` the decomposition is an identity (`TauCeti.BesovSpace.lowPass_smul_lowPass`). The choice
`N = 1` is the decomposition `T_u v = ∑ⱼ S_{j-1} u · Δⱼ v`,
`R(u, v) = ∑_{|j - k| ≤ 1} Δⱼ u · Δₖ v` of Bahouri–Chemin–Danchin; a larger gap is needed when the
pieces of the partition have wider supports.

The point of the decomposition is the spectral localization of its terms. The block `Δⱼ v`,
`j ≥ 1`, has Fourier transform carried by the annulus `2^{j-1} φ.rIn ≤ ‖ξ‖ ≤ 2^j φ.rOut`, and
`S_{j-N} u` by the much smaller ball of radius `2^{j-N-1} φ.rOut`, so the Fourier transform of the
product `S_{j-N} u · Δⱼ v` is carried by an annulus of size `2^j`, with inner radius
`2^{j-1} (φ.rIn - 2^{-N} φ.rOut)`. This is positive once `2^N φ.rIn > φ.rOut`, and then the terms
of the paraproducts are spectrally localized in dyadic annuli
(`TauCeti.BesovSpace.isVanishingOn_fourier_lowPass_smul_block`,
`TauCeti.BesovSpace.isVanishingOn_fourier_block_smul_lowPass`). The terms of the resonant part are
only localized in balls of radius `O(2^j)`
(`TauCeti.BesovSpace.isVanishingOn_fourier_block_smul_sum_block`), which is why the resonant term
needs positive total regularity. The products are located with the spectrum of a product of two
band-limited functions (`MeasureTheory.Lp.isVanishingOn_fourier_smul`).

The paraproduct estimates live in
`TauCeti.Analysis.FunctionalSpaces.BesovSpace.Paraproduct.Estimate` and the resonant remainder
estimates live in `TauCeti.Analysis.FunctionalSpaces.BesovSpace.Paraproduct.Resonant`.

## Main declarations

* `TauCeti.BesovSpace.isVanishingOn_fourier_lowPass_smul_block` and
  `TauCeti.BesovSpace.isVanishingOn_fourier_block_smul_lowPass`: the terms of the two paraproducts
  have spectra in dyadic annuli.
* `TauCeti.BesovSpace.isVanishingOn_fourier_block_smul_sum_block`: the terms of the resonant part
  have spectra in dyadic balls.
* `TauCeti.BesovSpace.lowPass_smul_lowPass`: Bony's decomposition of `S_M u · S_M v`.

## References

* J.-M. Bony, *Calcul symbolique et propagation des singularités pour les équations aux dérivées
  partielles non linéaires*, Ann. Sci. École Norm. Sup. (4) 14 (1981), 209–246.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Chapter 2
  (Bony's decomposition).
-/

public section

noncomputable section

open MeasureTheory Metric Set Distribution FourierTransform TemperedDistribution
open scoped ENNReal SchwartzMap Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti.BesovSpace

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

section Spectrum

variable {s' : ℝ} {q' p₁ p₂ r : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)]
  [p₁.HolderTriple p₂ r]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The dyadic radii of a paraproduct term: adding the ball of radius `2^m φ.rOut` carrying
`S_{m+1}` to the annulus carrying `Δ_{m+N+1}` gives an annulus of size `2^{m+N+1}` with inner
radius `2^{m+N} (φ.rIn - 2^{-N} φ.rOut)`. -/
private theorem closedBall_add_annulus_subset (φ : ContDiffBump (0 : E)) (N m : ℕ) :
    closedBall (0 : E) (2 ^ m * φ.rOut) +
        (closedBall 0 (2 ^ (m + N + 1) * φ.rOut) \ ball 0 (2 ^ (m + N) * φ.rIn)) ⊆
      closedBall 0 (2 ^ (m + N + 1) * (2 * φ.rOut)) \
        ball 0 (2 ^ (m + N + 1) * ((φ.rIn - φ.rOut / 2 ^ N) / 2)) := by
  refine (closedBall_zero_add_diff_ball_subset _ _ _).trans
    (sdiff_subset_sdiff (closedBall_subset_closedBall ?_) (ball_subset_ball (le_of_eq ?_)))
  · have h : (2 : ℝ) ^ m ≤ 2 ^ (m + N + 1) := pow_le_pow_right₀ one_le_two (by omega)
    nlinarith [φ.rOut_pos]
  · rw [pow_add, pow_succ, pow_add]
    field_simp

/-- **The spectrum of a term of the paraproduct `T_u v`.** The Fourier transform of
`S_{j-N} u · Δⱼ v` vanishes outside the annulus
`2^{j-1} (φ.rIn - 2^{-N} φ.rOut) ≤ ‖ξ‖ ≤ 2^{j+1} φ.rOut`. The inner radius is positive when
`2^N φ.rIn > φ.rOut`. -/
theorem isVanishingOn_fourier_lowPass_smul_block (N j : ℕ) (u : BesovSpace ℂ φ s p₁ q)
    (v : BesovSpace F φ s' p₂ q') :
    IsVanishingOn (𝓕 ((u.lowPass (j - N) • v.block j : Lp F r (volume : Measure E)) :
        𝓢'(E, F)) : 𝓢'(E, F))
      (closedBall 0 (2 ^ j * (2 * φ.rOut)) \
        ball 0 (2 ^ j * ((φ.rIn - φ.rOut / 2 ^ N) / 2)))ᶜ := by
  rcases le_or_gt j N with hjN | hjN
  · -- For `j ≤ N` the cut-off `S_{j-N} = S_0` vanishes.
    rw [Nat.sub_eq_zero_of_le hjN, lowPass_zero_right, Lp.zero_smul]
    intro ψ _
    simp
  obtain ⟨m, rfl⟩ : ∃ m, j = m + N + 1 := ⟨j - N - 1, by omega⟩
  rw [show m + N + 1 - N = m + 1 by omega]
  have hv := v.coe_block (m + N + 1) ▸ isVanishingOn_fourier_littlewoodPaleyBlock_succ φ (m + N)
    v.toDistr
  have h := Lp.isVanishingOn_fourier_smul (r := r) (isCompact_closedBall _ _)
    ((isCompact_closedBall _ _).diff isOpen_ball) (u.isVanishingOn_fourier_lowPass_succ m) hv
  exact h.mono (compl_subset_compl.2 (closedBall_add_annulus_subset φ N m))

/-- **The spectrum of a term of the paraproduct `T_v u`.** The Fourier transform of
`Δⱼ u · S_{j-N} v` vanishes outside the annulus
`2^{j-1} (φ.rIn - 2^{-N} φ.rOut) ≤ ‖ξ‖ ≤ 2^{j+1} φ.rOut`. -/
theorem isVanishingOn_fourier_block_smul_lowPass (N j : ℕ) (u : BesovSpace ℂ φ s p₁ q)
    (v : BesovSpace F φ s' p₂ q') :
    IsVanishingOn (𝓕 ((u.block j • v.lowPass (j - N) : Lp F r (volume : Measure E)) :
        𝓢'(E, F)) : 𝓢'(E, F))
      (closedBall 0 (2 ^ j * (2 * φ.rOut)) \
        ball 0 (2 ^ j * ((φ.rIn - φ.rOut / 2 ^ N) / 2)))ᶜ := by
  rcases le_or_gt j N with hjN | hjN
  · rw [Nat.sub_eq_zero_of_le hjN, lowPass_zero_right, Lp.smul_zero]
    intro ψ _
    simp
  obtain ⟨m, rfl⟩ : ∃ m, j = m + N + 1 := ⟨j - N - 1, by omega⟩
  rw [show m + N + 1 - N = m + 1 by omega]
  have hu := u.coe_block (m + N + 1) ▸ isVanishingOn_fourier_littlewoodPaleyBlock_succ φ (m + N)
    u.toDistr
  have h := Lp.isVanishingOn_fourier_smul (r := r) ((isCompact_closedBall _ _).diff isOpen_ball)
    (isCompact_closedBall _ _) hu (v.isVanishingOn_fourier_lowPass_succ m)
  exact h.mono (compl_subset_compl.2
    ((add_comm _ _).subset.trans (closedBall_add_annulus_subset φ N m)))

/-- **The spectrum of a term of the resonant part.** If every index in `t` is at most `j + N`,
then the Fourier transform of `Δⱼ u · ∑_{k ∈ t} Δₖ v` vanishes outside the closed ball of radius
`2^j (1 + 2^N) φ.rOut`. The resonant part `R(u, v)` with gap `N` has the terms with
`t = {k | |k - j| ≤ N}`. -/
theorem isVanishingOn_fourier_block_smul_sum_block (N j : ℕ) {t : Finset ℕ}
    (ht : ∀ k ∈ t, k ≤ j + N) (u : BesovSpace ℂ φ s p₁ q) (v : BesovSpace F φ s' p₂ q') :
    IsVanishingOn (𝓕 ((u.block j • ∑ k ∈ t, v.block k : Lp F r (volume : Measure E)) :
        𝓢'(E, F)) : 𝓢'(E, F))
      (closedBall 0 (2 ^ j * ((1 + 2 ^ N) * φ.rOut)))ᶜ := by
  have hu := u.coe_block j ▸ isVanishingOn_fourier_littlewoodPaleyBlock φ j u.toDistr
  have hv : IsVanishingOn (𝓕 ((∑ k ∈ t, v.block k : Lp F p₂ (volume : Measure E)) : 𝓢'(E, F)) :
      𝓢'(E, F)) (closedBall 0 (2 ^ (j + N) * φ.rOut))ᶜ := by
    simpa only [Lp.toTemperedDistribution_sum, coe_block] using
      isVanishingOn_fourier_sum_littlewoodPaleyBlock φ ht v.toDistr
  have h := Lp.isVanishingOn_fourier_smul_closedBall (r := r)
    (mul_pos (pow_pos two_pos _) φ.rOut_pos).le (mul_pos (pow_pos two_pos _) φ.rOut_pos).le hu hv
  rwa [zero_add, pow_add, show (2 : ℝ) ^ j * φ.rOut + 2 ^ j * 2 ^ N * φ.rOut =
    2 ^ j * ((1 + 2 ^ N) * φ.rOut) by ring] at h

end Spectrum

section Decomposition

variable {s' : ℝ} {q' p₁ p₂ r : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [p₁.HolderTriple p₂ r]

/-- **Bony's decomposition.** For every gap `N`, the product of the low-frequency cut-offs
`S_M u · S_M v = ∑_{k, l < M} Δₖ u · Δₗ v` splits into the truncated paraproducts
`∑_{j < M} S_{j-N} u · Δⱼ v` (the pairs with `k + N < l`) and `∑_{j < M} Δⱼ u · S_{j-N} v` (the
pairs with `l + N < k`) and the truncated resonant part, the pairs with `|k - l| ≤ N`. -/
theorem lowPass_smul_lowPass (N M : ℕ) (u : BesovSpace ℂ φ s p₁ q) (v : BesovSpace F φ s' p₂ q') :
    (u.lowPass M • v.lowPass M : Lp F r (volume : Measure E)) =
      ∑ j ∈ Finset.range M, (u.lowPass (j - N) • v.block j : Lp F r (volume : Measure E)) +
        ∑ j ∈ Finset.range M, (u.block j • v.lowPass (j - N) : Lp F r (volume : Measure E)) +
        ∑ j ∈ Finset.range M, (u.block j •
          ∑ k ∈ (Finset.range M).filter (fun k ↦ k ≤ j + N ∧ j ≤ k + N), v.block k :
            Lp F r (volume : Measure E)) := by
  set g : ℕ → ℕ → Lp F r (volume : Measure E) := fun k l ↦ u.block k • v.block l
  set P := Finset.range M ×ˢ Finset.range M
  -- Expand every term as a sum of products of blocks over a set of pairs of indices.
  have hL : (u.lowPass M • v.lowPass M : Lp F r (volume : Measure E)) = ∑ x ∈ P, g x.1 x.2 := by
    rw [lowPass_eq_sum, lowPass_eq_sum, Lp.sum_smul, Finset.sum_product]
    simp only [Lp.smul_sum, g]
  have hT : ∑ j ∈ Finset.range M, (u.lowPass (j - N) • v.block j : Lp F r (volume : Measure E)) =
      ∑ x ∈ P.filter (fun x ↦ x.1 + N < x.2), g x.1 x.2 := by
    rw [Finset.sum_finset_product_right' _ (Finset.range M) (fun l ↦ Finset.range (l - N))
      fun x ↦ by simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; omega]
    simp only [lowPass_eq_sum, Lp.sum_smul, g]
  have hT' : ∑ j ∈ Finset.range M, (u.block j • v.lowPass (j - N) : Lp F r (volume : Measure E)) =
      ∑ x ∈ P.filter (fun x ↦ x.2 + N < x.1), g x.1 x.2 := by
    rw [Finset.sum_finset_product' _ (Finset.range M) (fun k ↦ Finset.range (k - N))
      fun x ↦ by simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; omega]
    simp only [lowPass_eq_sum, Lp.smul_sum, g]
  have hR : ∑ j ∈ Finset.range M, (u.block j •
        ∑ k ∈ (Finset.range M).filter (fun k ↦ k ≤ j + N ∧ j ≤ k + N), v.block k :
          Lp F r (volume : Measure E)) =
      ∑ x ∈ P.filter (fun x ↦ x.2 ≤ x.1 + N ∧ x.1 ≤ x.2 + N), g x.1 x.2 := by
    rw [Finset.sum_finset_product' _ (Finset.range M)
      (fun k ↦ (Finset.range M).filter (fun l ↦ l ≤ k + N ∧ k ≤ l + N))
      fun x ↦ by simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; tauto]
    simp only [Lp.smul_sum, g]
  -- The three conditions on a pair of indices are exclusive and exhaustive.
  rw [hL, hT, hT', hR, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  split_ifs <;> first | (exfalso; omega) | simp

end Decomposition

end TauCeti.BesovSpace
