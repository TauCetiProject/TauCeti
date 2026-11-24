/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.LowPass
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.ProductSpectrum
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Annulus
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Ball
import TauCeti.Analysis.Normed.Group.Pointwise
import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.Analysis.SpecialFunctions.Pow.Real
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

The sizes of the terms are controlled by those of the low-frequency cut-offs and the blocks,
through Hölder's inequality `‖f g‖_r ≤ ‖f‖_{p₁} ‖g‖_{p₂}` (`MeasureTheory.Lp.norm_smul_le`). The
cut-offs are bounded in two ways: if `u` is an `Lᵖ` function, then `‖S_m u‖_p ≤ ‖𝓕⁻ φ‖₁ ‖u‖_p`
for every `m`, since `S_m` is convolution with an `L¹`-dilate of `𝓕⁻ φ`
(`TauCeti.BesovSpace.norm_lowPass_le_of_toDistr_eq`); and if `u ∈ B^α_{p,q}` with `α < 0`, then
`‖S_m u‖_p ≤ 2^{-α m} ‖u‖ / (2^{-α} - 1)`, summing the geometric bounds of the blocks
(`TauCeti.BesovSpace.norm_lowPass_le_of_neg`).

Together these give the **paraproduct and resonant estimates** of Bahouri–Chemin–Danchin
(Theorems 2.82 and 2.85). With `1/r = 1/p₁ + 1/p₂` and `v ∈ B^β_{p₂,q}`, the paraproduct `T_u v`
converges in the tempered distributions and lies in `B^β_{r,q}` with norm `O(‖u‖_{p₁} ‖v‖)` when
`u` is an `L^{p₁}` function, and in `B^{α+β}_{r,q}` with norm `O(‖u‖ ‖v‖)` when `u ∈ B^α_{p₁,q₁}`
with `α < 0`; the terms are summed by the reconstruction from pieces with spectra in dyadic
annuli (`TauCeti.BesovSpace.exists_hasSum_toDistr_and_norm_le_of_annulus`), which needs no
condition on the regularity. When `α + β > 0` the resonant part `R(u, v)` lies in
`B^{α+β}_{r,q}` with norm `O(‖u‖ ‖v‖)`, by the reconstruction from pieces with spectra in dyadic
balls (`TauCeti.BesovSpace.exists_hasSum_toDistr_and_norm_le_of_ball`). For `p₁ = p₂ = r = ∞`
and `q = q₁ = ∞` these are the estimates `‖T_u v‖_{𝒞^β} ≲ ‖u‖_∞ ‖v‖_{𝒞^β}`,
`‖T_u v‖_{𝒞^{α+β}} ≲ ‖u‖_{𝒞^α} ‖v‖_{𝒞^β}` for `α < 0`, and
`‖R(u, v)‖_{𝒞^{α+β}} ≲ ‖u‖_{𝒞^α} ‖v‖_{𝒞^β}` for `α + β > 0` on the Hölder–Zygmund scale. The
constants depend only on the bump function, the gap and the regularities.

## Main declarations

* `TauCeti.BesovSpace.isVanishingOn_fourier_lowPass_smul_block` and
  `TauCeti.BesovSpace.isVanishingOn_fourier_block_smul_lowPass`: the terms of the two paraproducts
  have spectra in dyadic annuli.
* `TauCeti.BesovSpace.isVanishingOn_fourier_block_smul_sum_block`: the terms of the resonant part
  have spectra in dyadic balls.
* `TauCeti.BesovSpace.lowPass_smul_lowPass`: Bony's decomposition of `S_M u · S_M v`.
* `TauCeti.BesovSpace.exists_hasSum_lowPass_smul_block_and_norm_le_of_toDistr_eq` and
  `TauCeti.BesovSpace.exists_hasSum_lowPass_smul_block_and_norm_le_of_neg`: the paraproduct
  estimates for `T_u v`, with a bounded or a negative-regularity low-frequency factor;
  `TauCeti.BesovSpace.exists_hasSum_block_smul_lowPass_and_norm_le_of_toDistr_eq` and
  `TauCeti.BesovSpace.exists_hasSum_block_smul_lowPass_and_norm_le_of_neg` are the same estimates
  for `T_v u`, whose low-frequency factor is vector-valued.
* `TauCeti.BesovSpace.rpow_mul_norm_block_smul_sum_block_le`: the weighted bound on the terms of
  the resonant part, and on their sub-sums.
* `TauCeti.BesovSpace.exists_hasSum_block_smul_sum_block_and_norm_le`: the resonant estimate.

## References

* J.-M. Bony, *Calcul symbolique et propagation des singularités pour les équations aux dérivées
  partielles non linéaires*, Ann. Sci. École Norm. Sup. (4) 14 (1981), 209–246.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Chapter 2
  (Bony's decomposition and the proofs of the paraproduct and remainder estimates, Theorems 2.82
  and 2.85).
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
  rw [lowPass_eq_sum, lowPass_eq_sum, Lp.sum_smul,
    Finset.sum_congr rfl fun k _ ↦ Lp.smul_sum _ _ _, Finset.sum_range_sum_range_split_gap N]
  simp only [lowPass_eq_sum, Lp.sum_smul, Lp.smul_sum]

end Decomposition

section Estimates

/-!
### The paraproduct and resonant estimates

The infinite paraproducts `T_u v = ∑ⱼ S_{j-N} u · Δⱼ v` and `T_v u = ∑ⱼ Δⱼ u · S_{j-N} v` and the
resonant part `R(u, v) = ∑ⱼ Δⱼ u · ∑_{|k - j| ≤ N} Δₖ v` are series in the tempered distributions.
For the paraproducts, with `2^N φ.rIn > φ.rOut`, the terms have spectra in dyadic annuli, so the
series converge for every regularity and are summed into Besov spaces by
`TauCeti.BesovSpace.exists_hasSum_toDistr_and_norm_le_of_annulus`; the terms of the resonant part
only have spectra in dyadic balls, so it is summed by
`TauCeti.BesovSpace.exists_hasSum_toDistr_and_norm_le_of_ball`, which needs positive total
regularity. In each case the weighted norm of the `j`-th term is bounded by Hölder's inequality and
the bounds on the cut-offs and the blocks of the two factors. The constants depend only on the bump
function, the gap `N` and the regularities, not on the integrability exponents.
-/

variable (φ)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The inner radius `(φ.rIn - 2^{-N} φ.rOut) / 2` of the annuli carrying the terms of the
paraproducts is positive when `φ.rOut < 2^N φ.rIn`. -/
private theorem paraproduct_inner_radius_pos {N : ℕ} (hN : φ.rOut < 2 ^ N * φ.rIn) :
    0 < (φ.rIn - φ.rOut / 2 ^ N) / 2 := by
  have h : φ.rOut / 2 ^ N < φ.rIn := by
    rw [div_lt_iff₀ (by positivity)]
    linarith
  linarith

variable {φ}

/-- For `s < 0`, the low-frequency cut-off at `j - N` satisfies
`2^{js} ‖S_{j-N} u‖_p ≤ ‖u‖ / (2^{-s} - 1)`: by `TauCeti.BesovSpace.norm_lowPass_le_of_neg`,
`‖S_{j-N} u‖_p ≤ 2^{-s (j - N)} ‖u‖ / (2^{-s} - 1)`, and `2^{js} 2^{-s (j - N)} ≤ 1`. -/
private theorem rpow_mul_norm_lowPass_sub_le_of_neg [Fact (1 ≤ q)] (hs : s < 0)
    (u : BesovSpace F φ s p q) (N j : ℕ) :
    2 ^ (s * j) * ‖u.lowPass (j - N)‖ ≤ ‖u‖ / (2 ^ (-s) - 1) := by
  have hD : (0 : ℝ) < 2 ^ (-s) - 1 := sub_pos.2 (Real.one_lt_rpow one_lt_two (neg_pos.2 hs))
  calc 2 ^ (s * j) * ‖u.lowPass (j - N)‖
      ≤ 2 ^ (s * j) * (2 ^ (-s * (j - N : ℕ)) / (2 ^ (-s) - 1) * ‖u‖) := by
        gcongr
        exact norm_lowPass_le_of_neg hs u _
    _ = 2 ^ (s * j) * 2 ^ (-s * (j - N : ℕ)) * (‖u‖ / (2 ^ (-s) - 1)) := by ring
    _ ≤ 1 * (‖u‖ / (2 ^ (-s) - 1)) := by
        gcongr
        exact Real.rpow_mul_mul_rpow_neg_mul_le_one one_le_two hs.le
          (by exact_mod_cast Nat.sub_le j N)
    _ = _ := one_mul _

variable (φ) in
/-- **Series of annular pieces dominated by the blocks of a Besov element.** There is `C ≥ 0`,
depending only on `φ`, `s`, `a` and `b`, with the following property. If `gⱼ ∈ Lᵖ` has spectrum in
the annulus `2^j a ≤ ‖ξ‖ ≤ 2^j b` and `2^{js} ‖gⱼ‖_p ≤ K 2^{jβ} ‖Δⱼ v‖_{p'}` for some
`v ∈ B^β_{p',q}`, then `∑ⱼ gⱼ` converges in the tempered distributions to an element of
`B^s_{p,q}` of norm at most `C K ‖v‖`. -/
private theorem exists_hasSum_and_norm_le_of_annulus_of_block {F' : Type*} [NormedAddCommGroup F']
    [NormedSpace ℂ F'] [CompleteSpace F'] (s β : ℝ) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p p' q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')] [Fact (1 ≤ q)]
      (g : ℕ → Lp F p (volume : Measure E)) (v : BesovSpace F' φ β p' q) {K : ℝ}, 0 ≤ K →
      (∀ j : ℕ, IsVanishingOn (𝓕 (g j : 𝓢'(E, F)) : 𝓢'(E, F))
        (closedBall 0 (2 ^ j * b) \ ball 0 (2 ^ j * a))ᶜ) →
      (∀ j : ℕ, 2 ^ (s * j) * ‖g j‖ ≤ K * (2 ^ (β * j) * ‖v.block j‖)) →
      ∃ w : BesovSpace F φ s p q, HasSum (fun j ↦ (g j : 𝓢'(E, F))) w.toDistr ∧
        ‖w‖ ≤ C * K * ‖v‖ := by
  obtain ⟨C, hC⟩ := exists_hasSum_toDistr_and_norm_le_of_annulus (F := F) φ s ha b
  refine ⟨max C 0, le_max_right _ _, fun {p p' q} _ _ _ g v K hK hg hgv ↦ ?_⟩
  set c := v.weightedBlockNorms
  have hc (j : ℕ) : c j = _ := v.weightedBlockNorms_apply j
  have hcv : ‖c‖ ≤ ‖v‖ := (norm_weightedBlockNorms v).le
  obtain ⟨w, hw, hwn⟩ := hC g (K • c) (fun j ↦ (hg j).mono (compl_subset_compl.2 sdiff_subset))
    (fun j _ ↦ (hg j).mono (subset_compl_iff_disjoint_right.2 disjoint_sdiff_right)) fun j ↦ by
      rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hc]
      exact hgv j
  refine ⟨w, hw, hwn.trans ?_⟩
  calc C * ‖K • c‖ ≤ max C 0 * (K * ‖v‖) := by
        rw [norm_smul, Real.norm_of_nonneg hK]
        gcongr
        exact le_max_left _ _
    _ = max C 0 * K * ‖v‖ := by ring

variable (φ) in
/-- **The paraproduct estimate for a bounded low-frequency factor** (Bahouri–Chemin–Danchin,
Theorem 2.82). Let `φ.rOut < 2^N φ.rIn`. There is `C ≥ 0`, depending only on `φ`, `N` and `β`, with
the following property for all exponents `1 ≤ p₁, p₂, r, q ≤ ∞` with `1/r = 1/p₁ + 1/p₂`. If the
tempered distribution of `u` is an `L^{p₁}` function `f` and `v ∈ B^β_{p₂,q}`, then the paraproduct
`T_u v = ∑ⱼ S_{j-N} u · Δⱼ v` converges in the tempered distributions to an element of
`B^β_{r,q}` of norm at most `C ‖f‖_{p₁} ‖v‖`. -/
theorem exists_hasSum_lowPass_smul_block_and_norm_le_of_toDistr_eq (β : ℝ) {N : ℕ}
    (hN : φ.rOut < 2 ^ N * φ.rIn) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)]
      [Fact (1 ≤ q)] [p₁.HolderTriple p₂ r] {α : ℝ} {q₁ : ℝ≥0∞} (u : BesovSpace ℂ φ α p₁ q₁)
      {f : Lp ℂ p₁ (volume : Measure E)}, u.toDistr = f → ∀ v : BesovSpace F φ β p₂ q,
      ∃ w : BesovSpace F φ β r q,
        HasSum (fun j ↦ ((u.lowPass (j - N) • v.block j : Lp F r (volume : Measure E)) :
          𝓢'(E, F))) w.toDistr ∧ ‖w‖ ≤ C * ‖f‖ * ‖v‖ := by
  obtain ⟨C, hC, hCw⟩ := exists_hasSum_and_norm_le_of_annulus_of_block (F := F) (F' := F) φ β β
    (paraproduct_inner_radius_pos φ hN) (2 * φ.rOut)
  set A := ∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖
  refine ⟨C * A, by positivity, fun {p₁ p₂ r q} _ _ _ _ _ {α q₁} u f hf v ↦ ?_⟩
  obtain ⟨w, hw, hwn⟩ := hCw (fun j ↦ (u.lowPass (j - N) • v.block j :
    Lp F r (volume : Measure E))) v (K := A * ‖f‖) (by positivity)
    (fun j ↦ isVanishingOn_fourier_lowPass_smul_block N j u v) fun j ↦ by
      calc 2 ^ (β * j) * ‖u.lowPass (j - N) • v.block j‖
          ≤ 2 ^ (β * j) * (‖u.lowPass (j - N)‖ * ‖v.block j‖) := by
            gcongr
            exact Lp.norm_smul_le _ _
        _ ≤ 2 ^ (β * j) * (A * ‖f‖ * ‖v.block j‖) := by
            gcongr
            exact norm_lowPass_le_of_toDistr_eq u hf _
        _ = A * ‖f‖ * (2 ^ (β * j) * ‖v.block j‖) := by ring
  exact ⟨w, hw, hwn.trans_eq (by ring)⟩

variable (φ) in
/-- **The paraproduct estimate for a low-frequency factor of negative regularity**
(Bahouri–Chemin–Danchin, Theorem 2.82). Let `α < 0` and `φ.rOut < 2^N φ.rIn`. There is `C ≥ 0`,
depending only on `φ`, `N`, `α` and `β`, with the following property for all exponents
`1 ≤ p₁, p₂, r, q, q₁ ≤ ∞` with `1/r = 1/p₁ + 1/p₂`. If `u ∈ B^α_{p₁,q₁}` and `v ∈ B^β_{p₂,q}`,
then the paraproduct `T_u v = ∑ⱼ S_{j-N} u · Δⱼ v` converges in the tempered distributions to an
element of `B^{α+β}_{r,q}` of norm at most `C ‖u‖ ‖v‖`. -/
theorem exists_hasSum_lowPass_smul_block_and_norm_le_of_neg {α : ℝ} (hα : α < 0) (β : ℝ)
    {N : ℕ} (hN : φ.rOut < 2 ^ N * φ.rIn) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q q₁ : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)]
      [Fact (1 ≤ q)] [Fact (1 ≤ q₁)] [p₁.HolderTriple p₂ r] (u : BesovSpace ℂ φ α p₁ q₁)
      (v : BesovSpace F φ β p₂ q), ∃ w : BesovSpace F φ (α + β) r q,
        HasSum (fun j ↦ ((u.lowPass (j - N) • v.block j : Lp F r (volume : Measure E)) :
          𝓢'(E, F))) w.toDistr ∧ ‖w‖ ≤ C * ‖u‖ * ‖v‖ := by
  obtain ⟨C, hC, hCw⟩ := exists_hasSum_and_norm_le_of_annulus_of_block (F := F) (F' := F) φ
    (α + β) β (paraproduct_inner_radius_pos φ hN) (2 * φ.rOut)
  have hD : (0 : ℝ) < 2 ^ (-α) - 1 := sub_pos.2 (Real.one_lt_rpow one_lt_two (neg_pos.2 hα))
  refine ⟨C / (2 ^ (-α) - 1), by positivity, fun {p₁ p₂ r q q₁} _ _ _ _ _ _ u v ↦ ?_⟩
  obtain ⟨w, hw, hwn⟩ := hCw (fun j ↦ (u.lowPass (j - N) • v.block j :
    Lp F r (volume : Measure E))) v (K := ‖u‖ / (2 ^ (-α) - 1)) (by positivity)
    (fun j ↦ isVanishingOn_fourier_lowPass_smul_block N j u v) fun j ↦ by
      calc 2 ^ ((α + β) * j) * ‖u.lowPass (j - N) • v.block j‖
          ≤ 2 ^ (α * j) * ‖u.lowPass (j - N)‖ * (2 ^ (β * j) * ‖v.block j‖) := by
            rw [add_mul, Real.rpow_add two_pos, mul_mul_mul_comm]
            gcongr
            exact Lp.norm_smul_le _ _
        _ ≤ _ := by
            gcongr
            exact rpow_mul_norm_lowPass_sub_le_of_neg hα u N j
  exact ⟨w, hw, hwn.trans_eq (by ring)⟩

variable (φ) in
/-- **The paraproduct estimate for a bounded low-frequency factor**, for the paraproduct
`T_v u = ∑ⱼ Δⱼ u · S_{j-N} v` whose low-frequency factor is vector-valued
(Bahouri–Chemin–Danchin, Theorem 2.82). Let `φ.rOut < 2^N φ.rIn`. There is `C ≥ 0`, depending only
on `φ`, `N` and `α`, with the following property for all exponents `1 ≤ p₁, p₂, r, q ≤ ∞` with
`1/r = 1/p₁ + 1/p₂`. If `u ∈ B^α_{p₁,q}` and the tempered distribution of `v` is an `L^{p₂}`
function `g`, then `T_v u` converges in the tempered distributions to an element of `B^α_{r,q}` of
norm at most `C ‖u‖ ‖g‖_{p₂}`. -/
theorem exists_hasSum_block_smul_lowPass_and_norm_le_of_toDistr_eq (α : ℝ) {N : ℕ}
    (hN : φ.rOut < 2 ^ N * φ.rIn) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)]
      [Fact (1 ≤ q)] [p₁.HolderTriple p₂ r] (u : BesovSpace ℂ φ α p₁ q) {β : ℝ} {q₂ : ℝ≥0∞}
      (v : BesovSpace F φ β p₂ q₂) {g : Lp F p₂ (volume : Measure E)}, v.toDistr = g →
      ∃ w : BesovSpace F φ α r q,
        HasSum (fun j ↦ ((u.block j • v.lowPass (j - N) : Lp F r (volume : Measure E)) :
          𝓢'(E, F))) w.toDistr ∧ ‖w‖ ≤ C * ‖u‖ * ‖g‖ := by
  obtain ⟨C, hC, hCw⟩ := exists_hasSum_and_norm_le_of_annulus_of_block (F := F) (F' := ℂ) φ α α
    (paraproduct_inner_radius_pos φ hN) (2 * φ.rOut)
  set A := ∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖
  refine ⟨C * A, by positivity, fun {p₁ p₂ r q} _ _ _ _ _ u {β q₂} v g hg ↦ ?_⟩
  obtain ⟨w, hw, hwn⟩ := hCw (fun j ↦ (u.block j • v.lowPass (j - N) :
    Lp F r (volume : Measure E))) u (K := A * ‖g‖) (by positivity)
    (fun j ↦ isVanishingOn_fourier_block_smul_lowPass N j u v) fun j ↦ by
      calc 2 ^ (α * j) * ‖u.block j • v.lowPass (j - N)‖
          ≤ 2 ^ (α * j) * (‖u.block j‖ * ‖v.lowPass (j - N)‖) := by
            gcongr
            exact Lp.norm_smul_le _ _
        _ ≤ 2 ^ (α * j) * (‖u.block j‖ * (A * ‖g‖)) := by
            gcongr
            exact norm_lowPass_le_of_toDistr_eq v hg _
        _ = A * ‖g‖ * (2 ^ (α * j) * ‖u.block j‖) := by ring
  exact ⟨w, hw, hwn.trans_eq (by ring)⟩

variable (φ) in
/-- **The paraproduct estimate for a low-frequency factor of negative regularity**, for the
paraproduct `T_v u = ∑ⱼ Δⱼ u · S_{j-N} v` whose low-frequency factor is vector-valued
(Bahouri–Chemin–Danchin, Theorem 2.82). Let `β < 0` and `φ.rOut < 2^N φ.rIn`. There is `C ≥ 0`,
depending only on `φ`, `N`, `α` and `β`, with the following property for all exponents
`1 ≤ p₁, p₂, r, q, q₂ ≤ ∞` with `1/r = 1/p₁ + 1/p₂`. If `u ∈ B^α_{p₁,q}` and `v ∈ B^β_{p₂,q₂}`,
then `T_v u` converges in the tempered distributions to an element of `B^{α+β}_{r,q}` of norm at
most `C ‖u‖ ‖v‖`. -/
theorem exists_hasSum_block_smul_lowPass_and_norm_le_of_neg (α : ℝ) {β : ℝ} (hβ : β < 0)
    {N : ℕ} (hN : φ.rOut < 2 ^ N * φ.rIn) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q q₂ : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)]
      [Fact (1 ≤ q)] [Fact (1 ≤ q₂)] [p₁.HolderTriple p₂ r] (u : BesovSpace ℂ φ α p₁ q)
      (v : BesovSpace F φ β p₂ q₂), ∃ w : BesovSpace F φ (α + β) r q,
        HasSum (fun j ↦ ((u.block j • v.lowPass (j - N) : Lp F r (volume : Measure E)) :
          𝓢'(E, F))) w.toDistr ∧ ‖w‖ ≤ C * ‖u‖ * ‖v‖ := by
  obtain ⟨C, hC, hCw⟩ := exists_hasSum_and_norm_le_of_annulus_of_block (F := F) (F' := ℂ) φ
    (α + β) α (paraproduct_inner_radius_pos φ hN) (2 * φ.rOut)
  have hD : (0 : ℝ) < 2 ^ (-β) - 1 := sub_pos.2 (Real.one_lt_rpow one_lt_two (neg_pos.2 hβ))
  refine ⟨C / (2 ^ (-β) - 1), by positivity, fun {p₁ p₂ r q q₂} _ _ _ _ _ _ u v ↦ ?_⟩
  obtain ⟨w, hw, hwn⟩ := hCw (fun j ↦ (u.block j • v.lowPass (j - N) :
    Lp F r (volume : Measure E))) u (K := ‖v‖ / (2 ^ (-β) - 1)) (by positivity)
    (fun j ↦ isVanishingOn_fourier_block_smul_lowPass N j u v) fun j ↦ by
      calc 2 ^ ((α + β) * j) * ‖u.block j • v.lowPass (j - N)‖
          ≤ 2 ^ (α * j) * ‖u.block j‖ * (2 ^ (β * j) * ‖v.lowPass (j - N)‖) := by
            rw [add_mul, Real.rpow_add two_pos, mul_mul_mul_comm]
            gcongr
            exact Lp.norm_smul_le _ _
        _ ≤ 2 ^ (α * j) * ‖u.block j‖ * (‖v‖ / (2 ^ (-β) - 1)) := by
            gcongr
            exact rpow_mul_norm_lowPass_sub_le_of_neg hβ v N j
        _ = _ := mul_comm _ _
  exact ⟨w, hw, hwn.trans_eq (by ring)⟩

/-- **The terms of the resonant part.** For `u ∈ B^α_{p₁,q₁}`, `v ∈ B^β_{p₂,q}` and a set `t` of
block indices with `|k - j| ≤ N` for `k ∈ t`, with `L = N + 1`,
`2^{j(α+β)} ‖Δⱼ u · ∑_{k ∈ t} Δₖ v‖_r ≤ ‖u‖ 2^{|β| L} ∑_{j - L ≤ k < j + L} 2^{kβ} ‖Δₖ v‖`.
For `t = [j - N, j + N]` this bounds the `j`-th term of `R(u, v)` with gap `N`. -/
theorem rpow_mul_norm_block_smul_sum_block_le {α β : ℝ} {p₁ p₂ r q q₁ : ℝ≥0∞}
    [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ q₁)] [p₁.HolderTriple p₂ r]
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q) {N j : ℕ} {t : Finset ℕ}
    (ht : t ⊆ Finset.Icc (j - N) (j + N)) :
    2 ^ ((α + β) * j) * ‖(u.block j • ∑ k ∈ t, v.block k : Lp F r (volume : Measure E))‖ ≤
      ‖u‖ * (2 ^ (|β| * (N + 1 : ℕ)) *
        ∑ k ∈ Finset.Ico (j - (N + 1)) (j + (N + 1)), 2 ^ (β * k) * ‖v.block k‖) := by
  -- This combines `2^{jα} ‖Δⱼ u‖_{p₁} ≤ ‖u‖` with `2^{jβ} ≤ 2^{|β| L} 2^{kβ}` for `|k - j| ≤ N`.
  have hsub : t ⊆ Finset.Ico (j - (N + 1)) (j + (N + 1)) := fun k hk ↦ by
    have := ht hk
    simp only [Finset.mem_Icc, Finset.mem_Ico] at this ⊢
    omega
  have hv : 2 ^ (β * j) * ‖∑ k ∈ t, v.block k‖ ≤
      2 ^ (|β| * (N + 1 : ℕ)) *
        ∑ k ∈ Finset.Ico (j - (N + 1)) (j + (N + 1)), 2 ^ (β * k) * ‖v.block k‖ := by
    -- Extend the sum over `t` by zero to the window `Ico (j - L) (j + L)`.
    rw [← Finset.inter_eq_right.2 hsub, ← Finset.sum_ite_mem]
    refine (TauCeti.two_rpow_mul_norm_sum_Ico_le β (C := 1) (x := v.block)
      (fun k ↦ by split_ifs <;> simp) j (N + 1)).trans_eq ?_
    rw [max_eq_left zero_le_one, one_mul]
  calc 2 ^ ((α + β) * j) * ‖(u.block j • ∑ k ∈ t, v.block k : Lp F r (volume : Measure E))‖
      ≤ 2 ^ (α * j) * ‖u.block j‖ * (2 ^ (β * j) * ‖∑ k ∈ t, v.block k‖) := by
        rw [add_mul, Real.rpow_add two_pos, mul_mul_mul_comm]
        gcongr
        exact Lp.norm_smul_le _ _
    _ ≤ _ := by
        gcongr
        exact u.rpow_mul_norm_block_le j

variable (φ) in
/-- **The resonant estimate** (Bahouri–Chemin–Danchin, Theorem 2.85). Let `0 < α + β` and let `N`
be a gap. There is `C ≥ 0`, depending only on `φ`, `N`, `α` and `β`, with the following property
for all exponents `1 ≤ p₁, p₂, r, q, q₁ ≤ ∞` with `1/r = 1/p₁ + 1/p₂`. If `u ∈ B^α_{p₁,q₁}` and
`v ∈ B^β_{p₂,q}`, then the resonant part `R(u, v) = ∑ⱼ Δⱼ u · ∑_{|k - j| ≤ N} Δₖ v` converges in
the tempered distributions to an element of `B^{α+β}_{r,q}` of norm at most `C ‖u‖ ‖v‖`. -/
theorem exists_hasSum_block_smul_sum_block_and_norm_le {α β : ℝ} (hαβ : 0 < α + β) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q q₁ : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)]
      [Fact (1 ≤ q)] [Fact (1 ≤ q₁)] [p₁.HolderTriple p₂ r] (u : BesovSpace ℂ φ α p₁ q₁)
      (v : BesovSpace F φ β p₂ q), ∃ w : BesovSpace F φ (α + β) r q,
        HasSum (fun j ↦ ((u.block j • ∑ k ∈ Finset.Icc (j - N) (j + N), v.block k :
          Lp F r (volume : Measure E)) : 𝓢'(E, F))) w.toDistr ∧ ‖w‖ ≤ C * ‖u‖ * ‖v‖ := by
  obtain ⟨C, hC, hCw⟩ :=
    exists_hasSum_toDistr_and_norm_le_of_ball (F := F) φ hαβ ((1 + 2 ^ N) * φ.rOut)
  set L : ℕ := N + 1
  refine ⟨C * 2 ^ (|β| * L) * (2 * L), by positivity,
    fun {p₁ p₂ r q q₁} _ _ _ _ _ _ u v ↦ ?_⟩
  set c := v.weightedBlockNorms
  have hc (j : ℕ) : c j = _ := v.weightedBlockNorms_apply j
  have hcv : ‖c‖ ≤ ‖v‖ := (norm_weightedBlockNorms v).le
  -- The window sums of the weighted block norms of `v`, as an element of `ℓ^q`.
  obtain ⟨W, hW, hWn⟩ := lp.exists_eq_sum_Ico_sub_add_and_norm_le c L
  obtain ⟨w, hw, hwn⟩ := hCw _ ((‖u‖ * 2 ^ (|β| * L)) • W)
    (fun j ↦ isVanishingOn_fourier_block_smul_sum_block N j
      (fun k hk ↦ (Finset.mem_Icc.1 hk).2) u v) fun j ↦ by
      rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hW, mul_assoc]
      have h := rpow_mul_norm_block_smul_sum_block_le (r := r) (N := N) (j := j) u v subset_rfl
      simp only [← hc] at h
      exact h
  refine ⟨w, hw, hwn.trans ?_⟩
  calc C * ‖(‖u‖ * 2 ^ (|β| * L)) • W‖ ≤ C * (‖u‖ * 2 ^ (|β| * L) * (2 * L * ‖v‖)) := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        gcongr
        exact hWn.trans (by gcongr)
    _ = C * 2 ^ (|β| * L) * (2 * L) * ‖u‖ * ‖v‖ := by ring

end Estimates

end TauCeti.BesovSpace
