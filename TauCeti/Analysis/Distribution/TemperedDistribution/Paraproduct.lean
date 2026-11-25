/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.WeightedApproximateIdentity

/-!
# Bony's decomposition of a product of bounded functions

Let `Δₖ` be the inhomogeneous Littlewood–Paley blocks built from a bump function `φ`
(`littlewoodPaleyBlock`) and `Sⱼ = ∑_{k < j} Δₖ` the low-frequency
truncations (`littlewoodPaleyLowPass`). For bounded functions `f` and `g`,
**Bony's decomposition** splits the product into two paraproducts and a resonant term,

`f g = T_f g + T_g f + R(f, g)`, where `T_f g = ∑ⱼ S_{j-1} f · Δⱼ g`,
`T_g f = ∑ₖ Δₖ f · S_{k-1} g` and `R(f, g) = ∑_{|j - k| ≤ 1} Δₖ f · Δⱼ g`.

The three sums run over the pairs `(k, j)` of block indices with `k ≤ j - 2`, `j ≤ k - 2` and
`|j - k| ≤ 1` respectively, which partition all pairs. This file proves the decomposition at the
level of the dyadic partial sums:

* `TemperedDistribution.tendsto_toTemperedDistribution_smul_of_littlewoodPaleyLowPass_eq`: the
  products `Sⱼ f · Sⱼ g` of the low-frequency truncations of `f, g ∈ L^∞` converge to `f g` in the
  tempered distributions. The truncations converge to `f` and `g` only weakly-* in `L^∞`, which
  alone does not pass to products. But `S_{j+1}` is the average against the dilates
  `2^{jn} 𝓕⁻ φ (2^j ·)` of the Schwartz kernel `𝓕⁻ φ`, whose integral is `φ 0 = 1`
  (`ae_eq_integral_of_littlewoodPaleyLowPass_succ_eq`). So `S_{j+1} f → f`
  in `L¹` against every integrable weight
  (`MeasureTheory.tendsto_lintegral_eNorm_mul_eNorm_integral_smul_comp_sub_smul_sub`), and the
  truncations are bounded in `L^∞` uniformly in `j`
  (`exists_littlewoodPaleyLowPass_succ_eq_and_norm_le`). Writing
  `Sⱼ f · Sⱼ g - f g = (Sⱼ f - f) · Sⱼ g + f · (Sⱼ g - g)` and pairing with a Schwartz function
  gives the convergence.
* `TemperedDistribution.tendsto_toTemperedDistribution_paraproduct_add_paraproduct_add_resonant`:
  **Bony's decomposition**. Since `S_N f · S_N g = ∑_{k, j < N} Δₖ f · Δⱼ g`, sorting the pairs
  `(k, j)` into the three classes writes `S_N f · S_N g` as the sum of the partial sums of
  `T_f g`, `T_g f` and `R(f, g)` up to `N`, and this sum converges to `f g`.

The spectral localization of the terms, and the corresponding finite decomposition of
`S_M u · S_M v` for elements of Besov spaces, are in
`TauCeti.Analysis.FunctionalSpaces.BesovSpace.Paraproduct`.

The blocks and truncations of an `L^∞` function are `L^∞` functions
(`exists_littlewoodPaleyBlock_eq_and_norm_le`,
`exists_littlewoodPaleyLowPass_succ_eq_and_norm_le`), and the truncations are represented by the
sums of the representatives of the blocks (`littlewoodPaleyLowPass_eq_sum`); the statements take
these functions as data, through the hypotheses identifying their tempered distributions.

## References

* J.-M. Bony, *Calcul symbolique et propagation des singularités pour les équations aux dérivées
  partielles non linéaires*, Ann. Sci. École Norm. Sup. (4) 14 (1981), 209–246.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Section 2.6.1
  (Definition 2.78 and the decomposition `uv = T_u v + T_v u + R(u, v)`).
-/

public section

open MeasureTheory Filter Topology Set Finset
open scoped ENNReal FourierTransform SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TemperedDistribution

variable (φ : ContDiffBump (0 : E))

/-- `S_{j+1}` averages against the dilates of `𝓕⁻ φ` by `2^{-j} → 0`, so it converges to the
identity in `L¹` against the weight `ψ`: if `u ∈ L^∞` and `Sⱼ u = cⱼ ∈ L^∞`, then
`∫ |ψ| ‖c_{j+1} - u‖ → 0`. -/
private theorem tendsto_lintegral_eNorm_mul_eNorm_sub_of_littlewoodPaleyLowPass_eq (ψ : 𝓢(E, ℂ))
    (u : Lp F ∞ (volume : Measure E)) {c : ℕ → Lp F ∞ (volume : Measure E)}
    (hc : ∀ j, littlewoodPaleyLowPass F φ j (u : 𝓢'(E, F)) = c j) :
    Tendsto (fun j ↦ ∫⁻ x, ‖ψ x‖ₑ * ‖c (j + 1) x - u x‖ₑ) atTop (𝓝 0) := by
  have hdil : Tendsto (fun j : ℕ ↦ ((2 : ℝ) ^ j)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  refine ((tendsto_lintegral_eNorm_mul_eNorm_integral_smul_comp_sub_smul_sub
    φ.integrable_fourierInv φ.integral_fourierInv ψ.integrable (Lp.aestronglyMeasurable u)
    (Lp.ae_norm_le_norm_top u)).comp hdil).congr fun j ↦ ?_
  refine lintegral_congr_ae <|
    (ae_eq_integral_of_littlewoodPaleyLowPass_succ_eq φ j (hc (j + 1))).mono fun x hx ↦ ?_
  dsimp only [Function.comp_apply] at hx ⊢
  rw [hx]

/-- **The products of the low-frequency truncations converge to the product.** Let `f, g ∈ L^∞`,
and let `aⱼ, bⱼ ∈ L^∞` be their low-frequency truncations, `Sⱼ f = aⱼ` and `Sⱼ g = bⱼ`. Then
`aⱼ · bⱼ → f · g` in the tempered distributions. -/
theorem tendsto_toTemperedDistribution_smul_of_littlewoodPaleyLowPass_eq
    (f : Lp ℂ ∞ (volume : Measure E)) (g : Lp F ∞ (volume : Measure E))
    {a : ℕ → Lp ℂ ∞ (volume : Measure E)} {b : ℕ → Lp F ∞ (volume : Measure E)}
    (ha : ∀ j, littlewoodPaleyLowPass ℂ φ j (f : 𝓢'(E, ℂ)) = a j)
    (hb : ∀ j, littlewoodPaleyLowPass F φ j (g : 𝓢'(E, F)) = b j) :
    Tendsto (fun j ↦ ((a j • b j : Lp F ∞ (volume : Measure E)) : 𝓢'(E, F))) atTop
      (𝓝 ((f • g : Lp F ∞ (volume : Measure E)) : 𝓢'(E, F))) := by
  -- The truncations of `g` are bounded in `L^∞` uniformly in `j`.
  set C := ∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖
  have hbC : ∀ j, ‖b (j + 1)‖ₑ ≤ ENNReal.ofReal (C * ‖g‖) := fun j ↦ by
    obtain ⟨g', hg', hg'C⟩ := exists_littlewoodPaleyLowPass_succ_eq_and_norm_le φ j g
    rw [Lp.toTemperedDistribution_injective ((hb (j + 1)).symm.trans hg'), ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hg'C
  refine PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.2 fun ψ ↦ ?_
  simp only [Lp.toTemperedDistribution_apply]
  rw [← tendsto_add_atTop_iff_nat 1, tendsto_iff_edist_tendsto_0]
  have hlim := (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (C * ‖g‖))
    (tendsto_lintegral_eNorm_mul_eNorm_sub_of_littlewoodPaleyLowPass_eq φ ψ f ha)
    (Or.inr ENNReal.ofReal_ne_top)).add (ENNReal.Tendsto.const_mul (a := ‖f‖ₑ)
      (tendsto_lintegral_eNorm_mul_eNorm_sub_of_littlewoodPaleyLowPass_eq φ ψ g hb)
      (Or.inr eNorm_ne_top))
  simp only [mul_zero, add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ bot_le)
    fun j ↦ ?_
  rw [eDist_eq_eNorm_sub]
  refine (TauCeti.eNorm_integral_smul_sub_integral_smul_le ψ.integrable _ f _ g).trans ?_
  gcongr
  exact hbC _

/-- **Bony's decomposition of a product of bounded functions.** Let `f, g ∈ L^∞`, and let
`xₖ, yⱼ ∈ L^∞` be their Littlewood–Paley blocks, `Δₖ f = xₖ` and `Δⱼ g = yⱼ`. Then the partial
sums up to `N` of the paraproduct `T_f g = ∑ⱼ S_{j-1} f · Δⱼ g`, of the paraproduct
`T_g f = ∑ₖ Δₖ f · S_{k-1} g` and of the resonant term `R(f, g) = ∑_{|j - k| ≤ 1} Δₖ f · Δⱼ g`
add up to a sequence converging to `f · g` in the tempered distributions. Here
`S_{j-1} f = ∑_{k < j - 1} xₖ`, with natural subtraction, so that `S_{j-1} = 0` for `j ≤ 1`. -/
theorem tendsto_toTemperedDistribution_paraproduct_add_paraproduct_add_resonant
    (f : Lp ℂ ∞ (volume : Measure E)) (g : Lp F ∞ (volume : Measure E))
    {x : ℕ → Lp ℂ ∞ (volume : Measure E)} {y : ℕ → Lp F ∞ (volume : Measure E)}
    (hx : ∀ k, littlewoodPaleyBlock ℂ φ k (f : 𝓢'(E, ℂ)) = x k)
    (hy : ∀ j, littlewoodPaleyBlock F φ j (g : 𝓢'(E, F)) = y j) :
    Tendsto (fun N ↦ (((∑ j ∈ range N, (∑ k ∈ range (j - 1), x k) • y j) +
        (∑ k ∈ range N, x k • ∑ j ∈ range (k - 1), y j) +
        ∑ k ∈ range N, x k • ∑ j ∈ (range N).filter (fun j ↦ j ≤ k + 1 ∧ k ≤ j + 1), y j :
          Lp F ∞ (volume : Measure E)) : 𝓢'(E, F))) atTop
      (𝓝 ((f • g : Lp F ∞ (volume : Measure E)) : 𝓢'(E, F))) := by
  refine (tendsto_toTemperedDistribution_smul_of_littlewoodPaleyLowPass_eq φ f g
    (littlewoodPaleyLowPass_eq_sum φ hx) (littlewoodPaleyLowPass_eq_sum φ hy)).congr
    fun N ↦ ?_
  congr 1
  rw [Lp.sum_smul, sum_congr rfl fun k _ ↦ Lp.smul_sum _ _ _, sum_range_sum_range_split_gap 1]
  simp only [Lp.sum_smul, Lp.smul_sum]

end TemperedDistribution
