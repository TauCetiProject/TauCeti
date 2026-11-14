/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
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
  (`exists_littlewoodPaleyLowPass_eq_and_norm_le`). Writing
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
`exists_littlewoodPaleyLowPass_eq_and_norm_le`); the statements take these
functions as data, through the hypotheses identifying their tempered distributions.

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

omit [CompleteSpace F] in
/-- Against a Schwartz function `ψ`, the products `a · b` and `f · g` of bounded functions differ by
at most `‖b‖_∞ ∫ |ψ| |a - f| + ‖f‖_∞ ∫ |ψ| ‖b - g‖`, from
`a · b - f · g = (a - f) · b + f · (b - g)`. -/
private theorem eNorm_integral_smul_sub_integral_smul_le (ψ : 𝓢(E, ℂ))
    (a f : Lp ℂ ∞ (volume : Measure E)) (b g : Lp F ∞ (volume : Measure E)) :
    ‖(∫ x, ψ x • (a • b : Lp F ∞ volume) x) - ∫ x, ψ x • (f • g : Lp F ∞ volume) x‖ₑ ≤
      ‖b‖ₑ * (∫⁻ x, ‖ψ x‖ₑ * ‖a x - f x‖ₑ) + ‖f‖ₑ * ∫⁻ x, ‖ψ x‖ₑ * ‖b x - g x‖ₑ := by
  have hint : ∀ u : Lp F ∞ (volume : Measure E), Integrable (fun x ↦ ψ x • u x) :=
    fun u ↦ ψ.integrable.smul_of_top_left (Lp.memLp u)
  have hm : AEMeasurable (fun x ↦ ‖ψ x‖ₑ * ‖a x - f x‖ₑ) :=
    ψ.continuous.eNorm.aemeasurable.mul
      ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _)).eNorm
  rw [← integral_sub (hint _) (hint _), ← lintegral_const_mul' _ _ eNorm_ne_top,
    ← lintegral_const_mul' _ _ eNorm_ne_top, ← lintegral_add_left' (hm.const_mul _)]
  refine (eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono_ae ?_)
  filter_upwards [Lp.coeFn_lpSMul (r := ∞) a b, Lp.coeFn_lpSMul (r := ∞) f g,
    Lp.ae_norm_le_norm_top b, Lp.ae_norm_le_norm_top f] with x hab hfg hb hf
  rw [← smul_sub, eNorm_smul, hab, hfg, Pi.smul_apply', Pi.smul_apply']
  have hsplit : a x • b x - f x • g x = (a x - f x) • b x + f x • (b x - g x) := by
    rw [sub_smul, smul_sub]
    abel
  have hb' : ‖b x‖ₑ ≤ ‖b‖ₑ := eNorm_le_iff_norm_le.2 hb
  have hf' : ‖f x‖ₑ ≤ ‖f‖ₑ := eNorm_le_iff_norm_le.2 hf
  calc ‖ψ x‖ₑ * ‖a x • b x - f x • g x‖ₑ
      ≤ ‖ψ x‖ₑ * (‖a x - f x‖ₑ * ‖b‖ₑ + ‖f‖ₑ * ‖b x - g x‖ₑ) := by
        rw [hsplit]
        gcongr
        refine (eNorm_add_le _ _).trans ?_
        rw [eNorm_smul, eNorm_smul]
        gcongr
    _ = ‖b‖ₑ * (‖ψ x‖ₑ * ‖a x - f x‖ₑ) + ‖f‖ₑ * (‖ψ x‖ₑ * ‖b x - g x‖ₑ) := by ring

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
  have hbC : ∀ j, ‖b j‖ₑ ≤ ENNReal.ofReal (C * ‖g‖) := fun j ↦ by
    obtain ⟨g', hg', hg'C⟩ := exists_littlewoodPaleyLowPass_eq_and_norm_le φ j g
    have : b j = g' := LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
      simpa only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply, hb] using hg'
    rw [this, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hg'C
  -- `S_{j+1}` averages against the dilates of `𝓕⁻ φ` by `2^{-j} → 0`, so it converges to the
  -- identity in `L¹` against the weight `ψ`.
  have hc : Tendsto (fun j : ℕ ↦ ((2 : ℝ) ^ j)⁻¹) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two),
      Eventually.of_forall fun j ↦ inv_ne_zero (pow_ne_zero j two_ne_zero)⟩
  refine PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.2 fun ψ ↦ ?_
  simp only [Lp.toTemperedDistribution_apply]
  rw [← tendsto_add_atTop_iff_nat 1, tendsto_iff_edist_tendsto_0]
  have hf := (tendsto_lintegral_eNorm_mul_eNorm_integral_smul_comp_sub_smul_sub
    φ.integrable_fourierInv φ.integral_fourierInv ψ.integrable (Lp.aestronglyMeasurable f)
    (Lp.ae_norm_le_norm_top f)).comp hc
  have hg := (tendsto_lintegral_eNorm_mul_eNorm_integral_smul_comp_sub_smul_sub
    φ.integrable_fourierInv φ.integral_fourierInv ψ.integrable (Lp.aestronglyMeasurable g)
    (Lp.ae_norm_le_norm_top g)).comp hc
  have hlim := (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (C * ‖g‖)) hf
    (Or.inr ENNReal.ofReal_ne_top)).add
    (ENNReal.Tendsto.const_mul (a := ‖f‖ₑ) hg (Or.inr eNorm_ne_top))
  simp only [mul_zero, add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ bot_le)
    fun j ↦ ?_
  have hIa : ∫⁻ x, ‖ψ x‖ₑ * ‖(∫ s, 𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) s • f (x - ((2 : ℝ) ^ j)⁻¹ • s)) -
      f x‖ₑ = ∫⁻ x, ‖ψ x‖ₑ * ‖a (j + 1) x - f x‖ₑ :=
    lintegral_congr_ae <| (ae_eq_integral_of_littlewoodPaleyLowPass_succ_eq φ j (ha (j + 1))).mono
      fun x hx ↦ by dsimp only at hx ⊢; rw [hx]
  have hIg : ∫⁻ x, ‖ψ x‖ₑ * ‖(∫ s, 𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) s • g (x - ((2 : ℝ) ^ j)⁻¹ • s)) -
      g x‖ₑ = ∫⁻ x, ‖ψ x‖ₑ * ‖b (j + 1) x - g x‖ₑ :=
    lintegral_congr_ae <| (ae_eq_integral_of_littlewoodPaleyLowPass_succ_eq φ j (hb (j + 1))).mono
      fun x hx ↦ by dsimp only at hx ⊢; rw [hx]
  dsimp only [Function.comp_apply]
  rw [hIa, hIg, eDist_eq_eNorm_sub]
  refine (eNorm_integral_smul_sub_integral_smul_le ψ _ f _ g).trans ?_
  gcongr
  exact hbC _

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] in
/-- The pairs `(k, j)` with `k, j < N` are partitioned into those with `k ≤ j - 2`, those with
`j ≤ k - 2` and those with `|j - k| ≤ 1`. -/
private theorem sum_range_sum_range_eq {M : Type*} [AddCommMonoid M] (N : ℕ) (c : ℕ → ℕ → M) :
    ∑ k ∈ range N, ∑ j ∈ range N, c k j =
      ∑ j ∈ range N, ∑ k ∈ range (j - 1), c k j + ∑ k ∈ range N, ∑ j ∈ range (k - 1), c k j +
        ∑ j ∈ range N, ∑ k ∈ (range N).filter (fun k ↦ j ≤ k + 1 ∧ k ≤ j + 1), c k j := by
  have hsplit : ∀ j ∈ range N, ∑ k ∈ range N, c k j =
      ∑ k ∈ range (j - 1), c k j + ∑ k ∈ (range N).filter (fun k ↦ j + 2 ≤ k), c k j +
        ∑ k ∈ (range N).filter (fun k ↦ j ≤ k + 1 ∧ k ≤ j + 1), c k j := fun j hj ↦ by
    rw [Finset.mem_range] at hj
    rw [← sum_filter_add_sum_filter_not (range N) (fun k ↦ k + 2 ≤ j),
      ← sum_filter_add_sum_filter_not ((range N).filter fun k ↦ ¬k + 2 ≤ j) (fun k ↦ j + 2 ≤ k),
      add_assoc]
    congr 1
    · congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    · congr 1 <;> congr 1 <;> ext k <;> simp only [Finset.mem_filter, Finset.mem_range] <;> omega
  rw [sum_comm, sum_congr rfl hsplit, sum_add_distrib, sum_add_distrib]
  congr 2
  refine sum_comm' fun j k ↦ ?_
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

/-- The truncation `S_N u` is represented by the sum of representatives of the blocks `Δₖ u`,
`k < N`. -/
private theorem littlewoodPaleyLowPass_eq_sum (u : Lp F ∞ (volume : Measure E))
    {z : ℕ → Lp F ∞ (volume : Measure E)}
    (hz : ∀ k, littlewoodPaleyBlock F φ k (u : 𝓢'(E, F)) = z k) (N : ℕ) :
    littlewoodPaleyLowPass F φ N (u : 𝓢'(E, F)) =
      ((∑ k ∈ range N, z k : Lp F ∞ volume) : 𝓢'(E, F)) := by
  rw [littlewoodPaleyLowPass_def, _root_.sum_apply,
    Lp.toTemperedDistribution_sum]
  exact sum_congr rfl fun k _ ↦ hz k

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
        ∑ j ∈ range N, ∑ k ∈ (range N).filter (fun k ↦ j ≤ k + 1 ∧ k ≤ j + 1), x k • y j :
          Lp F ∞ (volume : Measure E)) : 𝓢'(E, F))) atTop
      (𝓝 ((f • g : Lp F ∞ (volume : Measure E)) : 𝓢'(E, F))) := by
  refine (tendsto_toTemperedDistribution_smul_of_littlewoodPaleyLowPass_eq φ f g
    (littlewoodPaleyLowPass_eq_sum φ f hx) (littlewoodPaleyLowPass_eq_sum φ g hy)).congr
    fun N ↦ ?_
  congr 1
  rw [Lp.sum_smul, sum_congr rfl fun k _ ↦ Lp.smul_sum _ _ _, sum_range_sum_range_eq,
    sum_congr rfl fun j _ ↦ Lp.sum_smul _ _ _, sum_congr rfl fun k _ ↦ Lp.smul_sum _ _ _]

end TemperedDistribution
