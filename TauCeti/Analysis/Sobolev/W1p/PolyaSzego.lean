/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.VariationMeasure
public import TauCeti.Analysis.Sobolev.W1p.ChainRule
public import TauCeti.MeasureTheory.Function.SchwarzRearrangement
import TauCeti.Analysis.BoundedVariation.UniformIntegrable
import TauCeti.Analysis.BoundedVariation.WeakDerivative
import TauCeti.Analysis.Calculus.ContDiff.Convolution
import TauCeti.Analysis.Calculus.FDeriv.Measurable
import TauCeti.Analysis.Sobolev.Mollification.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.MeasureTheory.Function.DeLaValleePoussin
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Function.LpSeminorm.Restrict
import TauCeti.MeasureTheory.Function.SchwarzRearrangement.Lipschitz
import TauCeti.MeasureTheory.Function.SchwarzRearrangement.PolyaSzego
import TauCeti.MeasureTheory.Function.UniformIntegrable
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# The `W^{1,1}` Pólya–Szegő inequality

Let `E` be a finite-dimensional real inner product space equipped with an additive Haar measure
`mu`. While the BV Pólya–Szegő inequality
(`TauCeti.totalVariationOn_toReal_schwarzRearrangement_le`) shows that symmetric decreasing
rearrangement does not increase total variation, BV membership alone allows a Cantor-type singular
derivative measure. Exclusion of singular concentration in `W^{1,1}` requires preserving uniform
integrability of gradients across smooth approximations.

For `u : W1p mu ⊤ 1`, convolving `(W1p.value u)⁺` with any smooth compactly supported probability
kernel `rho` produces a globally Lipschitz function
(`HasCompactSupport.lipschitzWith_convolution_left_of_integrable`)
whose gradient satisfies `∫ Φ(‖D(rho ⋆ u⁺)‖) ∂mu ≤ ∫ Φ(‖∇u⁺‖) ∂mu` by convolution Jensen
(`TauCeti.HasWeakFDerivOn.lintegral_ofReal_map_norm_fderiv_convolution_le`), hence
`∫ Φ(‖D((rho ⋆ u⁺)*)‖) ∂mu ≤ ∫ Φ(‖∇u⁺‖) ∂mu` by the Lipschitz convex-integrand Pólya–Szegő
inequality (`LipschitzWith.lintegral_ofReal_comp_norm_fderiv_toReal_schwarzRearrangement_le`).
Choosing `Φ` superlinear via de la Vallée Poussin
(`MeasureTheory.Integrable.exists_convexOn_superlinear_integrable`) yields uniform
equi-integrability of `D((rho_n ⋆ u⁺)*)` across shrinking normalized smooth bumps `rho_n`, while
`Φ = id` bounds their `L¹` norms by `‖∇u⁺‖_{L¹}`. Since `(rho_n ⋆ u⁺)* → (u⁺)*` in `L¹` by
`L¹`-contraction of Schwarz rearrangement
(`TauCeti.lintegral_enorm_toReal_schwarzRearrangement_sub_rpow_le`),
`MeasureTheory.LocallyIntegrableOn.exists_hasWeakFDerivOn_integrableOn_of_uniformIntegrable` shows
that `|D((u⁺)*)| ≪ mu` and equips `(u⁺)*` (and similarly `|u|*`) with an `L¹` weak gradient
satisfying `‖∇((u⁺)*)‖_{L¹} ≤ ‖∇u⁺‖_{L¹} ≤ ‖∇u‖_{L¹}` and `‖∇(|u|*)‖_{L¹} ≤ ‖∇u‖_{L¹}`.

## Main declarations

* `TauCeti.W1p.exists_setLIntegral_enorm_fderiv_toReal_schwarzRearrangement_convolution_le`:
  quantitative equi-integrability `∫_s ‖D((rho ⋆ u)*)‖ₑ ∂mu ≤ T * mu s + ε` uniformly across all
  smooth compactly supported probability kernels `rho`.
* `TauCeti.W1p.schwarzRearrangement`: positive-part Schwarz rearrangement on `W1p mu ⊤ 1`, together
  with value and gradient `L¹` norm bounds, variation-measure absolute continuity, and `@[simp]`
  normal-form and idempotence lemmas.
* `TauCeti.W1p.schwarzRearrangementNorm`: absolute-value Schwarz rearrangement on `W1p mu ⊤ 1`,
  together with `L¹` norm preservation, weak-gradient norm bounds, variation-measure absolute
  continuity, and `@[simp]` interaction lemmas.

## References

* J. Brothers, W. P. Ziemer, *Minimal rearrangements of Sobolev functions*, J. Reine Angew. Math.
  **384** (1988), 153–179.
* G. Bianchi, R. J. Gardner, P. Gronchi, M. Kiderlen, *The Pólya–Szegő inequality for smoothing
  rearrangements*, J. Funct. Anal. **287** (2024), Theorem 5.8.
* E. H. Lieb, M. Loss, *Analysis*, 2nd ed., AMS, 2001, Theorem 7.17 and Lemma 7.17.
-/

public noncomputable section

open MeasureTheory Set Filter TopologicalSpace Metric ContinuousLinearMap
open scoped ContDiff ENNReal NNReal Topology Convolution RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]

/-- Combining convolution Jensen with the Lipschitz convex-integrand Pólya–Szegő inequality for any
`u : W1p mu ⊤ 1` and smooth compactly supported `mu`-probability kernel `rho`. -/
private theorem lintegral_ofReal_fderiv_schwarzRearrangement_convolution_le
    (u : W1p mu ⊤ 1) {rho : E → ℝ} (hrho : ContDiff ℝ ∞ rho) (hrho_cpt : HasCompactSupport rho)
    (hrho0 : 0 ≤ᵐ[mu] rho) (hrho1 : ∫ x, rho x ∂mu = 1)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ (fun z ↦ (schwarzRearrangement mu
        (fun y ↦ ENNReal.ofReal ((rho ⋆[lsmul ℝ ℝ, mu] ⇑(W1p.value u)) y))
        z).toReal) x‖) ∂mu ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖W1p.gradient u x‖) ∂mu := by
  have hu_int := W1p.integrable_value u
  have hK := hrho_cpt.lipschitzWith_convolution_left_of_integrable (lsmul ℝ ℝ)
    (hrho.of_le (by simp)) hu_int
  calc ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ (fun z ↦ (schwarzRearrangement mu
          (fun y ↦ ENNReal.ofReal ((rho ⋆[lsmul ℝ ℝ, mu] ⇑(W1p.value u)) y))
          z).toReal) x‖) ∂mu
      ≤ ∫⁻ x, ENNReal.ofReal
          (Φ ‖fderiv ℝ (rho ⋆[lsmul ℝ ℝ, mu] ⇑(W1p.value u)) x‖) ∂mu :=
        hK.lintegral_ofReal_comp_norm_fderiv_toReal_schwarzRearrangement_le mu hΦ hΦ0.le
    _ ≤ ∫⁻ x, ENNReal.ofReal (Φ ‖innerSL ℝ (W1p.gradient u x)‖) ∂mu := by
        rw [← convolution_flip]
        exact (W1p.hasWeakFDerivOn u).lintegral_ofReal_map_norm_fderiv_convolution_le
          hu_int.locallyIntegrable
          ((innerSL ℝ (E := E)).integrable_comp (W1p.integrable_gradient u)).locallyIntegrable
          hΦ hΦm hrho hrho_cpt hrho0 hrho1
    _ = ∫⁻ x, ENNReal.ofReal (Φ ‖W1p.gradient u x‖) ∂mu :=
        lintegral_congr fun x ↦ by rw [innerSL_apply_norm]

/-- `L¹` gradient bound (`Φ = id`) for the real Schwarz rearrangement of a mollification of
`u : W1p mu ⊤ 1`. -/
private theorem lintegral_enorm_fderiv_schwarzRearrangement_convolution_le
    (u : W1p mu ⊤ 1) {rho : E → ℝ} (hrho : ContDiff ℝ ∞ rho) (hrho_cpt : HasCompactSupport rho)
    (hrho0 : 0 ≤ᵐ[mu] rho) (hrho1 : ∫ x, rho x ∂mu = 1) :
    ∫⁻ x, ‖fderiv ℝ (fun z ↦ (schwarzRearrangement mu
        (fun y ↦ ENNReal.ofReal ((rho ⋆[lsmul ℝ ℝ, mu] ⇑(W1p.value u)) y))
        z).toReal) x‖ₑ ∂mu ≤
      ∫⁻ x, ‖W1p.gradient u x‖ₑ ∂mu := by
  simpa [ofReal_norm] using lintegral_ofReal_fderiv_schwarzRearrangement_convolution_le u
    hrho hrho_cpt hrho0 hrho1 (convexOn_id (convex_Ici 0)) monotoneOn_id rfl

omit [FiniteDimensional ℝ E] in
/-- De la Vallée Poussin superlinear convex function for `W1p.gradient u`, converted to an extended
Lebesgue finiteness bound with respect to `mu`. -/
private theorem exists_convexOn_superlinear_lintegral_gradient_ne_top (u : W1p mu ⊤ 1) :
    ∃ Φ : ℝ → ℝ, Φ 0 = 0 ∧ MonotoneOn Φ (Ici 0) ∧ ConvexOn ℝ (Ici 0) Φ ∧
      Tendsto (fun t ↦ Φ t / t) atTop atTop ∧
      ∫⁻ x, ENNReal.ofReal (Φ ‖W1p.gradient u x‖) ∂mu ≠ (∞ : ℝ≥0∞) := by
  obtain ⟨Φ, hΦ0, hΦm, hΦc, hΦsup, hΦint⟩ :=
    (W1p.integrable_gradient u).exists_convexOn_superlinear_integrable
  refine ⟨Φ, hΦ0, hΦm.monotoneOn _, hΦc.subset (subset_univ _) (convex_Ici 0), hΦsup, ?_⟩
  exact (lintegral_ofReal_ne_top_iff_integrable hΦint.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by simpa [hΦ0] using hΦm (norm_nonneg _))).2 hΦint

/-- **Quantitative equi-integrability of rearranged mollifications.** For any additive Haar measure
`mu`, any `u : W1p mu ⊤ 1`, and any `ε ≠ 0`, there is a slope `T : ℝ≥0` depending only on `u` and
`ε` such that for every smooth compactly supported `mu`-probability kernel `rho` and every set
`s : Set E`, the real Schwarz rearrangement of the positive part of `rho ⋆ W1p.value u` satisfies
`∫⁻ x in s, ‖fderiv ℝ ((rho ⋆ W1p.value u)*) x‖ₑ ∂mu ≤ T * mu s + ε`. -/
theorem W1p.exists_setLIntegral_enorm_fderiv_toReal_schwarzRearrangement_convolution_le
    (u : W1p mu ⊤ 1) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ T : ℝ≥0, ∀ ⦃rho : E → ℝ⦄,
      ContDiff ℝ ∞ rho → HasCompactSupport rho → 0 ≤ᵐ[mu] rho → ∫ x, rho x ∂mu = 1 →
      ∀ s : Set E,
        ∫⁻ x in s, ‖fderiv ℝ (fun z ↦ (schwarzRearrangement mu
          (fun y ↦ ENNReal.ofReal ((rho ⋆[lsmul ℝ ℝ, mu] ⇑(W1p.value u)) y))
          z).toReal) x‖ₑ ∂mu ≤ T * mu s + ε := by
  obtain ⟨Φ, hΦ0, hΦm, hΦc, hΦsup, hC⟩ := exists_convexOn_superlinear_lintegral_gradient_ne_top u
  let P (rho : E → ℝ) : Prop :=
    ContDiff ℝ ∞ rho ∧ HasCompactSupport rho ∧ 0 ≤ᵐ[mu] rho ∧ ∫ x, rho x ∂mu = 1
  obtain ⟨T, hT⟩ := exists_setLIntegral_enorm_le_mul_add (ι := Subtype P) hΦsup hC
    (fun r ↦ lintegral_ofReal_fderiv_schwarzRearrangement_convolution_le u
      r.property.1 r.property.2.1 r.property.2.2.1 r.property.2.2.2 hΦc hΦm hΦ0) hε
  exact ⟨T, fun rho h1 h2 h3 h4 s ↦ hT ⟨rho, h1, h2, h3, h4⟩ s⟩

/-- Uniform integrability of the Fréchet derivatives of rearranged mollifications for any
`w : W1p mu ⊤ 1` and bump family `phi`. -/
private theorem uniformIntegrable_fderiv_schwarzRearrangement_convolution
    (w : W1p mu ⊤ 1) {ι : Type*} (phi : ι → ContDiffBump (0 : E)) :
    UniformIntegrable
      (fun i ↦ fderiv ℝ fun z ↦ (schwarzRearrangement mu
        (fun y ↦ ENNReal.ofReal (((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] ⇑(W1p.value w)) y))
        z).toReal)
      1 (mu.restrict (⊤ : Opens E)) := by
  obtain ⟨Φ, hΦ0, hΦm, hΦc, hΦsup, hC⟩ := exists_convexOn_superlinear_lintegral_gradient_ne_top w
  rw [uniformIntegrable_restrict_coe_opens_top]
  refine ⟨unifIntegrable_of_lintegral_ofReal_le hΦsup
      (fun i ↦ (measurable_fderiv ℝ _).aestronglyMeasurable) hC fun i ↦
      lintegral_ofReal_fderiv_schwarzRearrangement_convolution_le w (phi i).contDiff_normed
        (phi i).hasCompactSupport_normed (ae_of_all _ (phi i).nonneg_normed)
        (phi i).integral_normed hΦc hΦm hΦ0, ?_⟩
  refine (iSup_le fun i ↦ ?_).trans_lt (W1p.integrable_gradient w).2
  rw [eLpNorm_one_eq_lintegral_eNorm (measurable_fderiv ℝ _).aestronglyMeasurable]
  exact lintegral_enorm_fderiv_schwarzRearrangement_convolution_le w
    (phi i).contDiff_normed (phi i).hasCompactSupport_normed (ae_of_all _ (phi i).nonneg_normed)
    (phi i).integral_normed

/-- The Schwarz rearrangement of `ENNReal.ofReal ∘ W1p.value (W1p.posPart hp u)` equals that of
`ENNReal.ofReal ∘ W1p.value u`. -/
private theorem schwarzRearrangement_ofReal_value_posPart (hp : 1 ≠ (∞ : ℝ≥0∞)) (u : W1p mu ⊤ 1) :
    schwarzRearrangement mu (fun y ↦ ENNReal.ofReal (W1p.value (W1p.posPart hp u) y)) =
      schwarzRearrangement mu (fun y ↦ ENNReal.ofReal (W1p.value u y)) := by
  refine schwarzRearrangement_congr_ae mu ?_
  have hpos : ⇑(W1p.value (W1p.posPart hp u)) =ᵐ[mu] fun y ↦ max (W1p.value u y) 0 := by
    rw [← mu.ae_restrict_coe_opens_top, W1p.value_posPart]
    exact Lp.coeFn_posPart (W1p.value u)
  exact hpos.mono fun _ hy ↦ by
    dsimp only
    rw [hy, ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]

/-- Core existence of an `L¹` weak gradient for the real Schwarz rearrangement of the positive part
of `u : W1p mu ⊤ 1`, bounded in `L¹` by the weak gradient of `u⁺`. -/
private theorem exists_hasWeakFDerivOn_of_w1p (u : W1p mu ⊤ 1) :
    ∃ g : E → E,
      HasWeakFDerivOn mu ⊤
        (fun x ↦ (schwarzRearrangement mu (fun y ↦ ENNReal.ofReal (W1p.value u y)) x).toReal)
        (fun x ↦ innerSL ℝ (g x)) ∧
      MemLp g 1 (mu.restrict (⊤ : Opens E)) ∧
      ∫⁻ x, ‖g x‖ₑ ∂mu ≤ ∫⁻ x, ‖W1p.gradient (W1p.posPart ENNReal.one_ne_top u) x‖ₑ ∂mu := by
  set w := W1p.posPart ENNReal.one_ne_top u
  let phi : ℕ → ContDiffBump (0 : E) := fun n ↦
    ⟨1 / ((n : ℝ) + 2), 1 / ((n : ℝ) + 1), by positivity, by gcongr; linarith⟩
  have hw_int := W1p.integrable_value w
  have hlip (n : ℕ) :=
    ((phi n).hasCompactSupport_normed (μ := mu)).lipschitzWith_convolution_left_of_integrable
      (lsmul ℝ ℝ) ((phi n).contDiff_normed (μ := mu) (n := 1)) hw_int
  let v_n : ℕ → E → ℝ := fun n x ↦ (schwarzRearrangement mu
    (fun y ↦ ENNReal.ofReal (((phi n).normed mu ⋆[lsmul ℝ ℝ, mu] ⇑(W1p.value w)) y))
    x).toReal
  let v₀ : E → ℝ := fun x ↦
    (schwarzRearrangement mu (fun y ↦ ENNReal.ofReal (W1p.value w y)) x).toReal
  have hv_weak (n : ℕ) : HasWeakFDerivOn mu ⊤ (v_n n) (fderiv ℝ (v_n n)) :=
    ((lipschitzWith_toReal_schwarzRearrangement mu (hlip n)).locallyLipschitz.locallyLipschitzOn
      (s := (⊤ : Opens E))).hasWeakFDerivOn_fderiv
  have hL1_bound (n : ℕ) : ∫⁻ x, ‖fderiv ℝ (v_n n) x‖ₑ ∂mu ≤ ∫⁻ x, ‖W1p.gradient w x‖ₑ ∂mu :=
    lintegral_enorm_fderiv_schwarzRearrangement_convolution_le w
      (phi n).contDiff_normed (phi n).hasCompactSupport_normed (ae_of_all _ (phi n).nonneg_normed)
      (phi n).integral_normed
  have hconv (K : Set E) (_ : IsCompact K) (_ : K ⊆ (⊤ : Opens E)) :
      Tendsto (fun n ↦ ∫⁻ x in K, ‖v_n n x - v₀ x‖ₑ ∂mu) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_lintegral_enorm_normed_convolution_sub (phi := phi)
        tendsto_one_div_add_atTop_nhds_zero_nat hw_int)
      (fun _ ↦ bot_le) fun n ↦ (setLIntegral_le_lintegral _ _).trans ?_
    simpa using lintegral_enorm_toReal_schwarzRearrangement_sub_rpow_le mu
      (hlip n).continuous.aemeasurable hw_int.aemeasurable le_rfl
  obtain ⟨g, hg_weak, hg_int, hg_le⟩ :=
    (hw_int.toReal_schwarzRearrangement.locallyIntegrable.locallyIntegrableOn ⊤)
      |>.exists_hasWeakFDerivOn_integrableOn_of_uniformIntegrable hv_weak
        (uniformIntegrable_fderiv_schwarzRearrangement_convolution w phi) hconv
  have hv₀_eq : v₀ = fun x ↦
      (schwarzRearrangement mu (fun y ↦ ENNReal.ofReal (W1p.value u y)) x).toReal := by
    ext x
    simp only [v₀, w, schwarzRearrangement_ofReal_value_posPart ENNReal.one_ne_top u]
  rw [hv₀_eq] at hg_weak
  rw [IntegrableOn, mu.restrict_coe_opens_top] at hg_int
  rw [mu.restrict_coe_opens_top] at hg_le
  exact ⟨g, hg_weak, memLp_restrict_coe_opens_top.2 (memLp_one_iff_integrable.2 hg_int),
    hg_le.trans (liminf_le_of_frequently_le' (Eventually.of_forall hL1_bound).frequently)⟩

namespace W1p

/-- `L¹` membership of the real Schwarz rearrangement of `(W1p.value u)⁺` on `⊤`. -/
private theorem memLp_toReal_schwarzRearrangement_value (u : W1p mu ⊤ 1) :
    MemLp
      (fun x ↦ (TauCeti.schwarzRearrangement mu
        (fun y ↦ ENNReal.ofReal (W1p.value u y)) x).toReal)
      1 (mu.restrict (⊤ : Opens E)) :=
  memLp_restrict_coe_opens_top.2
    (memLp_one_iff_integrable.2 (W1p.integrable_value u).toReal_schwarzRearrangement)

/-- Chosen pointwise weak-gradient representative for the real Schwarz rearrangement of
`(W1p.value u)⁺`. -/
private def schwarzRearrangementRawGradient (u : W1p mu ⊤ 1) : E → E :=
  Classical.choose (exists_hasWeakFDerivOn_of_w1p u)

/-- `schwarzRearrangementRawGradient u` is a weak gradient for the real Schwarz rearrangement of
`(W1p.value u)⁺`. -/
private theorem hasWeakFDerivOn_schwarzRearrangementRawGradient (u : W1p mu ⊤ 1) :
    HasWeakFDerivOn mu ⊤
      (fun x ↦ (TauCeti.schwarzRearrangement mu
        (fun y ↦ ENNReal.ofReal (W1p.value u y)) x).toReal)
      (fun x ↦ innerSL ℝ (schwarzRearrangementRawGradient u x)) :=
  (Classical.choose_spec (exists_hasWeakFDerivOn_of_w1p u)).1

/-- `schwarzRearrangementRawGradient u` lies in `L¹` on `⊤`. -/
private theorem memLp_schwarzRearrangementRawGradient (u : W1p mu ⊤ 1) :
    MemLp (schwarzRearrangementRawGradient u) 1 (mu.restrict (⊤ : Opens E)) :=
  (Classical.choose_spec (exists_hasWeakFDerivOn_of_w1p u)).2.1

/-- `L¹` bound for `schwarzRearrangementRawGradient u` in terms of `W1p.posPart`. -/
private theorem lintegral_enorm_schwarzRearrangementRawGradient_le (u : W1p mu ⊤ 1) :
    ∫⁻ x, ‖schwarzRearrangementRawGradient u x‖ₑ ∂mu ≤
      ∫⁻ x, ‖W1p.gradient (W1p.posPart ENNReal.one_ne_top u) x‖ₑ ∂mu :=
  (Classical.choose_spec (exists_hasWeakFDerivOn_of_w1p u)).2.2

/-- Weak-gradient compatibility between the `Lp` classes used to construct
`W1p.schwarzRearrangement u`. -/
private theorem hasWeakFDerivOn_toLp_schwarzRearrangement (u : W1p mu ⊤ 1) :
    HasWeakFDerivOn mu ⊤
      ((memLp_toReal_schwarzRearrangement_value u).toLp _)
      (fun x ↦ innerSL ℝ (((memLp_schwarzRearrangementRawGradient u).toLp _) x)) := by
  refine ((hasWeakFDerivOn_schwarzRearrangementRawGradient u).congr_ae
    (memLp_toReal_schwarzRearrangement_value u).coeFn_toLp.symm).congr_ae_deriv ?_
  filter_upwards [(memLp_schwarzRearrangementRawGradient u).coeFn_toLp] with x hx
  rw [hx]

/-- **Positive-part Schwarz rearrangement on `W^{1,1}`.** Maps `u : W1p mu ⊤ 1` to the `W^{1,1}`
element whose value is the real Schwarz rearrangement of the positive part `(W1p.value u)⁺`. -/
def schwarzRearrangement (u : W1p mu ⊤ 1) : W1p mu ⊤ 1 :=
  W1p.mk
    ((memLp_toReal_schwarzRearrangement_value u).toLp _)
    ((memLp_schwarzRearrangementRawGradient u).toLp _)
    (hasWeakFDerivOn_toLp_schwarzRearrangement u)

/-- The value of `W1p.schwarzRearrangement u` agrees almost everywhere with the real Schwarz
rearrangement of `(W1p.value u)⁺`. -/
theorem value_schwarzRearrangement_ae (u : W1p mu ⊤ 1) :
    ⇑(W1p.value (W1p.schwarzRearrangement u)) =ᵐ[mu.restrict (⊤ : Opens E)]
      fun x ↦ (TauCeti.schwarzRearrangement mu
        (fun y ↦ ENNReal.ofReal (W1p.value u y)) x).toReal := by
  rw [schwarzRearrangement, W1p.value_mk]
  exact MemLp.coeFn_toLp _

/-- Positive-part Schwarz rearrangement maps `0` to `0`. -/
@[simp]
theorem schwarzRearrangement_zero :
    W1p.schwarzRearrangement (0 : W1p (E := E) mu ⊤ 1) = 0 := by
  refine W1p.ext_value (Lp.ext ?_)
  filter_upwards [value_schwarzRearrangement_ae (0 : W1p (E := E) mu ⊤ 1)] with x hx
  simp [hx]

/-- Precomposing `W1p.schwarzRearrangement` with `W1p.posPart` leaves it unchanged. -/
@[simp]
theorem schwarzRearrangement_posPart (hp : 1 ≠ (∞ : ℝ≥0∞)) (u : W1p mu ⊤ 1) :
    W1p.schwarzRearrangement (W1p.posPart hp u) = W1p.schwarzRearrangement u := by
  refine W1p.ext_value (Lp.ext ?_)
  filter_upwards [value_schwarzRearrangement_ae (W1p.posPart hp u),
    value_schwarzRearrangement_ae u] with x hx1 hx2
  rw [hx1, hx2, schwarzRearrangement_ofReal_value_posPart hp u]

/-- `W1p.schwarzRearrangement` is idempotent. -/
@[simp]
theorem schwarzRearrangement_schwarzRearrangement (u : W1p mu ⊤ 1) :
    W1p.schwarzRearrangement (W1p.schwarzRearrangement u) = W1p.schwarzRearrangement u := by
  refine W1p.ext_value (Lp.ext ?_)
  have hval : ⇑(W1p.value (W1p.schwarzRearrangement u)) =ᵐ[mu]
      fun x ↦ (TauCeti.schwarzRearrangement mu
        (fun y ↦ ENNReal.ofReal (W1p.value u y)) x).toReal :=
    mu.ae_restrict_coe_opens_top ▸ value_schwarzRearrangement_ae u
  have hae : (fun y ↦ ENNReal.ofReal (W1p.value (W1p.schwarzRearrangement u) y)) =ᵐ[mu]
      TauCeti.schwarzRearrangement mu (fun y ↦ ENNReal.ofReal (W1p.value u y)) := by
    filter_upwards [hval, (W1p.integrable_value u).ae_schwarzRearrangement_ofReal_ne_top]
      with y hy hfin
    rw [hy, ENNReal.ofReal_toReal hfin]
  filter_upwards [value_schwarzRearrangement_ae (W1p.schwarzRearrangement u),
    value_schwarzRearrangement_ae u] with x hx1 hx2
  rw [hx1, hx2, TauCeti.schwarzRearrangement_congr_ae mu hae,
    TauCeti.schwarzRearrangement_schwarzRearrangement]

/-- The everywhere-defined radial rearrangement of the positive part `(W1p.value u)⁺` has weak
gradient `W1p.gradient (W1p.schwarzRearrangement u)` on the whole space. -/
theorem hasWeakFDerivOn_toReal_schwarzRearrangement (u : W1p mu ⊤ 1) :
    HasWeakFDerivOn mu ⊤
      (fun x ↦ (TauCeti.schwarzRearrangement mu
        (fun y ↦ ENNReal.ofReal (W1p.value u y)) x).toReal)
      (fun x ↦ innerSL ℝ (W1p.gradient (W1p.schwarzRearrangement u) x)) :=
  (W1p.hasWeakFDerivOn (W1p.schwarzRearrangement u)).congr_ae (value_schwarzRearrangement_ae u)

/-- **Exclusion of singular concentration for the positive-part Schwarz rearrangement.** For
`u : W1p mu ⊤ 1`, the BV variation measure of the real Schwarz rearrangement of `(W1p.value u)⁺` is
absolutely continuous with respect to `mu`, with density
`‖W1p.gradient (W1p.schwarzRearrangement u) ·‖ₑ`. -/
theorem variationMeasure_toReal_schwarzRearrangement_eq_withDensity (u : W1p mu ⊤ 1) :
    variationMeasure mu ⊤
      (fun x ↦ (TauCeti.schwarzRearrangement mu
        (fun y ↦ ENNReal.ofReal (W1p.value u y)) x).toReal) =
      (mu.comap ((↑) : (⊤ : Opens E) → E)).withDensity
        fun x ↦ ‖W1p.gradient (W1p.schwarzRearrangement u) (x : E)‖ₑ := by
  rw [(hasWeakFDerivOn_toReal_schwarzRearrangement u).variationMeasure_eq_withDensity]
  congr 1 with x
  rw [← ofReal_norm, innerSL_apply_norm, ofReal_norm]

/-- The `L¹` norm of `W1p.value (W1p.schwarzRearrangement u)` equals that of `(W1p.value u)⁺`. -/
@[simp]
theorem norm_value_schwarzRearrangement_eq_posPart (u : W1p mu ⊤ 1) :
    ‖W1p.value (W1p.schwarzRearrangement u)‖ = ‖Lp.posPart (W1p.value u)‖ := by
  have hu_int := W1p.integrable_value u
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (value_schwarzRearrangement_ae u),
    eLpNorm_congr_ae (Lp.coeFn_posPart (W1p.value u)), eLpNorm_restrict_coe_opens_top,
    eLpNorm_restrict_coe_opens_top,
    eLpNorm_one_eq_lintegral_eNorm hu_int.toReal_schwarzRearrangement.aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_eNorm hu_int.pos_part.aestronglyMeasurable]
  congr 1
  have hlhs : ∫⁻ x, ‖(TauCeti.schwarzRearrangement mu
        (fun y ↦ ENNReal.ofReal (W1p.value u y)) x).toReal‖ₑ ∂mu =
      ∫⁻ x, TauCeti.schwarzRearrangement mu (fun y ↦ ENNReal.ofReal (W1p.value u y)) x ∂mu := by
    refine lintegral_congr_ae ?_
    filter_upwards [hu_int.ae_schwarzRearrangement_ofReal_ne_top] with x hx
    rw [Real.eNorm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx]
  rw [hlhs, lintegral_schwarzRearrangement mu hu_int.aemeasurable.ennreal_ofReal]
  refine lintegral_congr fun x ↦ ?_
  rw [Real.eNorm_of_nonneg (le_max_right _ _), ENNReal.ofReal_max, ENNReal.ofReal_zero,
    max_eq_left zero_le]

/-- Positive-part Schwarz rearrangement does not increase the `L¹` value norm. -/
theorem norm_value_schwarzRearrangement_le (u : W1p mu ⊤ 1) :
    ‖W1p.value (W1p.schwarzRearrangement u)‖ ≤ ‖W1p.value u‖ := by
  rw [norm_value_schwarzRearrangement_eq_posPart]
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [Lp.coeFn_posPart (W1p.value u)] with x hx
  rw [hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ (0 : ℝ))]
  exact max_le (le_abs_self _) (abs_nonneg _)

/-- For almost-everywhere nonnegative `u : W1p mu ⊤ 1`, Schwarz rearrangement preserves the `L¹`
value norm. -/
theorem norm_value_schwarzRearrangement_of_ae_nonneg {u : W1p mu ⊤ 1}
    (hu : ∀ᵐ x ∂mu.restrict (⊤ : Opens E), 0 ≤ W1p.value u x) :
    ‖W1p.value (W1p.schwarzRearrangement u)‖ = ‖W1p.value u‖ := by
  rw [norm_value_schwarzRearrangement_eq_posPart, ← W1p.value_posPart ENNReal.one_ne_top,
    W1p.posPart_eq_self_of_ae_nonneg ENNReal.one_ne_top hu]

/-- **Sharp positive-part `W^{1,1}` Pólya–Szegő inequality.** The `L¹` norm of the weak gradient of
`W1p.schwarzRearrangement u` is at most that of `u⁺`. -/
theorem norm_gradient_schwarzRearrangement_le_posPart (u : W1p mu ⊤ 1) :
    ‖W1p.gradient (W1p.schwarzRearrangement u)‖ ≤
      ‖W1p.gradient (W1p.posPart ENNReal.one_ne_top u)‖ := by
  have hgrad_ae : ⇑(W1p.gradient (W1p.schwarzRearrangement u)) =ᵐ[mu.restrict (⊤ : Opens E)]
      schwarzRearrangementRawGradient u := by
    rw [schwarzRearrangement, W1p.gradient_mk]
    exact (memLp_schwarzRearrangementRawGradient u).coeFn_toLp
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hgrad_ae]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) ?_
  have hm1 : MemLp (schwarzRearrangementRawGradient u) 1 mu :=
    memLp_restrict_coe_opens_top.1 (memLp_schwarzRearrangementRawGradient u)
  have hm2 := W1p.memLp_gradient (W1p.posPart ENNReal.one_ne_top u)
  rw [eLpNorm_restrict_coe_opens_top, eLpNorm_restrict_coe_opens_top,
    eLpNorm_one_eq_lintegral_eNorm hm1.aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_eNorm hm2.aestronglyMeasurable]
  exact lintegral_enorm_schwarzRearrangementRawGradient_le u

/-- **`W^{1,1}` Pólya–Szegő inequality, `L¹` norm form.** The `L¹` norm of the weak gradient of
`W1p.schwarzRearrangement u` is at most that of `u`. -/
theorem norm_gradient_schwarzRearrangement_le (u : W1p mu ⊤ 1) :
    ‖W1p.gradient (W1p.schwarzRearrangement u)‖ ≤ ‖W1p.gradient u‖ := by
  refine (norm_gradient_schwarzRearrangement_le_posPart u).trans (Lp.norm_le_norm_of_ae_le ?_)
  filter_upwards [W1p.gradient_posPart_ae ENNReal.one_ne_top u] with x hx
  rw [hx]
  exact norm_indicator_le_norm_self _ _

/-- **`W^{1,1}` Pólya–Szegő inequality, Bochner integral form.** -/
theorem integral_norm_gradient_schwarzRearrangement_le (u : W1p mu ⊤ 1) :
    ∫ x, ‖W1p.gradient (W1p.schwarzRearrangement u) x‖ ∂mu ≤ ∫ x, ‖W1p.gradient u x‖ ∂mu := by
  simpa [L1.norm_eq_integral_norm] using norm_gradient_schwarzRearrangement_le u

/-- **Absolute-value Schwarz rearrangement on `W^{1,1}`.** Maps `u : W1p mu ⊤ 1` to the `W^{1,1}`
element whose value is the real Schwarz rearrangement of `|W1p.value u|`. -/
def schwarzRearrangementNorm (u : W1p mu ⊤ 1) : W1p mu ⊤ 1 :=
  W1p.schwarzRearrangement (W1p.posPart ENNReal.one_ne_top u + W1p.posPart ENNReal.one_ne_top (-u))

/-- Defining formula of `W1p.schwarzRearrangementNorm` in terms of `W1p.schwarzRearrangement` and
`W1p.posPart`. -/
theorem schwarzRearrangementNorm_def (u : W1p mu ⊤ 1) :
    W1p.schwarzRearrangementNorm u =
      W1p.schwarzRearrangement
        (W1p.posPart ENNReal.one_ne_top u + W1p.posPart ENNReal.one_ne_top (-u)) :=
  (rfl)

/-- The value of `W1p.schwarzRearrangementNorm u` agrees almost everywhere with the real Schwarz
rearrangement of `‖W1p.value u ·‖ₑ`. -/
theorem value_schwarzRearrangementNorm_ae (u : W1p mu ⊤ 1) :
    ⇑(W1p.value (W1p.schwarzRearrangementNorm u)) =ᵐ[mu.restrict (⊤ : Opens E)]
      fun x ↦ (TauCeti.schwarzRearrangement mu (fun y ↦ ‖W1p.value u y‖ₑ) x).toReal := by
  have hae : ⇑(W1p.value (W1p.posPart ENNReal.one_ne_top u +
        W1p.posPart ENNReal.one_ne_top (-u))) =ᵐ[mu] fun x ↦ |W1p.value u x| :=
    mu.ae_restrict_coe_opens_top ▸ W1p.value_posPart_add_posPart_neg_ae ENNReal.one_ne_top u
  have hcongr : TauCeti.schwarzRearrangement mu
      (fun y ↦ ENNReal.ofReal
        (W1p.value (W1p.posPart ENNReal.one_ne_top u + W1p.posPart ENNReal.one_ne_top (-u)) y)) =
      TauCeti.schwarzRearrangement mu (fun y ↦ ‖W1p.value u y‖ₑ) := by
    refine TauCeti.schwarzRearrangement_congr_ae mu ?_
    filter_upwards [hae] with y hy
    rw [hy, ← Real.norm_eq_abs, ofReal_norm]
  filter_upwards [value_schwarzRearrangement_ae
    (W1p.posPart ENNReal.one_ne_top u + W1p.posPart ENNReal.one_ne_top (-u))] with x hx
  rw [schwarzRearrangementNorm_def, hx, hcongr]

/-- For almost-everywhere nonnegative `u : W1p mu ⊤ 1`, `W1p.schwarzRearrangementNorm u` agrees with
`W1p.schwarzRearrangement u`. -/
theorem schwarzRearrangementNorm_eq_schwarzRearrangement_of_ae_nonneg {u : W1p mu ⊤ 1}
    (hu : ∀ᵐ x ∂mu.restrict (⊤ : Opens E), 0 ≤ W1p.value u x) :
    W1p.schwarzRearrangementNorm u = W1p.schwarzRearrangement u := by
  refine W1p.ext_value (Lp.ext ?_)
  have hu' : ∀ᵐ y ∂mu, 0 ≤ W1p.value u y := mu.ae_restrict_coe_opens_top ▸ hu
  have hae : (fun y ↦ ‖W1p.value u y‖ₑ) =ᵐ[mu] fun y ↦ ENNReal.ofReal (W1p.value u y) :=
    hu'.mono fun _ hy ↦ Real.eNorm_of_nonneg hy
  filter_upwards [value_schwarzRearrangementNorm_ae u, value_schwarzRearrangement_ae u]
    with x hx1 hx2
  rw [hx1, hx2, TauCeti.schwarzRearrangement_congr_ae mu hae]

/-- Absolute-value Schwarz rearrangement maps `0` to `0`. -/
@[simp]
theorem schwarzRearrangementNorm_zero :
    W1p.schwarzRearrangementNorm (0 : W1p (E := E) mu ⊤ 1) = 0 := by
  rw [schwarzRearrangementNorm_def, neg_zero, W1p.posPart_zero, add_zero, schwarzRearrangement_zero]

/-- Absolute-value Schwarz rearrangement is invariant under negation. -/
@[simp]
theorem schwarzRearrangementNorm_neg (u : W1p mu ⊤ 1) :
    W1p.schwarzRearrangementNorm (-u) = W1p.schwarzRearrangementNorm u := by
  rw [schwarzRearrangementNorm_def, schwarzRearrangementNorm_def, neg_neg, add_comm]

/-- Applying `W1p.schwarzRearrangementNorm` to `W1p.posPart hp u` reduces to
`W1p.schwarzRearrangement u`. -/
@[simp]
theorem schwarzRearrangementNorm_posPart (hp : 1 ≠ (∞ : ℝ≥0∞)) (u : W1p mu ⊤ 1) :
    W1p.schwarzRearrangementNorm (W1p.posPart hp u) = W1p.schwarzRearrangement u := by
  rw [schwarzRearrangementNorm_eq_schwarzRearrangement_of_ae_nonneg
      (W1p.value_posPart_nonneg_ae hp u),
    schwarzRearrangement_posPart]

/-- `W1p.schwarzRearrangement` fixes `W1p.schwarzRearrangementNorm u`. -/
@[simp]
theorem schwarzRearrangement_schwarzRearrangementNorm (u : W1p mu ⊤ 1) :
    W1p.schwarzRearrangement (W1p.schwarzRearrangementNorm u) = W1p.schwarzRearrangementNorm u := by
  rw [schwarzRearrangementNorm_def, schwarzRearrangement_schwarzRearrangement]

/-- `W1p.schwarzRearrangementNorm` fixes `W1p.schwarzRearrangement u`. -/
@[simp]
theorem schwarzRearrangementNorm_schwarzRearrangement (u : W1p mu ⊤ 1) :
    W1p.schwarzRearrangementNorm (W1p.schwarzRearrangement u) = W1p.schwarzRearrangement u := by
  have h0 : ∀ᵐ x ∂mu.restrict (⊤ : Opens E), 0 ≤ W1p.value (W1p.schwarzRearrangement u) x :=
    (value_schwarzRearrangement_ae u).mono fun _ hx ↦ hx.symm ▸ ENNReal.toReal_nonneg
  rw [schwarzRearrangementNorm_eq_schwarzRearrangement_of_ae_nonneg h0,
    schwarzRearrangement_schwarzRearrangement]

/-- `W1p.schwarzRearrangementNorm` is idempotent. -/
@[simp]
theorem schwarzRearrangementNorm_schwarzRearrangementNorm (u : W1p mu ⊤ 1) :
    W1p.schwarzRearrangementNorm (W1p.schwarzRearrangementNorm u) =
      W1p.schwarzRearrangementNorm u := by
  conv_lhs => arg 1; rw [schwarzRearrangementNorm_def]
  rw [schwarzRearrangementNorm_schwarzRearrangement, ← schwarzRearrangementNorm_def]

/-- The canonical everywhere-defined radial rearrangement `|u|*` has weak gradient
`W1p.gradient (W1p.schwarzRearrangementNorm u)` on the whole space. -/
theorem hasWeakFDerivOn_toReal_schwarzRearrangementNorm (u : W1p mu ⊤ 1) :
    HasWeakFDerivOn mu ⊤
      (fun x ↦ (TauCeti.schwarzRearrangement mu (fun y ↦ ‖W1p.value u y‖ₑ) x).toReal)
      (fun x ↦ innerSL ℝ (W1p.gradient (W1p.schwarzRearrangementNorm u) x)) :=
  (W1p.hasWeakFDerivOn (W1p.schwarzRearrangementNorm u)).congr_ae
    (value_schwarzRearrangementNorm_ae u)

/-- **Exclusion of singular concentration for `|u|*`.** For `u : W1p mu ⊤ 1`, the BV variation
measure of `|u|*` is absolutely continuous with respect to `mu`, with density
`‖W1p.gradient (W1p.schwarzRearrangementNorm u) ·‖ₑ`. -/
theorem variationMeasure_toReal_schwarzRearrangementNorm_eq_withDensity (u : W1p mu ⊤ 1) :
    variationMeasure mu ⊤
      (fun x ↦ (TauCeti.schwarzRearrangement mu (fun y ↦ ‖W1p.value u y‖ₑ) x).toReal) =
      (mu.comap ((↑) : (⊤ : Opens E) → E)).withDensity
        fun x ↦ ‖W1p.gradient (W1p.schwarzRearrangementNorm u) (x : E)‖ₑ := by
  rw [(hasWeakFDerivOn_toReal_schwarzRearrangementNorm u).variationMeasure_eq_withDensity]
  congr 1 with x
  rw [← ofReal_norm, innerSL_apply_norm, ofReal_norm]

/-- Absolute-value Schwarz rearrangement preserves the `L¹` value norm. -/
@[simp]
theorem norm_value_schwarzRearrangementNorm (u : W1p mu ⊤ 1) :
    ‖W1p.value (W1p.schwarzRearrangementNorm u)‖ = ‖W1p.value u‖ := by
  have hae := W1p.value_posPart_add_posPart_neg_ae ENNReal.one_ne_top u
  rw [schwarzRearrangementNorm_def, norm_value_schwarzRearrangement_of_ae_nonneg
    (hae.mono fun _ hx ↦ hx.symm ▸ abs_nonneg _), Lp.norm_def, Lp.norm_def]
  congr 1
  exact eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    (hae.mono fun x hx ↦ by rw [hx, Real.norm_eq_abs, abs_abs, Real.norm_eq_abs])

/-- **Signed `W^{1,1}` Pólya–Szegő inequality, `L¹` norm form.** Rearranging `|u|` does not
increase the `L¹` norm of the weak gradient. -/
theorem norm_gradient_schwarzRearrangementNorm_le (u : W1p mu ⊤ 1) :
    ‖W1p.gradient (W1p.schwarzRearrangementNorm u)‖ ≤ ‖W1p.gradient u‖ := by
  refine (norm_gradient_schwarzRearrangement_le _).trans (Lp.norm_le_norm_of_ae_le ?_)
  filter_upwards [Lp.coeFn_add (W1p.gradient (W1p.posPart ENNReal.one_ne_top u))
      (W1p.gradient (W1p.posPart ENNReal.one_ne_top (-u))),
    W1p.gradient_posPart_ae ENNReal.one_ne_top u,
    W1p.gradient_posPart_ae ENNReal.one_ne_top (-u),
    W1p.value_neg_ae u, Lp.coeFn_neg (W1p.gradient u)] with x hadd hp1 hp2 hvneg hgneg
  rw [W1p.gradient_add, hadd, Pi.add_apply, hp1, hp2]
  by_cases hxpos : (0 : ℝ) < W1p.value u x
  · have hxneg : ¬ (0 : ℝ) < W1p.value (-u) x := by
      rw [hvneg, Pi.neg_apply]
      linarith
    rw [indicator_of_mem hxpos, indicator_of_notMem hxneg, add_zero]
  · rw [indicator_of_notMem hxpos, zero_add]
    refine (norm_indicator_le_norm_self _ _).trans_eq ?_
    rw [W1p.gradient_neg, hgneg, Pi.neg_apply, norm_neg]

/-- **Signed `W^{1,1}` Pólya–Szegő inequality, Bochner integral form.** -/
theorem integral_norm_gradient_schwarzRearrangementNorm_le (u : W1p mu ⊤ 1) :
    ∫ x, ‖W1p.gradient (W1p.schwarzRearrangementNorm u) x‖ ∂mu ≤ ∫ x, ‖W1p.gradient u x‖ ∂mu := by
  simpa [L1.norm_eq_integral_norm] using norm_gradient_schwarzRearrangementNorm_le u

end W1p

end TauCeti
