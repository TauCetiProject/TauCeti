/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Distribution.TestFunction
import TauCeti.Data.ENNReal.Holder
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn
import TauCeti.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import TauCeti.Topology.UniformSpace.UniformConvergence.ENorm

/-!
# Convergence of bilinear pairings against test functions

Passing to the limit in weak formulations frequently pairs a fixed `C^n` test function
`φ ∈ 𝓓^{n}(Ω, W₀)` through a continuous bilinear map `P : W₀ →L[ℝ] G' →L[ℝ] H'` with a
convergent sequence of functions, operator families, or normalized-bump mollifications. Keeping
these limit theorems in a separate module avoids pulling convolution and approximate-identity
machinery into basic test-function integration.

## Main results

* `TestFunction.tendsto_integral_bilin_of_tendsto_lintegral_enorm_sub`:
  `∫ P (φ ·) (g i ·) → ∫ P (φ ·) (g₀ ·)` when `g i → g₀` in `L¹` on a set containing
  `tsupport φ`.
* `TestFunction.tendsto_integral_bilin_clm_of_tendstoUniformlyOn`:
  `∫ P (φ ·) (A i · (u ·)) → ∫ P (φ ·) (B · (u ·))` when `A i` is eventually continuous and
  converges uniformly on `tsupport φ`, and `u` is locally integrable on `Ω`.
* `TestFunction.tendsto_integral_bilin_normed_convolution`:
  `∫ P (φ ·) (B ((ρ i ⋆ 1_W U) ·) (u ·)) → ∫ P (φ ·) (B (U ·) (u ·))` when `U ∈ Lᵖ(W)`,
  `u ∈ L^q(W)` and `p⁻¹ + q⁻¹ ≤ 1`.
-/

public section

open Filter MeasureTheory Set TopologicalSpace
open scoped Convolution Distributions ENNReal Topology

namespace TestFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {Ω : Opens E} {n : ℕ∞}

/-- If `g i → g₀` in `L¹(s)` on a set `s` containing the topological support of `φ`, then the
bilinear pairings `∫ x, P (φ x) (g i x) ∂μ` converge to `∫ x, P (φ x) (g₀ x) ∂μ`. The
approximating pairings need only be eventually integrable, and the limiting pairing needs only to be
almost everywhere strongly measurable. -/
theorem tendsto_integral_bilin_of_tendsto_lintegral_enorm_sub
    {W₀ G' H' : Type*} [NormedAddCommGroup W₀] [NormedSpace ℝ W₀]
    [NormedAddCommGroup G'] [NormedSpace ℝ G'] [NormedAddCommGroup H'] [NormedSpace ℝ H']
    {μ : Measure E} {ι : Type*} {l : Filter ι} {s : Set E} (P : W₀ →L[ℝ] G' →L[ℝ] H')
    (φ : 𝓓^{n}(Ω, W₀)) (hφs : tsupport (φ : E → W₀) ⊆ s)
    {g : ι → E → G'} {g₀ : E → G'}
    (hg : ∀ᶠ i in l, Integrable (fun x => P ((φ : E → W₀) x) (g i x)) μ)
    (hg₀ : AEStronglyMeasurable (fun x => P ((φ : E → W₀) x) (g₀ x)) μ)
    (hlim : Tendsto (fun i => ∫⁻ x in s, ‖g i x - g₀ x‖ₑ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, P ((φ : E → W₀) x) (g i x) ∂μ) l
      (𝓝 (∫ x, P ((φ : E → W₀) x) (g₀ x) ∂μ)) := by
  obtain ⟨M, hM⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hind : Tendsto (fun i => ∫⁻ x, ‖s.indicator (g i) x - s.indicator g₀ x‖ₑ ∂μ) l (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
      fun i => (lintegral_mono fun x => by
        by_cases hx : x ∈ s <;> simp [hx]).trans (lintegral_indicator_le _ s)
  have hlimP := P.tendsto_lintegral_enorm_bilin_sub_of_norm_le (ae_of_all _ hM) hind
  refine tendsto_integral_of_L1 _ hg₀ hg (hlimP.congr fun i => lintegral_congr fun x => ?_)
  by_cases hxs : x ∈ s
  · simp [hxs]
  · simp [hxs, image_eq_zero_of_notMem_tsupport fun h => hxs (hφs h)]

/-- Pairing a `C^n` test function `φ` through `P` against `x ↦ A i x (u x)` converges to
`∫ x, P (φ x) (B x (u x)) ∂μ` when `A i → B` uniformly on `tsupport φ`, `A i` is eventually
continuous on `tsupport φ`, and `u` is locally integrable on `Ω`. -/
theorem tendsto_integral_bilin_clm_of_tendstoUniformlyOn [OpensMeasurableSpace E]
    {W₀ G' H' F' : Type*} [NormedAddCommGroup W₀] [NormedSpace ℝ W₀]
    [NormedAddCommGroup G'] [NormedSpace ℝ G'] [NormedAddCommGroup H'] [NormedSpace ℝ H']
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] {μ : Measure E} {ι : Type*} {l : Filter ι}
    (P : W₀ →L[ℝ] G' →L[ℝ] H') (φ : 𝓓^{n}(Ω, W₀)) {u : E → F'} (hu : LocallyIntegrableOn u Ω μ)
    {A : ι → E → F' →L[ℝ] G'} {B : E → F' →L[ℝ] G'}
    (hA : ∀ᶠ i in l, ContinuousOn (A i) (tsupport (φ : E → W₀)))
    (hunif : TendstoUniformlyOn A B l (tsupport (φ : E → W₀))) :
    Tendsto (fun i => ∫ x, P ((φ : E → W₀) x) (A i x (u x)) ∂μ) l
      (𝓝 (∫ x, P ((φ : E → W₀) x) (B x (u x)) ∂μ)) := by
  rcases eq_or_neBot l with rfl | _
  · exact tendsto_bot
  set K := tsupport (φ : E → W₀)
  have hKm : MeasurableSet K := (isClosed_tsupport _).measurableSet
  have huK : IntegrableOn u K μ :=
    hu.integrableOn_compact_subset φ.tsupport_subset φ.hasCompactSupport
  have hint {C : E → F' →L[ℝ] G'} (hC : ContinuousOn C K) :
      Integrable (fun x => P ((φ : E → W₀) x) (C x (u x))) μ :=
    (integrableOn_iff_integrable_of_support_subset
      fun _ hx => subset_tsupport _ fun h0 => hx (by simp [h0])).1 <|
      memLp_one_iff_integrable.1 <| P.memLp_of_bilin 1 φ.memLp_top <|
        (ContinuousLinearMap.id ℝ (F' →L[ℝ] G')).memLp_of_bilin 1
          (hC.memLp_top_restrict_of_subset_isCompact φ.hasCompactSupport hKm subset_rfl)
          (memLp_one_iff_integrable.2 huK)
  have hsup : Tendsto (fun i => (⨆ y ∈ K, ‖A i y - B y‖ₑ) * ∫⁻ x in K, ‖u x‖ₑ ∂μ) l (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hunif.tendsto_iSup_enorm_sub (Or.inr huK.2.ne)
  refine φ.tendsto_integral_bilin_of_tendsto_lintegral_enorm_sub P subset_rfl
    (hA.mono fun _ => hint) (hint (hunif.continuousOn hA.frequently)).aestronglyMeasurable
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsup
      (fun _ => zero_le) fun i => ?_)
  rw [← lintegral_const_mul'' _ huK.aestronglyMeasurable.eNorm]
  refine setLIntegral_mono' hKm fun x hx => ?_
  rw [← sub_apply]
  exact ((A i x - B x).le_opENorm (u x)).trans
    (by gcongr; exact le_biSup (fun y => ‖A i y - B y‖ₑ) hx)

/-- Pairing a `C^n` test function supported in a null-measurable set `W` through `P` against
`x ↦ B (((ρ i).normed μ ⋆ 1_W U) x) (u x)` converges to `∫ x, P (φ x) (B (U x) (u x)) ∂μ` when
`U ∈ Lᵖ(W)`, `u ∈ L^q(W)` and `p⁻¹ + q⁻¹ ≤ 1` (allowing `p = ∞` or `q = ∞`). -/
theorem tendsto_integral_bilin_normed_convolution
    [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {W₀ H₀ H₁ F' G' : Type*} [NormedAddCommGroup W₀] [NormedSpace ℝ W₀]
    [NormedAddCommGroup H₀] [NormedSpace ℝ H₀] [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [CompleteSpace H₁] [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
    [NormedAddCommGroup G'] [NormedSpace ℝ G']
    (P : W₀ →L[ℝ] H₀ →L[ℝ] H₁) (B : F' →L[ℝ] G' →L[ℝ] H₀)
    {p q : ℝ≥0∞} (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {W : Set E} (hW : NullMeasurableSet W μ) (φ : 𝓓^{n}(Ω, W₀))
    (hφW : tsupport (φ : E → W₀) ⊆ W) {U : E → F'} (hU : MemLp U p (μ.restrict W))
    {u : E → G'} (hu : MemLp u q (μ.restrict W))
    {ι : Type*} {l : Filter ι} {ρ : ι → ContDiffBump (0 : E)}
    (hρ : Tendsto (fun i => (ρ i).rOut) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, P ((φ : E → W₀) x)
        (B (((ρ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] W.indicator U) x)
          (u x)) ∂μ)
      l (𝓝 (∫ x, P ((φ : E → W₀) x) (B (U x) (u x)) ∂μ)) := by
  let _ : Fact (1 ≤ p) := ⟨ENNReal.one_le_left_of_inv_add_inv_le_one hpq⟩
  have : p.HolderConjugate p.conjExponent := .conjExponent Fact.out
  have hp'q : p.conjExponent ≤ q := ENNReal.conjExponent_le_of_inv_add_inv_le_one hpq
  set K : Set E := tsupport (φ : E → W₀)
  have hKm : NullMeasurableSet K μ := (isClosed_tsupport _).measurableSet.nullMeasurableSet
  have : IsFiniteMeasure (μ.restrict K) :=
    isFiniteMeasure_restrict.2 φ.hasCompactSupport.measure_lt_top.ne
  have huK : MemLp u p.conjExponent (μ.restrict K) :=
    (hu.mono_measure (Measure.restrict_mono hφW le_rfl)).mono_exponent hp'q
  let C : W₀ →L[ℝ] G' →L[ℝ] F' →L[ℝ] H₁ :=
    ((ContinuousLinearMap.compL ℝ F' H₀ H₁).comp P).bilinearComp
      (ContinuousLinearMap.id ℝ W₀) B.flip
  have ha : MemLp (fun x => C ((φ : E → W₀) x) (K.indicator u x)) p.conjExponent μ :=
    C.memLp_of_bilin p.conjExponent φ.memLp_top ((memLp_indicator_iff_restrict hKm).2 huK)
  have hlim := (ContinuousLinearMap.id ℝ (F' →L[ℝ] H₁)).tendsto_integral_bilin_normed_convolution
    hρ ha ((memLp_indicator_iff_restrict hW).2 hU)
  have hpt (x : E) (y : F') :
      C ((φ : E → W₀) x) (K.indicator u x) y = P ((φ : E → W₀) x) (B y (u x)) := by
    by_cases hx : x ∈ K
    · simp [C, hx]
    · simp [C, image_eq_zero_of_notMem_tsupport hx]
  have hlim_rhs : ∫ x, P ((φ : E → W₀) x) (B (W.indicator U x) (u x)) ∂μ =
      ∫ x, P ((φ : E → W₀) x) (B (U x) (u x)) ∂μ :=
    integral_congr_ae (.of_forall fun x => by
      by_cases hx : x ∈ W
      · simp [hx]
      · simp [image_eq_zero_of_notMem_tsupport fun h => hx (hφW h)])
  simpa only [ContinuousLinearMap.id_apply, hpt, hlim_rhs] using hlim

end TestFunction
