/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder
public import TauCeti.Analysis.Sobolev.Circle.OfContinuousMap
import TauCeti.Analysis.Fourier.Uniqueness
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Norm
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Slice pairings of sections of the cylinder with loops

Let `F` be a complex inner product space and `η : ℝ × ℝ → F` a section of the trivial bundle over
the cylinder, square integrable on the strip `ℝ × [0, 1]`
(`TauCeti.CylinderSobolev.stripMeasure`). Its slice pairing with a loop `ψ` is the function
`s ↦ ∫₀¹ Re ⟪ψ(t), η(s, t)⟫`. This file shows how the slice pairing computes the pairing of `η`
with product sections `φ(s) ψ(t)`, and that the slice pairings with all continuous loops of
period one determine `η`.

## Main results

* `TauCeti.CylinderSobolev.integrable_re_inner_smul`: the pairing of `η` with a product section
  `φ(s) ψ(t)` is integrable on the strip.
* `TauCeti.CylinderSobolev.integral_re_inner_smul_eq_integral_mul_slice`: Fubini's theorem for
  the pairing of `η` with a product section `φ(s) ψ(t)`.
* `TauCeti.CylinderSobolev.integrableOn_slice_re_inner` and
  `TauCeti.CylinderSobolev.locallyIntegrable_slice_re_inner`: the slice pairing with a bounded loop
  is locally integrable.
* `TauCeti.CylinderSobolev.integral_abs_slice_re_inner_le`: the integral of the absolute value of
  the slice pairing over `[a, b]` is bounded by `((b - a) B² + ‖η‖²_{L²}) / 2`.
* `TauCeti.CylinderSobolev.abs_integral_re_inner_smul_le`: Cauchy–Schwarz for product sections,
  `|∫ Re ⟪φ ⊗ χ, η⟫| ≤ ‖φ‖_{L²} ‖η‖_{L²} ‖χ‖_{H⁰}`.
* `TauCeti.CylinderSobolev.slice_re_inner_ae_eq_zero_of_hilbertBasis`: if the slice pairings of
  `η` with continuous loops forming a Hilbert basis of `H⁰` vanish almost everywhere, so do its
  slice pairings with every continuous loop.
* `TauCeti.CylinderSobolev.ae_eq_zero_of_forall_slice_re_inner_ae_eq_zero`: if the slice pairings
  of `η` with every continuous loop vanish almost everywhere, then `η` vanishes almost everywhere.
-/

public section

noncomputable section

open MeasureTheory Set Filter Complex
open TauCeti.StripSobolev (stripMeasure)

namespace TauCeti.CylinderSobolev

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The pairing of `η` with a product section `φ(s) ψ(t)`, for `φ` continuous with compact support
and `ψ` continuous, is integrable on the strip. -/
theorem integrable_re_inner_smul {η : ℝ × ℝ → F} (hη : MemLp η 2 stripMeasure) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) {ψ : ℝ → F} (hψ : Continuous ψ) :
    Integrable (fun z ↦ (inner ℂ (φ z.1 • ψ z.2) (η z)).re) stripMeasure :=
  ((memLp_smul_of_hasCompactSupport hφ hφc hψ 2).integrable_inner (𝕜 := ℂ) hη).re

/-- **Fubini for product sections.** Pairing `η` with `φ(s) ψ(t)` over the strip integrates `φ`
against the slice pairing `s ↦ ∫₀¹ Re ⟪ψ(t), η(s, t)⟫`. -/
theorem integral_re_inner_smul_eq_integral_mul_slice {η : ℝ × ℝ → F}
    (hη : MemLp η 2 stripMeasure) {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {ψ : ℝ → F} (hψ : Continuous ψ) :
    ∫ z, (inner ℂ (φ z.1 • ψ z.2) (η z)).re ∂stripMeasure =
      ∫ s, φ s * ∫ t in Icc (0 : ℝ) 1, (inner ℂ (ψ t) (η (s, t))).re := by
  have hint := integrable_re_inner_smul hη hφ hφc hψ
  rw [stripMeasure_eq_prod] at hint ⊢
  rw [integral_prod _ hint]
  refine integral_congr_ae (ae_of_all _ fun s ↦ ?_)
  simp only [inner_smul_left_eq_smul, Complex.smul_re, smul_eq_mul]
  exact integral_const_mul _ _

/-- The slice pairing `s ↦ ∫₀¹ Re ⟪ψ(t), η(s, t)⟫` of `η` with a bounded continuous `ψ` is
integrable on every interval `[a, b]`. -/
theorem integrableOn_slice_re_inner {η : ℝ × ℝ → F} (hη : MemLp η 2 stripMeasure) {ψ : ℝ → F}
    (hψ : Continuous ψ) {B : ℝ} (hB : ∀ t, ‖ψ t‖ ≤ B) (a b : ℝ) :
    IntegrableOn (fun s ↦ ∫ t in Icc (0 : ℝ) 1, (inner ℂ (ψ t) (η (s, t))).re) (Icc a b) := by
  set μ : Measure (ℝ × ℝ) := (volume.restrict (Icc a b)).prod (volume.restrict (Icc (0 : ℝ) 1))
  have hμ : μ ≤ stripMeasure := by
    rw [stripMeasure_eq_prod]
    exact Measure.prod_mono Measure.restrict_le_self le_rfl
  have hψ2 : MemLp (fun z : ℝ × ℝ ↦ ψ z.2) 2 μ :=
    MemLp.of_bound (hψ.comp continuous_snd).aestronglyMeasurable B (ae_of_all _ fun z ↦ hB z.2)
  exact (hψ2.integrable_inner (𝕜 := ℂ) (hη.mono_measure hμ)).re.integral_prod_left

/-- **Growth of the slice pairing.** If `‖ψ‖ ≤ B` and `‖η‖²` is integrable on the strip, the
integral over `[a, b]` of the absolute value of the slice pairing `s ↦ ∫₀¹ Re ⟪ψ(t), η(s, t)⟫` is
at most `((b - a) B² + ∫ ‖η‖²) / 2`. -/
theorem integral_abs_slice_re_inner_le {η : ℝ × ℝ → F} (hη : MemLp η 2 stripMeasure) {ψ : ℝ → F}
    (hψ : Continuous ψ) {B : ℝ} (hB : ∀ t, ‖ψ t‖ ≤ B) {a b : ℝ} (hab : a ≤ b) :
    ∫ s in Icc a b, |∫ t in Icc (0 : ℝ) 1, (inner ℂ (ψ t) (η (s, t))).re| ≤
      ((b - a) * B ^ 2 + ∫ z, ‖η z‖ ^ 2 ∂stripMeasure) / 2 := by
  set μ : Measure (ℝ × ℝ) := (volume.restrict (Icc a b)).prod (volume.restrict (Icc (0 : ℝ) 1))
  have hμ : μ ≤ stripMeasure := by
    rw [stripMeasure_eq_prod]
    exact Measure.prod_mono Measure.restrict_le_self le_rfl
  have hμuniv : μ.real univ = b - a := by
    simp [μ, Measure.real, ← univ_prod_univ, Measure.prod_prod, Real.volume_Icc, hab]
  have hη2 : Integrable (fun z ↦ ‖η z‖ ^ 2) stripMeasure :=
    (memLp_two_iff_integrable_sq_norm hη.aestronglyMeasurable).1 hη
  set G : ℝ × ℝ → ℝ := fun z ↦ (B ^ 2 + ‖η z‖ ^ 2) / 2
  have hG : Integrable G μ :=
    ((integrable_const _).add (hη2.mono_measure hμ)).div_const _
  have hgG (z : ℝ × ℝ) : ‖(inner ℂ (ψ z.2) (η z)).re‖ ≤ G z := by
    have h1 := (abs_re_le_norm (inner ℂ (ψ z.2) (η z))).trans (norm_inner_le_norm (ψ z.2) (η z))
    have h2 : ‖ψ z.2‖ * ‖η z‖ ≤ B * ‖η z‖ := mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
    have h3 := two_mul_le_add_sq B ‖η z‖
    rw [Real.norm_eq_abs]
    simp only [G]
    nlinarith
  have hg : Integrable (fun z : ℝ × ℝ ↦ (inner ℂ (ψ z.2) (η z)).re) μ :=
    hG.mono' ((hψ.comp continuous_snd).aestronglyMeasurable.inner (𝕜 := ℂ)
      (hη.aestronglyMeasurable.mono_measure hμ)).re (ae_of_all _ hgG)
  calc ∫ s in Icc a b, |∫ t in Icc (0 : ℝ) 1, (inner ℂ (ψ t) (η (s, t))).re|
      ≤ ∫ s in Icc a b, ∫ t in Icc (0 : ℝ) 1, ‖(inner ℂ (ψ t) (η (s, t))).re‖ :=
        integral_mono hg.integral_prod_left.abs hg.norm.integral_prod_left fun s ↦ by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_integral_norm _
    _ = ∫ z, ‖(inner ℂ (ψ z.2) (η z)).re‖ ∂μ := (integral_prod _ hg.norm).symm
    _ ≤ ∫ z, G z ∂μ := integral_mono hg.norm hG hgG
    _ = ((b - a) * B ^ 2 + ∫ z, ‖η z‖ ^ 2 ∂μ) / 2 := by
        simp only [G]
        rw [integral_div, integral_add (integrable_const _) (hη2.mono_measure hμ),
          integral_const, hμuniv, smul_eq_mul]
    _ ≤ ((b - a) * B ^ 2 + ∫ z, ‖η z‖ ^ 2 ∂stripMeasure) / 2 := by
        have := integral_mono_measure hμ (ae_of_all _ fun z ↦ by positivity) hη2
        linarith

/-- The slice pairing `s ↦ ∫₀¹ Re ⟪χ(t), η(s, t)⟫` with a continuous loop `χ` of period one is
locally integrable. -/
theorem locallyIntegrable_slice_re_inner {η : ℝ × ℝ → F} (hη : MemLp η 2 stripMeasure)
    (χ : C(AddCircle (1 : ℝ), F)) :
    LocallyIntegrable fun s ↦ ∫ t in Icc (0 : ℝ) 1, (inner ℂ (χ t) (η (s, t))).re := by
  refine locallyIntegrable_iff.2 fun k hk ↦ ?_
  obtain ⟨R, hR⟩ := hk.isBounded.subset_closedBall 0
  refine (integrableOn_slice_re_inner hη (χ.continuous.comp (AddCircle.continuous_mk' 1))
    (fun t ↦ χ.norm_coe_le_norm _) (-|R|) |R|).mono_set fun x hx ↦ ?_
  have := hR hx
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  exact ⟨by linarith [neg_abs_le x, le_abs_self R], by linarith [le_abs_self x, le_abs_self R]⟩

/-- **Cauchy–Schwarz for product sections.** The pairing of `η` with `φ(s) χ(t)` is bounded by
`‖φ‖_{L²} ‖η‖_{L²} ‖χ‖_{H⁰}`, by Cauchy–Schwarz on the strip and Parseval's identity. -/
theorem abs_integral_re_inner_smul_le [FiniteDimensional ℂ F] {η : ℝ × ℝ → F}
    (hη : MemLp η 2 stripMeasure) {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (χ : C(AddCircle (1 : ℝ), F)) :
    |∫ z, (inner ℂ (φ z.1 • χ z.2) (η z)).re ∂stripMeasure| ≤
      Real.sqrt (∫ s, φ s ^ 2) * ‖hη.toLp η‖ * ‖CircleSobolev.ofContinuousMap 1 χ‖ := by
  have hu := memLp_smul_of_hasCompactSupport (ψ := fun t : ℝ ↦ χ t) hφ hφc
    (χ.continuous.comp (AddCircle.continuous_mk' 1)) 2
  -- `‖φ ⊗ χ‖² = ‖φ‖² ‖χ‖²`, by Fubini and Parseval's identity.
  have hnorm : ‖hu.toLp _‖ = Real.sqrt (∫ s, φ s ^ 2) * ‖CircleSobolev.ofContinuousMap 1 χ‖ := by
    refine (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, Real.sq_sqrt (integral_nonneg fun s ↦ sq_nonneg _), MemLp.norm_toLp_sq,
      stripMeasure_eq_prod]
    simp_rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [integral_prod_mul (μ := volume) (ν := volume.restrict (Icc (0 : ℝ) 1))
      (fun s ↦ φ s ^ 2) fun t : ℝ ↦ ‖χ t‖ ^ 2,
      CircleSobolev.integral_norm_sq_eq_mul_norm_ofContinuousMap_sq, one_mul]
  have hu' : (fun z ↦ inner ℂ (hu.toLp _ z) (η z)) =ᵐ[stripMeasure]
      fun z ↦ inner ℂ (φ z.1 • χ z.2) (η z) :=
    hu.coeFn_toLp.mono fun z hz ↦ congrArg (inner ℂ · (η z)) hz
  have hre : ∫ z, (inner ℂ (φ z.1 • χ z.2) (η z)).re ∂stripMeasure =
      RCLike.re (inner ℂ (hu.toLp _) (hη.toLp η)) := by
    rw [L2.inner_toLp (hu.toLp _) hη, integral_congr_ae hu']
    exact integral_re (hu.integrable_inner (𝕜 := ℂ) hη)
  rw [hre]
  refine ((abs_re_le_norm _).trans (norm_inner_le_norm _ _)).trans (le_of_eq ?_)
  rw [hnorm]
  ring

/-- **From a Hilbert basis of loops to all loops.** If `H⁰` has a Hilbert basis of continuous
loops `e i` whose slice pairings `s ↦ ∫₀¹ Re ⟪e i (t), η(s, t)⟫` vanish almost everywhere, then
the slice pairing of `η` with every continuous loop vanishes almost everywhere. -/
theorem slice_re_inner_ae_eq_zero_of_hilbertBasis [FiniteDimensional ℂ F] {η : ℝ × ℝ → F}
    (hη : MemLp η 2 stripMeasure) {ι : Type*} (b : HilbertBasis ι ℝ (CircleSobolev 0 F))
    (e : ι → C(AddCircle (1 : ℝ), F)) (hb : ∀ i, b i = CircleSobolev.ofContinuousMap 1 (e i))
    (he : ∀ i, (fun s ↦ ∫ t in Icc (0 : ℝ) 1, (inner ℂ (e i t) (η (s, t))).re) =ᵐ[volume] 0)
    (ψ : C(AddCircle (1 : ℝ), F)) :
    (fun s ↦ ∫ t in Icc (0 : ℝ) 1, (inner ℂ (ψ t) (η (s, t))).re) =ᵐ[volume] 0 := by
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero (locallyIntegrable_slice_re_inner hη ψ)
    fun φ hφ hφc ↦ ?_
  have hint (χ : C(AddCircle (1 : ℝ), F)) :
      Integrable (fun z ↦ (inner ℂ (φ z.1 • χ z.2) (η z)).re) stripMeasure :=
    integrable_re_inner_smul hη hφ.continuous hφc (χ.continuous.comp (AddCircle.continuous_mk' 1))
  -- The functional `Λ χ = ∫ ⟪φ ⊗ χ, η⟫` on continuous loops is real-linear.
  let Λ : C(AddCircle (1 : ℝ), F) →ₗ[ℝ] ℝ :=
    { toFun := fun χ ↦ ∫ z, (inner ℂ (φ z.1 • χ z.2) (η z)).re ∂stripMeasure
      map_add' := fun χ χ' ↦ by
        simp only [ContinuousMap.add_apply, smul_add, inner_add_left, add_re]
        exact integral_add (hint χ) (hint χ')
      map_smul' := fun c χ ↦ by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply, smul_eq_mul, smul_comm (φ _) c,
          inner_smul_left_eq_smul, Complex.smul_re]
        exact integral_const_mul _ _ }
  have hΛ (χ : C(AddCircle (1 : ℝ), F)) :
      Λ χ = ∫ s, φ s * ∫ t in Icc (0 : ℝ) 1, (inner ℂ (χ t) (η (s, t))).re :=
    integral_re_inner_smul_eq_integral_mul_slice (ψ := fun t : ℝ ↦ χ t) hη hφ.continuous hφc
      (χ.continuous.comp (AddCircle.continuous_mk' 1))
  have h0 := CircleSobolev.eq_zero_of_abs_le_of_hilbertBasis 1 Λ
    (abs_integral_re_inner_smul_le hη hφ.continuous hφc) b e hb
    (fun i ↦ by rw [hΛ]; exact integral_eq_zero_of_ae ((he i).mono fun s hs ↦ by simp [hs])) ψ
  rw [hΛ] at h0
  simpa [smul_eq_mul] using h0

/-- **Vanishing slice pairings force vanishing.** If the slice pairing
`s ↦ ∫₀¹ Re ⟪ψ(t), η(s, t)⟫` of `η` with every continuous loop `ψ` of period one vanishes almost
everywhere, then `η` vanishes almost everywhere on the strip: by separability of the space of
loops, for almost every `s` the slice pairing vanishes for all loops at once, so the slice
`η(s, ·)` vanishes, and Fubini's theorem applies. -/
theorem ae_eq_zero_of_forall_slice_re_inner_ae_eq_zero [SecondCountableTopology F]
    {η : ℝ × ℝ → F}
    (hη : MemLp η 2 stripMeasure)
    (h : ∀ ψ : C(AddCircle (1 : ℝ), F),
      (fun s ↦ ∫ t in Icc (0 : ℝ) 1, (inner ℂ (ψ t) (η (s, t))).re) =ᵐ[volume] 0) :
    η =ᵐ[stripMeasure] 0 := by
  set ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have hηp : MemLp η 2 ((volume : Measure ℝ).prod ν) := stripMeasure_eq_prod ▸ hη
  -- Almost every slice is integrable on `[0, 1]`.
  have hslice : ∀ᵐ s, Integrable (fun t ↦ η (s, t)) ν := by
    have h2 := ((memLp_two_iff_integrable_sq_norm hηp.aestronglyMeasurable).1 hηp).prod_right_ae
    filter_upwards [h2, hηp.aestronglyMeasurable.prodMk_left] with s hs hm
    exact ((memLp_two_iff_integrable_sq_norm hm).2 hs).integrable one_le_two
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense C(AddCircle (1 : ℝ), F)
  have hfin : ∀ᵐ s, ∀ᵐ t ∂ν, η (s, t) = 0 := by
    filter_upwards [hslice, (ae_ball_iff hDc).2 fun ψ _ ↦ h ψ] with s hs hsD
    have hs' : IntegrableOn (fun t ↦ η (s, t)) (Icc (0 : ℝ) 1) := hs
    exact hs'.ae_eq_zero_of_forall_integral_re_inner_continuousMap_eq_zero
      (hs'.integral_re_inner_continuousMap_eq_zero_of_dense hD hsD)
  -- Pass to a strongly measurable representative to apply Fubini's theorem to the zero set.
  have hηη' : η =ᵐ[(volume : Measure ℝ).prod ν] hηp.aestronglyMeasurable.mk η :=
    hηp.aestronglyMeasurable.ae_eq_mk
  have h' : ∀ᵐ s, ∀ᵐ t ∂ν, hηp.aestronglyMeasurable.mk η (s, t) = 0 := by
    filter_upwards [Measure.ae_ae_of_ae_prod hηη', hfin] with s h1 h2
    filter_upwards [h1, h2] with t ht1 ht2
    rw [← ht1, ht2]
  have hmeas : MeasurableSet {z : ℝ × ℝ | hηp.aestronglyMeasurable.mk η z = 0} :=
    hηp.aestronglyMeasurable.stronglyMeasurable_mk.measurableSet_eq_fun stronglyMeasurable_const
  rw [stripMeasure_eq_prod]
  filter_upwards [hηη', (Measure.ae_prod_mem_iff_ae_ae_mem hmeas).2 h'] with z h1 h2
  rw [h1]
  exact h2

end TauCeti.CylinderSobolev
