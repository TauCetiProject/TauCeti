/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Slice
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# The coarea pairing identity for slices by smooth functions

For a locally normal `(k + 1)`-current `T` on an open set `Ω ⊆ E`, a smooth function `u : E → ℝ`,
a smooth scalar weight `g : ℝ → ℝ`, and a test `k`-form `φ`, integrating the level-set pairings
`g(t) ⟨T, u, t⟩(φ)` over `t ∈ ℝ` recovers the contraction of `T` with `(g ∘ u) du`:

`∫ t, g t * slice T u t φ = T (smulLeftCLM (hg.comp hu) (oneFormWedgeCLM _ φ))`.

Taking `g = 1` gives `∫ t, slice T u t φ = T (du ∧ φ)`.

The proof avoids weak-star Fubini arguments by applying the one-dimensional fundamental theorem of
calculus directly to the `L¹(‖S‖)` curve `s ↦ (∫_{a}^{s} g(t) ψ((m + 1)(t - u(·))) dt) • η`,
comparing with the antiderivative `H(s) = ∫_{s}^{M} g(t) dt` as `m → ∞`, and concluding via the
Leibniz rule `∂((H ∘ u) T) = (H ∘ u) ∂T + (g ∘ u) (T ⌞ du)`.

## Main declarations

* `Distribution.continuous_apply_smulLeftCLM_smoothTransition`,
  `Distribution.continuous_neg_oneFormWedgeCLM_smoothTransition`: continuity in `t` of the
  smooth-transition approximants to Borel restriction and slicing.
* `Distribution.integral_mul_slice_apply`: the coarea pairing identity
  `∫ g(t) ⟨T, u, t⟩(φ) dt = T((g ∘ u) • (du ∧ φ))` for smooth `u` and `g`.
* `Distribution.integral_slice_apply`: `∫ ⟨T, u, t⟩(φ) dt = T(du ∧ φ)` for smooth `u`.

## References

* H. Federer, *Geometric Measure Theory*, §4.3.2 (coarea formula for slices of normal currents).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §5.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter TestFunction ContinuousLinearMap
open scoped ENNReal NNReal Distributions Topology ContDiff

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {Ω : Opens E} {k : ℕ} {u : E → ℝ}

private theorem exists_lipschitzWith_smoothTransition :
    ∃ K : ℝ≥0, LipschitzWith K Real.smoothTransition := by
  obtain ⟨L₁, hL₁⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  let K : ℝ≥0 := ⟨max L₁ 0, le_max_right _ _⟩
  refine ⟨K, lipschitzWith_of_nnNorm_deriv_le
    ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp)) fun τ => ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnNorm]
  exact (hL₁ τ).trans (le_max_left _ _)

/-- The integrated smooth-transition multiplier `(∫_{a}^{b} g t ψ((m + 1) (t - u x)) dt) • η x`
belongs to `L¹(μ; G)` for every locally finite Borel measure `μ` on `Ω`. -/
private theorem memLp_intervalIntegral_mul_smoothTransition_smul {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] (μ : Measure Ω) [IsFiniteMeasureOnCompacts μ]
    (hu : ContDiff ℝ ∞ u) {g : ℝ → ℝ} (hg : Continuous g) (η : 𝓓(Ω, G)) (a b : ℝ) (m : ℕ) :
    MemLp (fun x : Ω =>
      (∫ t in a..b, g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x))) • η x) 1 μ := by
  obtain ⟨Lψ, hLip⟩ := exists_lipschitzWith_smoothTransition
  have hgi (y : E) : IntervalIntegrable
      (fun t => g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u y))) volume a b :=
    (hg.mul (Real.smoothTransition.continuous.comp
      (continuous_const.mul (continuous_id.sub continuous_const)))).intervalIntegrable a b
  have hJcont : Continuous fun x : E =>
      ∫ t in a..b, g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) := by
    rw [Metric.continuous_iff]
    intro x₀ ε hε
    let I : ℝ := ∫ t in uIoc a b, |g t|
    have _hI0 : 0 ≤ I := integral_nonneg fun _ => abs_nonneg _
    let K : ℝ := (I + 1) * ((Lψ : ℝ) + 1) * ((m : ℝ) + 1)
    have hKpos : 0 < K := by positivity
    obtain ⟨δ, hδ, huδ⟩ := Metric.continuousAt_iff.1 hu.continuous.continuousAt
      (ε / K) (div_pos hε hKpos)
    refine ⟨δ, hδ, fun x hx => ?_⟩
    have hux : |u x - u x₀| < ε / K := by simpa [Real.dist_eq] using huδ hx
    rw [Real.dist_eq, ← intervalIntegral.integral_sub (hgi x) (hgi x₀)]
    have hp (t : ℝ) : |g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) -
        g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x₀))| ≤
        |g t| * ((Lψ : ℝ) * (((m : ℝ) + 1) * |u x - u x₀|)) := by
      rw [← mul_sub, abs_mul]
      gcongr
      have hd := hLip.dist_le_mul (((m : ℝ) + 1) * (t - u x)) (((m : ℝ) + 1) * (t - u x₀))
      simp only [Real.dist_eq] at hd
      refine hd.trans_eq ?_
      rw [show ((m : ℝ) + 1) * (t - u x) - ((m : ℝ) + 1) * (t - u x₀) =
        -((m : ℝ) + 1) * (u x - u x₀) by ring, abs_mul, abs_neg,
        abs_of_pos (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
    have habs := intervalIntegral.norm_integral_le_integral_norm_uIoc
      (f := fun t => g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) -
        g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x₀)))
      (a := a) (b := b) (μ := volume)
    simp only [Real.norm_eq_abs] at habs
    calc |∫ t in a..b, (g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) -
            g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x₀)))|
        ≤ ∫ t in uIoc a b, |g t| * ((Lψ : ℝ) * (((m : ℝ) + 1) * |u x - u x₀|)) :=
          habs.trans (integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
            ((intervalIntegrable_iff.1 (hg.abs.intervalIntegrable a b)).mul_const _)
            (ae_of_all _ hp))
      _ = I * ((Lψ : ℝ) * (((m : ℝ) + 1) * |u x - u x₀|)) := integral_mul_const _ _
      _ ≤ K * |u x - u x₀| := by
          have h3 : I * (Lψ : ℝ) ≤ (I + 1) * ((Lψ : ℝ) + 1) :=
            mul_le_mul (le_add_of_nonneg_right zero_le_one)
              (le_add_of_nonneg_right zero_le_one) Lψ.coe_nonneg (by positivity)
          calc I * ((Lψ : ℝ) * (((m : ℝ) + 1) * |u x - u x₀|))
              = (I * (Lψ : ℝ)) * (((m : ℝ) + 1) * |u x - u x₀|) := by ring
            _ ≤ ((I + 1) * ((Lψ : ℝ) + 1)) * (((m : ℝ) + 1) * |u x - u x₀|) :=
                mul_le_mul_of_nonneg_right h3 (by positivity)
            _ = K * |u x - u x₀| := by ring
      _ < K * (ε / K) := mul_lt_mul_of_pos_left hux hKpos
      _ = ε := mul_div_cancel₀ ε hKpos.ne'
  have hJbound (x : Ω) :
      ‖(∫ t in a..b, g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x))) • η x‖ ≤
        (∫ t in uIoc a b, |g t|) * ‖η x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    gcongr
    have habs := intervalIntegral.norm_integral_le_integral_norm_uIoc
      (f := fun t => g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x)))
      (a := a) (b := b) (μ := volume)
    simp only [Real.norm_eq_abs] at habs
    refine habs.trans (integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
      (intervalIntegrable_iff.1 (hg.abs.intervalIntegrable a b)) (ae_of_all _ fun t => ?_))
    dsimp only
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.smoothTransition.abs_le_one _)
  exact ((TestFunction.memLp_subtype (p := 1) (μ := μ) η).norm.const_mul
    (∫ t in uIoc a b, |g t|)).mono
    (((hJcont.comp continuous_subtype_val).smul
      (η.continuous.comp continuous_subtype_val)).aestronglyMeasurable)
    (ae_of_all _ fun x => (hJbound x).trans (le_abs_self _))

/-- Continuity of `s ↦ S (ψ((m + 1) (s - u ·)) • η)` for a locally finite-mass functional `S`. -/
theorem continuous_apply_smulLeftCLM_smoothTransition {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {S : 𝓓(Ω, G) →L[ℝ] ℝ} (hS : HasLocallyFiniteMass S) (hu : ContDiff ℝ ∞ u)
    (η : 𝓓(Ω, G)) (m : ℕ) :
    Continuous fun s : ℝ => S (smulLeftCLM
      (Real.smoothTransition.contDiff.comp
        (contDiff_const.mul (contDiff_const.sub hu)) :
          ContDiff ℝ ∞ fun x => Real.smoothTransition (((m : ℝ) + 1) * (s - u x))) η) := by
  obtain ⟨Lψ, hLip⟩ := exists_lipschitzWith_smoothTransition
  let hf (s : ℝ) : ContDiff ℝ ∞ fun x => Real.smoothTransition (((m : ℝ) + 1) * (s - u x)) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub hu))
  simp_rw [← extendL1_toLp hS]
  refine (extendL1 S).continuous.comp ?_
  rw [Metric.continuous_iff]
  intro s₀ ε hε
  let K : ℝ := ((Lψ : ℝ) + 1) * ((m : ℝ) + 1) * (‖TestFunction.toLp 1 (massMeasure S) η‖ + 1)
  have hKpos : 0 < K := by positivity
  refine ⟨ε / K, div_pos hε hKpos, fun s hs => ?_⟩
  have hss₀ : |s - s₀| < ε / K := by simpa [Real.dist_eq] using hs
  rw [dist_eq_norm, TestFunction.toLp_apply, TestFunction.toLp_apply, ← MemLp.toLp_sub,
    Lp.norm_toLp]
  have hle_lp : eLpNorm (fun x : Ω => smulLeftCLM (hf s) η x - smulLeftCLM (hf s₀) η x) 1
      (massMeasure S) ≤
      ENNReal.ofReal ((Lψ : ℝ) * ((m : ℝ) + 1) * |s - s₀|) *
        eLpNorm (fun x : Ω => η x) 1 (massMeasure S) := by
    change eLpNorm ((fun x : Ω => smulLeftCLM (hf s) η x) -
        fun x : Ω => smulLeftCLM (hf s₀) η x) 1 (massMeasure S) ≤ _
    rw [eLpNorm_one_eq_lintegral_eNorm
        (((TestFunction.memLp_subtype (p := 1) (smulLeftCLM (hf s) η)).sub
          (TestFunction.memLp_subtype (p := 1) (smulLeftCLM (hf s₀) η))).aestronglyMeasurable),
      eLpNorm_one_eq_lintegral_eNorm
        (TestFunction.memLp_subtype (p := 1) η).aestronglyMeasurable,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    dsimp only [Pi.sub_apply]
    have hψ_le : |Real.smoothTransition (((m : ℝ) + 1) * (s - u x)) -
        Real.smoothTransition (((m : ℝ) + 1) * (s₀ - u x))| ≤
        (Lψ : ℝ) * ((m : ℝ) + 1) * |s - s₀| := by
      have hd := hLip.dist_le_mul (((m : ℝ) + 1) * (s - u x)) (((m : ℝ) + 1) * (s₀ - u x))
      simp only [Real.dist_eq] at hd
      refine hd.trans_eq ?_
      rw [show ((m : ℝ) + 1) * (s - u x) - ((m : ℝ) + 1) * (s₀ - u x) =
        ((m : ℝ) + 1) * (s - s₀) by ring, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < (m : ℝ) + 1), ← mul_assoc]
    have hsub : smulLeftCLM (hf s) η x - smulLeftCLM (hf s₀) η x =
        (Real.smoothTransition (((m : ℝ) + 1) * (s - u x)) -
          Real.smoothTransition (((m : ℝ) + 1) * (s₀ - u x))) • η x := by
      simp [sub_smul]
    rw [hsub, eNorm_smul]
    gcongr
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal hψ_le
  have hfin := (TestFunction.memLp_subtype (p := 1) (μ := massMeasure S) η).eLpNorm_lt_top.ne
  have htoReal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hle_lp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ← Lp.norm_toLp (f := fun x : Ω => η x)
      (hf := TestFunction.memLp_subtype (p := 1) η), ← TestFunction.toLp_apply] at htoReal
  refine htoReal.trans_lt ?_
  have hprod_le : (Lψ : ℝ) * ((m : ℝ) + 1) * ‖TestFunction.toLp 1 (massMeasure S) η‖ ≤ K := by
    have h1 : (Lψ : ℝ) ≤ (Lψ : ℝ) + 1 := le_add_of_nonneg_right zero_le_one
    have h2 : ‖TestFunction.toLp 1 (massMeasure S) η‖ ≤
        ‖TestFunction.toLp 1 (massMeasure S) η‖ + 1 := le_add_of_nonneg_right zero_le_one
    have h3 : (Lψ : ℝ) * ((m : ℝ) + 1) ≤ ((Lψ : ℝ) + 1) * ((m : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    exact mul_le_mul h3 h2 (norm_nonneg _) (by positivity)
  calc (Lψ : ℝ) * ((m : ℝ) + 1) * |s - s₀| * ‖TestFunction.toLp 1 (massMeasure S) η‖
      = (Lψ : ℝ) * ((m : ℝ) + 1) * ‖TestFunction.toLp 1 (massMeasure S) η‖ * |s - s₀| := by ring
    _ ≤ K * |s - s₀| := mul_le_mul_of_nonneg_right hprod_le (abs_nonneg _)
    _ < K * (ε / K) := mul_lt_mul_of_pos_left hss₀ hKpos
    _ = ε := mul_div_cancel₀ ε hKpos.ne'

/-- Continuity of the smooth-transition slice approximant `t ↦ -T (dfₘ(t) ∧ φ)` in `t`. -/
theorem continuous_neg_oneFormWedgeCLM_smoothTransition
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T) (hu : ContDiff ℝ ∞ u)
    (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) (m : ℕ) :
    Continuous fun t : ℝ =>
      -T (oneFormWedgeCLM (k := k)
        (contDiff_infty_iff_fderiv.1 (Real.smoothTransition.contDiff.comp
          (contDiff_const.mul (contDiff_const.sub hu)) :
            ContDiff ℝ ∞ fun x => Real.smoothTransition (((m : ℝ) + 1) * (t - u x)))).2 φ) := by
  obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
  let hf (t : ℝ) : ContDiff ℝ ∞ fun x => Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub hu))
  refine ((continuous_apply_smulLeftCLM_smoothTransition hT₁ hu (extDerivCLM φ) m).sub
    (continuous_apply_smulLeftCLM_smoothTransition hT₂ hu φ m)).congr fun t => ?_
  dsimp only [Pi.sub_apply]
  have hL := DFunLike.congr_fun (comp_smulLeftCLM_comp_extDerivCLM T (hf t)) φ
  simp only [comp_apply, sub_apply] at hL
  rw [comp_apply]
  linarith

private theorem abs_apply_smulLeftCLM_smoothTransition_le {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {S : 𝓓(Ω, G) →L[ℝ] ℝ} (hS : HasLocallyFiniteMass S) (hu : ContDiff ℝ ∞ u)
    (η : 𝓓(Ω, G)) (m : ℕ) (t : ℝ) :
    |S (smulLeftCLM
      (Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub hu)) :
        ContDiff ℝ ∞ fun x => Real.smoothTransition (((m : ℝ) + 1) * (t - u x))) η)| ≤
      ‖TestFunction.toLp 1 (massMeasure S) η‖ := by
  let hf : ContDiff ℝ ∞ fun x => Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub hu))
  rw [← extendL1_toLp hS, ← Real.norm_eq_abs]
  refine (norm_extendL1_apply_le _).trans ?_
  rw [TestFunction.toLp_apply, TestFunction.toLp_apply, Lp.norm_toLp, Lp.norm_toLp]
  refine ENNReal.toReal_mono (TestFunction.memLp_subtype (p := 1) η).eLpNorm_lt_top.ne ?_
  rw [eLpNorm_one_eq_lintegral_eNorm
      (TestFunction.memLp_subtype (p := 1) (smulLeftCLM hf η)).aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_eNorm (TestFunction.memLp_subtype (p := 1) η).aestronglyMeasurable]
  refine lintegral_mono fun x => ?_
  rw [smulLeftCLM_apply, eNorm_smul]
  refine mul_le_of_le_one_left bot_le ?_
  rw [← ofReal_norm, Real.norm_eq_abs]
  exact ENNReal.ofReal_le_one.2 (Real.smoothTransition.abs_le_one _)

/-- Interchanging `∫_{a}^{b} dt` with a locally finite-mass functional `S` on the smooth
transition multipliers `g t • ψ((m + 1) (t - u x)) • η x`, proved via the scalar fundamental
theorem of calculus along `s ↦ extendL1 S (toLp ((∫_{a}^{s} g t ψ_m(t, ·) dt) • η))`. -/
private theorem intervalIntegral_mul_apply_smulLeftCLM_smoothTransition {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {S : 𝓓(Ω, G) →L[ℝ] ℝ} (hS : HasLocallyFiniteMass S) (hu : ContDiff ℝ ∞ u)
    {g : ℝ → ℝ} (hg : Continuous g) (η : 𝓓(Ω, G)) (a b : ℝ) (m : ℕ) :
    ∫ t in a..b, g t * S (smulLeftCLM
        (Real.smoothTransition.contDiff.comp
          (contDiff_const.mul (contDiff_const.sub hu)) :
            ContDiff ℝ ∞ fun x => Real.smoothTransition (((m : ℝ) + 1) * (t - u x))) η) =
      extendL1 S ((memLp_intervalIntegral_mul_smoothTransition_smul
        (massMeasure S) hu hg η a b m).toLp _) := by
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  obtain ⟨Lψ, hLip⟩ := exists_lipschitzWith_smoothTransition
  let hf (s : ℝ) : ContDiff ℝ ∞ fun x => Real.smoothTransition (((m : ℝ) + 1) * (s - u x)) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub hu))
  let J (s : ℝ) (x : E) : ℝ :=
    ∫ t in a..s, g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x))
  have hgi (x : E) (s₁ s₂ : ℝ) : IntervalIntegrable
      (fun t => g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x))) volume s₁ s₂ :=
    (hg.mul (Real.smoothTransition.continuous.comp
      (continuous_const.mul (continuous_id.sub continuous_const)))).intervalIntegrable s₁ s₂
  let hmem (s : ℝ) :=
    memLp_intervalIntegral_mul_smoothTransition_smul (massMeasure S) hu hg η a s m
  let q (s : ℝ) : Lp G 1 (massMeasure S) := (hmem s).toLp _
  have hderiv_q (s : ℝ) :
      HasDerivAt q (g s • TestFunction.toLp 1 (massMeasure S) (smulLeftCLM (hf s) η)) s := by
    rw [hasDerivAt_iff_tendsto_slope_zero, Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    let Nη : ℝ := ‖TestFunction.toLp 1 (massMeasure S) η‖
    have hNpos : 0 < Nη + 1 := by positivity
    let ε' : ℝ := ε / (Nη + 1)
    have hε' : 0 < ε' := div_pos hε hNpos
    obtain ⟨δ₁, hδ₁, hgδ₁⟩ := Metric.continuousAt_iff.1 (hg.continuousAt (x := s))
      (ε' / 2) (half_pos hε')
    obtain ⟨δ₂, hδ₂, hδ₂lt⟩ := exists_pos_mul_lt (half_pos hε')
      (|g s| * (Lψ : ℝ) * ((m : ℝ) + 1))
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun h hh0 hhδ => ?_⟩
    have hhne : h ≠ 0 := mem_compl_singleton_iff.1 hh0
    have hhlt1 : |h| < δ₁ := by
      simpa [Real.dist_eq] using hhδ.trans_le (min_le_left _ _)
    have hhlt2 : |h| < δ₂ := by
      simpa [Real.dist_eq] using hhδ.trans_le (min_le_right _ _)
    rw [dist_eq_norm]
    have hq_norm :
        ‖h⁻¹ • (q (s + h) - q s) -
            g s • TestFunction.toLp 1 (massMeasure S) (smulLeftCLM (hf s) η)‖ ≤ ε' * Nη := by
      have hdiff_eq :
          h⁻¹ • (q (s + h) - q s) -
            g s • TestFunction.toLp 1 (massMeasure S) (smulLeftCLM (hf s) η) =
          (((hmem (s + h)).sub (hmem s)).const_smul h⁻¹ |>.sub
            ((TestFunction.memLp_subtype (p := 1) (smulLeftCLM (hf s) η)).const_smul
              (g s))).toLp _ := by
        dsimp only [q]
        rw [TestFunction.toLp_apply, ← MemLp.toLp_sub, ← MemLp.toLp_const_smul,
          ← MemLp.toLp_const_smul, ← MemLp.toLp_sub]
      rw [hdiff_eq, Lp.norm_toLp]
      have hNη_eq : Nη = (eLpNorm (fun x : Ω => η x) 1 (massMeasure S)).toReal := by
        dsimp only [Nη]
        rw [TestFunction.toLp_apply, Lp.norm_toLp]
      rw [hNη_eq, ← ENNReal.toReal_ofReal hε'.le, ← ENNReal.toReal_mul]
      refine ENNReal.toReal_mono
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (TestFunction.memLp_subtype (p := 1) η).eLpNorm_lt_top.ne) ?_
      rw [eLpNorm_one_eq_lintegral_eNorm
        ((((hmem (s + h)).sub (hmem s)).const_smul h⁻¹ |>.sub
          ((TestFunction.memLp_subtype (p := 1) (smulLeftCLM (hf s) η)).const_smul
            (g s))).aestronglyMeasurable),
        eLpNorm_one_eq_lintegral_eNorm
          (TestFunction.memLp_subtype (p := 1) η).aestronglyMeasurable,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun x => ?_
      have hsub_J : J (s + h) x - J s x =
          ∫ t in s..(s + h), g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) :=
        sub_eq_of_eq_add'
          (intervalIntegral.integral_add_adjacent_intervals (hgi x a s) (hgi x s (s + h))).symm
      have hpoint_val :
          h⁻¹ * (J (s + h) x - J s x) -
              g s * Real.smoothTransition (((m : ℝ) + 1) * (s - u x)) =
            h⁻¹ * ∫ t in s..(s + h),
              (g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) -
                g s * Real.smoothTransition (((m : ℝ) + 1) * (s - u x))) := by
        rw [hsub_J, intervalIntegral.integral_sub (hgi x s (s + h))
          intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul,
          add_sub_cancel_left]
        field_simp [hhne]
      have hval_le : |h⁻¹ * (J (s + h) x - J s x) -
          g s * Real.smoothTransition (((m : ℝ) + 1) * (s - u x))| ≤ ε' := by
        rw [hpoint_val, abs_mul, abs_inv]
        have hint_le : ‖∫ t in s..(s + h),
            (g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) -
               g s * Real.smoothTransition (((m : ℝ) + 1) * (s - u x)))‖ ≤
            ε' * |s + h - s| := by
          refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
          have hts : |t - s| ≤ |h| := by
            rw [Set.mem_uIoc] at ht
            rcases ht with ⟨ht1, ht2⟩ | ⟨ht1, ht2⟩
            · rw [abs_of_pos (sub_pos.2 ht1), abs_of_pos (by linarith)]
              linarith
            · rw [abs_of_nonpos (sub_nonpos.2 ht2), abs_of_neg (by linarith)]
              linarith
          have hg_lt : |g t - g s| < ε' / 2 := by
            simpa [Real.dist_eq] using hgδ₁ (hts.trans_lt hhlt1)
          have hψ_le : |Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) -
              Real.smoothTransition (((m : ℝ) + 1) * (s - u x))| ≤
              (Lψ : ℝ) * ((m : ℝ) + 1) * |h| := by
            have hd := hLip.dist_le_mul (((m : ℝ) + 1) * (t - u x)) (((m : ℝ) + 1) * (s - u x))
            simp only [Real.dist_eq] at hd
            refine hd.trans ?_
            rw [show ((m : ℝ) + 1) * (t - u x) - ((m : ℝ) + 1) * (s - u x) =
              ((m : ℝ) + 1) * (t - s) by ring, abs_mul,
              abs_of_pos (by positivity : (0 : ℝ) < (m : ℝ) + 1), ← mul_assoc]
            exact mul_le_mul_of_nonneg_left hts (by positivity)
          rw [Real.norm_eq_abs, show g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) -
              g s * Real.smoothTransition (((m : ℝ) + 1) * (s - u x)) =
            (g t - g s) * Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) +
              g s * (Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) -
                Real.smoothTransition (((m : ℝ) + 1) * (s - u x))) by ring]
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
          have h1 : |g t - g s| * |Real.smoothTransition (((m : ℝ) + 1) * (t - u x))| ≤
              ε' / 2 :=
            (mul_le_of_le_one_right (abs_nonneg _)
              (Real.smoothTransition.abs_le_one _)).trans hg_lt.le
          have h2 : |g s| * |Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) -
              Real.smoothTransition (((m : ℝ) + 1) * (s - u x))| ≤ ε' / 2 := by
            calc |g s| * |Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) -
                    Real.smoothTransition (((m : ℝ) + 1) * (s - u x))|
                ≤ |g s| * ((Lψ : ℝ) * ((m : ℝ) + 1) * |h|) :=
                  mul_le_mul_of_nonneg_left hψ_le (abs_nonneg _)
              _ = |g s| * (Lψ : ℝ) * ((m : ℝ) + 1) * |h| := by ring
              _ ≤ |g s| * (Lψ : ℝ) * ((m : ℝ) + 1) * δ₂ :=
                  mul_le_mul_of_nonneg_left hhlt2.le (by positivity)
              _ ≤ ε' / 2 := hδ₂lt.le
          linarith
        rw [add_sub_cancel_left, Real.norm_eq_abs] at hint_le
        calc |h|⁻¹ * |∫ t in s..(s + h),
                (g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) -
                  g s * Real.smoothTransition (((m : ℝ) + 1) * (s - u x)))|
            ≤ |h|⁻¹ * (ε' * |h|) := mul_le_mul_of_nonneg_left hint_le (by positivity)
          _ = ε' := by field_simp [abs_ne_zero.2 hhne]
      dsimp only [Pi.sub_apply, Pi.smul_apply]
      rw [smulLeftCLM_apply, ← sub_smul, smul_smul, smul_smul, ← sub_smul, eNorm_smul]
      gcongr
      rw [← ofReal_norm, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_ofReal hval_le
    refine hq_norm.trans_lt ?_
    calc ε' * Nη < ε' * (Nη + 1) := mul_lt_mul_of_pos_left (lt_add_one Nη) hε'
      _ = ε := div_mul_cancel₀ ε hNpos.ne'
  have hderiv_S (s : ℝ) :
      HasDerivAt (fun s => extendL1 S (q s)) (g s * S (smulLeftCLM (hf s) η)) s :=
    ((extendL1 S).hasFDerivAt.comp_hasDerivAt s (hderiv_q s)).congr_deriv
      (by simp [map_smul, smul_eq_mul, extendL1_toLp hS])
  have hcont_prod : Continuous fun t : ℝ => g t * S (smulLeftCLM (hf t) η) :=
    hg.mul (continuous_apply_smulLeftCLM_smoothTransition hS hu η m)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv_S s)
    (hcont_prod.intervalIntegrable a b)]
  have hqa : q a = 0 := by
    rw [← norm_eq_zero, Lp.norm_toLp]
    simp
  rw [hqa, map_zero, sub_zero]

/-- Limit of the integrated smooth-transition multiplier against `S` as `m → ∞`: on a test form
`η` whose `u`-values lie strictly inside `(-M, M)`, it converges to `S ((H ∘ u) • η)` where
`H s = ∫_{s}^{M} g t dt`. -/
private theorem tendsto_intervalIntegral_mul_apply_smulLeftCLM_smoothTransition {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {S : 𝓓(Ω, G) →L[ℝ] ℝ} (hS : HasLocallyFiniteMass S) (hu : ContDiff ℝ ∞ u)
    {g H : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {M : ℝ} (hM : 0 < M)
    (hH : ContDiff ℝ ∞ H) (hH_eq : ∀ s, H s = ∫ t in s..M, g t) (η : 𝓓(Ω, G))
    (hη : ∀ x : Ω, (x : E) ∈ tsupport η → |u x| < M) :
    Tendsto (fun m : ℕ => ∫ t in (-M)..M, g t * S (smulLeftCLM
        (Real.smoothTransition.contDiff.comp
          (contDiff_const.mul (contDiff_const.sub hu)) :
            ContDiff ℝ ∞ fun x => Real.smoothTransition (((m : ℝ) + 1) * (t - u x))) η))
      atTop (𝓝 (S (smulLeftCLM (hH.comp hu) η))) := by
  simp_rw [intervalIntegral_mul_apply_smulLeftCLM_smoothTransition hS hu hg.continuous η (-M) M,
    ← extendL1_toLp hS (smulLeftCLM (hH.comp hu) η)]
  refine ((extendL1 S).continuous.tendsto _).comp ?_
  rw [tendsto_iff_eNorm_sub_tendsto_zero]
  have hle_M : -M ≤ M := by linarith
  let I : ℝ := ∫ t in uIoc (-M) M, |g t|
  have hI0 : 0 ≤ I := integral_nonneg fun _ => abs_nonneg _
  have hnorm (m : ℕ) :
      ‖(memLp_intervalIntegral_mul_smoothTransition_smul (massMeasure S) hu hg.continuous η
            (-M) M m).toLp _ -
          TestFunction.toLp 1 (massMeasure S) (smulLeftCLM (hH.comp hu) η)‖ₑ =
        ∫⁻ x : Ω, ‖((∫ t in (-M)..M,
            g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x))) - H (u x)) • η x‖ₑ
          ∂massMeasure S := by
    rw [TestFunction.toLp_apply, ← MemLp.toLp_sub, Lp.eNorm_toLp, eLpNorm_one_eq_lintegral_eNorm
      (((memLp_intervalIntegral_mul_smoothTransition_smul (massMeasure S) hu hg.continuous η
          (-M) M m).sub (TestFunction.memLp_subtype _)).aestronglyMeasurable)]
    refine lintegral_congr fun x => ?_
    simp [sub_smul]
  simp_rw [hnorm]
  rw [← lintegral_zero (μ := massMeasure S)]
  refine tendsto_lintegral_of_dominated_convergence' (fun x => (2 * ENNReal.ofReal I) * ‖η x‖ₑ)
    (fun m => ?_) (fun m => ae_of_all _ fun x => ?_) ?_ (ae_of_all _ fun x => ?_)
  · have hmem_sub := (memLp_intervalIntegral_mul_smoothTransition_smul (massMeasure S) hu
      hg.continuous η (-M) M m).sub (TestFunction.memLp_subtype (smulLeftCLM (hH.comp hu) η))
    exact hmem_sub.aestronglyMeasurable.eNorm.congr (ae_of_all _ fun x => by simp [sub_smul])
  · dsimp only
    by_cases hxts : (x : E) ∈ tsupport η
    · have hux : |u x| < M := hη x hxts
      have hux1 : -M ≤ u x := by linarith [neg_le_of_abs_le hux.le]
      have hux2 : u x ≤ M := (le_abs_self (u x)).trans hux.le
      have hJle :
          |∫ t in (-M)..M, g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x))| ≤ I := by
        have habs := intervalIntegral.norm_integral_le_integral_norm_uIoc
          (f := fun t => g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x)))
          (a := -M) (b := M) (μ := volume)
        simp only [Real.norm_eq_abs] at habs
        refine habs.trans (integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
          (intervalIntegrable_iff.1 (hg.continuous.abs.intervalIntegrable (-M) M))
          (ae_of_all _ fun t => ?_))
        dsimp only
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.smoothTransition.abs_le_one _)
      have hHle : |H (u x)| ≤ I := by
        rw [hH_eq (u x)]
        have habs := intervalIntegral.norm_integral_le_integral_norm_uIoc
          (f := g) (a := u x) (b := M) (μ := volume)
        simp only [Real.norm_eq_abs] at habs
        refine habs.trans (setIntegral_mono_set
          (intervalIntegrable_iff.1 (hg.continuous.abs.intervalIntegrable (-M) M))
          (ae_of_all _ fun _ => abs_nonneg _) ?_)
        rw [uIoc_of_le hux2, uIoc_of_le hle_M]
        exact Eventually.of_forall (Ioc_subset_Ioc_left hux1)
      rw [eNorm_smul]
      gcongr
      rw [← ofReal_norm, Real.norm_eq_abs, two_mul, ← ENNReal.ofReal_add hI0 hI0]
      exact ENNReal.ofReal_le_ofReal ((abs_sub _ _).trans (add_le_add hJle hHle))
    · have hη0 : η x = 0 := image_eq_zero_of_notMem_tsupport hxts
      simp [hη0]
  · have hc : 2 * ENNReal.ofReal I ≠ ⊤ := ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
    rw [lintegral_const_mul' _ _ hc, ← TestFunction.enorm_toLp_one]
    exact ENNReal.mul_ne_top hc eNorm_ne_top
  · by_cases hxts : (x : E) ∈ tsupport η
    · have hux : |u x| < M := hη x hxts
      have hux1 : -M ≤ u x := by linarith [neg_le_of_abs_le hux.le]
      have hux2 : u x ≤ M := (le_abs_self (u x)).trans hux.le
      have hJlim : Tendsto (fun m : ℕ =>
          ∫ t in (-M)..M, g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x)))
          atTop (𝓝 (H (u x))) := by
        have hind_eq : ∫ t in (-M)..M, (Ioi (u x)).indicator g t = H (u x) := by
          have hint_ind : IntervalIntegrable ((Ioi (u x)).indicator g) volume (-M) M := by
            rw [intervalIntegrable_iff]
            exact (hg.continuous.integrableOn_Icc.mono_set Ioc_subset_Icc_self).indicator
              measurableSet_Ioi
          have h1 : IntervalIntegrable ((Ioi (u x)).indicator g) volume (-M) (u x) :=
            hint_ind.mono_set (by
              rw [uIcc_of_le hux1, uIcc_of_le hle_M]
              exact Icc_subset_Icc_right hux2)
          have h2 : IntervalIntegrable ((Ioi (u x)).indicator g) volume (u x) M :=
            hint_ind.mono_set (by
              rw [uIcc_of_le hux2, uIcc_of_le hle_M]
              exact Icc_subset_Icc_left hux1)
          rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
          have hz : ∫ t in (-M)..(u x), (Ioi (u x)).indicator g t = 0 := by
            rw [intervalIntegral.integral_of_le hux1]
            refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
            have hnot : t ∉ Ioi (u x) := not_lt.2 ht.2
            simp [hnot]
          have heqH : ∫ t in (u x)..M, (Ioi (u x)).indicator g t = H (u x) := by
            rw [hH_eq (u x)]
            simp only [intervalIntegral.integral_of_le hux2]
            refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
            exact indicator_of_mem ht.1 g
          rw [hz, zero_add, heqH]
        rw [← hind_eq]
        refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
          (fun t => |g t|)
          (.of_forall fun m => (hg.continuous.mul
            (Real.smoothTransition.continuous.comp
              (continuous_const.mul (continuous_id.sub continuous_const)))).aestronglyMeasurable)
          (.of_forall fun m => ae_of_all _ fun t _ => by
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_of_le_one_right (abs_nonneg _) (Real.smoothTransition.abs_le_one _))
          (hg.continuous.abs.intervalIntegrable (-M) M) ?_
        have hne : ∀ᵐ t ∂volume, t ∈ uIoc (-M) M → t ≠ u x := by
          filter_upwards [compl_mem_ae_iff.2 (by simp : volume ({u x} : Set ℝ) = 0)] with t ht _
          exact ht
        filter_upwards [hne] with t ht htI
        rcases lt_trichotomy (u x) t with hlt | heq | hgt
        · rw [indicator_of_mem hlt]
          refine tendsto_const_nhds.congr' ?_
          have htop : Tendsto (fun m : ℕ => ((m : ℝ) + 1) * (t - u x)) atTop atTop :=
            (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const
              (sub_pos.2 hlt)
          filter_upwards [htop.eventually_ge_atTop 1] with m hm
          rw [Real.smoothTransition.one_of_one_le hm, mul_one]
        · exact (ht htI heq.symm).elim
        · have hnot : t ∉ Ioi (u x) := not_lt.2 hgt.le
          rw [indicator_of_notMem hnot]
          refine tendsto_const_nhds.congr' (.of_forall fun m => ?_)
          dsimp only
          have hle0 : ((m : ℝ) + 1) * (t - u x) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.2 hgt.le)
          rw [Real.smoothTransition.zero_of_nonpos hle0, mul_zero]
      have h := ENNReal.Tendsto.mul_const (hJlim.sub_const (H (u x))).eNorm
        (Or.inr eNorm_ne_top) (b := ‖η x‖ₑ)
      simpa [sub_self, eNorm_smul] using h
    · have hη0 : η x = 0 := image_eq_zero_of_notMem_tsupport hxts
      simp [hη0]

/-- **The coarea pairing identity for smooth functions.** For a locally normal `(k + 1)`-current
`T`, smooth `u : E → ℝ`, smooth `g : ℝ → ℝ`, and test `k`-form `φ`,
`∫ g(t) ⟨T, u, t⟩(φ) dt = T((g ∘ u) • (du ∧ φ))`. -/
theorem integral_mul_slice_apply {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : ContDiff ℝ ∞ u) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    ∫ t, g t * slice T u t φ =
      T (smulLeftCLM (hg.comp hu) (oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 hu).2 φ)) := by
  obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
  obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_closedBall (c := (0 : ℝ)).1
    (φ.hasCompactSupport.image_of_continuousOn
      (hu.continuous.continuousOn.mono φ.tsupport_subset)).isBounded
  let M : ℝ := max R 0 + 1
  have hM : 0 < M := by positivity
  have hle_M : -M ≤ M := by linarith
  have hφ_lt : ∀ x : Ω, (x : E) ∈ tsupport φ → |u x| < M := fun x hx => by
    have hxR : |u x| ≤ R := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hR ⟨x, hx, rfl⟩
    exact (hxR.trans (le_max_left _ _)).trans_lt (lt_add_one _)
  have hdφ_lt : ∀ x : Ω, (x : E) ∈ tsupport (extDerivCLM φ) → |u x| < M :=
    fun x hx => hφ_lt x (tsupport_extDerivCLM_subset φ hx)
  have hout : ∀ t ∉ Ioc (-M) M, g t * slice T u t φ = 0 := fun t ht => by
    rw [slice_apply_eq_zero_of_notMem_Ioc hT hφ_lt ht, mul_zero]
  have hint_eq : ∫ t, g t * slice T u t φ = ∫ t in (-M)..M, g t * slice T u t φ := by
    rw [intervalIntegral.integral_of_le hle_M,
      setIntegral_eq_integral_of_forall_compl_eq_zero hout]
  rw [hint_eq]
  let H : ℝ → ℝ := fun s => ∫ t in s..M, g t
  have hdH (s : ℝ) : HasDerivAt H (-g s) s := by
    have heq : H = fun s => -(∫ t in M..s, g t) :=
      funext fun s => by rw [intervalIntegral.integral_symm, neg_neg]
    rw [heq]
    exact (intervalIntegral.integral_hasDerivAt_right
      (hg.continuous.intervalIntegrable M s)
      (hg.continuous.stronglyMeasurableAtFilter volume (𝓝 s))
      hg.continuous.continuousAt).neg
  have hH : ContDiff ℝ ∞ H :=
    contDiff_infty_iff_deriv.2 ⟨fun s => (hdH s).differentiableAt,
      by rw [funext fun s => (hdH s).deriv]; exact hg.neg⟩
  let hf (m : ℕ) (t : ℝ) : ContDiff ℝ ∞ fun x =>
      Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub hu))
  have hlim_R :=
    (tendsto_intervalIntegral_mul_apply_smulLeftCLM_smoothTransition hT₁ hu hg hM hH
      (fun _ => rfl) (extDerivCLM φ) hdφ_lt).sub
    (tendsto_intervalIntegral_mul_apply_smulLeftCLM_smoothTransition hT₂ hu hg hM hH
      (fun _ => rfl) φ hφ_lt)
  let C : ℝ := ‖TestFunction.toLp 1 (massMeasure T) (extDerivCLM φ)‖ +
    ‖TestFunction.toLp 1 (massMeasure (T ∘L extDerivCLM)) φ‖
  have hlim_L : Tendsto (fun m : ℕ =>
      (∫ t in (-M)..M, g t * T (smulLeftCLM (hf m t) (extDerivCLM φ))) -
        ∫ t in (-M)..M, g t * (T ∘L extDerivCLM) (smulLeftCLM (hf m t) φ))
      atTop (𝓝 (∫ t in (-M)..M, g t * slice T u t φ)) := by
    have hsub_eq (m : ℕ) :
        (∫ t in (-M)..M, g t * T (smulLeftCLM (hf m t) (extDerivCLM φ))) -
          (∫ t in (-M)..M, g t * (T ∘L extDerivCLM) (smulLeftCLM (hf m t) φ)) =
        ∫ t in (-M)..M, g t * (T (smulLeftCLM (hf m t) (extDerivCLM φ)) -
          (T ∘L extDerivCLM) (smulLeftCLM (hf m t) φ)) := by
      have hi1 : IntervalIntegrable
          (fun t => g t * T (smulLeftCLM (hf m t) (extDerivCLM φ))) volume (-M) M :=
        (hg.continuous.mul
          (continuous_apply_smulLeftCLM_smoothTransition hT₁ hu (extDerivCLM φ)
            m)).intervalIntegrable (-M) M
      have hi2 : IntervalIntegrable
          (fun t => g t * (T ∘L extDerivCLM) (smulLeftCLM (hf m t) φ)) volume (-M) M :=
        (hg.continuous.mul
          (continuous_apply_smulLeftCLM_smoothTransition hT₂ hu φ m)).intervalIntegrable (-M) M
      rw [← intervalIntegral.integral_sub hi1 hi2]
      simp_rw [mul_sub]
    simp_rw [hsub_eq]
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun t => |g t| * C)
      (.of_forall fun m => (hg.continuous.mul
        ((continuous_apply_smulLeftCLM_smoothTransition hT₁ hu (extDerivCLM φ) m).sub
          (continuous_apply_smulLeftCLM_smoothTransition hT₂ hu φ m))).aestronglyMeasurable)
      (.of_forall fun m => ae_of_all _ fun t _ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left
          ((abs_sub _ _).trans
            (add_le_add (abs_apply_smulLeftCLM_smoothTransition_le hT₁ hu (extDerivCLM φ) m t)
              (abs_apply_smulLeftCLM_smoothTransition_le hT₂ hu φ m t)))
          (abs_nonneg _))
      ((hg.continuous.abs.intervalIntegrable (-M) M).mul_const C)
      (ae_of_all _ fun t _ => ?_)
    refine tendsto_const_nhds.mul ?_
    refine (tendsto_neg_oneFormWedgeCLM_slice_apply hT hu t φ).congr fun m => ?_
    have hL := DFunLike.congr_fun (comp_smulLeftCLM_comp_extDerivCLM T (hf m t)) φ
    simp only [comp_apply, sub_apply] at hL
    rw [comp_apply]
    linarith
  have heq_val := tendsto_nhds_unique hlim_L hlim_R
  rw [heq_val]
  have hLeib := DFunLike.congr_fun (comp_smulLeftCLM_comp_extDerivCLM T (hH.comp hu)) φ
  simp only [comp_apply, sub_apply] at hLeib
  have hsub_H :
      T (smulLeftCLM (hH.comp hu) (extDerivCLM φ)) -
        (T ∘L extDerivCLM) (smulLeftCLM (hH.comp hu) φ) =
      -T (oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 (hH.comp hu)).2 φ) := by
    rw [comp_apply]
    linarith
  rw [hsub_H]
  have hwedge :
      oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 (hH.comp hu)).2 φ =
        -smulLeftCLM (hg.comp hu) (oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 hu).2 φ) := by
    ext x
    have hfd : fderiv ℝ (H ∘ u) x = (-g (u x)) • fderiv ℝ u x :=
      ((hdH (u x)).comp_hasFDerivAt x
        ((hu.differentiable (by simp)) x).hasFDerivAt).fderiv
    have hsmul : ((-g (u x)) • fderiv ℝ u x).smulRight (φ x) =
        (-g (u x)) • (fderiv ℝ u x).smulRight (φ x) := by
      ext y
      simp [smul_smul]
    rw [oneFormWedgeCLM_apply, hfd, hsmul, ContinuousAlternatingMap.alternatizeUncurryFin_smul]
    simp [neg_smul]
  rw [hwedge, map_neg, neg_neg]

/-- **Integrating all slices recovers contraction with `du`.** For a locally normal
`(k + 1)`-current `T` and smooth `u : E → ℝ`, `∫ ⟨T, u, t⟩(φ) dt = T(du ∧ φ)`. -/
theorem integral_slice_apply {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : ContDiff ℝ ∞ u) (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    ∫ t, slice T u t φ = T (oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 hu).2 φ) := by
  have h := integral_mul_slice_apply hT hu (contDiff_const (c := (1 : ℝ))) φ
  simpa [show smulLeftCLM ((contDiff_const (c := (1 : ℝ))).comp hu)
      (oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 hu).2 φ) =
      oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 hu).2 φ by ext x; simp] using h

end Distribution
