/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Length
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Smooth dependence of the length of regular curves

The actual extended Riemannian length, read in the real numbers, depends smoothly on any
normed-space parameter of a jointly smooth family whose central velocity is nonzero on the
compact parameter interval. Each finite differentiability order uses a compact tube of regular
curves and the smooth parameter integral of their speeds. No completeness assumption is needed.
-/

public noncomputable section

open Bundle Filter MeasureTheory Set
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {C : P → ℝ → M} {w₀ : P}

section Finiteness

variable [IsManifold I 1 M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- Curves in a jointly differentiable family have finite length near a compact central
parameter segment. No nonvanishing-velocity assumption is required. -/
theorem eventually_pathELength_ne_top_of_contMDiffAt {a b : ℝ}
    (hC : ∀ t ∈ Icc a b,
      ContMDiffAt 𝓘(ℝ, P × ℝ) I 1 (fun z : P × ℝ ↦ C z.1 z.2) (w₀, t)) :
    ∀ᶠ w in 𝓝 w₀, Manifold.pathELength I (C w) a b ≠ ⊤ := by
  by_cases hab : a ≤ b
  swap
  · exact .of_forall fun _ ↦ by
      simp [Manifold.pathELength_eq_lintegral_mfderiv_Icc, Icc_eq_empty hab]
  rw [← uIcc_of_le hab] at hC
  obtain ⟨U, V, hUo, _, hwU, hV, hf⟩ :=
    TauCeti.exists_isOpen_prod_contMDiffOn isCompact_uIcc (by simp) hC
  filter_upwards [hUo.mem_nhds hwU] with w hw
  have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (C w) V :=
    hf.comp (contDiff_prodMk_right w).contMDiff.contMDiffOn fun t ht ↦ ⟨hw, ht⟩
  rw [hcurve.pathELength_eq_ofReal_integral_norm_curveVelocityWithin
    (by simpa only [uIcc_of_le hab] using hV)]
  exact ENNReal.ofReal_ne_top

end Finiteness

variable [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

omit [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
private theorem parameter_curveVelocity_eq_mfderiv {w : P} {t : ℝ}
    (hC : MDifferentiableAt 𝓘(ℝ, P × ℝ) I (fun z : P × ℝ ↦ C z.1 z.2) (w, t)) :
    curveVelocity I (C w) t =
      mfderiv 𝓘(ℝ, P × ℝ) I (fun z : P × ℝ ↦ C z.1 z.2) (w, t) (0, 1) :=
  hC.curveVelocity_comp_mfderiv (g := fun r : ℝ ↦ (w, r))
    ((hasDerivAt_const t w).prodMk (hasDerivAt_id t))

private theorem exists_open_prod_contDiffOn_speed {a b : ℝ} {n : ℕ}
    (hC : ∀ t ∈ uIcc a b,
      ContMDiffAt 𝓘(ℝ, P × ℝ) I (n + 1 : ℕ) (fun z : P × ℝ ↦ C z.1 z.2) (w₀, t))
    (hv : ∀ t ∈ uIcc a b, curveVelocity I (C w₀) t ≠ 0) :
    ∃ U V, IsOpen U ∧ IsOpen V ∧ w₀ ∈ U ∧ uIcc a b ⊆ V ∧
      ContMDiffOn 𝓘(ℝ, P × ℝ) I 1 (fun z : P × ℝ ↦ C z.1 z.2) (U ×ˢ V) ∧
      ContDiffOn ℝ n (fun z : P × ℝ ↦ ‖curveVelocity I (C z.1) z.2‖) (U ×ˢ V) := by
  obtain ⟨U, V, hUo, hVo, hwU, hV, hf⟩ :=
    TauCeti.exists_isOpen_prod_contMDiffOn isCompact_uIcc (by simp) hC
  have hUV : IsOpen (U ×ˢ V) := hUo.prod hVo
  let G : P × ℝ → ℝ := fun z ↦
    inner ℝ (mfderiv 𝓘(ℝ, P × ℝ) I (fun z ↦ C z.1 z.2) z (0, 1))
      (mfderiv 𝓘(ℝ, P × ℝ) I (fun z ↦ C z.1 z.2) z (0, 1))
  have hG : ContDiffOn ℝ n G (U ×ˢ V) :=
    hf.contDiffOn_inner_mfderiv (by exact_mod_cast le_rfl : (n : ℕ∞ω) + 1 ≤ (n + 1 : ℕ))
      hUV (0, 1) (0, 1)
  have hGeq (z : P × ℝ) (hz : z ∈ U ×ˢ V) : G z = ‖curveVelocity I (C z.1) z.2‖ ^ 2 := by
    dsimp only [G]
    rw [← parameter_curveVelocity_eq_mfderiv
      ((hf.contMDiffAt (hUV.mem_nhds hz)).mdifferentiableAt (by simp)),
      real_inner_self_eq_norm_sq]
  let W := (U ×ˢ V) ∩ G ⁻¹' Ioi 0
  have hWo : IsOpen W := hG.continuousOn.isOpen_inter_preimage hUV isOpen_Ioi
  have hsub : {w₀} ×ˢ uIcc a b ⊆ W := by
    rintro ⟨w, t⟩ ⟨hw, ht⟩
    have hww : w = w₀ := hw
    rw [hww]
    refine ⟨⟨hwU, hV ht⟩, ?_⟩
    rw [mem_preimage, mem_Ioi, hGeq (w₀, t) ⟨hwU, hV ht⟩]
    exact pow_pos (norm_pos_iff.2 (hv t ht)) 2
  have hspeed : ContDiffOn ℝ n (fun z : P × ℝ ↦ ‖curveVelocity I (C z.1) z.2‖) W := by
    refine ((hG.mono inter_subset_left).sqrt fun z hz ↦ ne_of_gt hz.2).congr ?_
    intro z hz
    rw [hGeq z hz.1, Real.sqrt_sq (norm_nonneg _)]
  obtain ⟨U₀, V₀, hU₀, hV₀, hw₀, hVV₀, hUV₀⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_uIcc hWo hsub
  exact ⟨U₀, V₀, hU₀, hV₀, hw₀ rfl, hVV₀,
    (hf.of_le (by simp)).mono (hUV₀.trans inter_subset_left), hspeed.mono hUV₀⟩

private theorem toReal_pathELength_eq_integral_speed {a b : ℝ} (hab : a ≤ b)
    {U : Set P} {V : Set ℝ} (hV : IsOpen V) (hI : uIcc a b ⊆ V)
    (hC : ContMDiffOn 𝓘(ℝ, P × ℝ) I 1 (fun z : P × ℝ ↦ C z.1 z.2) (U ×ˢ V))
    {w : P} (hw : w ∈ U) :
    (Manifold.pathELength I (C w) a b).toReal =
      ∫ t in a..b, ‖curveVelocity I (C w) t‖ := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (C w) V :=
    hC.comp (contDiff_prodMk_right w).contMDiff.contMDiffOn fun t ht ↦ ⟨hw, ht⟩
  rw [hcurve.pathELength_eq_ofReal_integral_norm_curveVelocityWithin
      (by simpa only [uIcc_of_le hab] using hI),
    ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hab fun _ _ ↦ norm_nonneg _)]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [curveVelocityWithin_of_mem_nhds (hV.mem_nhds (hI ht))]

/-- The length of a regular jointly smooth family is smooth in its normed-space parameter.
Joint smoothness is only required along the compact central parameter segment. -/
theorem contDiffAt_toReal_pathELength_of_curveVelocity_ne_zero {a b : ℝ}
    (hC : ∀ t ∈ Icc a b,
      ContMDiffAt 𝓘(ℝ, P × ℝ) I ∞ (fun z : P × ℝ ↦ C z.1 z.2) (w₀, t))
    (hv : ∀ t ∈ Icc a b, curveVelocity I (C w₀) t ≠ 0) :
    ContDiffAt ℝ ∞ (fun w ↦ (Manifold.pathELength I (C w) a b).toReal) w₀ := by
  by_cases hab : a ≤ b
  swap
  · have hzero (w : P) : Manifold.pathELength I (C w) a b = 0 := by
      simp [Manifold.pathELength_eq_lintegral_mfderiv_Icc, Icc_eq_empty hab]
    simpa only [hzero, ENNReal.toReal_zero] using
      (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : P ↦ (0 : ℝ)) w₀)
  rw [← uIcc_of_le hab] at hC hv
  refine contDiffAt_infty.2 fun n ↦ ?_
  obtain ⟨U, V, hUo, hVo, hwU, hV, hf, hspeed⟩ :=
    exists_open_prod_contDiffOn_speed (n := n) (fun t ht ↦ (hC t ht).of_le (by simp)) hv
  have hint : ContDiffOn ℝ n (fun w ↦ ∫ t in a..b, ‖curveVelocity I (C w) t‖) U :=
    ContDiffOn.parametric_intervalIntegral hUo (hspeed.mono (prod_mono_right hV))
  refine (hint.contDiffAt (hUo.mem_nhds hwU)).congr_of_eventuallyEq ?_
  exact eventually_of_mem (hUo.mem_nhds hwU) fun w hw ↦
    toReal_pathELength_eq_integral_speed hab hVo hV hf hw

end TauCeti.Manifold
