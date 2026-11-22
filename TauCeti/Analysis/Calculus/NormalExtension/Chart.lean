/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.PullbackEnd
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem
public import TauCeti.Analysis.Calculus.NormalExtension.Basic
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Charts given by a normal extension

A normal extension `(x, w) ↦ γ x + A x w` of `TauCeti.normalExtension` inverts near `(x₀, 0)` as
soon as its doubled frame `(v, w) ↦ Dγ x₀ v + A x₀ w` is invertible. This file packages the
resulting chart as an `OpenPartialHomeomorph` whose underlying map is the normal extension, and
gives the facts that hold for every such chart, whatever the frame `A`.

Such a chart is affine in the normal variable: `e (x, w) - e (x, 0) = A x w`, and
`De (x, w) - De (x, 0)` is `(v, w') ↦ (DA x v) w`. So for `C¹` data, a `C¹` inverse and a field
`J` that is Lipschitz near the base point, the pulled-back field `e^* J` is Lipschitz in the
normal variable near `(x₀, 0)`: `‖e^* J (x, w) - e^* J (x, 0)‖ ≤ C ‖w‖`. No derivative of `e^* J`
along the zero section is needed.

## Main declarations

* `TauCeti.exists_openPartialHomeomorph_normalExtension`: the inverse function theorem for a
  `C^ℓ` normal extension whose derivative at `(x₀, 0)` is a continuous linear equivalence, shared
  with the charts adapted to pseudoholomorphic discs.
* `TauCeti.exists_normalExtensionChart`: the inverse function theorem for any normal extension
  whose doubled frame is invertible, with a `C^ℓ` inverse on the whole target.
* `OpenPartialHomeomorph.symm_apply_of_coe_eq_normalExtension`: a normal-extension chart inverts
  the parametrization on the zero section.
* `OpenPartialHomeomorph.exists_norm_pullbackEnd_sub_pullbackEnd_le_of_coe_eq_normalExtension`:
  transverse Lipschitz control of the structure pulled back along any normal-extension chart.
-/

public noncomputable section

open Set Filter
open scoped Topology ContDiff NNReal

namespace TauCeti

section Chart

variable {𝕜 V E W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {γ : V → W} {A : V → E →L[𝕜] W}

/-- **Charts from a normal extension.** Let the normal extension `Φ (x, y) = γ x + A x y` be
`C^ℓ` on `U × E` for an open `U`, with `1 ≤ ℓ`, and let its derivative at `(x₀, 0)` be a
continuous linear equivalence, where `x₀ ∈ U` and `γ x₀` lies in an open `Ω`. Then `Φ`
restricts to a partial homeomorphism around `(x₀, 0)` with source in `U × E`, target in `Ω`,
and which is `C^ℓ` with `C^ℓ` inverse. -/
theorem exists_openPartialHomeomorph_normalExtension [CompleteSpace V] [CompleteSpace E]
    {U : Set V} {Ω : Set W} {x₀ : V} {ℓ : ℕ∞ω} (hU : IsOpen U) (hΩ : IsOpen Ω) (hx₀ : x₀ ∈ U)
    (hγx₀ : γ x₀ ∈ Ω) (hℓ : 1 ≤ ℓ) (hΦ : ContDiffOn 𝕜 ℓ (normalExtension γ A) (U ×ˢ univ))
    {L : (V × E) ≃L[𝕜] W}
    (hL : (L : (V × E) →L[𝕜] W) = fderiv 𝕜 (normalExtension γ A) (x₀, 0)) :
    ∃ e : OpenPartialHomeomorph (V × E) W, ⇑e = normalExtension γ A ∧
      (x₀, 0) ∈ e.source ∧ e.source ⊆ U ×ˢ univ ∧ e.target ⊆ Ω ∧
      ContDiffOn 𝕜 ℓ e e.source ∧ ContDiffOn 𝕜 ℓ e.symm e.target := by
  have hs : IsOpen ((U ×ˢ univ) ∩ normalExtension γ A ⁻¹' Ω) :=
    hΦ.continuousOn.isOpen_inter_preimage (hU.prod isOpen_univ) hΩ
  have hmem : (x₀, (0 : E)) ∈ (U ×ˢ univ) ∩ normalExtension γ A ⁻¹' Ω :=
    ⟨⟨hx₀, mem_univ _⟩, by rwa [mem_preimage, normalExtension_zero]⟩
  obtain ⟨e, he, hx, hsub, hsymm⟩ :=
    TauCeti.ContDiffOn.exists_openPartialHomeomorph (hΦ.mono inter_subset_left) hs hmem hℓ hL
  refine ⟨e, he, hx, fun p hp ↦ (hsub hp).1, fun y hy ↦ ?_, ?_, hsymm⟩
  · rw [← e.right_inv hy, he]
    exact (hsub (e.map_target hy)).2
  · rw [he]
    exact hΦ.mono fun p hp ↦ (hsub hp).1

/-- **Normal-extension charts exist.** Let `γ` and the frame `A` be `C^ℓ` on an open `U`, with
`1 ≤ ℓ`, and let `γ` map `U` into an open `Ω`. If at `x₀ ∈ U` the doubled frame
`(v, w) ↦ Dγ v + A x₀ w` is invertible, the normal extension restricts to a partial
homeomorphism around `(x₀, 0)` with source in `U × E`, target in `Ω`, and which is `C^ℓ` with
`C^ℓ` inverse. -/
theorem exists_normalExtensionChart [CompleteSpace V] [CompleteSpace E] {U : Set V}
    {Ω : Set W} {x₀ : V} {ℓ : ℕ∞ω} (hU : IsOpen U) (hΩ : IsOpen Ω) (hx₀ : x₀ ∈ U)
    (hℓ : 1 ≤ ℓ) (hγ : ContDiffOn 𝕜 ℓ γ U) (hA : ContDiffOn 𝕜 ℓ A U) (hγΩ : MapsTo γ U Ω)
    (hframe : ((fderiv 𝕜 γ x₀).coprod (A x₀)).IsInvertible) :
    ∃ e : OpenPartialHomeomorph (V × E) W, ⇑e = normalExtension γ A ∧
      (x₀, 0) ∈ e.source ∧ e.source ⊆ U ×ˢ univ ∧ e.target ⊆ Ω ∧
      ContDiffOn 𝕜 ℓ e e.source ∧ ContDiffOn 𝕜 ℓ e.symm e.target := by
  have hγ₁ : ContDiffAt 𝕜 1 γ x₀ := (hγ.contDiffAt (hU.mem_nhds hx₀)).of_le hℓ
  have hAc : ContinuousAt A x₀ := hA.continuousOn.continuousAt (hU.mem_nhds hx₀)
  obtain ⟨D, hD⟩ := hframe
  rw [← fderiv_normalExtension_zero (hγ₁.differentiableAt one_ne_zero) hAc] at hD
  exact exists_openPartialHomeomorph_normalExtension hU hΩ hx₀ (hγΩ hx₀) hℓ
    (contDiffOn_normalExtension hγ hA) hD

end Chart

end TauCeti

namespace OpenPartialHomeomorph

/-- A normal-extension chart inverts the parametrization on the zero section of its source. -/
theorem symm_apply_of_coe_eq_normalExtension {𝕜 V E W : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup V] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup W]
    [NormedSpace 𝕜 W] {γ : V → W} {A : V → E →L[𝕜] W} {e : OpenPartialHomeomorph (V × E) W}
    (he : ⇑e = TauCeti.normalExtension γ A) {x : V} (hx : (x, 0) ∈ e.source) :
    e.symm (γ x) = (x, 0) := by
  rw [← TauCeti.normalExtension_zero γ A x, ← he, e.left_inv hx]

section Lipschitz

variable {𝕜 V E W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- The pointwise estimate behind
`exists_norm_pullbackEnd_sub_pullbackEnd_le_of_coe_eq_normalExtension`: at `(x, w)` and `(x, 0)`,
given bounds on the derivatives of the chart and its inverse, on `J` and on the frame, and a
Lipschitz constant of `J` on a set containing both images. -/
private theorem norm_pullbackEnd_sub_pullbackEnd_le {γ : V → W} {A : V → E →L[𝕜] W}
    {J : W → W →L[𝕜] W} {e : OpenPartialHomeomorph (V × E) W} {K : ℝ≥0} {t : Set W}
    {BA BD BM BG BJ : ℝ} (he : ⇑e = TauCeti.normalExtension γ A) (hK : LipschitzOnWith K J t)
    {x : V} {w : E} (hps : (x, w) ∈ e.source) (hqs : (x, 0) ∈ e.source)
    (hγ : DifferentiableAt 𝕜 γ x) (hA : DifferentiableAt 𝕜 A x)
    (hpes : DifferentiableAt 𝕜 e.symm (e (x, w))) (hqes : DifferentiableAt 𝕜 e.symm (e (x, 0)))
    (hpt : e (x, w) ∈ t) (hqt : e (x, 0) ∈ t) (hBA : ‖A x‖ ≤ BA) (hBD : ‖fderiv 𝕜 A x‖ ≤ BD)
    (hBM : ‖fderiv 𝕜 (TauCeti.normalExtension γ A) (x, w)‖ ≤ BM)
    (hpG : ‖fderiv 𝕜 e.symm (e (x, w))‖ ≤ BG) (hqG : ‖fderiv 𝕜 e.symm (e (x, 0))‖ ≤ BG)
    (hpJ : ‖J (e (x, w))‖ ≤ BJ) (hBJ : ‖J (e (x, 0))‖ ≤ BJ) :
    ‖e.pullbackEnd J (x, w) - e.pullbackEnd J (x, 0)‖ ≤
      (BG * BD * BG * BJ * BM + BG * (K * BA) * BM + BG * BJ * BD) * ‖w‖ := by
  have hd {y : E} : DifferentiableAt 𝕜 e (x, y) := by
    rw [he]
    exact (TauCeti.hasFDerivAt_normalExtension hγ.hasFDerivAt hA.hasFDerivAt).differentiableAt
  -- The chart moves by `A x w` in the normal direction, and its derivative by `(DA ·) w`.
  have hM : ‖fderiv 𝕜 e (x, w) - fderiv 𝕜 e (x, 0)‖ ≤ BD * ‖w‖ := by
    rw [he]
    exact (TauCeti.norm_fderiv_normalExtension_sub_le hγ hA).trans (by gcongr)
  have hJ : ‖J (e (x, w)) - J (e (x, 0))‖ ≤ K * BA * ‖w‖ := by
    calc ‖J (e (x, w)) - J (e (x, 0))‖ ≤ K * ‖e (x, w) - e (x, 0)‖ := hK.norm_sub_le hpt hqt
      _ ≤ K * (BA * ‖w‖) := by
          rw [he]
          simp only [TauCeti.normalExtension_apply, add_sub_add_left_eq_sub, map_zero, sub_zero]
          gcongr
          exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
      _ = K * BA * ‖w‖ := by ring
  have hMp : ‖fderiv 𝕜 e (x, w)‖ ≤ BM := by rwa [he]
  have hBG : 0 ≤ BG := (norm_nonneg _).trans hpG
  have hBD' : 0 ≤ BD := (ContinuousLinearMap.opNorm_nonneg _).trans hBD
  have hBJ' : 0 ≤ BJ := (norm_nonneg _).trans hBJ
  have hBA' : 0 ≤ BA := (ContinuousLinearMap.opNorm_nonneg _).trans hBA
  rw [pullbackEnd_def, pullbackEnd_def]
  calc _ ≤ _ := ContinuousLinearMap.norm_comp_comp_sub_comp_comp_le (K := J (e (x, w)))
        (K' := J (e (x, 0)))
        (e.fderiv_symm_comp_fderiv_of_mem_source hps hd hpes)
        (e.fderiv_comp_fderiv_symm_of_mem_source hqs hd hqes)
    _ ≤ BG * (BD * ‖w‖) * BG * BJ * BM + BG * (K * BA * ‖w‖) * BM + BG * BJ * (BD * ‖w‖) := by
        gcongr
    _ = (BG * BD * BG * BJ * BM + BG * (K * BA) * BM + BG * BJ * BD) * ‖w‖ := by ring

/-- Near `(x₀, 0)`, the hypotheses of `norm_pullbackEnd_sub_pullbackEnd_le` hold with bounds
given by the values at `(x₀, 0)` plus one. -/
private theorem eventually_normalExtension_chart_bounds {γ : V → W} {A : V → E →L[𝕜] W}
    {J : W → W →L[𝕜] W} {e : OpenPartialHomeomorph (V × E) W} {x₀ : V} {K : ℝ≥0} {t : Set W}
    (he : ⇑e = TauCeti.normalExtension γ A) (hx₀ : (x₀, 0) ∈ e.source)
    (hγ : ContDiffAt 𝕜 1 γ x₀) (hA : ContDiffAt 𝕜 1 A x₀) (ht : t ∈ 𝓝 (γ x₀))
    (hJ : LipschitzOnWith K J t) (hes : ContDiffAt 𝕜 1 e.symm (γ x₀)) :
    ∀ᶠ q in 𝓝 (x₀, (0 : E)), q ∈ e.source ∧ (DifferentiableAt 𝕜 γ q.1 ∧
      DifferentiableAt 𝕜 A q.1) ∧ DifferentiableAt 𝕜 e.symm (e q) ∧ e q ∈ t ∧
      ‖A q.1‖ ≤ ‖A x₀‖ + 1 ∧ ‖fderiv 𝕜 A q.1‖ ≤ ‖fderiv 𝕜 A x₀‖ + 1 ∧
      ‖fderiv 𝕜 (TauCeti.normalExtension γ A) q‖ ≤
        ‖fderiv 𝕜 (TauCeti.normalExtension γ A) (x₀, 0)‖ + 1 ∧
      ‖fderiv 𝕜 e.symm (e q)‖ ≤ ‖fderiv 𝕜 e.symm (γ x₀)‖ + 1 ∧
      ‖J (e q)‖ ≤ ‖J (γ x₀)‖ + 1 := by
  have hep₀ : e (x₀, 0) = γ x₀ := by rw [he, TauCeti.normalExtension_zero]
  have hec : ContinuousAt e (x₀, 0) := e.continuousAt hx₀
  have hb {f : V × E → ℝ} {c : ℝ} (hf : Tendsto f (𝓝 (x₀, 0)) (𝓝 c)) :
      ∀ᶠ q in 𝓝 (x₀, (0 : E)), f q ≤ c + 1 :=
    hf.eventually (eventually_le_nhds (lt_add_one _))
  have hfst : Tendsto (Prod.fst : V × E → V) (𝓝 (x₀, 0)) (𝓝 x₀) := continuousAt_fst
  have hdiff : ∀ᶠ x in 𝓝 x₀, DifferentiableAt 𝕜 γ x ∧ DifferentiableAt 𝕜 A x :=
    ((hγ.eventually (by simp)).and (hA.eventually (by simp))).mono fun x hx ↦
      ⟨hx.1.differentiableAt one_ne_zero, hx.2.differentiableAt one_ne_zero⟩
  have hsymm : ∀ᶠ y in 𝓝 (e (x₀, 0)), DifferentiableAt 𝕜 e.symm y := by
    rw [hep₀]
    exact (hes.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt one_ne_zero
  have hG : Tendsto (fun q ↦ ‖fderiv 𝕜 e.symm (e q)‖) (𝓝 (x₀, 0))
      (𝓝 ‖fderiv 𝕜 e.symm (γ x₀)‖) :=
    ((hes.continuousAt_fderiv one_ne_zero).norm.tendsto.comp (hep₀ ▸ hec.tendsto))
  have hJt : Tendsto (fun q ↦ ‖J (e q)‖) (𝓝 (x₀, 0)) (𝓝 ‖J (γ x₀)‖) :=
    ((hJ.continuousOn.continuousAt ht).norm.tendsto.comp (hep₀ ▸ hec.tendsto))
  exact (e.open_source.eventually_mem hx₀).and <| (hfst.eventually hdiff).and <|
    (hec.eventually hsymm).and <| (hec.eventually_mem (by rwa [hep₀])).and <|
    (hb (hA.continuousAt.norm.tendsto.comp hfst)).and <|
    (hb ((continuous_norm.continuousAt.comp
      (hA.continuousAt_fderiv one_ne_zero)).tendsto.comp hfst)).and <|
    (hb ((TauCeti.contDiffAt_normalExtension hγ hA).continuousAt_fderiv
      one_ne_zero).norm.tendsto).and <| (hb hG).and (hb hJt)

/-- **Transverse Lipschitz control along a normal-extension chart.** Let `e` be a chart whose
underlying map is the normal extension `(x, w) ↦ γ x + A x w`, with `γ` and `A` of class `C¹`
at `x₀` and a `C¹` inverse at `γ x₀`, and let `J` be Lipschitz on a neighbourhood of `γ x₀`.
Then the pulled-back field `e^* J` is Lipschitz in the normal variable near `(x₀, 0)`:
`‖e^* J (x, w) - e^* J (x, 0)‖ ≤ C ‖w‖`. No regularity of `e^* J` in `x` is claimed. -/
theorem exists_norm_pullbackEnd_sub_pullbackEnd_le_of_coe_eq_normalExtension
    {γ : V → W} {A : V → E →L[𝕜] W} {J : W → W →L[𝕜] W} {e : OpenPartialHomeomorph (V × E) W}
    {x₀ : V} {K : ℝ≥0} {t : Set W} (he : ⇑e = TauCeti.normalExtension γ A)
    (hx₀ : (x₀, 0) ∈ e.source) (hγ : ContDiffAt 𝕜 1 γ x₀) (hA : ContDiffAt 𝕜 1 A x₀)
    (ht : t ∈ 𝓝 (γ x₀)) (hJ : LipschitzOnWith K J t) (hes : ContDiffAt 𝕜 1 e.symm (γ x₀)) :
    ∃ C, ∀ᶠ p in 𝓝 (x₀, (0 : E)),
      ‖e.pullbackEnd J p - e.pullbackEnd J (p.1, 0)‖ ≤ C * ‖p.2‖ := by
  have hgood := eventually_normalExtension_chart_bounds he hx₀ hγ hA ht hJ hes
  -- Each point `(x, w)` near `(x₀, 0)` is compared with its foot `(x, 0)`, also near `(x₀, 0)`.
  have hzero : Tendsto (fun p : V × E ↦ (p.1, (0 : E))) (𝓝 (x₀, 0)) (𝓝 (x₀, 0)) :=
    (continuous_fst.prodMk continuous_const).tendsto' _ _ rfl
  set BA := ‖A x₀‖ + 1
  set BD := ‖fderiv 𝕜 A x₀‖ + 1
  set BM := ‖fderiv 𝕜 (TauCeti.normalExtension γ A) (x₀, 0)‖ + 1
  set BG := ‖fderiv 𝕜 e.symm (γ x₀)‖ + 1
  set BJ := ‖J (γ x₀)‖ + 1
  refine ⟨BG * BD * BG * BJ * BM + BG * (K * BA) * BM + BG * BJ * BD, ?_⟩
  filter_upwards [hgood, hzero.eventually hgood] with p
    ⟨hps, ⟨hpγ, hpA⟩, hpes, hpt, hpA', hpDA, hpM, hpG, hpJ⟩ ⟨hqs, _, hqes, hqt, _, _, _, hqG, hqJ⟩
  exact norm_pullbackEnd_sub_pullbackEnd_le he hJ hps hqs hpγ hpA hpes hqes hpt hqt hpA' hpDA hpM
    hpG hqG hpJ hqJ

end Lipschitz

end OpenPartialHomeomorph
