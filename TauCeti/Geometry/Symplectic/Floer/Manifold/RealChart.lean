/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# The energy identity on rectangles in holomorphic coordinates, for a manifold target

A band of a cylindrical end of a punctured sphere is the image of a rectangle
`[α, β] × [γ, δ)` under the real chart of a holomorphic map `f`, such as an end lift, and in the
coordinates of `f` the perturbation datum of such an end is `g(s) G(t) dt`. This file proves the
energy identity over such an image, for a map `u` into a manifold `M` with a nondegenerate
two-form `ω`: the Floer energy is the symplectic area, plus `g(β)` times the integral of `G` along
the image of the side `s = β`, minus `g(α)` times that along the side `s = α`, minus the
integrated curvature.

The proof changes variables to the coordinates of `f`
(`TauCeti.SmoothTwoForm.integral_floerEnergyDensity_image` and its companions), where the
identity is the rectangle identity
`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity`. In these coordinates the
curvature is `g'(s) G(t)` inside the rectangle, by
`TauCeti.SmoothTwoForm.hamiltonianCurvature_continuation`, which makes it integrable.

## Main results

* `TauCeti.SmoothTwoForm.integrableOn_hamiltonianCurvature_image_realChart_Icc_prod_Ico`: the
  curvature is integrable over the image of the rectangle.
* `TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_image_realChart_Icc_prod_Ico`:
  the energy identity over the image of the rectangle.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity for Hamiltonian perturbations on punctured surfaces.
-/

public section

open Set Function MeasureTheory
open scoped Manifold Topology

namespace TauCeti.SmoothTwoForm

open Floer
open TauCeti.Complex (realChart realChart_apply)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

variable {ω : SmoothTwoForm I M} {f : ℂ → ℂ} {P : ℂ → M → ℂ →L[ℝ] ℝ} {Ω : Set (ℝ × ℝ)}
  {α β γ δ : ℝ} {g : ℝ → ℝ} {G : ℝ → M → ℝ}

omit [IsManifold I (⊤ : ℕ∞) M] in
/-- The pullback along the real chart of a `C²` holomorphic map `f` of a datum `P` that is `C¹` on
`Ω`, evaluated on a fixed tangent vector `v`, is `C¹` on the preimage of `Ω`. -/
private theorem contMDiffOn_uncurry_comp_realChart (hf : ContDiff ℂ 2 f)
    (hP : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : (ℝ × ℝ) × M ↦ P (Complex.equivRealProdCLM.symm p.1) p.2) (Ω ×ˢ univ)) (v : ℂ) :
    ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry fun w x ↦ P
      (f (Complex.equivRealProdCLM.symm w)) x (deriv f (Complex.equivRealProdCLM.symm w) * v))
      ((realChart f ⁻¹' Ω) ×ˢ univ) := by
  have hφ : ContDiff ℝ 1 (realChart f) := TauCeti.Complex.contDiff_realChart (hf.of_le one_le_two)
  have h₁ : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : (ℝ × ℝ) × M ↦ P (Complex.equivRealProdCLM.symm (realChart f p.1)) p.2)
      ((realChart f ⁻¹' Ω) ×ˢ univ) :=
    hP.comp ((hφ.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd).contMDiffOn
      fun p hp ↦ ⟨hp.1, mem_univ _⟩
  have h₂ : ContDiff ℝ 1 (fun w : ℝ × ℝ ↦ deriv f (Complex.equivRealProdCLM.symm w) * v) :=
    ((((contDiff_succ_iff_deriv.1 hf).2.2).restrict_scalars ℝ).comp
      Complex.equivRealProdCLM.symm.contDiff).mul contDiff_const
  refine (h₁.clm_apply (h₂.contMDiff.comp contMDiff_fst).contMDiffOn).congr fun ⟨w, x⟩ _ ↦ ?_
  simp only [uncurry_apply_pair, realChart_apply, ContinuousLinearEquiv.symm_apply_apply,
    comp_apply]

/-- In the coordinates of `f`, the curvature of the pulled-back datum along `u ∘ realChart f` is
integrable over the closed rectangle `[α, β] × [γ, δ]`: inside it the pulled-back datum is
`g(s) G(t) dt`, whose curvature is the continuous function `g'(s) G(t)`. -/
private theorem integrableOn_hamiltonianCurvature_comp_realChart_Icc (ω : SmoothTwoForm I M)
    (hf : ContDiff ℂ 2 f) (hfΩ : ∀ z ∈ Icc α β ×ˢ Icc γ δ, realChart f z ∈ Ω)
    {u : ℝ × ℝ → M} (hu : ContinuousOn u Ω) (hg : ContDiff ℝ 1 g)
    (hG : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry G))
    (hPf : ∀ z ∈ Icc α β ×ˢ Icc γ δ, ∀ x v,
      P (f (Complex.equivRealProdCLM.symm z)) x (deriv f (Complex.equivRealProdCLM.symm z) * v) =
        v.im * (g z.1 * G z.2 x)) :
    IntegrableOn (fun w ↦ ω.hamiltonianCurvature
        (fun w x ↦ P (f (Complex.equivRealProdCLM.symm w)) x
          (deriv f (Complex.equivRealProdCLM.symm w) * 1))
        (fun w x ↦ P (f (Complex.equivRealProdCLM.symm w)) x
          (deriv f (Complex.equivRealProdCLM.symm w) * Complex.I)) w (u (realChart f w)))
      (Icc ((α, γ) : ℝ × ℝ) (β, δ)) := by
  have hφ : Continuous (realChart f) :=
    (TauCeti.Complex.contDiff_realChart (n := 1) (hf.of_le one_le_two)).continuous
  -- The open rectangle and the closed one differ by a null set.
  have hae : Ioo α β ×ˢ Ioo γ δ =ᵐ[volume] Icc ((α, γ) : ℝ × ℝ) (β, δ) := by
    rw [Icc_prod_eq, Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc
  have hcont : ContinuousOn (fun w : ℝ × ℝ ↦ deriv g w.1 * G w.2 (u (realChart f w)))
      (Icc ((α, γ) : ℝ × ℝ) (β, δ)) := by
    have hu' : ContinuousOn (fun w ↦ u (realChart f w)) (Icc ((α, γ) : ℝ × ℝ) (β, δ)) :=
      hu.comp hφ.continuousOn fun w hw ↦ hfΩ w (by rwa [Icc_prod_eq] at hw)
    exact ((hg.continuous_deriv le_rfl).comp continuous_fst).continuousOn.mul
      (hG.continuous.comp_continuousOn (continuousOn_snd.prodMk hu'))
  refine (((hcont.integrableOn_compact isCompact_Icc).mono_set fun w hw ↦ by
    rw [Icc_prod_eq]
    exact ⟨Ioo_subset_Icc_self hw.1, Ioo_subset_Icc_self hw.2⟩).congr_fun (fun w hw ↦ ?_)
    (measurableSet_Ioo.prod measurableSet_Ioo)).congr_set_ae hae.symm
  -- Inside the rectangle the pulled-back datum is `g(s) G(t) dt` near `w`.
  have hnhds : Ioo α β ×ˢ Ioo γ δ ∈ 𝓝 w := (isOpen_Ioo.prod isOpen_Ioo).mem_nhds hw
  have hmem {w' : ℝ × ℝ} (hw' : w' ∈ Ioo α β ×ˢ Ioo γ δ) : w' ∈ Icc α β ×ˢ Icc γ δ :=
    ⟨Ioo_subset_Icc_self hw'.1, Ioo_subset_Icc_self hw'.2⟩
  have hs : (fun w x ↦ P (f (Complex.equivRealProdCLM.symm w)) x
      (deriv f (Complex.equivRealProdCLM.symm w) * 1)) =ᶠ[𝓝 w] fun _ _ ↦ 0 :=
    Filter.eventually_of_mem hnhds fun w' hw' ↦ funext fun x ↦ by
      dsimp only
      rw [hPf w' (hmem hw'), Complex.one_im, zero_mul]
  have ht : (fun w x ↦ P (f (Complex.equivRealProdCLM.symm w)) x
      (deriv f (Complex.equivRealProdCLM.symm w) * Complex.I)) =ᶠ[𝓝 w]
        fun w' y ↦ g w'.1 * G w'.2 y :=
    Filter.eventually_of_mem hnhds fun w' hw' ↦ funext fun x ↦ by
      dsimp only
      rw [hPf w' (hmem hw'), Complex.I_im, one_mul]
  have hGt : DifferentiableAt ℝ (fun t ↦ G t (u (realChart f w))) w.2 :=
    ((hG.comp (contMDiff_id.prodMk contMDiff_const)).contDiff.differentiable one_ne_zero) _
  rw [ω.hamiltonianCurvature_congr_of_eventuallyEq hs ht,
    ω.hamiltonianCurvature_continuation (hg.differentiable one_ne_zero _) hGt]

/-- **The curvature is integrable over the image of a rectangle of an end.** Let `f` be a `C²`
holomorphic map whose real chart is injective on the rectangle `[α, β] × [γ, δ)` and maps the
closed rectangle into an open set `Ω`, on which the datum `P` is `C¹`. If in the coordinates of
`f` the datum is `g(s) G(t) dt` on the closed rectangle, for `C¹` functions `g` and `G`, then
along every map `u` continuous on `Ω` the curvature is integrable over the image of the
rectangle. -/
theorem integrableOn_hamiltonianCurvature_image_realChart_Icc_prod_Ico (ω : SmoothTwoForm I M)
    (hf : ContDiff ℂ 2 f) (hinj : InjOn (realChart f) (Icc α β ×ˢ Ico γ δ)) (hΩ : IsOpen Ω)
    (hfΩ : ∀ z ∈ Icc α β ×ˢ Icc γ δ, realChart f z ∈ Ω)
    (hP : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : (ℝ × ℝ) × M ↦ P (Complex.equivRealProdCLM.symm p.1) p.2) (Ω ×ˢ univ))
    {u : ℝ × ℝ → M} (hu : ContinuousOn u Ω) (hg : ContDiff ℝ 1 g)
    (hG : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry G))
    (hPf : ∀ z ∈ Icc α β ×ˢ Icc γ δ, ∀ x v,
      P (f (Complex.equivRealProdCLM.symm z)) x (deriv f (Complex.equivRealProdCLM.symm z) * v) =
        v.im * (g z.1 * G z.2 x)) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      (realChart f '' (Icc α β ×ˢ Ico γ δ)) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set φ := realChart f
  set s : Set (ℝ × ℝ) := Icc α β ×ˢ Ico γ δ
  have hφ : ContDiff ℝ 2 φ := TauCeti.Complex.contDiff_realChart hf
  have hmeas : MeasurableSet s := measurableSet_Icc.prod measurableSet_Ico
  have hsΩ {w : ℝ × ℝ} (hw : w ∈ s) : φ w ∈ Ω := hfΩ w ⟨hw.1, Ico_subset_Icc_self hw.2⟩
  have hPm {w : ℝ × ℝ} (hw : w ∈ s) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
        (fun p : (ℝ × ℝ) × M ↦ P (Complex.equivRealProdCLM.symm p.1) p.2) (φ w, x) :=
    hP.contMDiffAt ((hΩ.prod isOpen_univ).mem_nhds ⟨hsΩ hw, mem_univ x⟩)
  have hdom {w : ℝ × ℝ} (hw : w ∈ s) (x : M) (v : ℂ) :
      DifferentiableAt ℝ (fun z ↦ P (Complex.equivRealProdCLM.symm z) x v) (φ w) :=
    (((hPm hw x).comp (φ w) (contMDiffAt_id.prodMk contMDiffAt_const)).clm_apply
      contMDiffAt_const).contDiffAt.differentiableAt one_ne_zero
  have htgt {w : ℝ × ℝ} (hw : w ∈ s) (x : M) (v : ℂ) :
      MDifferentiableAt I 𝓘(ℝ) (fun y ↦ P (Complex.equivRealProdCLM.symm (φ w)) y v) x :=
    (((hPm hw x).comp x (contMDiffAt_const.prodMk contMDiffAt_id)).clm_apply
      contMDiffAt_const).mdifferentiableAt one_ne_zero
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hmeas
    (fun w _ ↦ (hφ.differentiable (by norm_num) w).hasFDerivAt.hasFDerivWithinAt) hinj]
  refine ((integrableOn_hamiltonianCurvature_comp_realChart_Icc ω hf hfΩ hu hg hG
    hPf).mono_set fun w hw ↦ by
      rw [Icc_prod_eq]
      exact ⟨hw.1, Ico_subset_Icc_self hw.2⟩).congr_fun (fun w hw ↦ ?_) hmeas
  -- The curvature is a two-form, and the pulled-back datum is `P` at `f` on `f' v`.
  have hpb (v : ℝ × ℝ) : perturbationPullback φ (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x Complex.I) v =
        fun w x ↦ P (f (Complex.equivRealProdCLM.symm w)) x
          (deriv f (Complex.equivRealProdCLM.symm w) * Complex.equivRealProdCLM.symm v) := by
    funext w x
    exact perturbationPullback_realChart P (hf.differentiable (by norm_num) _).hasDerivAt v x
  have h := ω.hamiltonianCurvature_perturbationPullback
    (Ks := fun z x ↦ P (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ P (Complex.equivRealProdCLM.symm z) x Complex.I) hφ.contDiffAt
    (hdom hw (u (φ w)) 1)
    (hdom hw (u (φ w)) Complex.I) (htgt hw (u (φ w)) 1) (htgt hw (u (φ w)) Complex.I)
  rw [hpb, hpb, equivRealProdCLM_symm_stdComplexLineReal,
    equivRealProdCLM_symm_stdComplexLineImag] at h
  rw [abs_of_nonneg (TauCeti.Complex.det_fderiv_realChart_nonneg
      (hf.differentiable (by norm_num) _).hasDerivAt), smul_eq_mul, ← h]

variable [FiniteDimensional ℝ E]

/-- The energy identity of
`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_image_realChart_Icc_prod_Ico`
in the coordinates of `f`: for the pulled-back datum, which is `g(s) G(t) dt` on the closed
rectangle `[α, β] × [γ, δ]`. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_comp_realChart_Icc_prod_Ico
    (hω : ω.IsNondegenerate) (hf : ContDiff ℂ 2 f) (hαβ : α ≤ β) (hγδ : γ ≤ δ) (hΩ : IsOpen Ω)
    (hfΩ : ∀ z ∈ Icc α β ×ˢ Icc γ δ, realChart f z ∈ Ω)
    (hP : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : (ℝ × ℝ) × M ↦ P (Complex.equivRealProdCLM.symm p.1) p.2) (Ω ×ˢ univ))
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u Ω) (hg : ContDiff ℝ 1 g)
    (hG : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry G))
    (hPf : ∀ z ∈ Icc α β ×ˢ Icc γ δ, ∀ x v,
      P (f (Complex.equivRealProdCLM.symm z)) x (deriv f (Complex.equivRealProdCLM.symm z) * v) =
        v.im * (g z.1 * G z.2 x)) :
    ∫ w in Icc α β ×ˢ Ico γ δ, ω.floerEnergyDensity
        (fun w x ↦ P (f (Complex.equivRealProdCLM.symm w)) x
          (deriv f (Complex.equivRealProdCLM.symm w) * 1))
        (fun w x ↦ P (f (Complex.equivRealProdCLM.symm w)) x
          (deriv f (Complex.equivRealProdCLM.symm w) * Complex.I)) (u ∘ realChart f) w =
      (∫ w in Icc α β ×ˢ Ico γ δ, (SmoothBundleForm.eval₂ ω ((u ∘ realChart f) w)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ realChart f) w stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ realChart f) w stdComplexLineImag) : ℝ)) +
        (g β * (∫ t in γ..δ, G t (u (realChart f (β, t)))) -
          g α * ∫ t in γ..δ, G t (u (realChart f (α, t)))) -
        ∫ w in Icc α β ×ˢ Ico γ δ, ω.hamiltonianCurvature
          (fun w x ↦ P (f (Complex.equivRealProdCLM.symm w)) x
            (deriv f (Complex.equivRealProdCLM.symm w) * 1))
          (fun w x ↦ P (f (Complex.equivRealProdCLM.symm w)) x
            (deriv f (Complex.equivRealProdCLM.symm w) * Complex.I)) w (u (realChart f w)) := by
  have hφ : ContDiff ℝ 1 (realChart f) := TauCeti.Complex.contDiff_realChart (hf.of_le one_le_two)
  -- The half-open strip and the closed rectangle differ by a null set.
  have hae : Icc α β ×ˢ Ico γ δ =ᵐ[volume] Icc ((α, γ) : ℝ × ℝ) (β, δ) := by
    rw [Icc_prod_eq, Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq .rfl Ico_ae_eq_Icc
  simp only [setIntegral_congr_set hae]
  have hIccU : Icc ((α, γ) : ℝ × ℝ) (β, δ) ⊆ realChart f ⁻¹' Ω := fun z hz ↦ hfΩ z (by
    rw [Icc_prod_eq] at hz
    exact hz)
  have hΩ' : IsOpen (realChart f ⁻¹' Ω) := hΩ.preimage hφ.continuous
  have hu' : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ realChart f) (realChart f ⁻¹' Ω) :=
    hu.comp hφ.contMDiff.contMDiffOn fun _ hw ↦ hw
  have hR := integrableOn_hamiltonianCurvature_comp_realChart_Icc ω hf hfΩ hu.continuousOn hg
    hG hPf
  rw [hω.integral_floerEnergyDensity hΩ' hu' (contMDiffOn_uncurry_comp_realChart hf hP 1)
    (contMDiffOn_uncurry_comp_realChart hf hP Complex.I) (Prod.mk_le_mk.2 ⟨hαβ, hγδ⟩) hIccU
    (hω.integrableOn_floerEnergyDensity hΩ' hu' (contMDiffOn_uncurry_comp_realChart hf hP 1)
      (contMDiffOn_uncurry_comp_realChart hf hP Complex.I) isCompact_Icc hIccU hR) hR]
  -- The `ds` components vanish and the `dt` components are `g(s) G(t)` on the rectangle.
  have hs₀ {t₀ : ℝ} (ht₀ : t₀ ∈ Icc γ δ) :
      ∫ s in α..β, P (f (Complex.equivRealProdCLM.symm (s, t₀))) ((u ∘ realChart f) (s, t₀))
        (deriv f (Complex.equivRealProdCLM.symm (s, t₀)) * 1) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ 0) fun s hs ↦ ?_,
      intervalIntegral.integral_zero]
    rw [uIcc_of_le hαβ] at hs
    rw [hPf (s, t₀) ⟨hs, ht₀⟩, Complex.one_im, zero_mul]
  have ht {s₀ : ℝ} (hs₀ : s₀ ∈ Icc α β) :
      ∫ t in γ..δ, P (f (Complex.equivRealProdCLM.symm (s₀, t)))
          ((u ∘ realChart f) (s₀, t))
          (deriv f (Complex.equivRealProdCLM.symm (s₀, t)) * Complex.I) =
        g s₀ * ∫ t in γ..δ, G t (u (realChart f (s₀, t))) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le hγδ] at ht
    rw [hPf (s₀, t) ⟨hs₀, ht⟩, Complex.I_im, one_mul, comp_apply]
  rw [hs₀ ⟨hγδ, le_rfl⟩, hs₀ ⟨le_rfl, hγδ⟩, ht ⟨le_rfl, hαβ⟩, ht ⟨hαβ, le_rfl⟩]
  simp only [comp_apply]
  ring

/-- **The energy identity on the image of a rectangle of an end, for a manifold target.** Let `f`
be a `C²` holomorphic map, such as the end lift of a cylindrical end, whose real chart is injective
on the rectangle `[α, β] × [γ, δ)` and maps the closed rectangle `[α, β] × [γ, δ]` into an open
set `Ω`. Let the datum `P` and the map `u` into a finite-dimensional manifold with a nondegenerate
two-form be `C¹` on `Ω`, and suppose that in the coordinates of `f` the datum is `g(s) G(t) dt` on
that closed rectangle, for `C¹` functions `g` and `G`. Then over the image of the rectangle the
Floer energy is the symplectic area, plus `g(β)` times the integral of `G` along the image of the
side `s = β`, minus `g(α)` times that along the side `s = α`, minus the integrated curvature. -/
theorem IsNondegenerate.integral_floerEnergyDensity_image_realChart_Icc_prod_Ico
    (hω : ω.IsNondegenerate) (hf : ContDiff ℂ 2 f) (hαβ : α ≤ β) (hγδ : γ ≤ δ)
    (hinj : InjOn (realChart f) (Icc α β ×ˢ Ico γ δ)) (hΩ : IsOpen Ω)
    (hfΩ : ∀ z ∈ Icc α β ×ˢ Icc γ δ, realChart f z ∈ Ω)
    (hP : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : (ℝ × ℝ) × M ↦ P (Complex.equivRealProdCLM.symm p.1) p.2) (Ω ×ˢ univ))
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u Ω) (hg : ContDiff ℝ 1 g)
    (hG : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry G))
    (hPf : ∀ z ∈ Icc α β ×ˢ Icc γ δ, ∀ x v,
      P (f (Complex.equivRealProdCLM.symm z)) x (deriv f (Complex.equivRealProdCLM.symm z) * v) =
        v.im * (g z.1 * G z.2 x)) :
    ∫ z in realChart f '' (Icc α β ×ˢ Ico γ δ), ω.floerEnergyDensity
        (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (∫ z in realChart f '' (Icc α β ×ˢ Ico γ δ),
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (g β * (∫ t in γ..δ, G t (u (realChart f (β, t)))) -
          g α * ∫ t in γ..δ, G t (u (realChart f (α, t)))) -
        ∫ z in realChart f '' (Icc α β ×ˢ Ico γ δ), ω.hamiltonianCurvature
          (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  set φ := realChart f
  set s : Set (ℝ × ℝ) := Icc α β ×ˢ Ico γ δ
  have hφ : ContDiff ℝ 2 φ := TauCeti.Complex.contDiff_realChart hf
  have hmeas : MeasurableSet s := measurableSet_Icc.prod measurableSet_Ico
  have hφd (w : ℝ × ℝ) : DifferentiableAt ℝ φ w := hφ.differentiable (by norm_num) w
  have hdet (w : ℝ × ℝ) : 0 ≤ (fderiv ℝ φ w).det :=
    TauCeti.Complex.det_fderiv_realChart_nonneg (hf.differentiable (by norm_num) _).hasDerivAt
  have hsΩ {w : ℝ × ℝ} (hw : w ∈ s) : φ w ∈ Ω := hfΩ w ⟨hw.1, Ico_subset_Icc_self hw.2⟩
  have hud {w : ℝ × ℝ} (hw : w ∈ s) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (φ w) :=
    (hu.contMDiffAt (hΩ.mem_nhds (hsΩ hw))).mdifferentiableAt one_ne_zero
  have hPm {w : ℝ × ℝ} (hw : w ∈ s) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
        (fun p : (ℝ × ℝ) × M ↦ P (Complex.equivRealProdCLM.symm p.1) p.2) (φ w, x) :=
    hP.contMDiffAt ((hΩ.prod isOpen_univ).mem_nhds ⟨hsΩ hw, mem_univ x⟩)
  have hdom {w : ℝ × ℝ} (hw : w ∈ s) (x : M) (v : ℂ) :
      DifferentiableAt ℝ (fun z ↦ P (Complex.equivRealProdCLM.symm z) x v) (φ w) :=
    (((hPm hw x).comp (φ w) (contMDiffAt_id.prodMk contMDiffAt_const)).clm_apply
      contMDiffAt_const).contDiffAt.differentiableAt one_ne_zero
  have htgt {w : ℝ × ℝ} (hw : w ∈ s) (x : M) (v : ℂ) :
      MDifferentiableAt I 𝓘(ℝ) (fun y ↦ P (Complex.equivRealProdCLM.symm (φ w)) y v) x :=
    (((hPm hw x).comp x (contMDiffAt_const.prodMk contMDiffAt_id)).clm_apply
      contMDiffAt_const).mdifferentiableAt one_ne_zero
  -- Change variables to the coordinates of `f`, in each of the three integrals.
  rw [ω.integral_eval₂_mfderiv_stdComplexLine_image hmeas hinj (fun w _ ↦ hφd w)
      (fun w _ ↦ hdet w) (fun w hw ↦ hud hw),
    ω.integral_floerEnergyDensity_image hmeas hinj (fun w _ ↦ hφd w)
      (fun w _ ↦ hdet w) (fun w hw ↦ hud hw) (fun w hw ↦ htgt hw _ 1)
      (fun w hw ↦ htgt hw _ Complex.I),
    ω.integral_hamiltonianCurvature_image hmeas hinj (fun w _ ↦ hφ.contDiffAt) (fun w _ ↦ hdet w)
      (fun w hw ↦ hdom hw _ 1) (fun w hw ↦ hdom hw _ Complex.I) (fun w hw ↦ htgt hw _ 1)
      (fun w hw ↦ htgt hw _ Complex.I)]
  -- The pulled-back datum, evaluated on a tangent vector `v`, is `P` at `f` on `f' v`.
  have hpb (v : ℝ × ℝ) : perturbationPullback φ (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x Complex.I) v =
        fun w x ↦ P (f (Complex.equivRealProdCLM.symm w)) x
          (deriv f (Complex.equivRealProdCLM.symm w) * Complex.equivRealProdCLM.symm v) := by
    funext w x
    exact perturbationPullback_realChart P (hf.differentiable (by norm_num) _).hasDerivAt v x
  simp only [hpb, equivRealProdCLM_symm_stdComplexLineReal,
    equivRealProdCLM_symm_stdComplexLineImag]
  exact hω.integral_floerEnergyDensity_comp_realChart_Icc_prod_Ico hf hαβ hγδ hΩ hfΩ hP hu hg hG
    hPf

end TauCeti.SmoothTwoForm
