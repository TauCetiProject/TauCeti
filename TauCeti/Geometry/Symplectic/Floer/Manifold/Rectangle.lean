/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# The energy identity over a rectangle of a change of coordinates

Let `φ` be an orientation-preserving change of coordinates of the plane, `C²` on an open set
containing a closed rectangle `[a₁, b₁] × [t₀, t₁]`, along which a Hamiltonian datum `K` pulls
back to the continuation datum `P(s) H(t) dt`, as on a cylindrical end of a punctured surface in
the end coordinates. Over the image under `φ` of the half-open rectangle `[a₁, b₁] × [t₀, t₁)`,
on which `φ` is injective, this file gives the energy identity for a map into a manifold with a
nondegenerate two-form, and the integrability of the curvature.

## Main results

* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_image_of_perturbationPullback`: the
  energy is the symplectic area, plus the boundary terms of the two sides `s = a₁` and `s = b₁`,
  minus the integrated curvature.
* `SmoothTwoForm.integrableOn_hamiltonianCurvature_image_of_perturbationPullback`: the curvature
  is integrable over the image of the half-open rectangle as soon as the map is continuous on a
  set containing the image of the closed rectangle.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1,
  on Hamiltonian perturbations, curvature, and the energy identity.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 8.
-/

public noncomputable section

open Function
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {ω : SmoothTwoForm I M} {Ks Kt : ℝ × ℝ → M → ℝ} {u : ℝ × ℝ → M}

section PerturbationPullback

open Floer MeasureTheory Set Filter Topology

variable {φ : ℝ × ℝ → ℝ × ℝ} {P : ℝ → ℝ} {Hφ : ℝ → M → ℝ} {U V : Set (ℝ × ℝ)}

/-- Let `K` be a datum whose pullback along `φ` is `P(s) H(t) dt` on an open set `U`, with `P` and
`H` of class `C¹`. Along a map `u` continuous on `V`, the curvature of the pullback, in the
coordinates of `φ`, is continuous on every `S ⊆ U` on which `φ` is continuous with `φ(S) ⊆ V`. -/
private theorem continuousOn_hamiltonianCurvature_perturbationPullback (ω : SmoothTwoForm I M)
    {S : Set (ℝ × ℝ)} (hUo : IsOpen U) (hSU : S ⊆ U) (hφ : ContinuousOn φ S) (hSV : MapsTo φ S V)
    (hu : ContinuousOn u V)
    (hs : ∀ w ∈ U, perturbationPullback φ Ks Kt stdComplexLineReal w = 0)
    (ht : ∀ w ∈ U, perturbationPullback φ Ks Kt stdComplexLineImag w = fun x ↦ P w.1 * Hφ w.2 x)
    (hP : ContDiff ℝ 1 P) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry Hφ)) :
    ContinuousOn (fun w ↦ ω.hamiltonianCurvature (perturbationPullback φ Ks Kt stdComplexLineReal)
      (perturbationPullback φ Ks Kt stdComplexLineImag) w (u (φ w))) S :=
  (((hP.continuous_deriv le_rfl).comp continuous_fst).continuousOn.mul
    (hH.continuous.comp_continuousOn (continuousOn_snd.prodMk
      (hu.comp hφ hSV)))).congr fun _ hw ↦
    have hev : ∀ᶠ w' in 𝓝 _, w' ∈ U := hUo.mem_nhds (hSU hw)
    ω.hamiltonianCurvature_eq_deriv_mul_of_eventuallyEq (hev.mono hs) (hev.mono ht)
      (hP.differentiable one_ne_zero _)
      ((hH.curry_left (y := _)).contDiff.differentiable one_ne_zero _)

/-- **The curvature over the image of a rectangle is integrable.** Let `φ` be an
orientation-preserving change of coordinates, `C²` on an open set `U` containing the closed
rectangle `[a₁, b₁] × [t₀, t₁]`, and `K` a datum, jointly differentiable over `φ(U)`, whose
pullback along `φ` is the continuation datum `P(s) H(t) dt` on `U`, with `P` and `H` of class
`C¹`. Let `u` be continuous on a set `V` containing the image of the closed rectangle. Then the
curvature `R_K(u)` is integrable over the image under `φ` of the rectangle `[a₁, b₁] × [t₀, t₁)`,
on which `φ` is injective. -/
theorem integrableOn_hamiltonianCurvature_image_of_perturbationPullback (ω : SmoothTwoForm I M)
    {a₁ b₁ t₀ t₁ : ℝ} (hUo : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U)
    (hdet : ∀ w ∈ U, 0 ≤ (fderiv ℝ φ w).det) (hUV : MapsTo φ (Icc a₁ b₁ ×ˢ Icc t₀ t₁) V)
    (hu : ContinuousOn u V)
    (hKs : ∀ w ∈ U, ∀ x, MDifferentiableAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (uncurry Ks) (φ w, x))
    (hKt : ∀ w ∈ U, ∀ x, MDifferentiableAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (uncurry Kt) (φ w, x))
    (hs : ∀ w ∈ U, perturbationPullback φ Ks Kt stdComplexLineReal w = 0)
    (ht : ∀ w ∈ U, perturbationPullback φ Ks Kt stdComplexLineImag w = fun x ↦ P w.1 * Hφ w.2 x)
    (hP : ContDiff ℝ 1 P) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry Hφ))
    (hrect : Icc a₁ b₁ ×ˢ Icc t₀ t₁ ⊆ U) (hinj : InjOn φ (Icc a₁ b₁ ×ˢ Ico t₀ t₁)) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z))
      (φ '' (Icc a₁ b₁ ×ˢ Ico t₀ t₁)) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hmeas : MeasurableSet (Icc a₁ b₁ ×ˢ Ico t₀ t₁) := measurableSet_Icc.prod measurableSet_Ico
  have hsub : Icc a₁ b₁ ×ˢ Ico t₀ t₁ ⊆ Icc a₁ b₁ ×ˢ Icc t₀ t₁ :=
    prod_mono subset_rfl Ico_subset_Icc_self
  have hφU {w : ℝ × ℝ} (hw : w ∈ U) : ContDiffAt ℝ 2 φ w := hφ.contDiffAt (hUo.mem_nhds hw)
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hmeas
    (fun w hw ↦ ((hφU (hrect (hsub hw))).differentiableAt (by norm_num)).hasFDerivAt
      |>.hasFDerivWithinAt) hinj]
  -- In the coordinates of `φ` the curvature, times the Jacobian, is continuous on the rectangle.
  refine (((ω.continuousOn_hamiltonianCurvature_perturbationPullback hUo hrect
    (hφ.continuousOn.mono hrect) hUV hu hs ht hP hH).integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set hsub).congr_fun (fun w hw ↦ ?_) hmeas
  have hwU := hrect (hsub hw)
  rw [abs_of_nonneg (hdet w hwU), smul_eq_mul, ← ω.hamiltonianCurvature_perturbationPullback
    (hφU hwU) (hKs w hwU _).curry_left.differentiableAt
    (hKt w hwU _).curry_left.differentiableAt (hKs w hwU _).curry_right
    (hKt w hwU _).curry_right]

/-- **The energy identity over the image of a rectangle, for a manifold target.** Let `φ` be an
orientation-preserving change of coordinates of the plane, `C²` on an open set `U` containing the
closed rectangle `[a₁, b₁] × [t₀, t₁]`, and `K` a datum, jointly differentiable over `φ(U)`, whose
pullback along `φ` is the continuation datum `P(s) H(t) dt` on `U`, with `P` and `H` of class
`C¹`, as on a cylindrical end of a punctured surface in the end coordinates. Let `u` be `C¹` on an
open set `V ⊇ φ(U)`, for a nondegenerate two-form on a
finite-dimensional manifold. Over the image under `φ` of the rectangle `[a₁, b₁] × [t₀, t₁)`, on
which `φ` is injective, the Floer energy is the symplectic area, plus the boundary term
`P(b₁) ∫ H(t, u(φ(b₁, t))) dt - P(a₁) ∫ H(t, u(φ(a₁, t))) dt` of the two sides `s = b₁` and
`s = a₁`, minus the integrated curvature. The densities are integrable automatically. -/
theorem IsNondegenerate.integral_floerEnergyDensity_image_of_perturbationPullback
    [FiniteDimensional ℝ E] (hω : ω.IsNondegenerate) (hUo : IsOpen U) (hVo : IsOpen V)
    (hφ : ContDiffOn ℝ 2 φ U) (hdet : ∀ w ∈ U, 0 ≤ (fderiv ℝ φ w).det) (hUV : MapsTo φ U V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V)
    (hKs : ∀ w ∈ U, ∀ x, MDifferentiableAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (uncurry Ks) (φ w, x))
    (hKt : ∀ w ∈ U, ∀ x, MDifferentiableAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (uncurry Kt) (φ w, x))
    (hs : ∀ w ∈ U, perturbationPullback φ Ks Kt stdComplexLineReal w = 0)
    (ht : ∀ w ∈ U, perturbationPullback φ Ks Kt stdComplexLineImag w = fun x ↦ P w.1 * Hφ w.2 x)
    (hP : ContDiff ℝ 1 P) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry Hφ))
    {a₁ b₁ t₀ t₁ : ℝ} (hab : a₁ ≤ b₁) (ht₀₁ : t₀ ≤ t₁) (hrect : Icc a₁ b₁ ×ˢ Icc t₀ t₁ ⊆ U)
    (hinj : InjOn φ (Icc a₁ b₁ ×ˢ Ico t₀ t₁)) :
    ∫ z in φ '' (Icc a₁ b₁ ×ˢ Ico t₀ t₁), ω.floerEnergyDensity Ks Kt u z =
      (∫ z in φ '' (Icc a₁ b₁ ×ˢ Ico t₀ t₁), (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (P b₁ * (∫ t in t₀..t₁, Hφ t (u (φ (b₁, t)))) -
          P a₁ * ∫ t in t₀..t₁, Hφ t (u (φ (a₁, t)))) -
        ∫ z in φ '' (Icc a₁ b₁ ×ˢ Ico t₀ t₁), ω.hamiltonianCurvature Ks Kt z (u z) := by
  set Ks' := perturbationPullback φ Ks Kt stdComplexLineReal
  set Kt' := perturbationPullback φ Ks Kt stdComplexLineImag
  have hmeas : MeasurableSet (Icc a₁ b₁ ×ˢ Ico t₀ t₁) := measurableSet_Icc.prod measurableSet_Ico
  have hφU {w : ℝ × ℝ} (hw : w ∈ U) : ContDiffAt ℝ 2 φ w := hφ.contDiffAt (hUo.mem_nhds hw)
  have hud {w : ℝ × ℝ} (hw : w ∈ U) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (φ w) :=
    (hu.contMDiffAt (hVo.mem_nhds (hUV hw))).mdifferentiableAt one_ne_zero
  have hsU {w : ℝ × ℝ} (hw : w ∈ Icc a₁ b₁ ×ˢ Ico t₀ t₁) : w ∈ U :=
    hrect ⟨hw.1, Ico_subset_Icc_self hw.2⟩
  have hφd {w : ℝ × ℝ} (hw : w ∈ Icc a₁ b₁ ×ˢ Ico t₀ t₁) : DifferentiableAt ℝ φ w :=
    (hφU (hsU hw)).differentiableAt (by norm_num)
  -- Change variables to the coordinates of `φ`, in each of the three integrals.
  rw [ω.integral_eval₂_mfderiv_stdComplexLine_image hmeas hinj (fun w hw ↦ hφd hw)
      (fun w hw ↦ hdet w (hsU hw)) (fun w hw ↦ hud (hsU hw)),
    ω.integral_floerEnergyDensity_image hmeas hinj (fun w hw ↦ hφd hw)
      (fun w hw ↦ hdet w (hsU hw)) (fun w hw ↦ hud (hsU hw))
      (fun w hw ↦ (hKs w (hsU hw) _).curry_right) (fun w hw ↦ (hKt w (hsU hw) _).curry_right),
    ω.integral_hamiltonianCurvature_image hmeas hinj (fun w hw ↦ hφU (hsU hw))
      (fun w hw ↦ hdet w (hsU hw))
      (fun w hw ↦ (hKs w (hsU hw) _).curry_left.differentiableAt)
      (fun w hw ↦ (hKt w (hsU hw) _).curry_left.differentiableAt)
      (fun w hw ↦ (hKs w (hsU hw) _).curry_right) (fun w hw ↦ (hKt w (hsU hw) _).curry_right)]
  -- The half-open rectangle and the closed one differ by a null set.
  have hae : Icc a₁ b₁ ×ˢ Ico t₀ t₁ =ᵐ[volume] Icc ((a₁, t₀) : ℝ × ℝ) (b₁, t₁) := by
    rw [Icc_prod_eq, Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Filter.EventuallyEqSet.rfl Ico_ae_eq_Icc
  simp only [setIntegral_congr_set hae]
  have hIccU : Icc ((a₁, t₀) : ℝ × ℝ) (b₁, t₁) ⊆ U := by
    rw [Icc_prod_eq]
    exact hrect
  -- In the coordinates of `φ` the datum is `P(s) H(t) dt`, and its curvature is `P'(s) H(t)`.
  have hu' : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ φ) U :=
    hu.comp ((hφ.of_le (by norm_num)).contMDiffOn) hUV
  have hKs' : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Ks') (U ×ˢ univ) :=
    (contMDiffOn_const (c := (0 : ℝ))).congr fun p hp ↦ congrFun (hs p.1 hp.1) p.2
  have hPH : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 fun p : (ℝ × ℝ) × M ↦
      P p.1.1 * Hφ p.1.2 p.2 :=
    ((hP.comp contDiff_fst).contMDiff.comp contMDiff_fst).smul
      (hH.comp ((contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd))
  have hKt' : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Kt') (U ×ˢ univ) :=
    hPH.contMDiffOn.congr fun p hp ↦ congrFun (ht p.1 hp.1) p.2
  have hR : IntegrableOn (fun w ↦ ω.hamiltonianCurvature Ks' Kt' w ((u ∘ φ) w))
      (Icc ((a₁, t₀) : ℝ × ℝ) (b₁, t₁)) :=
    (ω.continuousOn_hamiltonianCurvature_perturbationPullback hUo hIccU
      (hφ.continuousOn.mono hIccU) (hUV.mono_left hIccU) hu.continuousOn hs ht hP
      hH).integrableOn_compact isCompact_Icc
  have hE := hω.integrableOn_floerEnergyDensity hUo hu' hKs' hKt' isCompact_Icc hIccU hR
  rw [hω.integral_floerEnergyDensity hUo hu' hKs' hKt' (Prod.mk_le_mk.2 ⟨hab, ht₀₁⟩) hIccU
    hE hR]
  -- The `ds` components vanish, and the `dt` components are `P(s) H(t)`.
  have hs₀ {c : ℝ} (hc : c ∈ Icc t₀ t₁) : ∫ s in a₁..b₁, Ks' (s, c) ((u ∘ φ) (s, c)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ 0) fun s hs' ↦ ?_,
      intervalIntegral.integral_zero]
    rw [uIcc_of_le hab] at hs'
    exact congrFun (hs (s, c) (hrect ⟨hs', hc⟩)) _
  have ht₀ {c : ℝ} (hc : c ∈ Icc a₁ b₁) :
      ∫ t in t₀..t₁, Kt' (c, t) ((u ∘ φ) (c, t)) = P c * ∫ t in t₀..t₁, Hφ t (u (φ (c, t))) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht' ↦ ?_
    rw [uIcc_of_le ht₀₁] at ht'
    exact congrFun (ht (c, t) (hrect ⟨hc, ht'⟩)) _
  rw [hs₀ ⟨le_rfl, ht₀₁⟩, hs₀ ⟨ht₀₁, le_rfl⟩, ht₀ ⟨le_rfl, hab⟩, ht₀ ⟨hab, le_rfl⟩]
  simp only [Function.comp_apply, Ks', Kt']
  ring

end PerturbationPullback

end TauCeti.SmoothTwoForm
